"""OSS Verify-built fuzz targets and projects absent from OSS-Fuzz."""
import hashlib
import io
import os
import re
import subprocess
import tempfile
import unittest

from oft import facts, fetch, lint, schema
from oft.tests.helpers import FIXTURE_RECIPE, build_record, older_shape, tree


PORT = {
    "repository": "theorem-labs/oss-verify",
    "commit": "d" * 40,
    "path": "projects/standin",
}


PORT_ASSET = {
    "release": "v2026.11.0",
    "file": "standin-port.tar.zst",
    "bytes": 1000,
    "sha256": "9" * 64,
}

def add_standin(t, port=True):
    """Add a standalone OSS Verify-built stand-in project (a name no real project has), built like GNU make, to a fixture copy."""
    release = t.yaml("release.yaml")
    release["counts"]["projects"] += 1
    release["counts"]["available"] += 1
    release["counts"]["harnesses"] += 1
    release["counts"]["binaries"] += 1
    t.put_yaml("release.yaml", release)
    build = {
        "system": "make",
        "clang": "20.1.8",
        "builder": release["images"]["builder"][0],
    }
    if port:
        build["oss_verify"] = PORT
    t.put_yaml("projects/standin/project.yaml", {
        "schema": "oss-fuzz-theorems/project/1",
        "project": "standin",
        "description": "A build automation tool",
        "homepage": "https://www.gnu.org/software/make/",
        "language": "c",
        "status": "available",
        "library": {
            "name": "GNU make",
            "repository": "https://git.savannah.gnu.org/git/make.git",
            "commit": "a" * 40,
            "version": "4.4",
            "licence": "GPL-3.0-or-later",
        },
        "harnesses": [{"name": "standin_eval_fuzzer", "status": "included", "origin": "oss-verify"}],
        "assets": {
            "bin": {"release": "v2026.11.0", "file": "standin-bin.tar.zst", "bytes": 1000, "sha256": "e" * 64},
            "src": {"release": "v2026.11.0", "file": "standin-src.tar.zst", "bytes": 1000, "sha256": "f" * 64},
            "src_manifest": {"release": "v2026.11.0", "file": "standin-src.MANIFEST.tsv", "bytes": 1000, "sha256": "0" * 64},
            "port": PORT_ASSET,
        },
        "build": build,
    })
    t.put_yaml("projects/standin/standin_eval_fuzzer/harness.yaml", {
        "schema": "oss-fuzz-theorems/harness/1",
        "project": "standin",
        "harness": "standin_eval_fuzzer",
        "rocq": "OssFuzzTheorems.standin.standin_eval_fuzzer",
        "origin": "oss-verify",
        "summary": "Evaluates an input makefile.",
        "entry": "LLVMFuzzerTestOneInput",
        "source": {
            "files": ["source/standin_eval_fuzzer.c"],
            "from": {"repository": "theorem-labs/oss-verify", "commit": "d" * 40,
                     "path": "projects/standin/standin_eval_fuzzer.c"},
            "modified": True,
            "licence": "GPL-3.0-or-later",
        },
        "library": {
            "repository": "https://git.savannah.gnu.org/git/make.git",
            "commit": "a" * 40,
            "version": "4.4",
            "licence": "GPL-3.0-or-later",
        },
        "modifications": ["The release driver passes the input file to the fuzz target."],
        "builds": {
            "plain": {"file": "standin_eval_fuzzer.plain", "bytes": 1000, "sha256": "1" * 64,
                      "segments": [1]},
        },
        "licence": "GPL-3.0-or-later",
        "checks": [],
        "statements": {
            "plain_halts": {"kind": "halts", "builds": ["plain"], "reading": "budget", "exits": [0, 2],
                            "status": "open"},
        },
    })
    t.write("projects/standin/standin_eval_fuzzer/source/standin_eval_fuzzer.c", "int LLVMFuzzerTestOneInput(void) { return 0; }\n")


def add_json_oss_verify_target(t):
    """Add a target OSS Verify builds alongside an OSS-Fuzz project target."""
    release = t.yaml("release.yaml")
    release["counts"]["harnesses"] += 1
    release["counts"]["binaries"] += 1
    t.put_yaml("release.yaml", release)
    project = t.yaml("projects/json/project.yaml")
    project["harnesses"].append({"name": "fuzz-extra", "status": "included", "origin": "oss-verify"})
    project["build"]["oss_verify"] = dict(PORT, path="projects/json")
    del project["assets"]["bin"]["recipe"]   # the port built the archive, and no recipe
    project["assets"].update({
        "src": {"release": "v2026.11.0", "file": "json-src.tar.zst", "bytes": 1000, "sha256": "3" * 64},
        "src_manifest": {"release": "v2026.11.0", "file": "json-src.MANIFEST.tsv", "bytes": 1000,
                         "sha256": "4" * 64},
        "port": dict(PORT_ASSET, file="json-port.tar.zst"),
    })
    t.put_yaml("projects/json/project.yaml", project)
    t.put_yaml("projects/json/fuzz-extra/harness.yaml", {
        "schema": "oss-fuzz-theorems/harness/1",
        "project": "json",
        "harness": "fuzz-extra",
        "rocq": "OssFuzzTheorems.json.fuzz_extra",
        "origin": "oss-verify",
        "summary": "Exercises an additional parser entry point.",
        "entry": "LLVMFuzzerTestOneInput",
        "source": {
            "files": ["source/fuzz-extra.c"],
            "from": {"repository": "https://github.com/nlohmann/json", "commit": "9" * 40,
                     "path": "test/fuzz-extra.c"},
            "modified": False,
            "licence": "MIT",
        },
        "library": {"repository": "https://github.com/nlohmann/json", "commit": "9" * 40, "licence": "MIT"},
        "modifications": [],
        "builds": {
            "plain": {"file": "fuzz-extra.plain", "bytes": 1000, "sha256": "2" * 64, "segments": [1]},
        },
        "licence": "MIT",
        "checks": [],
        "statements": {
            "plain_halts": {"kind": "halts", "builds": ["plain"], "reading": "budget", "exits": [0, 2],
                            "status": "open"},
        },
    })
    t.write("projects/json/fuzz-extra/source/fuzz-extra.c", "int LLVMFuzzerTestOneInput(void) { return 0; }\n")


def add_sqlpage(t):
    """Add a Rust project OSS-Fuzz does not have, whose own fuzz target (origin upstream) the port builds, as
    SQLPage's sql_file is: a plain and a UBSan build, one halts and one agreement statement."""
    release = t.yaml("release.yaml")
    release["counts"]["projects"] += 1
    release["counts"]["available"] += 1
    release["counts"]["harnesses"] += 1
    release["counts"]["binaries"] += 2
    t.put_yaml("release.yaml", release)
    repo, commit = "https://github.com/sqlpage/SQLPage", "b" * 40
    t.put_yaml("projects/sqlpage/project.yaml", {
        "schema": "oss-fuzz-theorems/project/1",
        "project": "sqlpage",
        "description": "A web server that runs applications written as SQL files",
        "homepage": "https://sql-page.com/",
        "language": "rust",
        "status": "available",
        "library": {"name": "SQLPage", "repository": repo, "commit": commit, "version": "0.47.0", "licence": "MIT"},
        "harnesses": [{"name": "sql_file", "status": "included", "origin": "upstream"}],
        "assets": {
            "bin": {"release": "v2026.11.0", "file": "sqlpage-bin.tar.zst", "bytes": 1000, "sha256": "5" * 64},
            "src": {"release": "v2026.11.0", "file": "sqlpage-src.tar.zst", "bytes": 1000, "sha256": "6" * 64},
            "src_manifest": {"release": "v2026.11.0", "file": "sqlpage-src.MANIFEST.tsv", "bytes": 1000,
                             "sha256": "7" * 64},
            "port": dict(PORT_ASSET, file="sqlpage-port.tar.zst"),
        },
        "build": {"system": "cargo", "clang": "20.1.8", "builder": release["images"]["builder"][0],
                  "oss_verify": dict(PORT, path="projects/sqlpage")},
    })
    t.put_yaml("projects/sqlpage/sql_file/harness.yaml", {
        "schema": "oss-fuzz-theorems/harness/1",
        "project": "sqlpage",
        "harness": "sql_file",
        "rocq": "OssFuzzTheorems.sqlpage.sql_file",
        "origin": "upstream",
        "summary": "Compiles the payload as a SQLPage SQL file for the database its first byte picks.",
        "entry": "LLVMFuzzerTestOneInput",
        "source": {
            "files": ["source/sql_file.rs"],
            "from": {"repository": repo, "commit": commit, "path": "fuzz/fuzz_targets/sql_file.rs"},
            "modified": False,
            "licence": "MIT",
        },
        "library": {"repository": repo, "commit": commit, "version": "0.47.0", "licence": "MIT"},
        "modifications": ["The fuzz target is linked as a static library with the driver, not with libFuzzer."],
        "builds": {
            "plain": {"file": "sql_file.plain", "bytes": 1000, "sha256": "8" * 64, "segments": [1]},
            "ubsan": {"file": "sql_file.ubsan", "bytes": 1000, "sha256": "9" * 64, "segments": [1]},
        },
        "licence": "NOASSERTION",
        "checks": [],
        "statements": {
            "plain_halts": {"kind": "halts", "builds": ["plain"], "reading": "budget", "exits": [0, 2],
                            "status": "open"},
            "ubsan_agrees": {"kind": "agreement", "builds": ["plain", "ubsan"], "reading": "alloc-forced-only",
                             "budgets": "standard", "status": "open"},
        },
    })
    t.write("projects/sqlpage/sql_file/source/sql_file.rs", "fuzz_target!(|data: &[u8]| {});\n")


def add_python_target(t):
    """Add a Python project OSS-Fuzz does not have, whose fuzz target OSS Verify builds (origin oss-verify): four
    builds, a check that raises, a halts statement and three alloc-forced-only agreement statements."""
    release = t.yaml("release.yaml")
    release["counts"]["projects"] += 1
    release["counts"]["available"] += 1
    release["counts"]["harnesses"] += 1
    release["counts"]["binaries"] += 4
    t.put_yaml("release.yaml", release)
    repo, commit = "https://github.com/example/pyhtml", "c" * 40
    t.put_yaml("projects/pyhtml/project.yaml", {
        "schema": "oss-fuzz-theorems/project/1",
        "project": "pyhtml",
        "description": "A Python library that turns HTML into text",
        "homepage": "https://github.com/example/pyhtml",
        "language": "python",
        "status": "available",
        "library": {"name": "pyhtml", "repository": repo, "commit": commit, "version": "1.0.0", "licence": "MIT"},
        "harnesses": [{"name": "fuzz_html", "status": "included", "origin": "oss-verify"}],
        "assets": {
            "bin": {"release": "v2026.11.0", "file": "pyhtml-bin.tar.zst", "bytes": 1000, "sha256": "5" * 64},
            "src": {"release": "v2026.11.0", "file": "pyhtml-src.tar.zst", "bytes": 1000, "sha256": "6" * 64},
            "src_manifest": {"release": "v2026.11.0", "file": "pyhtml-src.MANIFEST.tsv", "bytes": 1000,
                             "sha256": "7" * 64},
            "port": dict(PORT_ASSET, file="pyhtml-port.tar.zst"),
        },
        "build": {"system": "custom", "clang": "20.1.8", "builder": release["images"]["builder"][0],
                  "oss_verify": dict(PORT, path="projects/pyhtml")},
    })
    t.put_yaml("projects/pyhtml/fuzz_html/harness.yaml", {
        "schema": "oss-fuzz-theorems/harness/1",
        "project": "pyhtml",
        "harness": "fuzz_html",
        "rocq": "OssFuzzTheorems.pyhtml.fuzz_html",
        "origin": "oss-verify",
        "summary": "Turns the payload into text with the library's HTML tokenizer.",
        "entry": "LLVMFuzzerTestOneInput",
        "source": {
            "files": ["source/fuzz_html.py"],
            "from": {"repository": "theorem-labs/oss-verify", "commit": "d" * 40,
                     "path": "projects/pyhtml/fuzz_html.py"},
            "modified": False,
            "licence": "Apache-2.0",
        },
        "library": {"repository": repo, "commit": commit, "version": "1.0.0", "licence": "MIT"},
        "modifications": ["The harness runs in a static CPython linked with the driver, not under atheris."],
        "failure_handlers": "none",
        "builds": {
            "plain": {"file": "fuzz_html.plain", "bytes": 1000, "sha256": "8" * 64, "segments": [1]},
            "ubsan": {"file": "fuzz_html.ubsan", "bytes": 1000, "sha256": "9" * 64, "segments": [1]},
            "asan": {"file": "fuzz_html.asan", "bytes": 1000, "sha256": "a" * 64, "segments": [1]},
            "asan-ubsan": {"file": "fuzz_html.asan-ubsan", "bytes": 1000, "sha256": "b" * 64, "segments": [1]},
        },
        "licence": "NOASSERTION",
        "checks": [{"kind": "invariant", "strength": "full", "stops_with": "raise", "live": True,
                    "where": "source/fuzz_html.py:2", "what": "The text comes back unchanged."}],
        "statements": {
            "plain_halts": {"kind": "halts", "builds": ["plain"], "reading": "budget", "exits": [0, 2],
                            "binds_checks": True, "status": "open"},
            "asan_agrees": {"kind": "agreement", "builds": ["plain", "asan"], "reading": "alloc-forced-only",
                            "budgets": "asan", "status": "open"},
            "ubsan_agrees": {"kind": "agreement", "builds": ["plain", "ubsan"], "reading": "alloc-forced-only",
                             "budgets": "standard", "status": "open"},
            "asan_ubsan_agrees": {"kind": "agreement", "builds": ["plain", "asan-ubsan"],
                                  "reading": "alloc-forced-only", "budgets": "asan", "status": "open"},
        },
    })
    t.write("projects/pyhtml/fuzz_html/source/fuzz_html.py",
            "def TestOneInput(data):\n    _check(text(data) == text(data), \"P1: changed\")\n")


# the port's Go toolchain image, its row in the port's infra/toolchains.tsv
GO_IMAGE = ("ghcr.io/theorem-labs/oss-fuzz-theorems-toolchain-go@"
            "sha256:bb18d9228adb8ffc003ab49c0ae39b485da9814d583f2c53324b95d69ebe54a8")


def add_go_target(t):
    """Add a Go project OSS-Fuzz does not have, whose fuzz target OSS Verify builds (origin oss-verify), as go-yaml's
    FuzzDecode is: the plain build only, a check that ends with t.Fatal, and one halts statement with exits {0, 2}."""
    release = t.yaml("release.yaml")
    release["counts"]["projects"] += 1
    release["counts"]["available"] += 1
    release["counts"]["harnesses"] += 1
    release["counts"]["binaries"] += 1
    release["images"]["builder"].append(GO_IMAGE)
    t.put_yaml("release.yaml", release)
    repo, commit = "https://github.com/example/goyaml", "e" * 40
    t.put_yaml("projects/goyaml/project.yaml", {
        "schema": "oss-fuzz-theorems/project/1",
        "project": "goyaml",
        "description": "A YAML library for Go",
        "homepage": "https://github.com/example/goyaml",
        "language": "go",
        "status": "available",
        "library": {"name": "goyaml", "repository": repo, "commit": commit, "version": "3.0.5", "licence": "MIT"},
        "harnesses": [{"name": "fuzz_decode", "status": "included", "origin": "oss-verify"}],
        "assets": {
            "bin": {"release": "v2026.11.0", "file": "goyaml-bin.tar.zst", "bytes": 1000, "sha256": "5" * 64},
            "src": {"release": "v2026.11.0", "file": "goyaml-src.tar.zst", "bytes": 1000, "sha256": "6" * 64},
            "src_manifest": {"release": "v2026.11.0", "file": "goyaml-src.MANIFEST.tsv", "bytes": 1000,
                             "sha256": "7" * 64},
            "port": dict(PORT_ASSET, file="goyaml-port.tar.zst"),
        },
        "build": {"system": "go", "go": "1.27.1", "builder": GO_IMAGE,
                  "oss_verify": dict(PORT, path="projects/goyaml")},
    })
    t.put_yaml("projects/goyaml/fuzz_decode/harness.yaml", {
        "schema": "oss-fuzz-theorems/harness/1",
        "project": "goyaml",
        "harness": "fuzz_decode",
        "rocq": "OssFuzzTheorems.goyaml.fuzz_decode",
        "origin": "oss-verify",
        "summary": "Decodes the payload as YAML and fails when a decoded value does not encode again.",
        "entry": "FuzzDecode",
        "source": {
            "files": ["source/fuzz_test.go"],
            "from": {"repository": "theorem-labs/oss-verify", "commit": "d" * 40,
                     "path": "projects/goyaml/fuzz_test.go"},
            "modified": False,
            "licence": "Apache-2.0",
        },
        "library": {"repository": repo, "commit": commit, "version": "3.0.5", "licence": "MIT"},
        "modifications": ["The fuzz test runs under the port's patched Go runtime and Go driver, not libFuzzer."],
        "failure_handlers": "none",
        "builds": {
            "plain": {"file": "fuzz_decode.plain", "bytes": 1000, "sha256": "8" * 64, "segments": [1]},
        },
        "licence": "NOASSERTION",
        "checks": [{"kind": "roundtrip", "strength": "partial", "stops_with": "fail", "live": True,
                    "where": "source/fuzz_test.go:3", "what": "A decoded value encodes again."}],
        "statements": {
            "plain_halts": {"kind": "halts", "builds": ["plain"], "reading": "budget", "exits": [0, 2],
                            "binds_checks": True, "status": "open"},
        },
    })
    t.write("projects/goyaml/fuzz_decode/source/fuzz_test.go",
            "func FuzzDecode(f *testing.F) {\n\tf.Fuzz(func(t *testing.T, b []byte) {\n"
            "\t\tif err := check(b); err != nil { t.Fatal(err) }\n\t})\n}\n")


# a port-built build record in the shape docs/adding-a-proof.md gives: the port's project directory and the
# tools/check manifest under port/, in place of recipe/
MAKE_RECORD = {
    "PROVENANCE.yaml": "schema: x\n",
    "PROVENANCE.md": "# Build record\n",
    "port/manifest.yaml": "project: standin\n",
    "port/projects/standin/Dockerfile": "RUN fetch-commit $SRC/standin\n",
    "port/projects/standin/build.sh": "make\n",
    "port/projects/standin/sources": "git\tgnulib\thttps://github.com/coreutils/gnulib\t" + "2" * 40 + "\n",
    "LICENSES/standin-COPYING": "GPL\n",
}


def add_record(t, project, harness, files):
    """Write a build record under proofs/<project>/<harness>/provenance/."""
    for rel, text in files.items():
        t.write("proofs/%s/%s/provenance/%s" % (project, harness, rel), text)


class Rendering(unittest.TestCase):
    def test_an_oss_verify_target_has_its_own_rendered_wording(self):
        with tree(render=False) as t:
            add_standin(t)
            self.assertEqual(t.generate(), 0, t.last_output)
            page = t.read("projects/standin/README.md")
            harness = t.read("projects/standin/standin_eval_fuzzer/README.md")
            statements = t.read("projects/standin/standin_eval_fuzzer/Statements.v")
            readme = t.read("README.md")
            status = t.read("index/STATUS.md")
            projects = t.read("index/projects.tsv")
        self.assertIn("OSS-Fuzz: no project for standin", page)
        self.assertNotIn("github.com/google/oss-fuzz/tree/", page)
        self.assertIn("theorem-labs/oss-verify", page)
        self.assertNotIn("github.com/" + "theorem-labs/oss-verify/", page)
        self.assertIn("standin-port.tar.zst", page)
        self.assertTrue(all(piece in page for piece in ("infra/", "tools/", "projects/standin/", "tools/check")))
        self.assertIn("; a testcase needs", page)
        self.assertNotIn("cannot be rebuilt from this release alone", page)
        self.assertIn("OSS Verify builds and OSS-Fuzz does not run", harness)
        self.assertIn("How this program differs from a libFuzzer build of this fuzz target", harness)
        self.assertIn("which OSS Verify builds and OSS-Fuzz does not run", " ".join(statements.split()))
        self.assertIn("For each of the 5 projects in OSS-Fuzz", readme)
        self.assertTrue(any("`standin`" in sentence and "OSS-Fuzz has no project" in sentence and "it." in sentence
                            for sentence in readme.splitlines()))
        self.assertIn("all projects", readme)
        self.assertIn("Status of every project", status)
        self.assertTrue(any("`standin`" in sentence and "OSS-Fuzz has no project" in sentence and "it." in sentence
                            for sentence in status.splitlines()))
        self.assertIn("standin\tc\tavailable\t-\t0\t0", projects)

    def test_an_oss_verify_target_without_a_homepage_has_no_oss_fuzz_link(self):
        with tree(render=False) as t:
            add_standin(t)
            project = t.yaml("projects/standin/project.yaml")
            del project["homepage"]
            t.put_yaml("projects/standin/project.yaml", project)
            self.assertEqual(t.generate(), 0, t.last_output)
            page = t.read("projects/standin/README.md")
        self.assertIn("OSS-Fuzz: no project for standin", page)
        self.assertNotIn("https://github.com/google/oss-fuzz/tree/", page)

    def test_without_an_oss_verify_project_the_root_pages_keep_the_oss_fuzz_scope(self):
        with tree() as t:
            readme = t.read("README.md")
            status = t.read("index/STATUS.md")
        self.assertIn("For each of the 5 projects in OSS-Fuzz", readme)
        self.assertIn("all OSS-Fuzz projects", readme)
        self.assertNotIn("It also has project directories for", readme)
        self.assertIn("# Status of every OSS-Fuzz project", status)
        self.assertNotIn("For a project OSS-Fuzz has no project for", status)

    def test_root_pages_name_every_project_absent_from_oss_fuzz(self):
        with tree(render=False) as t:
            add_standin(t)
            project = t.yaml("projects/tcmalloc/project.yaml")
            del project["oss_fuzz"]
            t.put_yaml("projects/tcmalloc/project.yaml", project)
            release = t.yaml("release.yaml")
            release["oss_fuzz"]["projects"] -= 1
            t.put_yaml("release.yaml", release)
            self.assertEqual(t.generate(), 0, t.last_output)
            readme = t.read("README.md")
            status = t.read("index/STATUS.md")
        for page in (readme, status):
            self.assertIn("`standin`", page)
            self.assertIn("`tcmalloc`", page)
            self.assertIn("them.", page)
            self.assertNotIn("OSS Verify builds fuzz targets", page)

    def test_the_oss_fuzz_counts_leave_out_what_oss_verify_builds(self):
        """The paragraph on OSS-Fuzz's fuzz targets counts OSS-Fuzz's projects and their OSS-Fuzz targets alone, as the
        project pages do: a project OSS-Fuzz does not have, or a target OSS Verify builds in a project it has, leaves
        those counts as they were, while the count of every available project still takes it in.  The fixture's zlib
        has statements for 1 of OSS-Fuzz's 2 fuzz targets, plus an API driver, which is not a fuzz target."""
        oss_fuzz = "We can build the fuzz targets of 2 of these projects. 2 of their 3 fuzz targets have statements"
        for add, every in ((None, "The 2 available projects have 3 harnesses"),
                           (add_standin, "The 3 available projects have 4 harnesses"),
                           (add_json_oss_verify_target, "The 2 available projects have 4 harnesses")):
            with self.subTest(add=add and add.__name__), tree(render=False) as t:
                if add:
                    add(t)
                self.assertEqual(t.generate(), 0, t.last_output)
                readme = t.read("README.md")
                self.assertEqual(re.search(r"We can build the fuzz targets of .*? have statements", readme).group(),
                                 oss_fuzz)
                self.assertIn(every, readme)

    def test_an_oss_verify_target_is_separate_from_oss_fuzz_coverage(self):
        with tree(render=False) as t:
            add_json_oss_verify_target(t)
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertEqual([str(f) for f in t.lint()], [])
            page = t.read("projects/json/README.md")
            status = t.read("index/STATUS.md")
            opam = t.read("projects/json/rocq-oss-fuzz-theorems-json.opam")
            dune = t.read("dune-project")
            projects = t.read("index/projects.tsv")
        self.assertIn("OSS Verify builds and OSS-Fuzz does not run", page)
        self.assertIn("statements cover 1 of 1", page)
        self.assertIn("| 2 of 2 |", next(line for line in status.splitlines() if "../projects/json/" in line))
        self.assertIn("Theorem statements about json's fuzz targets, in Rocq", opam)
        self.assertIn('(synopsis "Theorem statements about json\'s fuzz targets")', dune)
        self.assertIn("; a testcase needs", page)
        self.assertNotIn("an OSS-Fuzz testcase", page)

    def test_a_project_whose_every_harness_is_modified_names_no_others(self):
        with tree(render=False) as t:
            add_standin(t)
            self.assertEqual(t.generate(), 0, t.last_output)
            page = t.read("projects/standin/README.md")
        self.assertIn("the harness files are modified in `standin_eval_fuzzer` (see each harness page)\n", page)
        self.assertNotIn("the others are unmodified", page)

    def test_a_project_with_an_unmodified_harness_names_the_others(self):
        with tree(render=False) as t:
            add_json_oss_verify_target(t)
            harness = t.yaml("projects/json/fuzz-extra/harness.yaml")
            harness["source"]["modified"] = True
            t.put_yaml("projects/json/fuzz-extra/harness.yaml", harness)
            self.assertEqual(t.generate(), 0, t.last_output)
            page = t.read("projects/json/README.md")
        self.assertIn("modified in `fuzz-extra` (see each harness page); the others are unmodified", page)

    def test_a_port_archive_is_checked_with_the_other_source_assets(self):
        with tree(render=False) as t, tempfile.TemporaryDirectory() as assets:
            add_standin(t)
            project = t.yaml("projects/standin/project.yaml")
            for asset in project["assets"].values():
                payload = asset["file"].encode()
                asset["bytes"] = len(payload)
                asset["sha256"] = hashlib.sha256(payload).hexdigest()
                with open(os.path.join(assets, asset["file"]), "wb") as f:
                    f.write(payload)
            t.put_yaml("projects/standin/project.yaml", project)
            out = io.StringIO()
            self.assertEqual(
                fetch.fetch(t.root, ["standin"], source=assets, only_check_assets=True, out=out), 0, out.getvalue())
        self.assertIn("standin-port.tar.zst", out.getvalue())
        self.assertIn("SHA-256 matches", out.getvalue())

    def test_a_port_built_project_fetches_no_recipe(self):
        """standin alone fetches no recipe; listed with zlib and json, the recipe their archives share comes once."""
        with tree(render=False) as t:
            add_standin(t)
            alone, every = io.StringIO(), io.StringIO()
            self.assertEqual(fetch.fetch(t.root, ["standin"], listing=True, out=alone), 0)
            self.assertEqual(fetch.fetch(t.root, ["zlib", "json", "standin"], listing=True, out=every), 0)
        self.assertIn("standin-src.tar.zst", alone.getvalue())
        self.assertIn("standin-port.tar.zst", alone.getvalue())
        self.assertNotIn("recipe.tar.zst", alone.getvalue())
        self.assertEqual([line.split()[1] for line in every.getvalue().splitlines()].count("recipe.tar.zst"), 1)

    def test_a_port_only_release_omits_the_recipe_source_description(self):
        with tree(render=False) as t:
            add_standin(t)
            # every binary archive port-built, so that release.yaml lists no recipe
            for name in ("zlib", "json"):
                project = t.yaml("projects/%s/project.yaml" % name)
                project["assets"].pop("src", None), project["assets"].pop("src_manifest", None)
                del project["assets"]["bin"]["recipe"]
                project["build"]["oss_verify"] = dict(PORT, path="projects/" + name)
                t.put_yaml("projects/%s/project.yaml" % name, project)
            release = t.yaml("release.yaml")
            del release["recipes"]
            t.put_yaml("release.yaml", release)
            self.assertEqual(t.generate(), 0, t.last_output)
            readme = t.read("README.md")
        self.assertNotIn("attached with the build recipe", readme)
        self.assertIn("port archive", readme)

    def test_a_mixed_release_scopes_the_recipe_sentence_to_recipe_built_projects(self):
        with tree(render=False) as t:
            add_standin(t)
            self.assertEqual(t.generate(), 0, t.last_output)
            readme = t.read("README.md")
        self.assertIn("Where a recipe-built project's page names them, the project's upstream source trees are "
                      "attached with the build recipe its binaries were built with", readme)
        self.assertNotIn("Where a project page names them", readme)

    def test_the_readme_names_port_sources_only_where_a_page_attaches_them(self):
        with tree(render=False) as t:
            add_json_oss_verify_target(t)
            project = t.yaml("projects/json/project.yaml")
            for k in ("src", "src_manifest", "port"):
                del project["assets"][k]
            t.put_yaml("projects/json/project.yaml", project)
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertEqual([str(f) for f in t.lint()], [])
            readme = t.read("README.md")
            page = t.read("projects/json/README.md")
        self.assertNotIn("Corresponding source", page)
        port_sentence = next(s for s in readme.split(". ") if "port-built project's page" in s)
        self.assertIn("when it attaches", port_sentence)

    def test_a_port_rebuild_is_said_to_fetch_over_the_network(self):
        with tree(render=False) as t:
            add_standin(t)
            self.assertEqual(t.generate(), 0, t.last_output)
            page = t.read("projects/standin/README.md")
        builder = next(line for line in page.splitlines() if line.startswith("- Builder image:"))
        self.assertIn("network", builder)
        self.assertIn("does not read", builder)

    def test_a_port_built_harness_does_not_call_the_driver_this_repositorys(self):
        with tree(render=False) as t:
            add_standin(t)
            harness = t.yaml("projects/standin/standin_eval_fuzzer/harness.yaml")
            harness["builds"]["plain"]["uninstrumented"] = [{"name": "cli.o", "kind": "driver"}]
            t.put_yaml("projects/standin/standin_eval_fuzzer/harness.yaml", harness)
            self.assertEqual(t.generate(), 0, t.last_output)
            page = t.read("projects/standin/standin_eval_fuzzer/README.md")
        self.assertIn("`cli.o` (the OSS Verify port's driver)", page)
        self.assertNotIn("this repository's driver", page)

    def test_unbuilt_entries_are_not_others_of_the_modified_harnesses(self):
        with tree(render=False) as t:
            add_standin(t)
            project = t.yaml("projects/standin/project.yaml")
            project["harnesses"].append({"name": "standin_held", "status": "not-included", "origin": "oss-verify",
                                         "reason": "not-yet-included"})
            t.put_yaml("projects/standin/project.yaml", project)
            self.assertEqual(t.generate(), 0, t.last_output)
            page = t.read("projects/standin/README.md")
        self.assertIn("modified in `standin_eval_fuzzer`", page)
        self.assertNotIn("the others are unmodified", page)


class ProjectsOwnTargets(unittest.TestCase):
    """A project OSS-Fuzz does not have, whose own fuzz target (origin upstream) the port builds: SQLPage's case."""

    def render(self, statements=None, asan=False):
        with tree(render=False) as t:
            add_sqlpage(t)
            if asan:            # an ASan build too, as SQLPage's sql_file has
                release = t.yaml("release.yaml")
                release["counts"]["binaries"] += 1
                t.put_yaml("release.yaml", release)
                harness = t.yaml("projects/sqlpage/sql_file/harness.yaml")
                harness["builds"]["asan"] = {"file": "sql_file.asan", "bytes": 1000, "sha256": "a" * 64,
                                             "segments": [1]}
                t.put_yaml("projects/sqlpage/sql_file/harness.yaml", harness)
            if statements:
                harness = t.yaml("projects/sqlpage/sql_file/harness.yaml")
                harness["statements"].update(statements)
                t.put_yaml("projects/sqlpage/sql_file/harness.yaml", harness)
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertEqual([str(f) for f in t.lint()], [])
            return {rel: t.read(rel) for rel in (
                "projects/sqlpage/README.md", "projects/sqlpage/sql_file/README.md",
                "projects/sqlpage/sql_file/Statements.v", "projects/json/fuzzer-parse_bjdata/Statements.v",
                "projects/json/fuzzer-parse_bjdata/README.md", "projects/zlib/checksum_fuzzer/README.md",
                "projects/json/README.md", "index/projects.tsv", "index/STATUS.md")}

    def test_its_own_target_is_not_called_one_oss_fuzz_builds(self):
        pages = self.render()
        harness = pages["projects/sqlpage/sql_file/README.md"]
        statements = " ".join(pages["projects/sqlpage/sql_file/Statements.v"].split())
        self.assertIn("sqlpage's own fuzz target `sql_file`", harness)
        self.assertIn("which OSS-Fuzz does not run", harness)
        self.assertNotIn("OSS-Fuzz builds", harness)
        self.assertIn("How this program differs from a libFuzzer build of this fuzz target", harness)
        self.assertIn("sqlpage's own fuzz target [sql_file], which OSS-Fuzz does not run", statements)
        self.assertNotIn("as OSS-Fuzz builds it", statements)
        # an OSS-Fuzz project's own target keeps its words
        self.assertIn("one of the targets OSS-Fuzz builds", pages["projects/json/fuzzer-parse_bjdata/README.md"])

    def test_its_own_targets_are_its_coverage_and_not_oss_fuzzs(self):
        pages = self.render()
        self.assertIn("Of sqlpage's own fuzz targets, which OSS-Fuzz does not run, statements cover 1 of 1.",
                      pages["projects/sqlpage/README.md"])
        self.assertIn("sqlpage\trust\tavailable\t-\t0\t0\t", pages["index/projects.tsv"])
        self.assertIn("| 1 of 1 |", next(line for line in pages["index/STATUS.md"].splitlines()
                                          if "../projects/sqlpage/" in line))

    def test_a_rust_build_is_described_by_the_rust_toolchain(self):
        pages = self.render()
        rust = " ".join(pages["projects/sqlpage/sql_file/Statements.v"].split())
        cxx = " ".join(pages["projects/json/fuzzer-parse_bjdata/Statements.v"].split())
        page = pages["projects/sqlpage/README.md"]
        self.assertIn("rustc's UB checks", rust)
        self.assertNotIn("a failed check executes a trap", rust)
        self.assertIn("UndefinedBehaviorSanitizer; a failed check executes a trap", cxx)
        self.assertNotIn("rustc", cxx)
        self.assertIn("built with cargo", page)
        everywhere = next(line for line in page.splitlines() if line.startswith("- Everywhere:"))
        self.assertIn("rustc", everywhere)
        self.assertIn("standard library", everywhere)

    def test_a_rust_ubsan_agreement_line_names_the_ub_checks(self):
        pages = self.render()
        rust = next(line for line in pages["projects/sqlpage/sql_file/README.md"].splitlines()
                    if line.startswith("| `ubsan_agrees`"))
        cxx = next(line for line in pages["projects/zlib/checksum_fuzzer/README.md"].splitlines()
                   if line.startswith("| `ubsan_agrees`"))
        self.assertIn("no UB check fails", rust)
        self.assertNotIn("UBSan never fires", rust)
        self.assertIn("UBSan never fires", cxx)

    def test_a_rust_ub_check_is_stated_as_an_exit_with_status_79(self):
        pages = self.render({"ubsan_halts": {"kind": "halts", "builds": ["ubsan"], "reading": "budget",
                                             "exits": [0, 2], "status": "open"}})
        rust = " ".join(pages["projects/sqlpage/sql_file/Statements.v"].split())
        self.assertIn("rustc's UB checks (status 79)", rust)
        self.assertIn("A failed rustc UB check writes its source location on standard error and exits with status "
                      "79, which is not allowed", rust)
        self.assertIn("a line the plain build, which makes no such check, does not write at that point", rust)
        self.assertNotIn("never writes", rust)
        for wrong in ("(they abort)", "A failed UB check aborts", "rustc UB check aborts"):
            self.assertNotIn(wrong, rust)

    def test_a_rust_halts_statement_that_allows_any_status_says_nothing_of_the_ub_checks(self):
        pages = self.render({"ubsan_halts_may_fail": {"kind": "halts", "builds": ["ubsan"], "reading": "may-fail",
                                                      "exits": "any", "status": "open"}})
        rust = " ".join(pages["projects/sqlpage/sql_file/Statements.v"].split())
        at = rust.index("Definition ubsan_halts_may_fail")
        doc = rust[rust.rindex("(**", 0, at):at]
        self.assertIn("exits with status 79, which this statement allows", doc)
        self.assertNotIn("no UB check this build makes fails", doc)

    def test_a_rust_may_fail_halts_statement_is_not_called_stronger(self):
        pages = self.render({"plain_halts_may_fail": {"kind": "halts", "builds": ["plain"], "reading": "may-fail",
                                                      "exits": "any", "status": "open"}})
        rust = " ".join(pages["projects/sqlpage/sql_file/Statements.v"].split())
        self.assertIn("It covers every input and any refusal, unlike [plain_halts], but allows any exit status: a "
                      "panic, which exits with status 79, does not falsify it.", rust)
        self.assertNotIn("stronger than", rust)

    def test_the_rust_header_gives_the_exit_statuses_of_a_panic_and_a_failed_allocation(self):
        pages = self.render()
        rust = " ".join(pages["projects/sqlpage/sql_file/Statements.v"].split())
        cxx = " ".join(pages["projects/json/fuzzer-parse_bjdata/Statements.v"].split())
        sentence = ("In this Rust fuzz target, the OSS Verify port's hooks end a failed allocation with status 2 and a "
                    "panic (a failed assertion, an unwrap, an overflow check or a failed rustc UB check) with status 79, "
                    "each after one line on standard error: neither aborts.")
        self.assertIn(sentence, rust)
        self.assertLess(rust.index(sentence), rust.index("WHAT THE HARNESS CHECKS"))
        self.assertNotIn("In this Rust fuzz target", cxx)

    def test_a_rust_asan_pair_read_alloc_forced_only_says_why(self):
        pages = self.render({"asan_agrees": {"kind": "agreement", "builds": ["plain", "asan"],
                                             "reading": "alloc-forced-only", "budgets": "asan", "status": "open"}},
                            asan=True)
        rust = " ".join(pages["projects/sqlpage/sql_file/Statements.v"].split())
        why = ("It is read alloc-forced-only because the allocation-failure hook writes the failed allocation's size "
               "on standard error, and ASan's allocator asks the kernel for memory at other allocations than musl's")
        at = rust.index("Definition asan_agrees")
        self.assertIn(why, rust[rust.rindex("(**", 0, at):at])
        at = rust.index("Definition ubsan_agrees")       # the UBSan pair makes the same requests as the plain build
        self.assertNotIn(why, rust[rust.rindex("(**", 0, at):at])

    def test_a_rust_project_page_says_a_failed_ub_check_exits_with_status_79(self):
        pages = self.render()
        family = next(line for line in pages["projects/sqlpage/README.md"].splitlines()
                      if line.startswith("- **`<build>_agrees`**"))
        self.assertIn("a failed rustc UB check is not an error: it exits with status 79", family)
        self.assertNotIn("A sanitizer report aborts, so this rules out", family)
        cxx = next(line for line in pages["projects/json/README.md"].splitlines()
                   if line.startswith("- **`<build>_agrees`**"))
        self.assertIn("A sanitizer report aborts, so this rules out", cxx)


class PythonTargets(unittest.TestCase):
    """A Python project OSS-Fuzz does not have, whose fuzz target OSS Verify builds."""

    def render(self):
        with tree(render=False) as t:
            add_python_target(t)
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertEqual([str(f) for f in t.lint()], [])
            return {rel: " ".join(t.read(rel).split()) for rel in (
                "projects/pyhtml/README.md", "projects/pyhtml/fuzz_html/README.md",
                "projects/pyhtml/fuzz_html/Statements.v", "projects/json/fuzzer-parse_bjdata/Statements.v",
                "projects/json/README.md")}

    @staticmethod
    def doc(statements, name):
        at = statements.index("Definition %s " % name)
        return statements[statements.rindex("(**", 0, at):at]

    def test_the_header_gives_the_exit_statuses_of_the_interpreter_host(self):
        pages = self.render()
        python = pages["projects/pyhtml/fuzz_html/Statements.v"]
        cxx = pages["projects/json/fuzzer-parse_bjdata/Statements.v"]
        sentence = ("The OSS Verify port's host ends an uncaught Python exception (a failed check of the harness "
                    "included) with status 79, an uncaught MemoryError with status 2 and an uncaught SystemExit with "
                    "status 77")
        self.assertIn(sentence, python)
        self.assertIn("static CPython 3.11.13", python)
        self.assertLess(python.index(sentence), python.index("WHAT THE HARNESS CHECKS"))
        self.assertNotIn("In this Python fuzz target", cxx)
        self.assertNotIn("In this Rust fuzz target", python)

    def test_a_check_that_raises_exits_with_status_79_and_binds_a_statement_that_excludes_it(self):
        pages = self.render()
        python = pages["projects/pyhtml/fuzz_html/Statements.v"]
        self.assertIn("[an uncaught Python exception (status 79); confirmed in the binary]", python)
        self.assertIn("an uncaught Python exception (status 79); confirmed in the binary.",
                      pages["projects/pyhtml/fuzz_html/README.md"])
        self.assertIn("Check (a) ends the process when it fails", self.doc(python, "plain_halts"))

    def test_asan_instruments_the_interpreter_not_the_python_code(self):
        pages = self.render()
        asan = self.doc(pages["projects/pyhtml/fuzz_html/Statements.v"], "asan_agrees")
        self.assertIn("(the C code: the CPython interpreter, which runs the harness and pyhtml as bytecode, the "
                      "port's interpreter host, and the driver,", asan)
        self.assertNotIn("(the harness, pyhtml and the driver", asan)
        self.assertIn("(the harness, nlohmann/json and the driver",
                      self.doc(pages["projects/json/fuzzer-parse_bjdata/Statements.v"], "asan_agrees"))

    def test_the_asan_ubsan_pair_names_the_same_instrumented_c_code(self):
        pages = self.render()
        pair = self.doc(pages["projects/pyhtml/fuzz_html/Statements.v"], "asan_ubsan_agrees")
        self.assertIn("neither sanitizer fires on any such input in the code they instrument (the C code: the CPython "
                      "interpreter, which runs the harness and pyhtml as bytecode, the port's interpreter host, and "
                      "the driver,", pair)
        self.assertNotIn("(the harness, pyhtml and the driver", pair)

    def test_a_python_pair_read_alloc_forced_only_says_why(self):
        pages = self.render()
        python = pages["projects/pyhtml/fuzz_html/Statements.v"]
        why = ("It is read alloc-forced-only because CPython ends with abort() (a fatal error) when some allocations "
               "it makes while it starts are refused")
        self.assertIn(why, self.doc(python, "asan_agrees"))
        self.assertIn("As [asan_agrees], for the UBSan build", self.doc(python, "ubsan_agrees"))
        self.assertNotIn(why, pages["projects/json/fuzzer-parse_bjdata/Statements.v"])

    def test_the_project_page_says_the_python_code_is_frozen_bytecode(self):
        pages = self.render()
        everywhere = pages["projects/pyhtml/README.md"].split("- Everywhere:", 1)[1].split("- ", 1)[0]
        self.assertIn("a static CPython 3.11.13", everywhere)
        self.assertIn("frozen into the binary as CPython bytecode", everywhere)
        self.assertIn("clang 20.1.8 with `-Os -g`", pages["projects/json/README.md"])
        self.assertNotIn("CPython", pages["projects/json/README.md"])


class GoTargets(unittest.TestCase):
    """A Go project OSS-Fuzz does not have, whose fuzz target OSS Verify builds: go-yaml's case."""
    PAGES = ("projects/goyaml/README.md", "projects/goyaml/fuzz_decode/README.md",
             "projects/goyaml/fuzz_decode/Statements.v", "projects/json/fuzzer-parse_bjdata/Statements.v",
             "projects/json/README.md", "projects/pyhtml/README.md")

    def render(self):
        with tree(render=False) as t:
            add_go_target(t)
            add_python_target(t)
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertEqual([str(f) for f in t.lint()], [])
            return {rel: " ".join(t.read(rel).split()) for rel in self.PAGES}

    def lint(self, project=None, harness=None):
        """The lint findings of the Go fixture with project.yaml and harness.yaml changed by the two functions."""
        with tree(render=False) as t:
            add_go_target(t)
            for rel, change in (("projects/goyaml/project.yaml", project),
                                ("projects/goyaml/fuzz_decode/harness.yaml", harness)):
                if change:
                    data = t.yaml(rel)
                    change(data)
                    t.put_yaml(rel, data)
            return [str(f) for f in t.lint()]

    def test_the_project_page_names_the_go_compiler_and_no_c_library(self):
        pages = self.render()
        everywhere = pages["projects/goyaml/README.md"].split("- Everywhere:", 1)[1].split(" - ", 1)[0]
        self.assertIn("the Go 1.27.1 compiler and linker for all of the code", everywhere)
        self.assertIn("with no cgo and so no C library", everywhere)
        self.assertNotIn("musl", everywhere)
        self.assertNotIn("clang", everywhere)
        self.assertIn("RV64G, musl, clang 20.1.8 with `-Os -g`", pages["projects/json/README.md"])
        self.assertIn("RV64G, musl, clang 20.1.8 with `-Os -g` for the C code (a static CPython",
                      pages["projects/pyhtml/README.md"])

    def test_the_project_page_discloses_the_runtime_patches(self):
        pages = self.render()
        page = pages["projects/goyaml/README.md"]
        self.assertIn("- Go runtime: these binaries do not run the stock Go 1.27.1 runtime.", page)
        for words in ("signal handlers (no `rt_sigaction` or `sigaltstack`)", "(so one thread)", "(so one CPU)",
                      "`os.Getenv` returns `\"\"`", "the open-file limit's read and raise", "riscv64 hardware probe",
                      "//go:debug containermaxprocs=0 updatemaxprocs=0 decoratemappings=0",
                      "a panic on the fuzz target's goroutine", "a panic on another goroutine",
                      "exit with status 79", "exits with status 80", "segmentation fault (status 139)"):
            self.assertIn(words, page)
        self.assertLess(page.index("- Everywhere:"), page.index("- Go runtime:"))
        self.assertLess(page.index("- Go runtime:"), page.index("- Builder image:"))
        self.assertIn("built with OSS-Fuzz's Go helpers", page)
        for other in ("projects/json/README.md", "projects/pyhtml/README.md"):
            self.assertNotIn("Go runtime", pages[other])

    def test_the_licence_sentence_names_go_parts_not_a_c_library(self):
        pages = self.render()
        self.assertIn("Each binary is a combined work of goyaml, the Go modules it uses, the harness, Go's standard "
                      "library and runtime with the port's patches, and the port's Go driver;",
                      pages["projects/goyaml/README.md"])
        self.assertNotIn("the C library, the compiler's runtime", pages["projects/goyaml/README.md"])

    def test_the_harness_page_names_no_toolchain_runtime(self):
        page = self.render()["projects/goyaml/fuzz_decode/README.md"]
        self.assertNotIn("compiler-rt", page)
        self.assertNotIn("the C library", page)

    def test_each_statement_file_says_how_a_go_target_ends_a_failure(self):
        pages = self.render()
        go = pages["projects/goyaml/fuzz_decode/Statements.v"]
        for words in ("One build of the fuzz target [fuzz_decode]",
                      "A driver written in Go and linked into the build reads FILE",
                      "calls the Go fuzz target FuzzDecode on the payload",
                      "for a testing.F fuzz test, the function its f.Fuzz call registers",
                      "built by Go 1.27.1's compiler, assembler and linker",
                      "t.Fatal, t.Error or t.Fail in a fuzz test exit with status 79",
                      "os.Exit during a call of the harness with status 77", "with status 80",
                      "the runtime exits with status 2 when the system refuses it memory",
                      "a load through a nil pointer is a segmentation fault (status 139)"):
            self.assertIn(words, go)
        self.assertLess(go.index("In this Go fuzz target"), go.index("WHAT THE HARNESS CHECKS"))
        self.assertNotIn("In this Go fuzz target", pages["projects/json/fuzzer-parse_bjdata/Statements.v"])
        self.assertNotIn("FuzzDecode(payload, length)", go)

    def test_its_one_statement_is_a_halts_statement_with_exits_0_and_2(self):
        pages = self.render()
        go = pages["projects/goyaml/fuzz_decode/Statements.v"]
        self.assertEqual(go.count("Definition "), 1)
        self.assertIn("Definition plain_halts : Prop := halts_within_budget Budgets.Standard.lim_source "
                      "Exits.ok_or_refused", go)
        self.assertNotIn("agrees", go)
        self.assertNotIn("halts_may_fail", go)

    def test_a_failing_go_test_check_is_status_79_and_binds_the_halts_statement(self):
        pages = self.render()
        go = pages["projects/goyaml/fuzz_decode/Statements.v"]
        self.assertIn("[t.Fatal, t.Error or t.Fail (status 79); confirmed in the binary]", go)
        self.assertIn("Check (a) ends the process when it fails", go)

    def test_a_go_project_names_its_go_toolchain_and_no_clang(self):
        for change in (lambda p: p["build"].pop("go"), lambda p: p["build"].update(clang="20.1.8")):
            self.assertTrue(any("a Go project names build.go, the Go toolchain, and no build.clang" in f
                                for f in self.lint(project=change)))
        found = self.lint(project=lambda p: p["build"].update(system="custom"))
        self.assertTrue(any("build.system is go exactly for a Go project" in f for f in found), found)

    def test_only_a_go_project_names_build_go(self):
        with tree(render=False) as t:
            add_python_target(t)
            project = t.yaml("projects/pyhtml/project.yaml")
            project["build"]["go"] = "1.27.1"
            t.put_yaml("projects/pyhtml/project.yaml", project)
            found = [str(f) for f in t.lint()]
        self.assertTrue(any("only a Go project names build.go" in f for f in found), found)
        with tree(render=False) as t:
            add_python_target(t)
            project = t.yaml("projects/pyhtml/project.yaml")
            project["build"]["system"] = "go"
            t.put_yaml("projects/pyhtml/project.yaml", project)
            found = [str(f) for f in t.lint()]
        self.assertTrue(any("build.system is go exactly for a Go project" in f for f in found), found)

    def test_a_go_fuzz_target_has_only_the_plain_build(self):
        def ubsan(h):
            h["builds"]["ubsan"] = {"file": "fuzz_decode.ubsan", "bytes": 1000, "sha256": "9" * 64, "segments": [1]}
        found = self.lint(harness=ubsan)
        self.assertTrue(any("builds.ubsan: a Go fuzz target has only the plain build" in f for f in found), found)

    def test_a_go_fuzz_target_has_no_agreement_statement(self):
        def agrees(h):
            h["builds"]["ubsan"] = {"file": "fuzz_decode.ubsan", "bytes": 1000, "sha256": "9" * 64, "segments": [1]}
            h["statements"]["ubsan_agrees"] = {"kind": "agreement", "builds": ["plain", "ubsan"],
                                               "reading": "may-fail", "budgets": "standard", "status": "open"}
        found = self.lint(harness=agrees)
        self.assertTrue(any("statements.ubsan_agrees: a Go fuzz target's one statement is plain_halts" in f
                            for f in found), found)

    def test_a_go_fuzz_target_has_no_may_fail_statement(self):
        def may_fail(h):
            h["statements"]["plain_halts_may_fail"] = {"kind": "halts", "builds": ["plain"], "reading": "may-fail",
                                                       "exits": [0, 2], "binds_checks": True, "status": "open"}
        found = self.lint(harness=may_fail)
        self.assertTrue(any("statements.plain_halts_may_fail: a Go fuzz target's one statement is plain_halts" in f
                            for f in found), found)

    def test_a_go_check_has_only_go_stops(self):
        for stop in ("raise", "abort", "assert", "trap", "throw"):
            found = self.lint(harness=lambda h, stop=stop: h["checks"][0].update(stops_with=stop))
            self.assertTrue(any("checks[0]: a Go check stops with one of" in f for f in found), (stop, found))

    def test_a_go_project_has_no_api_driver(self):
        def api(h):
            h["origin"] = "this-repository"
        found = self.lint(harness=api)
        self.assertTrue(any("a Go project has no API driver" in f for f in found), found)

    def test_a_go_project_is_built_by_the_port_in_the_go_image(self):
        found = self.lint(project=lambda p: p["build"].pop("oss_verify"))
        self.assertTrue(any("a Go project's binaries are built by the OSS Verify port" in f for f in found), found)
        with tree(render=False) as t:
            add_go_target(t)
            release = t.yaml("release.yaml")
            project = t.yaml("projects/goyaml/project.yaml")
            project["build"]["builder"] = release["images"]["builder"][0]
            t.put_yaml("projects/goyaml/project.yaml", project)
            json = t.yaml("projects/json/project.yaml")
            json["build"]["builder"] = GO_IMAGE
            t.put_yaml("projects/json/project.yaml", json)
            found = [str(f) for f in t.lint()]
        for p in ("goyaml", "json"):
            self.assertTrue(any("projects/%s/project.yaml" % p in f and "build.builder is the port's Go toolchain "
                                "image" in f for f in found), (p, found))

    def test_a_c_project_still_names_its_clang(self):
        with tree(render=False) as t:
            project = t.yaml("projects/json/project.yaml")
            project["build"].pop("clang")
            t.put_yaml("projects/json/project.yaml", project)
            found = [str(f) for f in t.lint()]
        self.assertTrue(any("build.clang names the clang that compiled the C code" in f for f in found), found)

    def test_a_go_halts_statement_allows_exactly_0_and_2(self):
        for exits in ("any", [0], [0, 2, 79]):
            def change(h, exits=exits):
                h["statements"]["plain_halts"]["exits"] = exits
                h["statements"]["plain_halts"]["binds_checks"] = exits != "any"
            found = self.lint(harness=change)
            self.assertTrue(any("statements.plain_halts: a Go fuzz target's halts statement allows exactly the "
                                "statuses 0 and 2" in f for f in found), (exits, found))

    def test_a_failing_go_test_check_is_for_go_harnesses_only(self):
        with tree(render=False) as t:
            add_python_target(t)
            harness = t.yaml("projects/pyhtml/fuzz_html/harness.yaml")
            harness["checks"][0]["stops_with"] = "fail"
            t.put_yaml("projects/pyhtml/fuzz_html/harness.yaml", harness)
            found = [str(f) for f in t.lint()]
        self.assertTrue(any("stops_with: fail is t.Fatal, t.Error or t.Fail in a Go fuzz test" in f for f in found),
                        found)


class Linting(unittest.TestCase):
    def test_a_project_absent_from_oss_fuzz_counts_as_no_oss_fuzz_project(self):
        with tree(render=False) as t:
            add_standin(t)
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertEqual([str(f) for f in t.lint()], [])

    def test_an_oss_verify_port_rejects_a_different_repository(self):
        with tree(render=False) as t:
            add_standin(t)
            project = t.yaml("projects/standin/project.yaml")
            project["build"]["oss_verify"]["repository"] = "theorem-labs/" + "other"
            errors = schema.validate("project", project)
        self.assertTrue(any("project.build.oss_verify.repository:" in e for e in errors), errors)

    def test_an_oss_verify_port_rejects_a_path_outside_projects(self):
        with tree(render=False) as t:
            add_standin(t)
            project = t.yaml("projects/standin/project.yaml")
            project["build"]["oss_verify"]["path"] = "ports/standin"
            errors = schema.validate("project", project)
        self.assertTrue(any("project.build.oss_verify.path:" in e for e in errors), errors)

    def test_an_oss_verify_origin_requires_the_port_that_built_it(self):
        with tree(render=False) as t:
            add_standin(t, port=False)
            found = t.lint()
        self.assertTrue(any("standin_eval_fuzzer: origin oss-verify requires build.oss_verify" in f.msg for f in found))

    def test_a_fuzz_target_of_a_project_absent_from_oss_fuzz_cannot_be_oss_fuzzs(self):
        for origin in ("oss-fuzz", None):
            with self.subTest(origin=origin), tree(render=False) as t:
                add_standin(t)
                p = t.yaml("projects/standin/project.yaml")
                if origin is None:
                    del p["harnesses"][0]["origin"]
                else:
                    p["harnesses"][0]["origin"] = origin
                t.put_yaml("projects/standin/project.yaml", p)
                found = t.lint()
                self.assertTrue(any("standin_eval_fuzzer: OSS-Fuzz has no such project" in f.msg for f in found),
                                [str(f) for f in found])

    def test_a_projects_own_fuzz_target_absent_from_oss_fuzz_may_be_upstream(self):
        with tree(render=False) as t:
            add_standin(t)
            project = t.yaml("projects/standin/project.yaml")
            project["harnesses"][0]["origin"] = "upstream"
            t.put_yaml("projects/standin/project.yaml", project)
            harness = t.yaml("projects/standin/standin_eval_fuzzer/harness.yaml")
            harness["origin"] = "upstream"
            harness["source"]["from"] = {
                "repository": "https://git.savannah.gnu.org/git/make.git",
                "commit": "a" * 40,
                "path": "fuzz/standin_eval_fuzzer.c",
            }
            t.put_yaml("projects/standin/standin_eval_fuzzer/harness.yaml", harness)
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertEqual([str(f) for f in t.lint()], [])

    def test_a_project_absent_from_oss_fuzz_cannot_take_an_oss_fuzz_reason(self):
        for status, reason in (("no-harness", "none-at-commit"), ("excluded", "stub-harness")):
            with self.subTest(reason=reason), tree(render=False) as t:
                p = t.yaml("projects/tcmalloc/project.yaml")
                del p["oss_fuzz"]
                p["status"], p["reason"] = status, reason
                t.put_yaml("projects/tcmalloc/project.yaml", p)
                found = t.lint()
                self.assertTrue(any("reason %s says what OSS-Fuzz has for the project" % reason in f.msg
                                    for f in found), [str(f) for f in found])

    def test_an_oss_fuzz_project_keeps_its_oss_fuzz_reason(self):
        with tree(render=False) as t:
            p = t.yaml("projects/tcmalloc/project.yaml")
            p["status"], p["reason"] = "no-harness", "none-at-commit"
            t.put_yaml("projects/tcmalloc/project.yaml", p)
            found = t.lint()
        self.assertFalse(any("says what OSS-Fuzz has for the project" in f.msg for f in found),
                         [str(f) for f in found])

    def test_a_private_repository_cannot_be_a_source_link(self):
        with tree(render=False) as t:
            add_standin(t)
            harness = t.yaml("projects/standin/standin_eval_fuzzer/harness.yaml")
            harness["source"]["from"]["repository"] = "https://github.com/theorem-labs/" + "agent-infra"
            t.put_yaml("projects/standin/standin_eval_fuzzer/harness.yaml", harness)
            found = t.lint()
        self.assertTrue(any(f.rule == "links" and "theorem-labs/" + "agent-infra" in f.msg for f in found), found)

    def test_a_port_built_source_bundle_requires_its_port_archive(self):
        with tree(render=False) as t:
            add_standin(t)
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertEqual([str(f) for f in t.lint()], [])
            project = t.yaml("projects/standin/project.yaml")
            del project["assets"]["port"]
            t.put_yaml("projects/standin/project.yaml", project)
            found = t.lint()
        self.assertTrue(any("build.oss_verify and assets.src" in f.msg for f in found), found)

    def test_a_port_archive_requires_a_port_built_project(self):
        with tree(render=False) as t:
            project = t.yaml("projects/zlib/project.yaml")
            project["assets"]["port"] = dict(PORT_ASSET, file="zlib-port.tar.zst")
            t.put_yaml("projects/zlib/project.yaml", project)
            found = t.lint()
        self.assertTrue(any("assets.port requires build.oss_verify" in f.msg for f in found), found)

    def test_a_port_source_is_checked_for_private_repository_links(self):
        with tree(render=False) as t:
            add_standin(t)
            t.write("projects/standin/standin_eval_fuzzer/source/standin_eval_fuzzer.c",
                    "// https://github.com/theorem-labs/" + "agent-infra\n")
            found = t.lint()
        self.assertTrue(any(f.rule == "links" and "agent-infra" in f.msg for f in found), found)

    def test_changed_only_reads_an_unchanged_source_again_when_its_origin_changes(self):
        """Whether a source file is an upstream copy or OSS Verify's own text is a fact: when origin changes to
        oss-verify and the source does not, --changed-only still reads the source, and finds what a full lint finds."""
        rel = "projects/json/fuzz-extra/source/fuzz-extra.c"

        def origin(t, value):
            project = t.yaml("projects/json/project.yaml")
            next(e for e in project["harnesses"] if e["name"] == "fuzz-extra")["origin"] = value
            t.put_yaml("projects/json/project.yaml", project)
            harness = t.yaml("projects/json/fuzz-extra/harness.yaml")
            harness["origin"] = value
            t.put_yaml("projects/json/fuzz-extra/harness.yaml", harness)

        with tree(render=False) as t:
            add_json_oss_verify_target(t)
            origin(t, "upstream")
            t.write(rel, "/* mail someone" + "@" + "example.com, https://github.com/theorem-labs/" + "agent-infra */\n",
                    "a")
            git = ["git", "-C", t.root, "-c", "user.name=t", "-c", "user.email=t@t", "-c", "commit.gpgsign=false"]
            subprocess.run(git[:3] + ["init", "-q"], check=True)
            subprocess.run(git + ["add", "-A"], check=True)
            subprocess.run(git + ["commit", "-q", "-m", "base"], check=True)
            origin(t, "oss-verify")   # the source does not change
            in_source = lambda found: sorted((f.rule, f.where) for f in found if f.where.startswith(rel + ":"))
            whole = in_source(t.lint())
            only = in_source(t.lint(changed_only="HEAD"))
        self.assertEqual(sorted({r for r, _ in whole}), ["links", "private-data"])
        self.assertEqual(only, whole)

    def test_an_oss_verify_source_keeps_licence_links(self):
        rel = "projects/standin/standin_eval_fuzzer/source/standin_eval_fuzzer.c"
        attacks = ["// https:{s}example.ts{d}net/x".format(s="//", d=".")]
        controls = [" * along with this program.  If not, see <https:{s}www.gnu.org/licenses/>.".format(s="//"),
                    " *      http:{s}www.apache.org/licenses/LICENSE-2.0".format(s="//")]
        self.assertRefused("links", {rel: (attacks, controls)})

    def test_only_an_oss_verify_target_may_name_the_port(self):
        spellings = ["theorem-labs/oss-verify"] + [u.format(s="//", o="theorem-labs") for u in (
            "https:{s}github.com/{o}/oss-verify", "https:{s}github.com/{o}/oss-verify.git",
            "https:{s}github.com/{o}/oss-verify/", "https:{s}github.com/Theorem-Labs/OSS-Verify",
            "https:{s}www.github.com/{o}/oss-verify.git/")]
        control = "https:{s}github.com/{o}/oss-verify-proofs".format(s="//", o="theorem-labs")
        for repo in spellings + [control]:
            with self.subTest(repo=repo), tree(render=False) as t:
                harness = t.yaml("projects/zlib/checksum_fuzzer/harness.yaml")
                harness["source"]["from"]["repository"] = repo
                t.put_yaml("projects/zlib/checksum_fuzzer/harness.yaml", harness)
                found = t.lint()
                named = any("only an oss-verify target may name" in f.msg for f in found)
                self.assertEqual(named, repo != control, [str(f) for f in found])

    def test_an_unbuilt_oss_verify_entry_requires_a_port(self):
        with tree(render=False) as t:
            add_standin(t, port=False)
            project = t.yaml("projects/standin/project.yaml")
            del project["assets"]["port"]
            project["harnesses"][0]["origin"] = "upstream"
            project["harnesses"].append({
                "name": "not-built",
                "status": "not-included",
                "origin": "oss-verify",
                "reason": "not-attempted",
            })
            t.put_yaml("projects/standin/project.yaml", project)
            harness = t.yaml("projects/standin/standin_eval_fuzzer/harness.yaml")
            harness["origin"] = "upstream"
            harness["source"]["from"]["repository"] = "https://git.savannah.gnu.org/git/make.git"
            t.put_yaml("projects/standin/standin_eval_fuzzer/harness.yaml", harness)
            found = t.lint()
        self.assertTrue(any("not-built: origin oss-verify requires build.oss_verify" in f.msg for f in found), found)

    def test_a_port_archive_is_attached_with_the_source_bundle(self):
        with tree(render=False) as t:
            add_standin(t)
            project = t.yaml("projects/standin/project.yaml")
            project["assets"]["port"]["release"] = "v2026.11.0-src"
            t.put_yaml("projects/standin/project.yaml", project)
            found = t.lint()
        self.assertTrue(any("assets.port and assets.src are attached to different releases" in f.msg for f in found),
                        found)

    def test_a_port_archive_goes_with_the_source_trees(self):
        with tree(render=False) as t:
            add_json_oss_verify_target(t)
            project = t.yaml("projects/json/project.yaml")
            del project["assets"]["src"], project["assets"]["src_manifest"]
            t.put_yaml("projects/json/project.yaml", project)
            found = t.lint()
        self.assertTrue(any("assets.port goes with assets.src" in f.msg for f in found), found)

    def test_an_oss_verify_port_path_names_this_project(self):
        with tree(render=False) as t:
            add_standin(t)
            project = t.yaml("projects/standin/project.yaml")
            project["build"]["oss_verify"]["path"] = "projects/zlib"
            t.put_yaml("projects/standin/project.yaml", project)
            found = t.lint()
        self.assertTrue(any("build.oss_verify.path must be projects/standin" in f.msg for f in found), found)

    def test_an_oss_verify_entry_cannot_be_unbuilt(self):
        with tree(render=False) as t:
            add_standin(t)
            project = t.yaml("projects/standin/project.yaml")
            project["harnesses"] += [
                {"name": "make_not_built", "status": "not-included", "origin": "oss-verify", "reason": "not-attempted"},
                {"name": "standin_held", "status": "not-included", "origin": "oss-verify", "reason": "not-yet-included"},
            ]
            t.put_yaml("projects/standin/project.yaml", project)
            found = [f.msg for f in t.lint()]
        self.assertTrue(any("make_not_built: origin oss-verify" in m and "not-attempted" in m for m in found), found)
        self.assertFalse(any("standin_held: origin oss-verify" in m for m in found), found)

    def test_every_github_host_spelling_of_a_private_repository_is_refused(self):
        for host, path in (("https://www.github.com/", "theorem-labs/" + "agent-infra"),
                           ("https://GitHub.com/", "theorem-labs/" + "agent-infra"),
                           ("https://github.com/", "Theorem-Labs/" + "Agent-Infra")):
            url = host + path
            with self.subTest(url=url), tree(render=False) as t:
                add_standin(t)
                project = t.yaml("projects/standin/project.yaml")
                project["homepage"] = url
                t.put_yaml("projects/standin/project.yaml", project)
                found = t.lint()
                self.assertTrue(any(f.rule == "links" and url in f.msg for f in found), [str(f) for f in found])

    def test_a_port_claim_contradicts_a_recipe_build_record(self):
        with tree(render=False) as t:
            project = t.yaml("projects/zlib/project.yaml")
            project["build"]["oss_verify"] = dict(PORT, path="projects/zlib")
            project["assets"]["port"] = dict(PORT_ASSET, file="zlib-port.tar.zst")
            t.put_yaml("projects/zlib/project.yaml", project)
            t.write("proofs/zlib/checksum_fuzzer/provenance/recipe/tools/build-body.sh", "#!/bin/sh\n")
            found = t.lint()
        self.assertTrue(any("checksum_fuzzer's build record carries a build recipe" in f.msg
                            and "build.oss_verify" in f.msg for f in found), [str(f) for f in found])

    def test_a_port_built_build_record_keeps_its_build_scripts_under_port(self):
        with tree(render=False) as t:
            add_standin(t)
            add_record(t, "standin", "standin_eval_fuzzer", MAKE_RECORD)
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertEqual([str(f) for f in t.lint()], [])

    def test_a_recipe_built_project_cannot_have_a_port_build_record(self):
        with tree(render=False) as t:
            add_record(t, "zlib", "checksum_fuzzer", {"port/manifest.yaml": "project: zlib\n"})
            found = t.lint()
        self.assertTrue(any("checksum_fuzzer's build record carries a port build" in f.msg for f in found),
                        [str(f) for f in found])

    def test_a_port_build_record_holds_only_this_projects_port_directory(self):
        with tree(render=False) as t:
            add_standin(t)
            add_record(t, "standin", "standin_eval_fuzzer", dict(MAKE_RECORD, **{"port/projects/zlib/build.sh": "make\n"}))
            self.assertEqual(t.generate(), 0, t.last_output)
            found = [str(f) for f in t.lint()]
        self.assertTrue(any("port/projects/zlib/build.sh" in f and "matches no path pattern" in f for f in found),
                        found)

    def test_a_port_build_record_is_checked_for_private_repository_links(self):
        with tree(render=False) as t:
            add_standin(t)
            add_record(t, "standin", "standin_eval_fuzzer", dict(MAKE_RECORD, **{
                "port/projects/standin/build.sh": "# https://github.com/theorem-labs/" + "agent-infra\n"}))
            found = t.lint()
        self.assertTrue(any(f.rule == "links" and "port/projects/standin/build.sh" in f.where for f in found),
                        [str(f) for f in found])

    def test_a_port_build_record_does_not_name_the_build_host(self):
        with tree(render=False) as t:
            add_standin(t)
            add_record(t, "standin", "standin_eval_fuzzer", dict(MAKE_RECORD, **{
                "port/manifest.yaml": "project: standin\nrebuild:\n  kind: same-host\n  host: buildbox-7\n"
                                      "  result: identical\n"}))
            self.assertEqual(t.generate(), 0, t.last_output)
            found = [str(f) for f in t.lint()]
        self.assertTrue(any("port/manifest.yaml" in f and "host" in f and f.startswith("private-data") for f in found),
                        found)

    def test_a_port_project_contact_can_be_cleared(self):
        rel = "proofs/standin/standin_eval_fuzzer/provenance/port/projects/standin/project.yaml"
        with tree(render=False) as t:
            add_standin(t)
            add_record(t, "standin", "standin_eval_fuzzer", dict(MAKE_RECORD, **{
                "port/projects/standin/project.yaml": "primary_contact: bug-make" + "@gnu.org\n"}))
            self.assertEqual(t.generate(), 0, t.last_output)
            found = [f for f in t.lint() if f.where.startswith(rel + ":")]
            self.assertEqual(len(found), 1, [str(f) for f in found])
            t.put_yaml("tools/oft/lint-exceptions.yaml", {
                "schema": "oss-fuzz-theorems/lint-exceptions/1",
                "exceptions": [{"path": rel, "rule": "private-data", "key": found[0].key, "count": 1,
                                "reason": "a test"}]})
            self.assertEqual(t.lint(), [])

    def test_a_port_build_script_author_address_can_be_cleared(self):
        rel = "proofs/standin/standin_eval_fuzzer/provenance/port/projects/standin/build.sh"
        with tree(render=False) as t:
            add_standin(t)
            add_record(t, "standin", "standin_eval_fuzzer", dict(MAKE_RECORD, **{
                "port/projects/standin/build.sh": "# Copyright 2026 A. Author <author" + "@example.org>\n"}))
            self.assertEqual(t.generate(), 0, t.last_output)
            found = [f for f in t.lint() if f.where.startswith(rel + ":")]
            self.assertEqual(len(found), 1, [str(f) for f in found])
            t.put_yaml("tools/oft/lint-exceptions.yaml", {
                "schema": "oss-fuzz-theorems/lint-exceptions/1",
                "exceptions": [{"path": rel, "rule": "private-data", "key": found[0].key, "count": 1,
                                "reason": "a test"}]})
            self.assertEqual(t.lint(), [])

    def test_an_address_outside_the_port_project_copy_is_not_cleared(self):
        # PROVENANCE.md is outside port/; port/manifest.yaml is inside port/ but outside port/projects/<p>/, the edge
        # of the rule.
        for name, text in (("PROVENANCE.md", MAKE_RECORD["PROVENANCE.md"] + "\nContact: author" + "@example.org\n"),
                           ("port/manifest.yaml", "project: standin\nnote: author" + "@example.org\n")):
            rel = "proofs/standin/standin_eval_fuzzer/provenance/" + name
            with self.subTest(rel=rel), tree(render=False) as t:
                add_standin(t)
                add_record(t, "standin", "standin_eval_fuzzer", dict(MAKE_RECORD, **{name: text}))
                self.assertEqual(t.generate(), 0, t.last_output)
                found = [f for f in t.lint() if f.where.startswith(rel + ":")]
                self.assertEqual(len(found), 1, [str(f) for f in found])
                t.put_yaml("tools/oft/lint-exceptions.yaml", {
                    "schema": "oss-fuzz-theorems/lint-exceptions/1",
                    "exceptions": [{"path": rel, "rule": "private-data", "key": found[0].key, "count": 1,
                                    "reason": "a test"}]})
                kept = t.lint()
                self.assertTrue(any(f.where.startswith(rel + ":") and f.rule == "private-data" for f in kept),
                                [str(f) for f in kept])
                self.assertTrue(any(f.rule == "paths" and "not used" in f.msg for f in kept),
                                [str(f) for f in kept])

    def test_a_port_project_exception_does_not_clear_a_host_path_or_url_user_information(self):
        # Only an e-mail address is clearable in a copied build script: a host path and a URL's user information,
        # which can be a credential (an address-shaped "token@host" after "//user:"), stay findings.
        rel = "proofs/standin/standin_eval_fuzzer/provenance/port/projects/standin/build.sh"
        for text in ("# built in /" + "data/someone/make\n",
                     "git clone https://oauth2:glpat-x1y2z3a4b5" + "@gitlab.example.com/g/r.git\n"):
            with self.subTest(text=text), tree(render=False) as t:
                add_standin(t)
                add_record(t, "standin", "standin_eval_fuzzer", dict(MAKE_RECORD, **{"port/projects/standin/build.sh": text}))
                self.assertEqual(t.generate(), 0, t.last_output)
                found = [f for f in t.lint() if f.where.startswith(rel + ":")]
                self.assertEqual(len(found), 1, [str(f) for f in found])
                t.put_yaml("tools/oft/lint-exceptions.yaml", {
                    "schema": "oss-fuzz-theorems/lint-exceptions/1",
                    "exceptions": [{"path": rel, "rule": "private-data", "key": found[0].key, "count": 1,
                                    "reason": "a test"}]})
                kept = t.lint()
                self.assertTrue(any(f.where.startswith(rel + ":") and f.rule == "private-data" for f in kept),
                                [str(f) for f in kept])
                self.assertTrue(any(f.rule == "paths" and "not used" in f.msg for f in kept),
                                [str(f) for f in kept])

    def test_a_port_shaped_path_under_proofs_lib_is_no_port_record(self):
        # proofs/lib/ is the shared proof library: a file shaped like a port copy there is no build record, so an
        # address in it is held to the rules of this repository's own text and no exception clears it.
        rel = "proofs/lib/x/provenance/port/projects/x/build.sh"
        with tree(render=False) as t:
            add_standin(t)
            t.write(rel, "# Copyright 2026 A. Author <author" + "@example.org>\n")
            self.assertEqual(t.generate(), 0, t.last_output)
            found = [f for f in t.lint() if f.where.startswith(rel + ":") and f.rule == "private-data"]
            self.assertEqual(len(found), 1, [str(f) for f in found])
            t.put_yaml("tools/oft/lint-exceptions.yaml", {
                "schema": "oss-fuzz-theorems/lint-exceptions/1",
                "exceptions": [{"path": rel, "rule": "private-data", "key": found[0].key, "count": 1,
                                "reason": "a test"}]})
            kept = t.lint()
        self.assertTrue(any(f.where.startswith(rel + ":") and f.rule == "private-data" for f in kept),
                        [str(f) for f in kept])
        self.assertFalse(lint.verbatim("proofs/lib/x/provenance/recipe/notes.md"))
        self.assertFalse(lint.port_record("proofs/lib/x/provenance/port/manifest.yaml"))

    def test_a_port_build_record_refuses_private_links_and_keeps_upstream_ones(self):
        for url in ("https://dispatch.example.ts" + ".net/issues/1", "http:" + "//127.0.0.1:8080/x",
                    "http:" + "//buildhost/x", "https://github.com./theorem-labs/" + "agent-infra",
                    "https://GITHUB.COM:443/theorem-labs/" + "agent-infra",
                    "https:" + "//user" + "@github.com/theorem-labs/" + "agent-infra"):
            with self.subTest(url=url), tree(render=False) as t:
                add_standin(t)
                add_record(t, "standin", "standin_eval_fuzzer", dict(MAKE_RECORD, **{
                    "port/projects/standin/build.sh": "# %s\n" % url}))
                self.assertEqual(t.generate(), 0, t.last_output)
                found = [f for f in t.lint() if f.rule == "links"]
                self.assertTrue(any("port/projects/standin/build.sh" in f.where and url in f.msg for f in found),
                                [str(f) for f in found])
                self.assertFalse(any("port/projects/standin/sources" in f.where for f in found),
                                 [str(f) for f in found])

    def test_a_non_web_link_to_a_private_machine_is_refused(self):
        def f(lines):
            return [line.format(s="//", d=".") for line in lines]
        attacks = f(("# git:{s}gitmirror/gnulib.git", "# ssh:{s}git@100{d}88.1.2/gnulib.git",
                     "# ssh:{s}git@100{d}88.1/gnulib.git", "# git:{s}[fd7a:115c:a1e0::1]/make.git",
                     "# git+ssh:{s}buildbox-7/make.git"))
        controls = f(("# git:{s}git.savannah.gnu.org/make.git", "# ssh:{s}git@8{d}8.8/gnulib.git",
                      "# https:{s}github.com/coreutils/gnulib"))
        self.assertRefused("links", {self.PORT_DIR + "sources": (attacks, controls)})

    def test_a_private_host_or_a_private_repository_is_refused_even_as_a_fact(self):
        for url in (u.format(s="//", o="theorem-labs", d=".") for u in (
                "https:{s}dispatch.example.ts{d}net/make", "https:{s}github.com./{o}/agent-infra",
                "https:{s}github.com/google/oss-fuzz/../../{o}/agent-infra", "https:{s}10.1/",
                "https:{s}dispatch{d}localhost/x", "https:{s}raw.github.com/{o}/agent-infra/main/README.md",
                # GitHub's web editors open a repository too
                "https:{s}github.dev/{o}/agent-infra", "https:{s}vscode.dev/github/{o}/agent-infra")):
            with self.subTest(url=url), tree(render=False) as t:
                add_standin(t)
                project = t.yaml("projects/standin/project.yaml")
                project["homepage"] = url
                t.put_yaml("projects/standin/project.yaml", project)
                self.assertEqual(t.generate(), 0, t.last_output)
                found = [f for f in t.lint() if f.rule == "links"]
                for page in ("projects/standin/project.yaml", "projects/standin/README.md"):
                    self.assertTrue(any(page in f.where and url in f.msg for f in found), [str(f) for f in found])

    def test_a_host_idna_refuses_is_a_finding_not_a_crash(self):
        """A host that IDNA refuses (an invalid Punycode label, a mixed-direction label, a joiner): lint reports the
        link where the stand-in project's homepage puts it (the facts and the rendered page) and in a doc, and does not stop."""
        home = "https:{s}xn--github-abc.com/".format(s="//")
        doc = ["[home](%s)" % home, "[he](https:{s}\u05d0a.com/)", "[zwj](https:{s}github\u200d.com/)"]
        with tree(render=False) as t:
            add_standin(t)
            project = t.yaml("projects/standin/project.yaml")
            project["homepage"] = home
            t.put_yaml("projects/standin/project.yaml", project)
            t.write("docs/x.md", "".join("%s\n\n" % line.format(s="//") for line in doc))
            self.assertEqual(t.generate(), 0, t.last_output)
            found = [f for f in t.lint() if f.rule == "links"]
        for page in ("projects/standin/project.yaml", "projects/standin/README.md"):
            self.assertTrue(any(f.where.startswith(page + ":") and home in f.msg for f in found),
                            [str(f) for f in found])
        self.assertEqual({int(f.where.rsplit(":", 1)[1]) for f in found if f.where.startswith("docs/x.md:")},
                         {1, 3, 5})

    PORT_DIR = "proofs/standin/standin_eval_fuzzer/provenance/port/projects/standin/"

    @staticmethod
    def to_a_private_repository(rel):
        """A link to a private repository from rel, in the two forms a check must resolve: a relative link that climbs out
        of this repository into the organisation (a ../ for each directory of rel, and for main/, blob/ and the
        repository), and a dot segment after a public repository's name."""
        return ["../" * (rel.count("/") + 3) + "agent-infra",
                "/{o}/oss-verify-proofs/../agent-infra".format(o="theorem-labs")]

    def assertRefused(self, rule, files):
        """files: {path: (attacks, controls)}, written into a fixture tree with the stand-in project and its build record, a blank line
        after each line.  rule refuses every attack line and no control line."""
        texts = {rel: "".join("%s\n\n" % line for line in attacks + controls)
                 for rel, (attacks, controls) in files.items()}
        with tree(render=False) as t:
            add_standin(t)
            add_record(t, "standin", "standin_eval_fuzzer", MAKE_RECORD)
            for rel, text in texts.items():
                t.write(rel, text)
            self.assertEqual(t.generate(), 0, t.last_output)
            found = [f for f in t.lint() if f.rule == rule]
        wrong = {"%s:%d" % (rel, no): texts[rel].split("\n")[no - 1] for rel, (attacks, _) in files.items()
                 for no in {int(f.where.rsplit(":", 1)[1]) for f in found if f.where.startswith(rel + ":")}
                 ^ set(range(1, 2 * len(attacks), 2))}
        self.assertEqual(wrong, {}, "lines refused or let through wrongly")

    def test_a_reference_definition_in_a_block_quote_or_a_list_item_is_read(self):
        markers = ("> ", "- ", "1. ", "> 2) ")
        attacks = ["%s[r%d%d]: %s" % (m, i, j, target) for i, m in enumerate(markers)
                   for j, target in enumerate(self.to_a_private_repository("docs/x.md"))]
        controls = ["%s[c%d]: ../README.md" % (m, i) for i, m in enumerate(markers)]
        self.assertRefused("links", {"docs/x.md": (attacks, controls)})

    def test_a_tag_is_read_past_an_angle_bracket_in_a_quoted_attribute(self):
        # also an attribute after a /, which GitHub reads as a link inside an HTML block, and an href after a quoted
        # value that holds the other quote kind and the word href
        tags = ('<a title="a>b" href="%s">x</a>', '<a title="1<2" href="%s">x</a>', '<div><a/href="%s">x</a></div>',
                '<div><a title=" href=\'" href="%s" x=\'y\'>x</a></div>')
        attacks = [tag % target for tag in tags for target in self.to_a_private_repository("docs/x.md")]
        self.assertRefused("links", {"docs/x.md": (attacks, [tag % "../README.md" for tag in tags])})

    def test_a_srcset_candidate_is_read(self):
        attacks = ['<picture><source media="(prefers-color-scheme: dark)" '
                   'srcset="../../../../agent-infra/raw/main/d.png 1x, l.png 2x"><img src="l.png"></picture>',
                   '<picture><source srcset="l.png 1x, ../../../../agent-infra/raw/main/d.png 2x"></picture>']
        controls = ['<picture><source srcset="../README.md 1x, l.png 2x"><img src="l.png"></picture>',
                    '<span title=\'a srcset="../../../../agent-infra/raw/main/d.png 1x"\'>x</span>']
        self.assertRefused("links", {"docs/x.md": (attacks, controls)})

    def test_a_bare_url_after_a_digit_an_underscore_or_a_non_ascii_letter_is_read(self):
        url = "https:{s}github.com/{o}/%s/../%s".format(s="//", o="theorem-labs")
        forms = [url % ("oss-verify-proofs-internal", "agent-infra"), url % ("oss-verify-proofs", "agent-infra")]
        attacks = [w % u for w in ("1%s", "_%s_", "x_%s", "\u017f%s") for u in forms]
        controls = [w % (url % ("oss-verify-proofs", "rocq-read-file")) for w in ("1%s", "_%s", "x_%s", "\u017f%s")]
        # GitHub's extent of a bare URL, past a quote, is only Markdown's
        past_a_quote = '1https:{s}github.com/google/oss-fuzz/"/../../../{o}/agent-infra'.format(s="//", o="theorem-labs")
        self.assertRefused("links", {
            "docs/x.md": (attacks + [past_a_quote], controls),
            self.PORT_DIR + "build.sh": (["# " + a for a in attacks], ["# " + c for c in controls])})

    def test_every_file_name_github_renders_as_markdown_is_read_as_markdown(self):
        files = {}
        for name in ("NOTES.MD", "NOTES.mdx", "notes.litcoffee", "Notes.Markdown"):
            rel = self.PORT_DIR + name
            files[rel] = (["[%d](%s)" % (i, target) for i, target in enumerate(self.to_a_private_repository(rel))],
                          ["[ok](sources)"])
        self.assertRefused("links", files)

    def test_a_scheme_named_in_prose_is_not_a_link(self):
        prose = ["Every link starts with `https://`.", "A `git://` remote.", "As in https://."]
        self.assertRefused("links", {"docs/x.md": (["https:{s}example.org/x".format(s="//")], prose)})

    def test_a_private_name_is_refused_in_any_text_link_or_not(self):
        def f(lines):
            return [u.format(o="theorem-labs", O="Theorem-Labs", d=".") for u in lines]
        hosts = f(("the dashboard at dispatch{d}tail12ec1c.ts{d}net", "on WIKI{d}Example{d}CORP",
                   "buildbox-7{d}internal:8080", "printer{d}home{d}arpa", "dev{d}LOCALHOST"))
        repositories = f(("C:\\src\\{o}\\agent-infra", "path %2F{o}%2fagent-infra", "github{d}com:{o}/agent-infra.git",
                          "&#47;{o}&#47;agent-infra", "/{O}/Agent-Infra", "/{o}//oss-verify-proofs-internal"))
        # public repositories, an image (the GHCR rule's), the port named but not as a path, a proof's qualified names
        controls = f(("/{o}/oss-verify-proofs", "/{o}/rocq-read-file.git", "ghcr{d}io/{o}/oss-fuzz-theorems-checker",
                      "the repository {o}/oss-verify", "Lemma AW_Init{d}internal", "Mod_X{d}Sub{d}internal",
                      "www{d}gnu{d}org"))
        self.assertRefused("private-data", {
            "docs/x.md": (hosts + repositories, controls),
            self.PORT_DIR + "build.sh": (hosts + repositories, controls),
            # an upstream copy keeps its authors' host names, but names no private repository
            "projects/zlib/checksum_fuzzer/source/checksum_fuzzer.c": (repositories, hosts + controls),
        })

    def test_a_private_repository_named_as_owner_and_name_is_refused(self):
        def f(lines):
            return [line.format(s="//", o="theorem-labs", d=".") for line in lines]
        attacks = f(("Clone it with `gh repo clone {o}/agent-infra`.",
                     "The images are built by {o}/agent-infra.",
                     "    uses: {o}/agent-infra/.github/actions/setup@v1",
                     "![stars](https:{s}api.star-history.com/svg?repos={o}/agent-infra)",
                     "Tracked in {o}/oss-verify-proofs-internal#4.",
                     "https:{s}github.com/orgs/{o}/agent-infra"))
        controls = f(("the `{o}/oss-verify` port", "see {o}/rocq-read-file",
                      "ghcr{d}io/{o}/oss-fuzz-theorems-checker"))
        self.assertRefused("private-data", {
            "docs/x.md": (attacks, controls),
            "tools/oft/templates/x.md.tmpl": (attacks, controls),
            self.PORT_DIR + "build.sh": (f(("# docs: https:{s}{o}.github.io/agent-infra/",
                                             "# docs: https:{s}{o}.github.io.//agent-infra/")),
                                         f(("# https:{s}{o}.github.io/rocq-read-file/",
                                             "# https:{s}{o}.github.io.//rocq-read-file/"))),
        })
    def test_a_private_pages_project_link_is_refused(self):
        def f(lines):
            return [line.format(s="//", o="theorem-labs") for line in lines]
        self.assertRefused("links", {
            self.PORT_DIR + "build.sh": (f(("# https:{s}{o}.github.io/agent-infra/",
                                             "# git:{s}Theorem-" "Labs.GitHub.IO./agent-infra/")),
                                         f(("# https:{s}{o}.github.io/rocq-read-file/",
                                             "# git:{s}theorem-labs.github.io./rocq-read-file/"))),
        })


    def test_a_shared_address_or_an_azure_internal_name_is_private(self):
        def f(lines):
            return [line.format(s="//", d=".") for line in lines]
        host = "box-1.0123abcd.xx.in" + "ternal.cloudapp{d}net"
        self.assertRefused("private-data", {
            "docs/x.md": (f(("Built on %s." % host, "ssh sami@100{d}88.1.2")),
                          f(("www{d}gnu{d}org", "version 100{d}1.2"))),
        })
        self.assertRefused("links", {self.PORT_DIR + "build.sh": (f(("# https:{s}%s:8080/x" % host,)), [])})

    def test_ordinary_code_names_are_not_private_host_names(self):
        def f(lines):
            return [line.format(s="//", o="theorem-labs", d=".") for line in lines]
        controls = f(("Python's `threading{d}local()` keeps it per thread.",
                      "`cp .env.example .env{d}local`",
                      "`import com.google.common{d}internal;`",
                      "https:{s}github.com/orgs/{o}/packages"))
        self.assertRefused("private-data", {
            "docs/x.md": (f(("on dev{d}internal", "call buildbox{d}internal()",
                               "import buildbox{d}internal;", "Require Import buildbox{d}internal.",
                               "Lemma x : box{d}tail12ec1c{d}ts{d}net.")), controls),
            "proofs/zlib/checksum_fuzzer/lib/RocqNames.v":
                ([], f(("Lemma ok : Spec{d}internal.", "Require Import Parser{d}Internal."))),
        })

    # Links that GitHub renders, each to a private theorem-labs repository or a machine on a private network as a
    # browser opens it (urls.parse); {s} is the // after a scheme and {o} the organisation, so that this file holds no
    # such link itself.
    ATTACKS = (
        # dot segments, plain and percent-encoded, in front of an allowed path or a public repository; a .. after an
        # encoded slash, which a browser resolves; an encoded climb, as a server that decodes %2F reads it; repeated
        # slashes
        "https:{s}github.com/google/oss-fuzz/../../{o}/agent-infra",
        "https:{s}github.com/google/oss-fuzz/%2e%2e/%2e%2e/{o}/agent-infra",
        "https:{s}github.com/rocq-prover/../{o}/agent-infra",
        "https:{s}github.com/{o}/oss-verify-proofs/../agent-infra",
        "[d](https:{s}github.com/google/oss-fuzz/(x)/../../../{o}/agent-infra)",
        "https:{s}github.com/{o}/oss-verify-proofs%2F/../agent-infra",
        "https:{s}github.com/google/oss-fuzz%2F..%2F..%2F{o}/agent-infra",
        "https:{s}github.com//{o}//agent-infra",
        # a host as a browser folds it: percent-encoded, full-width, IPv4 shorthand, hex and octal, localhost names
        "https:{s}githu%62.com/{o}/agent-infra",
        "https:{s}\uff47\uff49\uff54\uff48\uff55\uff42\uff0e\uff43\uff4f\uff4d/{o}/agent-infra",
        "http:{s}10.1:8080/",
        "http:{s}0x7f.1/",
        "http:{s}0177.0.0.1/",
        "http:{s}dispatch{d}localhost/",
        "https:{s}raw.github.com/{o}/agent-infra/main/README.md",
        "http:{s}[fd00::1]/x",
        # spellings GitHub renders as a link: an upper-case scheme, a protocol-relative link, a character reference,
        # backslash escapes, a bare URL GitHub links past a quote or a bar, a www. link, HTML, a scheme-relative path,
        # a reference definition, an image, a relative link that climbs to the organisation; and a bare URL written
        # with a character reference, which GitHub shows as the URL's text
        "HTTPS:{s}github.com/{o}/agent-infra",
        "[a]({s}github.com/{o}/agent-infra)",
        "[b](https&#58;{s}github.com/{o}/agent-infra)",
        "https&#58;{s}github.com/{o}/agent-infra",
        "[c](https\\:\\/\\/github.com\\/{o}\\/agent-infra)",
        'https:{s}github.com/google/oss-fuzz/"/../../../{o}/agent-infra',
        "https:{s}github.com/google/oss-fuzz/|/../../../{o}/agent-infra",
        "www.github.com/{o}/agent-infra",
        '<a href="HTTPS:\\\\github.com\\{o}\\agent-infra">e</a>',
        "<a href={s}github.com/{o}/agent-infra>f</a>",
        "[g](https:/{o}/agent-infra)",
        "[h](http:github.com/{o}/agent-infra)",
        "[r]: {s}github.com/{o}/agent-infra",
        '<img src="{s}github.com/{o}/agent-infra/raw/main/x.png">',
        "[i](" + "../" * 10 + "agent-infra)",
        "https:{s}user:pw" "@github.com/{o}/agent-infra",
        # a host IDNA refuses, which a browser may open: an invalid Punycode label, a mixed-direction label, a joiner,
        # and a label ending in a hyphen under a private suffix
        "https:{s}xn--github-abc.com/",
        "[he](https:{s}\u05d0a.com/)",
        "https:{s}github\u200d.com/",
        "https:{s}xn--github-.dispatch.tail12ec1c.ts{d}net/x",
    )
    # The same shapes, each to a public place: none is refused.
    CONTROLS = (
        "https:{s}github.com/{o}/oss-verify-proofs/../rocq-read-file",
        "HTTPS:{s}github.com/google/oss-fuzz/../oss-fuzz/projects/zlib",
        "[ok]({s}github.com/google/oss-fuzz)",
        "[up](" + "../" * 9 + "README.md)",
        "http:{s}0x7f.1.example.org/",
        "https:{s}\uff47\uff4e\uff55\uff0e\uff4f\uff52\uff47/software/make/",
        "www.gnu.org/software/make/",
        "[r2]: https&#58;{s}www.gnu.org/software/make/",
        # a host as a browser maps it (UTS #46, ß kept): plain, full-width, and as Punycode
        "https:{s}stra\u00dfe.de/",
        "https:{s}\uff53\uff54\uff52\uff41\u00df\uff45\uff0e\uff44\uff45/",
        "https:{s}xn--strae-oqa.de/",
    )
    # Absolute URLs in a file that is not Markdown, where only the URL pattern finds them.
    TEXT_ATTACKS = (
        "HTTPS:{s}github.com/{o}/agent-infra",
        "http:{s}[fd00::1]/x",
    )

    def test_a_link_is_judged_by_what_a_browser_opens(self):
        lines = [(u.format(s="//", o="theorem-labs", d="."), True) for u in self.ATTACKS] + \
                [(u.format(s="//", o="theorem-labs", d="."), False) for u in self.CONTROLS]
        text = "".join("%s\n\n" % line for line, _ in lines)
        refused = {2 * i + 1 for i, (_, attack) in enumerate(lines) if attack}
        script = "".join("# %s\n" % u.format(s="//", o="theorem-labs") for u in self.TEXT_ATTACKS)
        with tree(render=False) as t:
            add_standin(t)
            add_record(t, "standin", "standin_eval_fuzzer", dict(MAKE_RECORD, **{"port/projects/standin/NOTES.md": text,
                                                                          "port/projects/standin/build.sh": script}))
            self.assertEqual(t.generate(), 0, t.last_output)
            found = [f for f in t.lint() if f.rule == "links"]

        def flagged(name):
            where = "proofs/standin/standin_eval_fuzzer/provenance/port/projects/standin/%s:" % name
            return {int(f.where.rsplit(":", 1)[1]) for f in found if f.where.startswith(where)}
        self.assertEqual({no: text.split("\n")[no - 1] for no in flagged("NOTES.md") ^ refused}, {},
                         "lines refused or let through wrongly")
        self.assertEqual({no: script.split("\n")[no - 1] for no in flagged("build.sh") ^ set(
            range(1, len(self.TEXT_ATTACKS) + 1))}, {}, "lines refused or let through wrongly")

    def test_rendered_text_keeps_its_link_verdicts(self):
        allowed = ("https:{s}github.com/madler/zlib", "https:{s}github.com/madler/zlib/blob/master/README#x",
                   "https:{s}github.com/google/oss-fuzz/tree/0123/projects/zlib",
                   "http:{s}snapshot.debian.org/archive/debian/20261001T000000Z/", "[docs](../docs/building.md)",
                   "[here](#at-a-glance)", "[a harness](../projects/zlib/checksum_fuzzer/)", "plain text: zlib.net")
        refused = ("https:{s}example.org/x", "http:{s}www.zlib.net/", "https:{s}github.com/madler/zlibx",
                   "[x](https:{s}example.org/y)", "<https:{s}example.org/z>",
                   "https:{s}github.com/google/oss-fuzz/../../madler/zlibx", "https:{s}rocq-prover.org.example.com/",
                   "https:{s}reuse.software:8443/")
        lines = [(u.format(s="//"), False) for u in allowed] + [(u.format(s="//"), True) for u in refused]
        with tree(render=False) as t:
            t.write("notes/zlib-links.md", "".join("%s\n" % line for line, _ in lines))
            flagged = {int(f.where.rsplit(":", 1)[1]) for f in t.lint()
                       if f.rule == "links" and f.where.startswith("notes/zlib-links.md:")}
        self.assertEqual(flagged, {i + 1 for i, (_, bad) in enumerate(lines) if bad})


class PortBuiltRecipe(unittest.TestCase):
    """A port-built project's binaries were built by the OSS Verify port and by no recipe: its binary archive and its
    build records name none, in either shape of release.yaml."""

    def test_a_port_built_archive_needs_no_recipe(self):
        with tree(render=False) as t:
            add_standin(t)
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertEqual([str(f) for f in t.lint()], [])

    def test_a_port_built_archive_names_no_recipe(self):
        with tree(render=False) as t:
            add_standin(t)
            project = t.yaml("projects/standin/project.yaml")
            project["assets"]["bin"]["recipe"] = dict(FIXTURE_RECIPE)
            t.put_yaml("projects/standin/project.yaml", project)
            found = [str(f) for f in t.lint()]
        self.assertTrue(any(f.startswith("schema projects/standin/project.yaml:")
                            and "assets.bin.recipe: build.oss_verify says" in f for f in found), found)

    def test_the_older_shapes_recipe_does_not_stand_for_a_port_built_project(self):
        with tree(render=False) as t:
            older_shape(t)
            add_standin(t)
            loaded = facts.load(t.root)
            self.assertIsNone(facts.bin_recipe(loaded, loaded.projects["standin"]))
            self.assertEqual(facts.bin_recipe(loaded, loaded.projects["zlib"]), FIXTURE_RECIPE)
            out = io.StringIO()
            self.assertEqual(fetch.fetch(t.root, ["standin"], listing=True, out=out), 0, out.getvalue())
        self.assertIn("standin-port.tar.zst", out.getvalue())
        self.assertNotIn("recipe.tar.zst", out.getvalue())

    def test_a_port_built_build_record_cites_no_recipe(self):
        with tree(render=False) as t:
            add_standin(t)
            add_record(t, "standin", "standin_eval_fuzzer", MAKE_RECORD)
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertEqual([str(f) for f in t.lint()], [])
            self.assertEqual(facts.load(t.root).records, {})

    def test_a_port_built_build_record_cannot_cite_a_recipe(self):
        for shape in ("recipes", "recipe"):
            with self.subTest(shape=shape), tree(render=False) as t:
                if shape == "recipe":
                    older_shape(t)
                add_standin(t)
                add_record(t, "standin", "standin_eval_fuzzer", dict(MAKE_RECORD, **{"PROVENANCE.yaml": build_record()}))
                found = [str(f) for f in t.lint()]
                self.assertTrue(any(f.startswith("schema proofs/standin/standin_eval_fuzzer/provenance/PROVENANCE.yaml:")
                                    and "build.oss_verify says the OSS Verify port built projects/standin's binaries" in f
                                    for f in found), found)

    def test_a_port_built_build_record_cannot_name_a_recipe_it_does_not_cite(self):
        """A `recipe` key that cites nothing readable, or a record that is not a mapping, is a finding for a
        port-built project too, not a record that cites no recipe."""
        for text in ("recipe: nonsense\n", "recipe: {release: v2026.11.0}\n", "- recipe\n"):
            with self.subTest(text=text), tree(render=False) as t:
                add_standin(t)
                add_record(t, "standin", "standin_eval_fuzzer", dict(MAKE_RECORD, **{"PROVENANCE.yaml": text}))
                found = [str(f) for f in t.lint()]
                self.assertTrue(any(f.startswith("schema proofs/standin/standin_eval_fuzzer/provenance/PROVENANCE.yaml:")
                                    and "recipe.asset" in f for f in found), found)


if __name__ == "__main__":
    unittest.main()
