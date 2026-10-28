"""oft fetch, verify-sha and check, against stand-in archives and tools."""
import hashlib
import io
import json
import os
import re
import resource
import shutil
import stat
import subprocess
import sys
import tarfile
import tempfile
import unittest

from oft import check, facts, fetch, plan, rules, schema, yamlio
from oft.tests.helpers import REPO, add_findings, later_release, older_shape, recipe_only_rebuild, tree

HAVE_ZSTD = shutil.which("zstd") is not None
PR_YML = os.path.join(REPO, ".github", "workflows", "pr.yml")
HAVE_PR_YML = os.path.exists(PR_YML)     # the runner image, which runs these tests, holds only tools/oft
IMAGES_YML = os.path.join(REPO, ".github", "workflows", "images.yml")


def make_release(t, assets, members=None, tamper=None, padding=0):
    """Give zlib's published builds stand-in bytes, pack them as the release
    asset in `assets`, and record both levels of SHA-256 in the facts.
    `padding` zero bytes follow the tar's end-of-archive blocks, as a tar
    written with a large blocking factor has."""
    proj = facts.load(t.root).projects["zlib"]
    files = {}
    for h in proj.harnesses.values():
        y = t.yaml(os.path.join(h.dir, "harness.yaml"))
        for b, rec in h.builds():
            data = b"\x7fELF stand-in for " + rec["file"].encode()
            files["%s/%s" % (h.name, rec["file"])] = data
            y["builds"][b]["bytes"] = len(data)
            y["builds"][b]["sha256"] = hashlib.sha256(data).hexdigest()
        t.put_yaml(os.path.join(h.dir, "harness.yaml"), y)
    if tamper:
        files = tamper(files)
    raw = io.BytesIO()
    with tarfile.open(fileobj=raw, mode="w") as tf:
        for name, data in (members or files).items():
            info = tarfile.TarInfo(name)
            info.size = len(data)
            tf.addfile(info, io.BytesIO(data))
    tar = os.path.join(assets, "zlib-bin.tar")
    with open(tar, "wb") as f:
        f.write(raw.getvalue() + b"\0" * padding)
    subprocess.run(["zstd", "-q", "-f", "--rm", tar], check=True)
    arc = tar + ".zst"
    p = t.yaml("projects/zlib/project.yaml")
    p["assets"]["bin"]["bytes"] = os.path.getsize(arc)
    p["assets"]["bin"]["sha256"] = facts.sha256_file(arc)
    t.put_yaml("projects/zlib/project.yaml", p)
    assert t.generate() == 0, t.last_output
    return files


def run(fn, *a, **kw):
    buf = io.StringIO()
    rc = fn(*a, out=buf, **kw)
    return rc, buf.getvalue()


def withdraw_every_statement(t, harness):
    """Withdraw every statement of zlib's harness, as the schema allows of a harness with published builds, and render
    again: its Statements.v then defines none, and it has no Characterise.v."""
    rel = "projects/zlib/%s/harness.yaml" % harness
    y = t.yaml(rel)
    for st in y["statements"].values():
        for k in ("basis", "reason", "witness", "withheld", "gap"):
            st.pop(k, None)
        st.update(status="withdrawn", reason="a test")
    t.put_yaml(rel, y)
    characterise = t.path("projects/zlib/%s/Characterise.v" % harness)
    if os.path.exists(characterise):
        os.remove(characterise)
    assert t.generate() == 0, t.last_output


# Stands in for `rocq compile .../Defined.v` (check.check_defined): each name in the tuple oft_listed must be the
# Definition of a statement in the harness's Statements.v (the source beside the -Q mapping of its _build directory);
# one stated by Axiom or Parameter, or closed by Admitted, is an axiom Print Assumptions lists, as the kernel's does.
DEFINED_STUB = r'''import re, sys
args = sys.argv[1:]
src = None
for i, a in enumerate(args[:-2]):
    if a == "-Q" and args[i + 2] not in ("OssFuzzTheorems.Core", "OftDefined"):
        src = args[i + 1].replace("/_build/default/", "/")
listed = re.search(r"Definition oft_listed := \((.*)\)\.", open(args[-1]).read()).group(1)
try:
    stmts = open(src + "/Statements.v").read()
except OSError:
    sys.exit("Cannot find a physical path bound to logical path Statements.")
axioms = ["Corelib.Init.Something.prim : Prop"]
for name in (t.strip().lstrip("@") for t in listed.split(",")):
    s = name.rsplit(".", 1)[1]
    m = re.search(r"^(Definition|Axiom|Parameter) %s\b(.*?)(?=^Definition |\Z)" % re.escape(s), stmts, re.M | re.S)
    if not m:
        print("The reference %s was not found in the current environment." % name)
        sys.exit(1)
    if m.group(1) != "Definition" or "Admitted." in m.group(2):
        axioms.append("%s : Prop" % name)
print("Axioms:")
print("\n".join(axioms))
'''


@unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
class Fetch(unittest.TestCase):
    def test_fetch_and_verify(self):
        with tree() as t, tempfile.TemporaryDirectory() as a:
            files = make_release(t, a)
            rc, out = run(fetch.fetch, t.root, ["zlib"], source=a)
            self.assertEqual(rc, 0, out)
            self.assertIn("8 binaries, each SHA-256 checked", out)
            for name, data in files.items():
                with open(t.path("projects/zlib/bin", name), "rb") as f:
                    self.assertEqual(f.read(), data)
            self.assertEqual(run(fetch.verify_sha, t.root, ["zlib"])[0], 0)

    def test_an_archive_that_is_not_the_pinned_one(self):
        with tree() as t, tempfile.TemporaryDirectory() as a:
            make_release(t, a)
            with open(os.path.join(a, "zlib-bin.tar.zst"), "ab") as f:
                f.write(b"x")
            rc, out = run(fetch.fetch, t.root, ["zlib"], source=a)
            self.assertEqual(rc, 1)
            self.assertIn("project.yaml pins", out)

    def test_an_archive_with_padding_after_its_last_member(self):
        """tarfile stops at the end-of-archive blocks while zstd still has the
        padding after them to write; 4 MiB of it, more than a pipe holds, keeps
        zstd writing, so a fetch that closed the pipe early would kill it."""
        with tree() as t, tempfile.TemporaryDirectory() as a:
            make_release(t, a, padding=4 << 20)
            rc, out = run(fetch.fetch, t.root, ["zlib"], source=a)
            self.assertEqual(rc, 0, out)
            self.assertIn("8 binaries, each SHA-256 checked", out)

    def test_an_archive_cut_off_in_its_zstd_stream(self):
        """The pinned archive is cut off halfway: zstd fails on it, the project's fetch fails by name, nothing is
        unpacked or left staged, and the fetch goes on to the next project."""
        with tree() as t, tempfile.TemporaryDirectory() as a:
            make_release(t, a)
            arc = os.path.join(a, "zlib-bin.tar.zst")
            os.truncate(arc, os.path.getsize(arc) // 2)
            p = t.yaml("projects/zlib/project.yaml")
            p["assets"]["bin"]["bytes"] = os.path.getsize(arc)
            p["assets"]["bin"]["sha256"] = facts.sha256_file(arc)
            t.put_yaml("projects/zlib/project.yaml", p)
            rc, out = run(fetch.fetch, t.root, ["zlib", "imagemagick"], source=a)
            self.assertEqual(rc, 1)
            self.assertRegex(out, r"(?m)^zlib: zstd failed on \S+\.tar\.zst$")
            self.assertIn("imagemagick: imagemagick has no binaries in this release", out)
            self.assertEqual(os.listdir(t.path("projects/zlib/bin")), [])

    def test_a_member_that_is_not_a_harness_file(self):
        with tree() as t, tempfile.TemporaryDirectory() as a:
            make_release(t, a, tamper=lambda f: dict(f, **{"../escape": b"x"}))
            rc, out = run(fetch.fetch, t.root, ["zlib"], source=a)
            self.assertEqual(rc, 1)
            self.assertIn("unexpected member", out)
            self.assertFalse(os.path.exists(t.path("projects/zlib/escape")))

    def test_the_licence_files_of_the_copyleft_components(self):
        lic = {"LICENSES/zlib/LICENSE": b"zlib licence\n", "LICENSES/glib/COPYING": b"LGPL text\n"}
        with tree() as t, tempfile.TemporaryDirectory() as a:
            make_release(t, a, tamper=lambda f: dict(f, **lic))
            rc, out = run(fetch.fetch, t.root, ["zlib"], source=a)
            self.assertEqual(rc, 0, out)
            self.assertIn("8 binaries, each SHA-256 checked; 2 licence files", out)
            for name, data in lic.items():
                with open(t.path("projects/zlib/bin", name), "rb") as f:
                    self.assertEqual(f.read(), data)
            # a later archive without them leaves none behind
            make_release(t, a)
            self.assertEqual(run(fetch.fetch, t.root, ["zlib"], source=a)[0], 0)
            self.assertFalse(os.path.exists(t.path("projects/zlib/bin/LICENSES")))

    def test_a_licence_member_outside_licenses_component_file(self):
        for bad in ("LICENSES/COPYING", "LICENSES/zlib/doc/COPYING", "LICENSES/../escape", "LICENSES/.hidden/x",
                    "LICENSES/zlib/LICENSE\n"):
            with self.subTest(bad), tree() as t, tempfile.TemporaryDirectory() as a:
                make_release(t, a, tamper=lambda f: dict(f, **{bad: b"x"}))
                rc, out = run(fetch.fetch, t.root, ["zlib"], source=a)
                self.assertEqual(rc, 1, out)
                self.assertIn("unexpected member", out)
                self.assertEqual(os.listdir(t.path("projects/zlib/bin")), [], "nothing is unpacked or left staged")

    def test_licence_files_whose_names_join_alike(self):
        """Each member is staged under a name of its own, so two whose component and file names joined with __ are
        alike each land with their own bytes."""
        lic = {"LICENSES/a__b/c": b"first\n", "LICENSES/a/b__c": b"second\n"}
        with tree() as t, tempfile.TemporaryDirectory() as a:
            make_release(t, a, tamper=lambda f: dict(f, **lic))
            rc, out = run(fetch.fetch, t.root, ["zlib"], source=a)
            self.assertEqual(rc, 0, out)
            self.assertIn("8 binaries, each SHA-256 checked; 2 licence files", out)
            for name, data in lic.items():
                with open(t.path("projects/zlib/bin", name), "rb") as f:
                    self.assertEqual(f.read(), data)
            self.assertFalse([n for n in os.listdir(t.path("projects/zlib/bin")) if n.startswith(".fetch-")])

    def test_a_member_whose_bytes_are_not_pinned(self):
        with tree() as t, tempfile.TemporaryDirectory() as a:
            make_release(t, a, tamper=lambda f: dict(f, **{"checksum_fuzzer/checksum_fuzzer.asan": b"\x7fELF other"}))
            rc, out = run(fetch.fetch, t.root, ["zlib"], source=a)
            self.assertEqual(rc, 1)
            self.assertIn("does not match its harness.yaml SHA-256", out)

    def test_verify_sha_notices_a_changed_or_missing_file(self):
        with tree() as t, tempfile.TemporaryDirectory() as a:
            make_release(t, a)
            self.assertEqual(run(fetch.fetch, t.root, ["zlib"], source=a)[0], 0)
            with open(t.path("projects/zlib/bin/checksum_fuzzer/checksum_fuzzer.plain"), "ab") as f:
                f.write(b"!")
            rc, out = run(fetch.verify_sha, t.root, ["zlib"])
            self.assertEqual(rc, 1)
            self.assertIn("does not match", out)

    def test_a_project_without_binaries(self):
        with tree() as t:
            rc, out = run(fetch.fetch, t.root, ["imagemagick"])
            self.assertEqual(rc, 1)
            self.assertIn("no binaries in this release", out)


class Listing(unittest.TestCase):
    """`oft fetch --list`, whose rows for one tag are what release.yml compares a draft with: each tag lists exactly
    the files the facts attach to it, the recipe each binary archive pins among them."""

    def listed(self, t, release):
        rc, out = run(fetch.fetch, t.root, [], release=release, listing=True)
        return rc, sorted(line.split()[1] for line in out.splitlines() if line.startswith(release + " "))

    def test_one_release_lists_every_file(self):
        with tree() as t:
            rc, files = self.listed(t, "v2026.11.0")
            self.assertEqual(rc, 0)
            self.assertIn("zlib-bin.tar.zst", files)
            self.assertIn("zlib-src.tar.zst", files)
            self.assertIn("zlib-src.MANIFEST.tsv", files)
            self.assertIn("recipe.tar.zst", files)

    def test_a_source_release_lists_the_source_assets_and_the_recipe_and_the_release_the_binaries(self):
        with tree() as t:
            for name in ("zlib", "json"):
                p = t.yaml("projects/%s/project.yaml" % name)
                for k in ("src", "src_manifest"):
                    if k in p["assets"]:
                        p["assets"][k]["release"] = "v2026.11.0-src"
                p["assets"]["bin"]["recipe"]["release"] = "v2026.11.0-src"
                t.put_yaml("projects/%s/project.yaml" % name, p)
            r = t.yaml("release.yaml")
            r["recipes"][0]["release"] = "v2026.11.0-src"
            t.put_yaml("release.yaml", r)
            self.assertEqual(t.generate(), 0, t.last_output)
            rc, main = self.listed(t, "v2026.11.0")
            self.assertEqual(rc, 0)
            self.assertNotIn("zlib-src.tar.zst", main)
            self.assertNotIn("recipe.tar.zst", main)
            self.assertIn("zlib-bin.tar.zst", main)
            self.assertTrue(all(f.endswith("-bin.tar.zst") for f in main), main)
            rc, src = self.listed(t, "v2026.11.0-src")
            self.assertEqual(rc, 0)
            self.assertEqual(src, ["recipe.tar.zst", "zlib-src.MANIFEST.tsv", "zlib-src.tar.zst"])

    def test_each_release_lists_what_it_adds(self):
        """Without copying, a release holds only the files it adds: json's new archive, source assets and recipe; zlib's
        unchanged ones stay in the release that first held them."""
        with tree() as t:
            later_release(t)
            rc, new = self.listed(t, "v2026.12.0-src")
            self.assertEqual(rc, 0)
            self.assertEqual(new, ["json-src.MANIFEST.tsv", "json-src.tar.zst", "recipe-2.tar.zst"])
            self.assertEqual(self.listed(t, "v2026.12.0"), (0, ["json-bin.tar.zst"]))
            rc, old = self.listed(t, "v2026.11.0")
            self.assertEqual(rc, 0)
            self.assertEqual(old, ["recipe.tar.zst", "zlib-bin.tar.zst", "zlib-src.MANIFEST.tsv", "zlib-src.tar.zst"])

    def test_a_recipe_only_rebuild_lists_the_recipe_in_a_release_without_source_assets(self):
        """A rebuild with a new recipe adds the archive and the recipe it pins, and nothing else: the project's source
        asset and MANIFEST stay listed where they were."""
        with tree() as t:
            recipe_only_rebuild(t, record=False)
            self.assertEqual(self.listed(t, "v2026.12.0-src"), (0, ["recipe-2.tar.zst"]))
            self.assertEqual(self.listed(t, "v2026.12.0"), (0, ["zlib-bin.tar.zst"]))
            rc, old = self.listed(t, "v2026.11.0")
            self.assertEqual(rc, 0)
            self.assertEqual(old, ["json-bin.tar.zst", "recipe.tar.zst", "zlib-src.MANIFEST.tsv", "zlib-src.tar.zst"])

    def test_the_shape_before_recipes_lists_the_same_files(self):
        with tree() as t:
            newer = self.listed(t, "v2026.11.0")
            older_shape(t)
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertEqual(self.listed(t, "v2026.11.0"), newer)
            self.assertIn("recipe.tar.zst", newer[1])

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_a_recipe_that_fails_its_check_names_the_file_that_pins_it(self):
        """A project's archive names its own recipe, so a recipe that does not match points at that project.yaml; in
        the shape before recipes, release.yaml's one recipe stands in for it, and release.yaml is named."""
        for shape in ("newer", "older"):
            with self.subTest(shape=shape), tree() as t, tempfile.TemporaryDirectory() as a:
                if shape == "older":
                    older_shape(t)
                make_release(t, a)
                # only the binary archive and its recipe are checked: the source assets are not attached here
                p = t.yaml("projects/zlib/project.yaml")
                for k in ("src", "src_manifest"):
                    p["assets"].pop(k, None)
                t.put_yaml("projects/zlib/project.yaml", p)
                with open(os.path.join(a, "recipe.tar.zst"), "wb") as f:
                    f.write(b"not the pinned recipe")
                rc, out = run(fetch.fetch, t.root, ["zlib"], source=a, only_check_assets=True)
                self.assertEqual(rc, 1, out)
                want = "projects/zlib/project.yaml pins" if shape == "newer" else "release.yaml pins"
                self.assertIn(want, out)

    def test_a_project_that_attaches_nothing_is_not_an_error(self):
        """An available project that withholds every build has no `assets`: listing every project skips it."""
        with tree() as t:
            shutil.rmtree(t.path("counterexamples/json"))
            p = t.yaml("projects/json/project.yaml")
            del p["assets"]
            p["withheld"] = {"unpublished": True}
            t.put_yaml("projects/json/project.yaml", p)
            y = t.yaml("projects/json/fuzzer-parse_bjdata/harness.yaml")
            n = 0
            for b in y["builds"].values():
                b["withheld"] = "not-yet-published"
                for k in ("bytes", "sha256", "segments"):
                    del b[k]
                n += 1
            for s in y["statements"].values():
                for k in ("basis", "reason"):
                    s.pop(k, None)
                s["status"], s["withheld"] = "withheld", "not-yet-published"
            t.put_yaml("projects/json/fuzzer-parse_bjdata/harness.yaml", y)
            r = t.yaml("release.yaml")
            r["counts"]["binaries"] -= n
            t.put_yaml("release.yaml", r)
            self.assertEqual(t.generate(), 1)         # the statement files it rendered before are now stale
            for line in t.last_output.splitlines():
                if line.endswith("no longer produce; remove it"):
                    os.unlink(t.path(line.split(":")[0]))
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertEqual([str(f) for f in t.lint()], [])
            rc, out = run(fetch.fetch, t.root, [], all_projects=True, listing=True)
            self.assertEqual(rc, 0, out)
            files = sorted(line.split()[1] for line in out.splitlines())
            self.assertIn("zlib-bin.tar.zst", files)
            self.assertNotIn("json-bin.tar.zst", files)

    def test_a_project_that_publishes_builds_and_attaches_nothing_is_an_error(self):
        """lint refuses an available project with published builds and no `assets`; listing every project says so
        too, rather than hashing fewer files without a word."""
        with tree() as t:
            p = t.yaml("projects/json/project.yaml")
            del p["assets"]
            t.put_yaml("projects/json/project.yaml", p)
            self.assertTrue(any("an available project with published binaries needs 'assets'" in f.msg
                                for f in t.lint()))
            rc, out = run(fetch.fetch, t.root, [], all_projects=True, listing=True)
            self.assertEqual(rc, 1, out)
            self.assertIn("json: json has no binaries in this release", out)


ROCQCHK_OK = """Checking library: X
CONTEXT SUMMARY
===============

* Theory: Set is predicative

* Axioms:
    Corelib.Init.Something.prim
%s
* Constants/Inductives relying on type-in-type: <none>

* Constants/Inductives relying on unsafe (co)fixpoints: %s

* Inductives whose positivity is assumed: <none>

Modules were successfully checked
"""


class Tools:
    """Stand-ins for dune, rocq, rocqchk and qemu-riscv64 on PATH."""

    def __init__(self, d, extra_axiom="", unsafe="<none>", wrapper_fails=False, dune_fails_on=None):
        self.bin = os.path.join(d, "stub-bin")
        self.log = os.path.join(d, "calls.log")
        os.makedirs(self.bin)
        # dune copies each source it builds into _build/default (the real one does too), so the library's .v files are
        # on the proofs' -Q path, where `rocq dep -sort` below finds them.
        self.put("dune", 'echo "dune $*" >> "%s"\n%s'
                         'root=""; prev=""; for a in "$@"; do [ "$prev" = --root ] && root="$a"; prev="$a"; done\n'
                         'for a in "$@"; do case "$a" in proofs/*/lib/*.vo)\n'
                         '  mkdir -p "$root/_build/default/$(dirname "$a")" && cp "$root/${a%%.vo}.v" "$root/_build/default/${a%%.vo}.v" ;;\n'
                         'esac; done\nexit 0\n'
                 % (self.log, ('case "$*" in *%s*) exit 1 ;; esac\n' % dune_fails_on) if dune_fails_on else ""))
        body = ROCQCHK_OK % (("    " + extra_axiom + "\n") if extra_axiom else "", unsafe)
        with open(os.path.join(d, "rocqchk.out"), "w") as f:
            f.write(body)
        self.put("rocqchk", 'echo "rocqchk $*" >> "%s"\ncat "%s"\n' % (self.log, os.path.join(d, "rocqchk.out")))
        # what the wrapper's Print Assumptions prints (Set Printing Fully Qualified; Rocq 9.2.0's pr_assumptionset)
        wrapper = "Axioms:\nCorelib.Init.Something.prim : Prop\n"
        if extra_axiom:
            wrapper += extra_axiom + ("" if " : " in extra_axiom else " : False") + "\n"
        if unsafe != "<none>":
            wrapper += "%s is assumed to be guarded.\n" % unsafe
        with open(os.path.join(d, "wrapper.out"), "w") as f:
            f.write(wrapper)
        # `rocq dep -sort` prints, in order, the whole closure of the .v files it is given: the files of a library on its
        # -Q path (a ...lib logical name) first, as the real one does, then the files given.  A compile of check's
        # Defined.v is answered as the kernel would (DEFINED_STUB).
        defined = os.path.join(d, "defined_stub.py")
        with open(defined, "w") as f:
            f.write(DEFINED_STUB)
        self.put("rocq", 'echo "rocq $*" >> "%s"\nulimit -s >> "%s"\n'
                         'if [ "$1" = dep ] && [ "$2" = -sort ]; then\n'
                         '  prev=""; for a in "$@"; do\n'
                         '    case "$a" in *.lib) find "$prev" -name "*.v" | sort ;; esac; prev="$a"; done\n'
                         '  for f in "$@"; do case "$f" in *.v) echo "$f" ;; esac; done; exit 0; fi\n'
                         'case "$*" in *Defined.v) exec python3 "%s" "$@" ;; esac\n'
                         'case "$*" in *Wrapper.v*) cat "%s"; %s ;; esac\n'
                         'exit 0\n'
                 % (self.log, self.log, defined, os.path.join(d, "wrapper.out"),
                    "exit 1" if wrapper_fails else "exit 0"))
        # aborts on the 13-byte counterexample input, exits 0 on the 8-byte control
        # and records the core file limit it was started with
        self.put("qemu-riscv64", 'ulimit -c >> "%s"\n'
                                 'if [ "$(wc -c < "$2")" -gt 8 ]; then kill -ABRT $$; fi\nexit 0\n'
                 % os.path.join(d, "qemu-core-limit.log"))

    def put(self, name, body):
        p = os.path.join(self.bin, name)
        with open(p, "w") as f:
            f.write("#!/bin/sh\n" + body)
        os.chmod(p, os.stat(p).st_mode | stat.S_IEXEC)

    def calls(self):
        """Every call of a stand-in so far, one per line ("" when none ran)."""
        if not os.path.exists(self.log):
            return ""
        with open(self.log) as f:
            return f.read()


class Check(unittest.TestCase):
    # [check.raise_stack_limit] refuses a stack hard limit below 1 GiB, which a host can impose on every process
    # (systemd's DefaultLimitSTACK) and which a test cannot raise.  [test_rocq_runs_with_the_largest_stack_allowed] and
    # [test_a_stack_hard_limit_below_1_gib_is_refused_on_any_host] are about that refusal; the others are about what
    # `oft check` does, so on such a host they run with a stand-in that raises the soft limit to the hard limit and
    # refuses nothing.  A test that runs `oft check` in a new process gets the real one there, and expects the refusal.
    def setUp(self):
        self.d = tempfile.TemporaryDirectory()
        self.old_path = os.environ["PATH"]
        hard = resource.getrlimit(resource.RLIMIT_STACK)[1]
        self.stack_limit_is_low = hard != resource.RLIM_INFINITY and hard < check.STACK_NEEDED
        self.old_raise_stack_limit = check.raise_stack_limit
        if self.stack_limit_is_low:
            check.raise_stack_limit = lambda: resource.setrlimit(resource.RLIMIT_STACK, (hard, hard))

    def tearDown(self):
        check.raise_stack_limit = self.old_raise_stack_limit
        os.environ["PATH"] = self.old_path
        self.d.cleanup()

    def tools(self, **kw):
        tl = Tools(self.d.name, **kw)
        os.environ["PATH"] = tl.bin + os.pathsep + self.old_path
        return tl

    def ready(self, t):
        assets = os.path.join(self.d.name, "assets")
        os.makedirs(assets)
        make_release(t, assets)
        self.assertEqual(run(fetch.fetch, t.root, ["zlib"], source=assets)[0], 0)
        t.write("toolchain/allowed-axioms.txt", "Corelib.Init.Something.prim\n")

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_statements(self):
        with tree() as t:
            self.ready(t)
            tl = self.tools()
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="statements")
            self.assertEqual(rc, 0, out)
            self.assertIn("projects/zlib/checksum_fuzzer/Statements.vo", tl.calls())
            listed = facts.load(t.root).projects["zlib"].harnesses["checksum_fuzzer"].statements.values()
            self.assertIn("projects/zlib/checksum_fuzzer: statements compiled, each of the %d listed defined\n"
                          % sum(st.rendered() for st in listed), out)
            self.assertNotIn("rocqchk", tl.calls(), "rocqchk runs only when asked")

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_a_statements_v_that_defines_no_statement_harness_yaml_lists_fails(self):
        """It compiles, but it is a check of no statement: the kernel is asked for each one harness.yaml lists."""
        with tree() as t:
            self.ready(t)
            self.tools()
            stmts = "projects/zlib/checksum_fuzzer/Statements.v"
            text = t.read(stmts)
            t.write(stmts, text[:text.index("\nDefinition ")] + "\n")
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="statements")
            self.assertEqual(rc, 1, out)
            self.assertIn("FAIL statements: projects/zlib/checksum_fuzzer/Statements.v does not define every statement "
                          "harness.yaml lists", out)
            self.assertIn("0 step(s) passed, 1 failed", out)

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_a_missing_statements_v_fails_before_any_build(self):
        with tree() as t:
            self.ready(t)
            tl = self.tools()
            os.remove(t.path("projects/zlib/checksum_fuzzer/Statements.v"))
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="statements")
            self.assertEqual(rc, 1, out)
            self.assertIn("FAIL statements: projects/zlib/checksum_fuzzer/Statements.v is missing", out)
            self.assertFalse(os.path.exists(tl.log) and "dune build" in tl.calls(), "nothing is built")

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_a_unit_whose_every_statement_is_withdrawn_has_no_statement_to_check(self):
        """The schema takes a harness with published builds whose every statement is withdrawn; its Statements.v then
        defines none."""
        with tree() as t:
            self.ready(t)
            tl = self.tools()
            withdraw_every_statement(t, "checksum_fuzzer")
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="statements")
            self.assertEqual(rc, 1, out)
            self.assertIn("is withheld or withdrawn, so Statements.v defines none: nothing to check", out)
            self.assertFalse(os.path.exists(tl.log) and "dune build" in tl.calls(), "nothing is built")

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_proofs_asked_of_a_unit_with_no_proof_fail(self):
        """--parts statements,proofs of a unit with no proof would pass on its statements alone."""
        with tree() as t:
            self.ready(t)
            self.tools()
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="statements,proofs")
            self.assertEqual(rc, 1, out)
            self.assertIn("FAIL zlib/checksum_fuzzer: nothing to check for part proofs: the unit has no proof", out)
            self.assertIn("0 step(s) passed, 1 failed", out)
            # with a proof, the same parts pass
            self._proof(t)
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="statements,proofs")
            self.assertEqual(rc, 0, out)
            self.assertIn("2 step(s) passed, 0 failed", out)

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_without_parts_a_unit_is_checked_on_the_parts_it_has(self):
        """`./oft check p/h`, as every harness README and docs/proving.md say to run it: an unproved unit passes on its
        statements, and a proved one is checked with its proofs."""
        with tree() as t:
            self.ready(t)
            self.tools()
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"])
            self.assertEqual(rc, 0, out)
            self.assertIn("1 step(s) passed, 0 failed", out)
            self._proof(t)
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"])
            self.assertEqual(rc, 0, out)
            self.assertIn("proofs/zlib/checksum_fuzzer/plain_halts: proves", out)
            self.assertIn("2 step(s) passed, 0 failed", out)
            r = subprocess.run([sys.executable, "-m", "oft", "--root", t.root, "check", "zlib/checksum_fuzzer"],
                               cwd=os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))),
                               env=dict(os.environ, PYTHONDONTWRITEBYTECODE="1"), capture_output=True, text=True)
            if self.stack_limit_is_low:
                # a new process gets this host's low hard limit, which only root can raise: `oft check` refuses
                self.assertEqual(r.returncode, 1, r.stdout + r.stderr)
                self.assertIn("FAIL the stack's hard limit is", r.stdout, r.stdout + r.stderr)
                self.assertIn("(docker run --ulimit stack=-1:-1)\n", r.stdout, r.stdout + r.stderr)
                return
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            self.assertIn("2 step(s) passed, 0 failed", r.stdout)

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_a_statement_stated_as_an_axiom_fails(self):
        """Under its own name, an Axiom, a Parameter or a Definition closed by Admitted is not a definition: Print
        Assumptions lists it."""
        for how in ("Axiom plain_halts : Prop.\n", "Parameter plain_halts : Prop.\n",
                    "Definition plain_halts : Prop.\nAdmitted.\n"):
            self.tearDown()  # a fresh stand-in directory for each
            self.setUp()
            with self.subTest(how=how), tree() as t:
                self.ready(t)
                self.tools()
                stmts = "projects/zlib/checksum_fuzzer/Statements.v"
                text = t.read(stmts)
                i = text.index("Definition plain_halts : Prop :=")
                t.write(stmts, text[:i] + how + text[text.index("\nDefinition ", i + 1) + 1:])
                rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="statements")
                self.assertEqual(rc, 1, out)
                self.assertIn("Statements.v states plain_halts as an axiom (Axiom, Parameter or Admitted)", out)

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_statements_that_assume_an_axiom_outside_the_allowlist_fail(self):
        with tree() as t:
            self.ready(t)
            self.tools()
            t.write("toolchain/allowed-axioms.txt", "Corelib.Init.Something.other\n")
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="statements")
            self.assertEqual(rc, 1, out)
            self.assertIn("the statements assume axioms outside the allowlist: Corelib.Init.Something.prim", out)

    def _check_units(self, t, tl, **env):
        """Run check-units.sh over t with a docker that runs oft here; (the completed process, the docker calls)."""
        log = os.path.join(self.d.name, "check-units.log")
        open(log, "w").close()
        tl.put("docker", """echo "docker $*" >> "$CHECK_UNITS_LOG"
case "$1" in
  pull) exit 0 ;;
  run)
    while [ "$#" -gt 0 ] && [ "$1" != python3 ]; do shift; done
    shift 3
    [ "$1" = --root ] && shift 2
    PYTHONPATH="$TOOLS" python3 -m oft.check --root "$WORK" "$@"
    ;;
esac
""")
        tools = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
        env = dict(os.environ, WORK=t.root, TOOLS=os.path.dirname(tools), PROJECTS="zlib", CX_UNITS="", FINDINGS="",
                   ASSETS=os.path.join(self.d.name, "assets"),  # ready() put the release asset here
                   PYDEPS=self.d.name, CACHE=os.path.join(self.d.name, "cache"), GITHUB_REPOSITORY="example/proofs",
                   CHECK_UNITS_LOG=log, PYTHONDONTWRITEBYTECODE="1", **env)
        r = subprocess.run(["bash", os.path.join(tools, "ci", "check-units.sh")], env=env, capture_output=True,
                           text=True)
        with open(log) as f:
            return r, f.read()

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_check_units_checks_a_unit_with_no_proof_by_its_statements_and_one_with_a_proof_with_its_proofs(self):
        """CI's check job (check-units.sh) on the plan's job: a unit the plan leaves out of proof_units is a
        statements-only run, which passes; one in it is checked with its proofs."""
        with tree() as t:
            self.ready(t)
            tl = self.tools()
            self._proof(t)
            # the plan, of a commit of this tree (a stand-in checker in tools/oft/, as keys.checker reads one)
            t.write("tools/oft/check.py", "check\n")
            git = ["git", "-C", t.root, "-c", "user.name=t", "-c", "user.email=t" + "@" + "example.invalid",
                   "-c", "commit.gpgsign=false"]
            for args in (["init", "-q"], ["add", "-A"], ["commit", "-q", "-m", "x"]):
                subprocess.run(git + args, check=True, capture_output=True,
                               env=dict(os.environ, GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_NOSYSTEM="1"))
            buf = io.StringIO()
            plan.plan(t.root, units={"zlib/checksum_fuzzer", "zlib/api-driver"}, max_jobs=1, out=buf)
            job = json.loads(buf.getvalue())["jobs"][0]
            self.assertEqual(job["check_units"], "zlib/api-driver zlib/checksum_fuzzer")
            self.assertEqual(job["proof_units"], "zlib/checksum_fuzzer")
            r, calls = self._check_units(t, tl, UNITS=job["check_units"],
                                         PROOF_UNITS=json.dumps(job["proof_units"]))
            if self.stack_limit_is_low:
                # each check runs in a new process, with this host's low hard limit: the first refuses, as above
                self.assertNotEqual(r.returncode, 0, r.stdout + r.stderr)
                self.assertIn("FAIL the stack's hard limit is", r.stdout, r.stdout + r.stderr)
                self.assertIn("(docker run --ulimit stack=-1:-1)\n", r.stdout, r.stdout + r.stderr)
                self.assertIn("python3 -m oft.check --root /work zlib/", calls)
                return
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            self.assertIn("python3 -m oft.check --root /work zlib/checksum_fuzzer --parts statements,proofs\n", calls)
            self.assertIn("python3 -m oft.check --root /work zlib/api-driver --parts statements\n", calls)
            self.assertIn("2 step(s) passed, 0 failed", r.stdout)
            self.assertIn("1 step(s) passed, 0 failed", r.stdout)

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_check_units_refuses_a_job_that_does_not_say_which_units_have_proofs(self):
        """A plan without proof_units (null through toJSON), no PROOF_UNITS at all, or one that names a unit the job
        does not build: no unit is checked without its proofs because the plan said nothing."""
        with tree() as t:
            self.ready(t)
            tl = self.tools()
            self._proof(t)
            for env, why in (({}, "PROOF_UNITS is not set"), ({"PROOF_UNITS": "null"}, "PROOF_UNITS is null"),
                             ({"PROOF_UNITS": '"zlib/api-driver"'}, "PROOF_UNITS names zlib/api-driver")):
                with self.subTest(env=env):
                    r, calls = self._check_units(t, tl, UNITS="zlib/checksum_fuzzer", **env)
                    self.assertNotEqual(r.returncode, 0, r.stdout + r.stderr)
                    self.assertIn(why, r.stderr)
                    self.assertNotIn("docker run", calls)

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_statements_with_rocqchk(self):
        with tree() as t:
            self.ready(t)
            tl = self.tools()
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="statements", rocqchk=True)
            self.assertEqual(rc, 0, out)
            self.assertIn("OssFuzzTheorems.zlib.checksum_fuzzer.Characterise", tl.calls())

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_an_axiom_outside_the_allowlist(self):
        with tree() as t:
            self.ready(t)
            self.tools(extra_axiom="Top.cheat")
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="statements", rocqchk=True)
            self.assertEqual(rc, 1)
            self.assertIn("axioms outside the allowlist: Top.cheat", out)

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_unsafe_fixpoints(self):
        with tree() as t:
            self.ready(t)
            self.tools(unsafe="Top.loop")
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="statements", rocqchk=True)
            self.assertEqual(rc, 1)
            self.assertIn("rocqchk failed", out)

    def test_binaries_not_fetched(self):
        with tree() as t:
            t.write("toolchain/allowed-axioms.txt", "Corelib.Init.Something.prim\n")
            self.tools()
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="statements")
            self.assertEqual(rc, 1)
            self.assertIn("run ./oft fetch zlib", out)

    def _proof(self, t, body="Theorem plain_halts_holds : True. Proof. exact I. Qed.\n", s="plain_halts"):
        st = next(x for x in facts.load(t.root).statements() if x.id == "zlib/checksum_fuzzer/" + s)
        t.put_yaml("proofs/zlib/checksum_fuzzer/%s/proof.yaml" % s, {
            "schema": "oss-fuzz-theorems/proof/1", "proves": st.id, "fingerprint": st.fingerprint})
        t.write("proofs/zlib/checksum_fuzzer/%s/Proof.v" % s, body)
        self.assertEqual(t.generate(), 0, t.last_output)

    LIB_MOD = "OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib"

    def _two_proofs_and_a_library(self, t):
        t.write("proofs/zlib/checksum_fuzzer/lib/Base.v", "Definition one := 1.\n")
        t.write("proofs/zlib/checksum_fuzzer/lib/Sub/Deep.v", "Definition two := 2.\n")
        self._proof(t)
        self._proof(t, "Theorem plain_halts_may_fail_holds : True. Proof. exact I. Qed.\n", s="plain_halts_may_fail")

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_a_harness_library_is_built_once_by_dune_and_is_on_every_load_path(self):
        with tree() as t:
            self.ready(t)
            self._two_proofs_and_a_library(t)
            tl = self.tools()
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="proofs")
            self.assertEqual(rc, 0, out)
            self.assertIn("proofs/zlib/checksum_fuzzer/lib: 2 files compiled or taken from dune's cache", out)
            calls = tl.calls().splitlines()
            builds = [c for c in calls if c.startswith("dune build") and "/lib/" in c]
            self.assertEqual(len(builds), 1, "the library is built once for two proofs")
            self.assertTrue(builds[0].endswith(" proofs/zlib/checksum_fuzzer/lib/Base.vo"
                                               " proofs/zlib/checksum_fuzzer/lib/Sub/Deep.vo"), builds[0])
            self.assertFalse([c for c in calls if c.startswith("rocq compile") and "/lib/" in c.split()[-1]],
                             "no library file is compiled outside dune")
            mapping = "-Q %s %s" % (t.path("_build", "default", "proofs", "zlib", "checksum_fuzzer", "lib"),
                                    self.LIB_MOD)
            users = [c for c in calls if c.startswith("rocq compile") and c.endswith(("/Proof.v", "/Wrapper.v"))]
            self.assertEqual(len(users), 4, "two proofs and two wrappers compiled afresh")
            for c in users:
                self.assertIn(mapping, c)
            self.assertNotIn("rocqchk", tl.calls(), "rocqchk runs only when asked")

    def _refused_with(self, rel, text):
        """check's output for a harness library that also holds file rel; nothing is built."""
        with tree() as t:
            self.ready(t)
            self._two_proofs_and_a_library(t)
            t.write(rel, text)
            tl = self.tools()
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="proofs")
            self.assertEqual(rc, 1)
            self.assertNotIn("dune build", tl.calls())
            return out

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_a_harness_library_with_a_build_file_of_its_own_is_refused(self):
        rel = "proofs/zlib/checksum_fuzzer/lib/Sub/dune"
        out = self._refused_with(rel, "(rule (targets Deep.vo) (action (copy x Deep.vo)))\n")
        self.assertIn("%s: a proof library holds no build file but lib/dune" % rel, out)

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_a_harness_library_with_a_dune_file_variant_is_refused(self):
        rel = "proofs/zlib/checksum_fuzzer/lib/dune-file"
        self.assertIn("%s: a proof library holds no build file but lib/dune" % rel, self._refused_with(rel, "(rule)\n"))

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_a_build_file_above_a_harness_library_is_refused(self):
        # (subdir lib ...) or (env (_ (binaries ... as rocq))) there would reach the library's rules
        for rel in ("proofs/zlib/checksum_fuzzer/dune", "proofs/zlib/dune-file", "proofs/dune", "dune"):
            with self.subTest(rel=rel):
                self.d.cleanup()
                self.d = tempfile.TemporaryDirectory()
                out = self._refused_with(rel, "(subdir lib (rule (targets Base.vo) (action (copy x Base.vo))))\n")
                self.assertIn("%s: no directory above a proof library holds a build file" % rel, out)

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_a_symbolic_link_above_a_harness_library_is_refused(self):
        with tree() as t:
            self.ready(t)
            self._two_proofs_and_a_library(t)
            os.rename(t.path("proofs/zlib/checksum_fuzzer"), t.path("elsewhere"))
            os.symlink(t.path("elsewhere"), t.path("proofs/zlib/checksum_fuzzer"))
            tl = self.tools()
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="proofs")
            self.assertEqual(rc, 1)
            self.assertIn("proofs/zlib/checksum_fuzzer: a proof library holds no symbolic link", out)
            self.assertNotIn("dune build", tl.calls())

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_a_symbolic_link_in_a_harness_library_is_refused(self):
        with tree() as t:
            self.ready(t)
            self._two_proofs_and_a_library(t)
            os.makedirs(t.path("elsewhere"))
            t.write("elsewhere/dune", "(rule)\n")
            os.symlink(t.path("elsewhere"), t.path("proofs/zlib/checksum_fuzzer/lib/x"))
            tl = self.tools()
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="proofs")
            self.assertEqual(rc, 1)
            self.assertIn("proofs/zlib/checksum_fuzzer/lib/x: a proof library holds no symbolic link", out)
            self.assertNotIn("dune build", tl.calls())

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_lib_dune_is_built_as_this_tool_renders_it(self):
        # a tree rendered by other tools (a maintainer's change to the template) is built with this tool's rule
        with tree() as t:
            self.ready(t)
            self._two_proofs_and_a_library(t)
            rel = "proofs/zlib/checksum_fuzzer/lib/dune"
            want = t.read(rel)
            t.write(rel, want + "(rule (targets Base.vo) (action (copy x Base.vo)))\n")
            self.tools()
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="proofs")
            self.assertEqual(rc, 0, out)
            self.assertIn("%s: written as this oft generate renders it" % rel, out)
            self.assertEqual(t.read(rel), want)

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_with_rocqchk_one_run_checks_every_proof_of_a_harness(self):
        with tree() as t:
            self.ready(t)
            self._two_proofs_and_a_library(t)
            tl = self.tools()
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="proofs", rocqchk=True)
            self.assertEqual(rc, 0, out)
            chk = [c for c in tl.calls().splitlines() if c.startswith("rocqchk")]
            self.assertEqual(len(chk), 1)
            self.assertIn("-Q", chk[0])
            self.assertIn(self.LIB_MOD, chk[0])
            self.assertEqual(sorted(re.findall(r"(Wrap\.\w+\.Wrapper)\b", chk[0])),
                             ["Wrap.plain_halts.Wrapper", "Wrap.plain_halts_may_fail.Wrapper"])
            self.assertIn("proofs/zlib/checksum_fuzzer: rocqchk over the wrappers of 2 proof(s)", out)

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_a_harness_library_that_does_not_compile_fails_each_proof(self):
        with tree() as t:
            self.ready(t)
            self._two_proofs_and_a_library(t)
            tl = self.tools(dune_fails_on="Deep.vo")
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="proofs")
            self.assertEqual(rc, 1)
            self.assertEqual(out.count("proofs/zlib/checksum_fuzzer/lib: does not compile"), 2, out)
            self.assertEqual(len([c for c in tl.calls().splitlines() if c.startswith("dune build") and "/lib/" in c]), 1)
            self.assertNotIn("Wrapper.v", tl.calls())

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_a_proof_goes_through_the_wrapper(self):
        with tree() as t:
            self.ready(t)
            self._proof(t)
            tl = self.tools()
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="proofs")
            self.assertEqual(rc, 0, out)
            self.assertIn("proofs/zlib/checksum_fuzzer/plain_halts: proves zlib/checksum_fuzzer/plain_halts; "
                          "assumptions: 1 axioms, all allowed", out)
            wrapper = [l for l in tl.calls().splitlines() if "Wrapper.v" in l][0].split()[-1]
            with open(wrapper) as f:
                text = f.read()
            self.assertIn("Definition certified : OssFuzzTheorems.zlib.checksum_fuzzer.Statements.plain_halts := "
                          "OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.plain_halts.Proof.plain_halts_holds.\n"
                          "Set Printing Fully Qualified.\nPrint Assumptions certified.\n", text)

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_a_bound_proof_s_wrapper_imports_the_notation_its_bound_is_written_in(self):
        """A bound's b reaches the wrapper as `(n # d)`, QArith's notation, which Rocq parses only after QArith is
        imported: without the import every bound proof is refused as not of its statement."""
        with tree() as t:
            self.ready(t)
            st = next(x for x in facts.load(t.root).statements() if x.id == "zlib/checksum_fuzzer/asan_disagrees_at_most")
            t.put_yaml("proofs/zlib/checksum_fuzzer/asan_disagrees_at_most/proof.yaml", {
                "schema": "oss-fuzz-theorems/proof/1", "proves": st.id, "fingerprint": st.fingerprint,
                "bound": "1/4"})
            t.write("proofs/zlib/checksum_fuzzer/asan_disagrees_at_most/Proof.v",
                    "Theorem asan_disagrees_at_most_holds : True. Proof. exact I. Qed.\n")
            self.assertEqual(t.generate(), 0, t.last_output)
            tl = self.tools()
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="proofs")
            self.assertEqual(rc, 0, out)
            wrapper = [l for l in tl.calls().splitlines() if "Wrapper.v" in l][0].split()[-1]
            with open(wrapper) as f:
                lines = f.read().splitlines()
            certified = next(i for i, l in enumerate(lines) if l.startswith("Definition certified"))
            self.assertIn(" (1 # 4) := ", lines[certified])
            self.assertIn("From Stdlib Require Import QArith.", lines[:certified])

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_rocq_runs_with_the_largest_stack_allowed(self):
        # large proof terms overflow the usual 8 MiB stack in the release checker image
        check.raise_stack_limit = self.old_raise_stack_limit
        with tree() as t:
            self.ready(t)
            self._proof(t)
            tl = self.tools()
            soft, hard = resource.getrlimit(resource.RLIMIT_STACK)
            try:
                # the usual 8 MiB, or a hard limit below it
                resource.setrlimit(resource.RLIMIT_STACK, (min(8 << 20, hard) if self.stack_limit_is_low else 8 << 20,
                                                           hard))
                rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="proofs")
            finally:
                resource.setrlimit(resource.RLIMIT_STACK, (soft, hard))
            if self.stack_limit_is_low:
                # this host gives every process a hard limit below the 1 GiB Rocq needs, and a test cannot raise it:
                # what `oft check` owes here is the refusal, before it compiles anything
                self.assertEqual(rc, 1, out)
                self.assertIn("the stack's hard limit is %d bytes" % hard, out)
                self.assertIn("docker run --ulimit stack=-1:-1", out)
                return
            self.assertEqual(rc, 0, out)
            want = "unlimited" if hard == resource.RLIM_INFINITY else str(hard // 1024)
            seen = {l for l in tl.calls().splitlines() if l == "unlimited" or l.isdigit()}
            self.assertEqual(seen, {want})

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_a_stack_hard_limit_below_1_gib_is_refused_on_any_host(self):
        """A process may lower its own hard limit: `oft check` runs in one whose hard limit is just below 1 GiB (or
        this host's, when that is lower) and refuses before it compiles anything; at 1 GiB, where the host allows
        it, it checks."""
        with tree() as t:
            self.ready(t)
            self._proof(t)
            tl = self.tools()
            here = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
            argv = [sys.executable, "-m", "oft.check", "--root", t.root, "zlib/checksum_fuzzer", "--parts", "proofs"]
            low = resource.getrlimit(resource.RLIMIT_STACK)[1] if self.stack_limit_is_low else check.STACK_NEEDED - 1
            for hard in [low] + ([] if self.stack_limit_is_low else [check.STACK_NEEDED]):
                with self.subTest(hard=hard):
                    r = subprocess.run(argv, cwd=here, env=dict(os.environ, PYTHONDONTWRITEBYTECODE="1"),
                                       capture_output=True, text=True,
                                       preexec_fn=lambda: resource.setrlimit(resource.RLIMIT_STACK,
                                                                             (min(8 << 20, hard), hard)))
                    if hard < check.STACK_NEEDED:
                        self.assertEqual(r.returncode, 1, r.stdout + r.stderr)
                        self.assertIn("FAIL the stack's hard limit is %d bytes; Rocq needs at least %d "
                                      "(docker run --ulimit stack=-1:-1)\n" % (hard, check.STACK_NEEDED), r.stdout)
                        self.assertFalse(os.path.exists(tl.log) and "rocq " in tl.calls(), "nothing is compiled")
                    else:
                        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
                        self.assertIn("1 step(s) passed, 0 failed", r.stdout)

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_a_proof_of_another_statement(self):
        with tree() as t:
            self.ready(t)
            self._proof(t)
            self.tools(wrapper_fails=True)
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="proofs")
            self.assertEqual(rc, 1)
            self.assertIn("the proof is not of this statement", out)

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_an_axiom_outside_the_allowlist_fails_the_proof(self):
        with tree() as t:
            self.ready(t)
            self._two_proofs_and_a_library(t)
            self.tools(extra_axiom="Top.cheat : False")
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="proofs")
            self.assertEqual(rc, 1)
            for s in ("plain_halts", "plain_halts_may_fail"):
                self.assertIn("axioms outside the allowlist: Top.cheat", out)
                self.assertIn("FAIL proofs/zlib/checksum_fuzzer/%s:" % s, out)
            self.assertIn("0 step(s) passed, 2 failed", out)

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_unsafe_fixpoints_in_the_assumptions_fail_the_proof(self):
        with tree() as t:
            self.ready(t)
            self._proof(t)
            self.tools(unsafe="Top.loop")
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="proofs")
            self.assertEqual(rc, 1)
            self.assertIn("the proof relies on what the kernel did not check: Top.loop is assumed to be guarded.", out)

    def test_print_assumptions_is_parsed_or_refused(self):
        # the forms Rocq 9.2.0 prints (printing/printer.ml, pr_assumptionset)
        self.assertEqual(check.wrapper_assumptions("$ rocq compile x\nClosed under the global context\n"), set())
        self.assertEqual(check.wrapper_assumptions(
            "$ rocq compile x\nAxioms:\nA.b : forall P : Prop,\n  P\nC.d :\n  nat\n\nWarning: unrelated\n"),
            {"A.b", "C.d"})
        refused = {
            "Axioms:\nA.b : Prop\nTop.T is assumed to be positive.\n": "Top.T is assumed to be positive.",
            "Axioms:\nTop.f is assumed to be guarded.\n": "Top.f is assumed to be guarded.",
            "Axioms:\nTop.f relies on an unsafe hierarchy.\n": "Top.f relies on an unsafe hierarchy.",
            "Axioms:\nTop.eq relies on definitional UIP.\n": "Top.eq relies on definitional UIP.",
            "Axioms:\nA.b : Prop\nTheory:\nSet is impredicative\n": "Theory: Set is impredicative",
            "Theory:\nType hierarchy is collapsed (logic is inconsistent)\n": "Theory: Type hierarchy is collapsed",
            "Axioms:\nA.b : Prop\nTop.untyped\n": "Top.untyped",
            "Axioms:\n\n": "empty",
            "": "neither",
            "some other output\n": "neither",
        }
        for text, why in refused.items():
            with self.assertRaises(check.CheckError, msg=text) as cm:
                check.wrapper_assumptions(text)
            self.assertIn(why, str(cm.exception))

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_with_rocqchk_an_axiom_fails_every_proof_of_the_harness(self):
        with tree() as t:
            self.ready(t)
            self._two_proofs_and_a_library(t)
            tl = self.tools(extra_axiom="Top.cheat : False")
            os.remove(os.path.join(self.d.name, "wrapper.out"))
            with open(os.path.join(self.d.name, "wrapper.out"), "w") as f:
                f.write("Axioms:\nCorelib.Init.Something.prim : Prop\n")
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="proofs", rocqchk=True)
            self.assertEqual(rc, 1)
            for s in ("plain_halts", "plain_halts_may_fail"):
                self.assertIn("FAIL proofs/zlib/checksum_fuzzer/%s: axioms outside the allowlist: Top.cheat" % s, out)
            self.assertIn("0 step(s) passed, 2 failed", out)
            self.assertEqual(len([c for c in tl.calls().splitlines() if c.startswith("rocqchk")]), 1)

    def test_nothing_to_check(self):
        with tree() as t:
            t.write("toolchain/allowed-axioms.txt", "x\n")
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="proofs")
            self.assertEqual(rc, 1)
            self.assertIn("nothing to check", out)

    def test_a_counterexample_reproduces(self):
        with tree() as t:
            t.write("projects/json/bin/fuzzer-parse_bjdata/fuzzer-parse_bjdata.plain", "stand-in")
            self.tools()
            rc, out = run(check.run, t.root, ["json/fuzzer-parse_bjdata"], parts="counterexamples")
            self.assertEqual(rc, 0, out)
            self.assertIn("reproduces (exit 134 SIGABRT); control exits 0", out)

    def test_qemu_runs_with_no_core_file(self):
        """With a core file limit above zero here, qemu must still start with
        none, or this test could not tell the two apart."""
        soft, hard = resource.getrlimit(resource.RLIMIT_CORE)
        raised = 1 << 20 if hard == resource.RLIM_INFINITY else hard
        if raised == 0:
            self.skipTest("the core file limit cannot be raised here, so this test could not tell")
        resource.setrlimit(resource.RLIMIT_CORE, (raised, hard))
        try:
            with tree() as t:
                t.write("projects/json/bin/fuzzer-parse_bjdata/fuzzer-parse_bjdata.plain", "stand-in")
                self.tools()
                rc, out = run(check.run, t.root, ["json/fuzzer-parse_bjdata"], parts="counterexamples")
                self.assertEqual(rc, 0, out)
        finally:
            resource.setrlimit(resource.RLIMIT_CORE, (soft, hard))
        with open(os.path.join(self.d.name, "qemu-core-limit.log")) as f:
            limits = f.read().split()
        self.assertGreaterEqual(len(limits), 2, "qemu did not run")
        self.assertEqual(set(limits), {"0"}, "qemu must start with no core file")

    def test_a_counterexample_that_stopped_reproducing(self):
        with tree() as t:
            t.write("projects/json/bin/fuzzer-parse_bjdata/fuzzer-parse_bjdata.plain", "stand-in")
            t.write("counterexamples/json/fuzzer-parse_bjdata/plain_halts/input.bin", "\0" * 6)
            self.tools()
            rc, out = run(check.run, t.root, ["json/fuzzer-parse_bjdata"], parts="counterexamples")
            self.assertEqual(rc, 1)
            self.assertIn("no longer reproduces", out)


class ReachStep(unittest.TestCase):
    def pr_reach_step(self, head_release, base_release, changed, event="pull_request", old_base_tools=False):
        """pr.yml's reach step, run as the workflow runs it, with this text as the change's release.yaml and the
        base's (None: no such file), and these changed paths: (its exit, its output, the outputs it wrote).  With
        old_base_tools, the base's tools are an oft whose plan module has no images_differ."""
        with tempfile.TemporaryDirectory() as d:
            os.makedirs(os.path.join(d, "head"))
            os.makedirs(os.path.join(d, "base"))
            for side, text in (("head", head_release), ("base", base_release)):
                if text is not None:
                    with open(os.path.join(d, side, "release.yaml"), "w") as f:
                        f.write(text)
            if old_base_tools:
                os.makedirs(os.path.join(d, "base", "tools", "oft"))
                for name in ("__init__.py", "plan.py"):
                    open(os.path.join(d, "base", "tools", "oft", name), "w").close()
            else:
                # the base's tools, as the plan job's base worktree holds them
                os.symlink(os.path.dirname(os.path.dirname(os.path.abspath(check.__file__))),
                           os.path.join(d, "base", "tools"))
            os.mkdir(os.path.join(d, "bin"))
            with open(os.path.join(d, "bin", "python"), "w") as f:
                f.write('#!/bin/sh\nexec "%s" "$@"\n' % sys.executable)
            os.chmod(os.path.join(d, "bin", "python"), 0o755)
            tmp = os.path.join(d, "runner-temp")
            os.mkdir(tmp)
            with open(os.path.join(tmp, "changed.txt"), "w") as f:
                f.write("".join(rel + "\n" for rel in changed))
            script = os.path.join(d, "reach.sh")
            step = next(s for s in yamlio.load_file(PR_YML)["jobs"]["plan"]["steps"] if s.get("id") == "reach")
            with open(script, "w") as f:
                f.write(step["run"])
            out = os.path.join(d, "output")
            # the step starts python itself, and -B of this process does not reach that child: without this the run
            # leaves tools/oft/__pycache__ behind, which the repository's own lint then refuses
            env = dict(os.environ, PATH=os.path.join(d, "bin") + os.pathsep + os.environ["PATH"], RUNNER_TEMP=tmp,
                       GITHUB_OUTPUT=out, GITHUB_STEP_SUMMARY=os.path.join(d, "summary"), EVENT=event,
                       PYTHONDONTWRITEBYTECODE="1")
            r = subprocess.run(["bash", "--noprofile", "--norc", "-eo", "pipefail", script], cwd=d, env=env,
                               capture_output=True, text=True)
            got = {}
            if os.path.exists(out):
                with open(out) as f:
                    got = dict(line.rstrip("\n").split("=", 1) for line in f if "=" in line)
            return r.returncode, r.stdout + r.stderr, got

    @unittest.skipUnless(HAVE_PR_YML, "no .github/workflows/pr.yml beside tools/oft")
    def test_the_reach_step_runs_the_controls_when_release_yaml_names_another_image(self):
        """The controls run in the checker image release.yaml names, and no file under toolchain/ changes with that
        pin: a release.yaml whose checker or runner differs from the base's runs them, and the plan job hands the
        change's checker to the controls job.  A release.yaml the base's tools cannot compare counts as another
        image, and anything but a checker digest is handed over as nothing, which the controls job refuses."""
        with open(os.path.join(REPO, "tools", "oft", "tests", "fixtures", "tree", "release.yaml")) as f:
            base = f.read()
        checker = "ghcr.io/theorem-labs/oss-fuzz-theorems-checker@sha256:" + "1" * 64
        self.assertIn(checker, base)
        other_checker = base.replace("1" * 64, "a" * 64)
        other_runner = base.replace("2" * 64, "b" * 64)
        other_date = base.replace("date: 2026-11-02", "date: 2026-11-03")
        self.assertNotEqual(other_date, base)
        docs = ["docs/checking.md"]
        cases = [
            ("no release.yaml change", base, base, docs, "false", checker),
            ("another checker", other_checker, base, ["release.yaml"], "true", checker.replace("1" * 64, "a" * 64)),
            ("another runner", other_runner, base, ["release.yaml"], "true", checker),
            ("another key only", other_date, base, ["release.yaml"], "false", checker),
            ("a release.yaml that does not parse", "images: [\n", base, ["release.yaml"], "true", ""),
            ("no base release.yaml", base, None, ["release.yaml"], "true", checker),
            ("a checker that is not a digest", base.replace("@sha256:" + "1" * 64, ":latest"), base,
             ["release.yaml"], "true", ""),
        ]
        for name, head_release, base_release, changed, controls, handed in cases:
            with self.subTest(case=name):
                rc, output, got = self.pr_reach_step(head_release, base_release, changed)
                self.assertEqual(rc, 0, output)
                self.assertEqual((got.get("controls"), got.get("checker")), (controls, handed), output)
        # base tools older than plan.images_differ: the call fails, and that alone runs the controls (the images are
        # the same, so nothing else would)
        rc, output, got = self.pr_reach_step(other_date, base, ["release.yaml"], old_base_tools=True)
        self.assertEqual(rc, 0, output)
        self.assertEqual((got.get("controls"), got.get("checker")), ("true", checker), output)


class ImagesDailyRun(unittest.TestCase):
    PUBLIC_TREE = "e" * 40
    OLD_TREE = "d" * 40
    PINNED = "ghcr.io/theorem-labs/oss-fuzz-theorems-runner@sha256:" + "0" * 64

    def plan_step(self, versions, attested, labels):
        """images.yml's plan step on a daily run, as the workflow runs it, with stand-ins for gh and docker: the runner
        package's build- versions `versions` (digests, newest first), `attested` {digest: attestations this
        repository holds} (a digest not in it: the call fails), and `labels` {digest: its tools/oft tree label}.
        (its exit, its output, the outputs it wrote)."""
        with tempfile.TemporaryDirectory() as d:
            with open(os.path.join(d, "release.yaml"), "w") as f:
                f.write("images:\n  runner: %s\n" % self.PINNED)
            data = {"versions": versions, "attested": attested, "labels": labels,
                    "commit": "c" * 40, "tree": self.PUBLIC_TREE}
            with open(os.path.join(d, "data.json"), "w") as f:
                json.dump(data, f)
            os.mkdir(os.path.join(d, "bin"))
            stand_in = (
                "#!%s\nimport json, os, sys\n"
                "data = json.load(open(os.path.join(os.environ['STAND_IN_DATA'])))\n"
                "a = sys.argv[1:]\n" % sys.executable)
            gh = stand_in + (
                "path = a[1]\n"
                "if path.endswith('/commits/main'): print(data['commit'])\n"
                "elif '/contents/tools?' in path: print(data['tree'])\n"
                "elif '/versions?' in path: print('\\n'.join(data['versions']))\n"
                "elif '/attestations/' in path:\n"
                "    d = path.rsplit('/', 1)[1]\n"
                "    if d not in data['attested']: sys.exit('gh: Not Found (HTTP 404)')\n"
                "    print(data['attested'][d])\n"
                "else: sys.exit('gh stand-in: %r' % a)\n")
            docker = stand_in + (
                "ref = a[3]\n"
                "d = ref.rsplit('@', 1)[1]\n"
                "tree = data['labels'].get(d)\n"
                "print(json.dumps({'oss-fuzz-theorems.tools.tree': tree} if tree else {}))\n")
            for name, text in (("gh", gh), ("docker", docker)):
                with open(os.path.join(d, "bin", name), "w") as f:
                    f.write(text)
                os.chmod(os.path.join(d, "bin", name), 0o755)
            step = next(s for s in yamlio.load_file(IMAGES_YML)["jobs"]["plan"]["steps"] if s.get("id") == "plan")
            script = os.path.join(d, "plan.sh")
            with open(script, "w") as f:
                f.write(step["run"])
            tmp = os.path.join(d, "runner-temp")
            os.mkdir(tmp)
            out = os.path.join(d, "output")
            env = dict(os.environ, PATH=os.path.join(d, "bin") + os.pathsep + os.environ["PATH"], RUNNER_TEMP=tmp,
                       GITHUB_OUTPUT=out, GITHUB_STEP_SUMMARY=os.path.join(d, "summary"), EVENT="schedule",
                       CHOICE="", BEFORE="", GH_TOKEN="x", GITHUB_REF="refs/heads/main",
                       GITHUB_REPOSITORY_OWNER="theorem-labs", GITHUB_REPOSITORY="theorem-labs/oss-verify-proofs",
                       STAND_IN_DATA=os.path.join(d, "data.json"))
            r = subprocess.run(["bash", "--noprofile", "--norc", "-eo", "pipefail", script], cwd=d, env=env,
                               capture_output=True, text=True)
            got = {}
            if os.path.exists(out):
                with open(out) as f:
                    got = dict(line.rstrip("\n").split("=", 1) for line in f if "=" in line)
            return r.returncode, r.stdout + r.stderr, got

    @unittest.skipUnless(os.path.exists(IMAGES_YML) and shutil.which("jq"), "no images.yml beside tools/oft, or no jq")
    def test_the_daily_run_compares_the_newest_attested_runner(self):
        """A push that failed after `docker push` leaves a newest version with no attestation, labelled with the
        public tools tree; the attestations call answers it with an empty list.  The daily run passes over it and
        compares the newest runner this workflow finished, so a tree no attested runner carries is built again."""
        failed, finished = "sha256:" + "a" * 64, "sha256:" + "b" * 64
        labels = {failed: self.PUBLIC_TREE, finished: self.OLD_TREE}
        for name, attested in (("an empty list", {failed: 0, finished: 1}), ("a refused call", {finished: 2})):
            with self.subTest(newest_unattested=name):
                rc, output, got = self.plan_step([failed, finished], attested, labels)
                self.assertEqual(rc, 0, output)
                self.assertIn("runner ghcr.io/theorem-labs/oss-fuzz-theorems-runner@%s" % finished, output)
                self.assertEqual(got.get("images"), '["runner"]', output)
        rc, output, got = self.plan_step([finished], {finished: 1}, {finished: self.PUBLIC_TREE})
        self.assertEqual((rc, got.get("images")), (0, "[]"), output)

    @unittest.skipUnless(os.path.exists(IMAGES_YML) and shutil.which("jq"), "no images.yml beside tools/oft, or no jq")
    def test_the_daily_run_says_why_it_compares_the_pinned_runner(self):
        """With no attested runner, the run compares the runner release.yaml pins, and its log says why."""
        rc, output, got = self.plan_step(["sha256:" + "a" * 64], {}, {"sha256:" + "0" * 64: self.PUBLIC_TREE})
        self.assertEqual((rc, got.get("images")), (0, "[]"), output)
        self.assertIn("::warning::no pushed runner has an attestation of this repository", output)
        self.assertIn("runner %s" % self.PINNED, output)



FINDING = "findings/zlib/checksum_fuzzer/stand-in-abort"
UNPATCHED = "findings/zlib/unpatched.yaml"


def prune(t):
    """Mark the fixture finding pruned, its record showing no statement false, and drop its patch from the series."""
    y = t.yaml(FINDING + "/finding.yaml")
    y["state"] = "pruned"
    y["input"] = {b: dict(y["control"][b]) for b in y["control"]}
    t.put_yaml(FINDING + "/finding.yaml", y)
    t.write("findings/zlib/checksum_fuzzer/series", "")


def withhold_checksum_fuzzer(t):
    """Withhold every published checksum_fuzzer build and statement, but leave its findings and unpatched pins: the
    planner must still rerun the finding on the latter."""
    y = t.yaml("projects/zlib/checksum_fuzzer/harness.yaml")
    n = 0
    for build in y["builds"].values():
        build["withheld"] = "not-yet-published"
        for key in ("bytes", "sha256", "segments"):
            build.pop(key, None)
        n += 1
    for statement in y["statements"].values():
        for key in ("witness", "binds_checks"):
            statement.pop(key, None)
        statement["status"], statement["withheld"] = "withheld", "not-yet-published"
    t.put_yaml("projects/zlib/checksum_fuzzer/harness.yaml", y)
    release = t.yaml("release.yaml")
    release["counts"]["binaries"] -= n
    t.put_yaml("release.yaml", release)


def unpatched_release(t, assets, tamper=None):
    """Give the unpatched builds that the fixture's unpatched.yaml pins stand-in bytes, pack them as
    zlib-unpatched-bin.tar.zst in `assets`, and pin both levels of SHA-256 in unpatched.yaml."""
    y = t.yaml(UNPATCHED)
    files = {}
    for h, builds in y["harnesses"].items():
        for b, rec in builds.items():
            data = b"\x7fELF unpatched stand-in for " + rec["file"].encode()
            files["%s/%s" % (h, rec["file"])] = data
            rec["bytes"], rec["sha256"] = len(data), hashlib.sha256(data).hexdigest()
    raw = io.BytesIO()
    with tarfile.open(fileobj=raw, mode="w") as tf:
        for name, data in (tamper(files) if tamper else files).items():
            info = tarfile.TarInfo(name)
            info.size = len(data)
            tf.addfile(info, io.BytesIO(data))
    tar = os.path.join(assets, "zlib-unpatched-bin.tar")
    with open(tar, "wb") as f:
        f.write(raw.getvalue())
    subprocess.run(["zstd", "-q", "-f", "--rm", tar], check=True)
    y["asset"]["bytes"] = os.path.getsize(tar + ".zst")
    y["asset"]["sha256"] = facts.sha256_file(tar + ".zst")
    t.put_yaml(UNPATCHED, y)
    return files


# The unpatched binaries, run under qemu: a build aborts on an input that has the line "<build>: abort", prints
# "differs" first on one that has "<build>: differs", and otherwise prints "ran" and exits 0.
QEMU_BY_BUILD = ('b="${1##*.}"\n'
                 'if grep -qax "$b: abort" "$2"; then kill -ABRT $$; fi\n'
                 'if grep -qax "$b: differs" "$2"; then echo differs; fi\n'
                 'echo ran\nexit 0\n')


@unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
class Findings(unittest.TestCase):
    def setUp(self):
        self.d = tempfile.TemporaryDirectory()
        self.assets = os.path.join(self.d.name, "assets")
        os.makedirs(self.assets)
        self.old_path = os.environ["PATH"]
        self.tl = Tools(self.d.name)
        self.tl.put("qemu-riscv64", QEMU_BY_BUILD)
        os.environ["PATH"] = self.tl.bin + os.pathsep + self.old_path

    def tearDown(self):
        os.environ["PATH"] = self.old_path
        self.d.cleanup()

    def ready(self, t):
        add_findings(t)
        unpatched_release(t, self.assets)
        rc, out = run(fetch.fetch, t.root, ["zlib"], source=self.assets, findings=True)
        self.assertEqual(rc, 0, out)

    def check(self, t, **kw):
        return run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="findings", **kw)

    def test_fetch_unpacks_the_unpatched_binaries_under_findings(self):
        with tree() as t:
            add_findings(t)
            files = unpatched_release(t, self.assets)
            rc, out = run(fetch.fetch, t.root, ["zlib"], source=self.assets, findings=True)
            self.assertEqual(rc, 0, out)
            self.assertIn("zlib: zlib-unpatched-bin.tar.zst", out)
            self.assertIn("8 binaries, each SHA-256 checked", out)
            for name, data in files.items():
                with open(t.path("findings/zlib/bin", name), "rb") as f:
                    self.assertEqual(f.read(), data)
            self.assertFalse(os.path.exists(t.path("projects/zlib/bin")), "the published binaries are not fetched")
            self.assertEqual([str(f) for f in t.lint()], [], "the fetched binaries are never tracked")

    def test_fetch_unpacks_the_licence_files_beside_the_unpatched_binaries(self):
        """The unpatched archive may carry the licence files of the components compiled into its binaries, as a
        published one does; they go to findings/<p>/bin/LICENSES/."""
        lic = {"LICENSES/zlib/LICENSE": b"zlib licence\n"}
        with tree() as t:
            add_findings(t)
            unpatched_release(t, self.assets, tamper=lambda f: dict(f, **lic))
            rc, out = run(fetch.fetch, t.root, ["zlib"], source=self.assets, findings=True)
            self.assertEqual(rc, 0, out)
            self.assertIn("8 binaries, each SHA-256 checked; 1 licence files", out)
            with open(t.path("findings/zlib/bin/LICENSES/zlib/LICENSE"), "rb") as f:
                self.assertEqual(f.read(), lic["LICENSES/zlib/LICENSE"])
            self.assertEqual([str(f) for f in t.lint()], [], "the fetched licence files are never tracked")

    def test_fetch_lists_the_unpatched_asset(self):
        with tree() as t:
            add_findings(t)
            rc, out = run(fetch.fetch, t.root, ["zlib"], findings=True, listing=True)
            self.assertEqual(rc, 0, out)
            self.assertEqual(out, "findings-zlib zlib-unpatched-bin.tar.zst %s\n" % t.yaml(UNPATCHED)["asset"]["sha256"])

    def test_fetch_refuses_a_member_whose_sha256_differs_from_unpatched_yaml(self):
        with tree() as t:
            add_findings(t)
            unpatched_release(t, self.assets, tamper=lambda f: dict(
                f, **{"checksum_fuzzer/checksum_fuzzer.asan": b"\x7fELF other"}))
            rc, out = run(fetch.fetch, t.root, ["zlib"], source=self.assets, findings=True)
            self.assertEqual(rc, 1)
            self.assertIn("checksum_fuzzer/checksum_fuzzer.asan does not match its unpatched.yaml SHA-256", out)
            self.assertFalse(os.path.exists(t.path("findings/zlib/bin/checksum_fuzzer/checksum_fuzzer.plain")))

    def test_fetch_refuses_a_project_without_unpatched_binaries(self):
        with tree() as t:
            add_findings(t)
            rc, out = run(fetch.fetch, t.root, ["json"], source=self.assets, findings=True)
            self.assertEqual(rc, 1)
            self.assertIn("json: no findings/json/unpatched.yaml", out)

    def test_a_finding_whose_runs_match_its_record(self):
        with tree() as t:
            self.ready(t)
            rc, out = self.check(t)
            self.assertEqual(rc, 0, out)
            self.assertIn(FINDING + ": 6 runs match the record; the input shows asan_agrees and asan_ubsan_agrees "
                          "false\n", out)
            self.assertIn("oft check: 1 step(s) passed, 0 failed", out)

    def test_a_recorded_stdout_that_differs_names_the_build_the_input_and_both_values(self):
        with tree() as t:
            self.ready(t)
            y = t.yaml(FINDING + "/finding.yaml")
            y["input"]["plain"]["stdout_sha256"] = "0" * 63 + "1"
            t.put_yaml(FINDING + "/finding.yaml", y)
            rc, out = self.check(t)
            self.assertEqual(rc, 1)
            self.assertIn("FAIL %s: input.bin on plain: stdout_sha256 is %s, recorded %s" % (
                FINDING, y["control"]["plain"]["stdout_sha256"], "0" * 63 + "1"), out)

    def test_an_unpatched_binary_that_is_not_the_pinned_one(self):
        with tree() as t:
            self.ready(t)
            with open(t.path("findings/zlib/bin/checksum_fuzzer/checksum_fuzzer.asan"), "ab") as f:
                f.write(b"!")
            rc, out = self.check(t)
            self.assertEqual(rc, 1)
            self.assertIn("findings/zlib/bin/checksum_fuzzer/checksum_fuzzer.asan does not match its SHA-256 in "
                          "findings/zlib/unpatched.yaml (run ./oft fetch --findings zlib)", out)

    def test_a_pruned_finding_that_still_reproduces(self):
        with tree() as t:
            self.ready(t)
            prune(t)
            rc, out = self.check(t)
            self.assertEqual(rc, 1)
            self.assertIn("FAIL %s: pruned, but still reproduces: on the unpatched binaries the input shows "
                          "asan_agrees and asan_ubsan_agrees false" % FINDING, out)

    def test_a_pruned_finding_whose_input_agrees(self):
        with tree() as t:
            self.ready(t)
            prune(t)
            t.write(FINDING + "/input.bin", b"\0\0\0\0\0\0\nno longer aborts\n", "wb")
            rc, out = self.check(t)
            self.assertEqual(rc, 0, out)
            self.assertIn(FINDING + ": 6 runs match the record; pruned: the input shows no statement false\n", out)

    def test_record_prints_the_runs_to_commit(self):
        with tree() as t:
            self.ready(t)
            y = t.yaml(FINDING + "/finding.yaml")
            recorded = {"input": y.pop("input"), "control": y.pop("control")}
            t.put_yaml(FINDING + "/finding.yaml", y)
            rc, out = self.check(t)
            self.assertEqual(rc, 1, "without --record, a finding with no runs is a tree error")
            self.assertIn("no runs recorded", out)
            rc, out = self.check(t, record=True)
            self.assertEqual(rc, 0, out)
            head = "# %s/finding.yaml: add these runs\n" % FINDING
            self.assertIn(head, out)
            printed = out.split(head, 1)[1].split("\noft check:", 1)[0]
            self.assertEqual(yamlio.load(printed), recorded)
            t.put_yaml(FINDING + "/finding.yaml", dict(y, **yamlio.load(printed)))
            self.assertEqual(self.check(t)[0], 0)

    def test_record_prints_no_runs_unless_the_input_shows_each_statement_false(self):
        """The final gate's case: the record names asan_agrees and plain_halts, and its input aborts asan but exits 0
        on plain.  Runs printed for it would anchor a record lint refuses, whose statements never shrink."""
        with tree() as t:
            self.ready(t)
            y = t.yaml(FINDING + "/finding.yaml")
            del y["input"], y["control"]
            y["statements"] = ["asan_agrees", "plain_halts"]
            t.put_yaml(FINDING + "/finding.yaml", y)
            rc, out = self.check(t, record=True)
            self.assertEqual(rc, 1, out)
            self.assertIn("FAIL %s: on the unpatched binaries the input does not show plain_halts false, so there are "
                          "no runs to record" % FINDING, out)
            self.assertNotIn("add these runs", out)

    def test_record_prints_no_runs_when_the_control_shows_a_statement_false(self):
        with tree() as t:
            self.ready(t)
            y = t.yaml(FINDING + "/finding.yaml")
            del y["input"], y["control"]
            t.put_yaml(FINDING + "/finding.yaml", y)
            t.write(FINDING + "/control.bin", b"\0\0\0\0\0\0\nasan: abort\n", "wb")
            rc, out = self.check(t, record=True)
            self.assertEqual(rc, 1, out)
            self.assertIn("FAIL %s: the control does not behave normally: on the unpatched binaries it shows asan_agrees "
                          "false, so there are no runs to record" % FINDING, out)
            self.assertNotIn("add these runs", out)

    def test_record_of_a_pruned_finding_prints_runs_only_when_the_input_shows_none_false(self):
        with tree() as t:
            self.ready(t)
            prune(t)
            y = t.yaml(FINDING + "/finding.yaml")
            del y["input"], y["control"]
            t.put_yaml(FINDING + "/finding.yaml", y)
            rc, out = self.check(t, record=True)
            self.assertEqual(rc, 1, out)
            self.assertIn("pruned, but still reproduces", out)
            self.assertNotIn("add these runs", out)
            t.write(FINDING + "/input.bin", b"\0\0\0\0\0\0\nno longer aborts\n", "wb")
            rc, out = self.check(t, record=True)
            self.assertEqual(rc, 0, out)
            self.assertIn("add these runs", out)

    def test_record_prints_no_runs_when_a_build_times_out(self):
        """A timeout is not a fixed outcome: a slower or faster machine gives another.  The input runs past the limit
        on its first build, so --record fails, prints nothing, and the record stays a draft; the same timeout in a
        re-run fails that run."""
        self.tl.put("qemu-riscv64", 'if grep -qax "slow" "$2"; then exec sleep 30; fi\n' + QEMU_BY_BUILD)
        with tree() as t:
            self.ready(t)
            t.write(FINDING + "/input.bin", b"\0\0\0\0\0\0\nasan: abort\nslow\n", "wb")
            y = t.yaml(FINDING + "/finding.yaml")
            del y["input"], y["control"]
            t.put_yaml(FINDING + "/finding.yaml", y)
            rc, out = self.check(t, record=True, timeout=1)
            self.assertEqual(rc, 1, out)
            self.assertIn("FAIL %s: input.bin on plain ran past the 1 s limit: a timeout is not a fixed outcome, so "
                          "there are no runs to record" % FINDING, out)
            self.assertNotIn("add these runs", out)
        with tree() as t:
            self.ready(t)
            t.write(FINDING + "/input.bin", b"\0\0\0\0\0\0\nasan: abort\nslow\n", "wb")
            rc, out = self.check(t, timeout=1)
            self.assertEqual(rc, 1, out)
            self.assertIn("ran past the 1 s limit: a timeout is not a fixed outcome, so the record is not reproduced",
                          out)

    def test_record_prints_no_runs_ended_by_a_signal_no_finding_records(self):
        """The cross-model review's case: the input's asan runs die of SIGKILL, which the finding schema and the
        ledger refuse, so --record fails and prints nothing."""
        self.tl.put("qemu-riscv64", 'b="${1##*.}"\ncase "$b" in asan|asan-ubsan) '
                    'if grep -qax "$b: abort" "$2"; then kill -KILL $$; fi ;; esac\n' + QEMU_BY_BUILD)
        with tree() as t:
            self.ready(t)
            y = t.yaml(FINDING + "/finding.yaml")
            del y["input"], y["control"]
            t.put_yaml(FINDING + "/finding.yaml", y)
            rc, out = self.check(t, record=True)
            self.assertEqual(rc, 1, out)
            self.assertIn("FAIL %s: input.bin on asan ended by SIGKILL, which a finding's run does not record (only "
                          "SIGABRT, SIGILL, SIGSEGV, SIGBUS, SIGFPE, SIGTRAP), so there are no runs to record" % FINDING,
                          out)
            self.assertNotIn("add these runs", out)

    def test_the_run_shape_matches_the_finding_schema(self):
        """rules.run_ok, which --record and the ledger share, allows the signals the finding schema allows."""
        self.assertEqual(tuple(schema.load_schema("finding")["defs"]["run"]["fields"]["signal"]["values"]),
                         rules.RUN_SIGNALS)

    def test_record_without_the_findings_part(self):
        with tree() as t:
            self.ready(t)
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="counterexamples", record=True)
            self.assertEqual(rc, 1)
            self.assertIn("--record records findings: add findings to --parts", out)

    def test_a_unit_without_findings_has_nothing_to_check(self):
        with tree() as t:
            self.ready(t)
            rc, out = run(check.run, t.root, ["json/fuzzer-parse_bjdata"], parts="findings")
            self.assertEqual(rc, 1)
            self.assertIn("json/fuzzer-parse_bjdata: nothing to check for parts findings", out)

    def test_the_counterexample_check_is_unchanged_by_the_shared_run(self):
        with tree() as t:
            t.write("projects/json/bin/fuzzer-parse_bjdata/fuzzer-parse_bjdata.plain", "stand-in")
            t.write("counterexamples/json/fuzzer-parse_bjdata/plain_halts/input.bin",
                    "\0\0\0\0\0\0\nplain: abort\n")
            rc, out = run(check.run, t.root, ["json/fuzzer-parse_bjdata"], parts="counterexamples")
            self.assertEqual(rc, 0, out)
            self.assertIn("reproduces (exit 134 SIGABRT); control exits 0", out)

    def test_check_units_runs_a_withheld_finding_without_published_units(self):
        with tree() as t:
            add_findings(t)
            withhold_checksum_fuzzer(t)
            unpatched_release(t, self.assets)
            log = os.path.join(self.d.name, "check-units.log")
            tl = self.tl
            tl.put("qemu-riscv64", QEMU_BY_BUILD)
            tl.put("gh", """echo "gh $*" >> "$CHECK_UNITS_LOG"
for arg; do
  case "$arg" in *-unpatched-bin.tar.zst) cp "$CHECK_UNITS_SOURCE/$arg" "$CHECK_UNITS_DEST/$arg"; exit 0 ;; esac
done
exit 2
""")
            tl.put("docker", """echo "docker $*" >> "$CHECK_UNITS_LOG"
case "$1" in
  pull) exit 0 ;;
  run)
    while [ "$#" -gt 0 ] && [ "$1" != python3 ]; do shift; done
    shift 3
    [ "$1" = --root ] && shift 2
    PYTHONPATH="$TOOLS" python3 -m oft.check --root "$WORK" "$@"
    ;;
esac
""")
            assets = os.path.join(self.d.name, "ci-assets")
            cache = os.path.join(self.d.name, "cache")
            os.makedirs(assets)
            os.makedirs(cache)
            tools = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
            script = os.path.join(tools, "ci", "check-units.sh")
            env = dict(os.environ, PATH=tl.bin + os.pathsep + self.old_path, WORK=t.root, TOOLS=os.path.dirname(tools),
                       UNITS="", PROOF_UNITS='""', PROJECTS="", CX_UNITS="", FINDINGS="zlib/checksum_fuzzer",
                       ASSETS=assets,
                       PYDEPS=self.d.name, CACHE=cache, GITHUB_REPOSITORY="example/proofs",
                       CHECK_UNITS_LOG=log, CHECK_UNITS_SOURCE=self.assets, CHECK_UNITS_DEST=assets,
                       PYTHONDONTWRITEBYTECODE="1")
            r = subprocess.run(["bash", script], env=env, capture_output=True, text=True)
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            self.assertIn("oft check: 1 step(s) passed, 0 failed", r.stdout)
            with open(log) as f:
                calls = f.read()
            self.assertIn("gh release download findings-zlib", calls)
            self.assertIn("python3 -m oft.check --root /work zlib/checksum_fuzzer --parts findings", calls)
            self.assertNotIn("statements,proofs", calls)


if __name__ == "__main__":
    unittest.main()
