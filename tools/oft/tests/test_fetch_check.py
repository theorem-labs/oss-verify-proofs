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
import types
import unittest
from unittest import mock

from oft import check, facts, fetch, generate, layout, plan, port, rules, schema, symbols, unitpaths, yamlio
from oft.tests.helpers import (NEXT_RECIPE, OWN_RECIPE, REPO, add_findings, later_release, older_shape, own_recipe,
                               recipe_only_rebuild, rename_namespace, tree)

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
            fact = layout.symbol_fact(proj.name, h.name, b)
            if os.path.exists(t.path(fact)):
                # a symbol fact is of the binary harness.yaml pins (lint, schema): the stand-in one follows the pin
                t.write(fact, symbols.HEADER % y["builds"][b]["sha256"] + "\n" + t.read(fact).partition("\n")[2])
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


def regular(name):
    return tarfile.TarInfo(name)


def directory(name):
    info = tarfile.TarInfo(name)
    info.type = tarfile.DIRTYPE
    return info


def release_with(t, assets, extra):
    """make_release's archive with `extra`, a list of (TarInfo, its bytes or None for a member that has none),
    written after the pinned binaries and pinned in project.yaml.  For the members a dict of name to bytes cannot
    express: a directory, a symbolic link."""
    files = make_release(t, assets)
    raw = io.BytesIO()
    with tarfile.open(fileobj=raw, mode="w") as tf:
        for name, data in files.items():
            info = tarfile.TarInfo(name)
            info.size = len(data)
            tf.addfile(info, io.BytesIO(data))
        for info, data in extra:
            if data is not None:
                info.size = len(data)
            tf.addfile(info, io.BytesIO(data) if data is not None else None)
    tar = os.path.join(assets, "zlib-bin.tar")
    with open(tar, "wb") as f:
        f.write(raw.getvalue())
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


def same_run(out):
    """out with each path under the check's work directory, which every run makes anew, as WORK."""
    return re.sub(r"/\S*?oft-check-[^\s)]*", "WORK", out)


# What a view of the unit p/h holds besides the root's build files: its project's project.yaml and the unit's own
# paths, as tools/oft/keys.py keys them, in either layout (projects/{p}/{h} holds the per-project ones), with the
# binaries fetched into them (layout.unpatched_bin_dir for the findings').
VIEW_PATHS = ("projects/{p}/project.yaml", "projects/{p}/{h}", "projects/{p}/bin/{h}",
              "projects/{p}/unpatched-bin/{h}", "projects/{p}/unpatched.yaml", "proofs/{p}/{h}",
              "counterexamples/{p}/{h}", "findings/{p}/unpatched.yaml", "findings/{p}/{h}")
# The root entries a view leaves out: those that hold the files of every unit, and release.yaml.
NOT_IN_VIEW = {"projects", "proofs", "counterexamples", "findings", "notes", "patches", "index", "analyses",
               "release.yaml"}


def unit_view(t, unit, dest):
    """dest, made to hold only what a view of unit holds: the root's build files (dune-project, theories/,
    toolchain/), and VIEW_PATHS of the unit.  No release.yaml and no file of another unit."""
    p, h = unit.split("/")
    copies = [name for name in os.listdir(t.root) if name not in NOT_IN_VIEW]
    copies += [rel.format(p=p, h=h) for rel in VIEW_PATHS if os.path.exists(t.path(rel.format(p=p, h=h)))]
    for rel in copies:
        os.makedirs(os.path.dirname(os.path.join(dest, rel)), exist_ok=True)
        (shutil.copytree if os.path.isdir(t.path(rel)) else shutil.copy2)(t.path(rel), os.path.join(dest, rel))
    return dest


# Stands in for docker in check-units.sh.  It logs each call to $CHECK_UNITS_LOG.  `run` lays out each -v mount of
# the call in a directory of its own, as a copy of the mount's source at the mount's path, the shallower mounts
# first, and takes the write permission off each copy of a `:ro` mount once every mount is laid out (the containers
# run as a user, -u, so a write there fails as it does on a read-only mount).  It runs the container's
# `python3 -m oft.*` on the host with /work and /facts as those copies and the trusted tools at $TOOLS, and copies a
# writable /facts back to its source.  So a check sees what its mounts give it, and nothing else of the tree.
FAKE_DOCKER = r'''import os, shutil, stat, subprocess, sys, tempfile
with open(os.environ["CHECK_UNITS_LOG"], "a") as f:
    f.write("docker " + " ".join(sys.argv[1:]) + "\n")
args = sys.argv[1:]
if args[0] == "pull":
    sys.exit(0)
assert args[0] == "run", args
mounts, i = [], 1
while args[i] != "python3":
    if args[i] == "-v":
        src, dst, *mode = args[i + 1].split(":")
        mounts.append((src, dst, mode == ["ro"]))
    i += 2 if args[i] in ("-v", "-u", "-e", "-w", "--network", "--cpuset-cpus") else 1
root = tempfile.mkdtemp(prefix="container-")
for src, dst, _ro in sorted(mounts, key=lambda m: m[1].count("/")):
    if dst in ("/tools", "/pydeps"):
        continue
    at = root + dst
    if os.path.isdir(at):
        shutil.rmtree(at)  # an empty mount point in the view
    if os.path.isdir(src):
        shutil.copytree(src, at, symlinks=True)
    else:
        os.makedirs(os.path.dirname(at), exist_ok=True)
        shutil.copy2(src, at)

def chmod_tree(top, writable):
    paths = [top] if not os.path.isdir(top) else [top] + [os.path.join(dp, n) for dp, dn, fn in os.walk(top)
                                                           for n in dn + fn]
    for p in paths:
        if not os.path.islink(p):
            m = os.stat(p).st_mode
            os.chmod(p, (m | stat.S_IWUSR) if writable else (m & ~(stat.S_IWUSR | stat.S_IWGRP | stat.S_IWOTH)))

for src, dst, ro in mounts:
    if ro and dst not in ("/tools", "/pydeps"):
        chmod_tree(root + dst, writable=False)
cmd = [root + a if a in ("/work", "/facts") else a for a in args[i:]]
rc = subprocess.run(cmd, cwd=root + "/work", env=dict(os.environ, PYTHONPATH=os.environ["TOOLS"])).returncode
for src, dst, ro in mounts:
    if dst == "/facts" and not ro:
        shutil.copytree(root + dst, src, dirs_exist_ok=True)
chmod_tree(root, writable=True)
shutil.rmtree(root)
sys.exit(rc)
'''


def fake_docker(tl, d):
    """Put FAKE_DOCKER on tl's PATH as docker, its script in d."""
    script = os.path.join(d, "fake-docker.py")
    with open(script, "w") as f:
        f.write(FAKE_DOCKER)
    tl.put("docker", 'exec "%s" "%s" "$@"\n' % (sys.executable, script))


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
# Defined.v prints its assumptions with Redirect "assumptions": into assumptions.out in the compile's working directory
with open("assumptions.out", "w") as f:
    f.write("Axioms:\n" + "\n".join(axioms) + "\n")
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

    def test_a_harness_the_tree_has_no_home_for_is_skipped(self):
        """The release archive is built from the whole project, so it carries the binaries of harnesses this tree
        holds no build record of: minigzip_fuzzer, which projects/zlib/project.yaml lists and whose folder the tree
        does not hold.  Its members are skipped, never written, and the pinned ones land unchanged."""
        other = {"minigzip_fuzzer/minigzip_fuzzer.plain": b"\x7fELF another harness",
                 "minigzip_fuzzer/minigzip_fuzzer.asan": b"\x7fELF another harness, asan"}
        with tree() as t, tempfile.TemporaryDirectory() as a:
            files = make_release(t, a, tamper=lambda f: dict(f, **other))
            rc, out = run(fetch.fetch, t.root, ["zlib"], source=a)
            self.assertEqual(rc, 0, out)
            self.assertIn("8 binaries, each SHA-256 checked; 2 files of minigzip_fuzzer skipped, which this tree "
                          "has no home for", out)
            self.assertFalse(os.path.exists(t.path("projects/zlib/bin/minigzip_fuzzer")))
            for name, data in files.items():
                if name in other:
                    continue
                with open(t.path("projects/zlib/bin", name), "rb") as f:
                    self.assertEqual(f.read(), data)
            self.assertEqual(run(fetch.verify_sha, t.root, ["zlib"])[0], 0)

    def test_a_directory_member_of_a_skipped_harness_is_skipped_and_counts_nothing(self):
        with tree() as t, tempfile.TemporaryDirectory() as a:
            release_with(t, a, [(directory("minigzip_fuzzer/"), None),
                                (regular("minigzip_fuzzer/minigzip_fuzzer.plain"), b"\x7fELF another")])
            rc, out = run(fetch.fetch, t.root, ["zlib"], source=a)
            self.assertEqual(rc, 0, out)
            self.assertIn("8 binaries, each SHA-256 checked; 1 file of minigzip_fuzzer skipped", out)
            self.assertFalse(os.path.exists(t.path("projects/zlib/bin/minigzip_fuzzer")))

    def test_a_harness_no_project_yaml_names_is_still_refused(self):
        """The guard stands for a member the facts know nothing about: only the project's own harnesses are skipped."""
        for bad in ("other_fuzzer/other_fuzzer.plain", "minigzip_fuzzer/deeper/x", "minigzip_fuzzer"):
            with self.subTest(bad), tree() as t, tempfile.TemporaryDirectory() as a:
                make_release(t, a, tamper=lambda f: dict(f, **{bad: b"x"}))
                rc, out = run(fetch.fetch, t.root, ["zlib"], source=a)
                self.assertEqual(rc, 1, out)
                self.assertIn("unexpected member", out)
                self.assertEqual(os.listdir(t.path("projects/zlib/bin")), [], "nothing is unpacked or left staged")

    def test_an_unpinned_file_of_a_pinned_harness_is_still_refused(self):
        with tree() as t, tempfile.TemporaryDirectory() as a:
            make_release(t, a, tamper=lambda f: dict(f, **{"checksum_fuzzer/checksum_fuzzer.extra": b"x"}))
            rc, out = run(fetch.fetch, t.root, ["zlib"], source=a)
            self.assertEqual(rc, 1, out)
            self.assertIn("unexpected member", out)
            self.assertEqual(os.listdir(t.path("projects/zlib/bin")), [])

    def test_a_member_of_a_skipped_harness_that_is_no_file_is_refused(self):
        """A skipped harness's member is skipped by its name, not trusted by it: a symbolic link there is refused,
        as it is anywhere else in the archive."""
        link = tarfile.TarInfo("minigzip_fuzzer/minigzip_fuzzer.plain")
        link.type, link.linkname = tarfile.SYMTYPE, "../../../etc/passwd"
        with tree() as t, tempfile.TemporaryDirectory() as a:
            release_with(t, a, [(link, None)])
            rc, out = run(fetch.fetch, t.root, ["zlib"], source=a)
            self.assertEqual(rc, 1, out)
            self.assertIn("unexpected member", out)
            self.assertEqual(os.listdir(t.path("projects/zlib/bin")), [])

    def test_a_harness_whose_every_build_is_withheld_is_not_skipped(self):
        """A withheld build ships no binary, so a member of a harness this tree records and withholds is one the
        archive should not carry at all: it stays out of the skipped names, and _stage refuses it.  Only
        minigzip_fuzzer, which the tree holds no harness.yaml of, is skipped."""
        with tree() as t:
            proj = facts.load(t.root).projects["zlib"]
            self.assertEqual(fetch._other_harnesses(proj, fetch._expected(proj)), {"minigzip_fuzzer"})
            for rec in proj.harnesses["api-driver"].data["builds"].values():
                rec["withheld"] = "not-yet-published"
            self.assertEqual(fetch._expected(proj).keys() & {"api-driver/api-driver.plain"}, set())
            self.assertEqual(fetch._other_harnesses(proj, fetch._expected(proj)), {"minigzip_fuzzer"})

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
            self.assertEqual(new, ["json-src.MANIFEST.tsv", "json-src.tar.zst", NEXT_RECIPE["file"]])
            self.assertEqual(self.listed(t, "v2026.12.0"), (0, ["json-bin.tar.zst"]))
            rc, old = self.listed(t, "v2026.11.0")
            self.assertEqual(rc, 0)
            self.assertEqual(old, ["recipe.tar.zst", "zlib-bin.tar.zst", "zlib-src.MANIFEST.tsv", "zlib-src.tar.zst"])

    def test_a_recipe_only_rebuild_lists_the_recipe_in_a_release_without_source_assets(self):
        """A rebuild with a new recipe adds the archive and the recipe it pins, and nothing else: the project's source
        asset and MANIFEST stay listed where they were."""
        with tree() as t:
            recipe_only_rebuild(t, record=False)
            self.assertEqual(self.listed(t, "v2026.12.0-src"), (0, [NEXT_RECIPE["file"]]))
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

    def test_two_pins_of_one_recipe_file_that_differ_are_refused_naming_both(self):
        """Two private projects that pin recipes of their own under one file of one release, with different SHA-256s:
        oft lint refuses such facts, and a direct `oft fetch` of a tree that has not passed it refuses them too,
        names both files that pin them, and lists neither. Two that pin the same recipe list it once."""
        for other, refused in ((dict(OWN_RECIPE, sha256="7b" * 32), True), (OWN_RECIPE, False)):
            with self.subTest(refused=refused), tree() as t:
                own_recipe(t, "zlib", OWN_RECIPE)
                own_recipe(t, "json", other)
                rc, out = run(fetch.fetch, t.root, ["zlib", "json"], listing=True)
                own = "v2026.11.7-src %s " % OWN_RECIPE["file"]
                listed = [line for line in out.splitlines() if line.startswith(own)]
                if refused:
                    self.assertEqual(rc, 1, out)
                    self.assertIn("v2026.11.7-src: %s is pinned differently: projects/zlib/project.yaml pins 4000000 "
                                  "bytes, %s; projects/json/project.yaml pins 4000000 bytes, %s"
                                  % (OWN_RECIPE["file"], "7a" * 32, "7b" * 32), out)
                    self.assertEqual(listed, [])
                else:
                    self.assertEqual(rc, 0, out)
                    self.assertEqual(listed, [own + "7a" * 32])

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

    def __init__(self, d, extra_axiom="", unsafe="<none>", wrapper_fails=False, dune_fails_on=None, wrapper_says="",
                 compile_fails_on=None, dune_fail_output=None, dep_fails=None):
        self.bin = os.path.join(d, "stub-bin")
        self.log = os.path.join(d, "calls.log")
        os.makedirs(self.bin)
        # dune copies each source it builds into _build/default (the real one does too), so the library's .v files are
        # on the proofs' -Q path, where `rocq dep -sort` below finds them.  dune_fail_output: a file a build that fails
        # (dune_fails_on) prints first, as the real dune prints the rules it ran and their errors.
        self.put("dune", 'echo "dune $*" >> "%s"\n%s'
                         'root=""; prev=""; for a in "$@"; do [ "$prev" = --root ] && root="$a"; prev="$a"; done\n'
                         'for a in "$@"; do case "$a" in proofs/*/lib/*.vo|projects/*/proofs/lib/*.vo)\n'
                         '  mkdir -p "$root/_build/default/$(dirname "$a")" && cp "$root/${a%%.vo}.v" "$root/_build/default/${a%%.vo}.v" ;;\n'
                         'esac; done\nexit 0\n'
                 % (self.log, ('case "$*" in *%s*) %sexit 1 ;; esac\n' % (
                     dune_fails_on, 'cat "%s"; ' % dune_fail_output if dune_fail_output else ""))
                     if dune_fails_on else ""))
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
        # Defined.v is answered as the kernel would (DEFINED_STUB).  compile_fails_on: a compile whose arguments hold it
        # fails, as a proof that does not compile.
        defined = os.path.join(d, "defined_stub.py")
        with open(defined, "w") as f:
            f.write(DEFINED_STUB)
        self.put("rocq", 'echo "rocq $*" >> "%s"\nulimit -s >> "%s"\n'
                         'if [ "$1" = dep ] && [ "$2" = -sort ]; then\n'
                         # dep_fails: `rocq dep` refuses a proof it cannot parse, as it does for a
                         # missing final `.`; the round is a FAILED proof, not a round that did nothing
                         '%s'
                         '  prev=""; for a in "$@"; do\n'
                         '    case "$a" in *.lib) find "$prev" -name "*.v" | sort ;; esac; prev="$a"; done\n'
                         '  for f in "$@"; do case "$f" in *.v) echo "$f" ;; esac; done; exit 0; fi\n'
                         'case "$*" in *Defined.v) exec python3 "%s" "$@" ;; esac\n'
                         'case "$*" in *Wrapper.v*) cat "%s" > assumptions.out; printf %%s "%s"; %s ;; esac\n'
                         '%s'
                         'exit 0\n'
                 % (self.log, self.log,
                    ('  case "$*" in *%s*) echo "Syntax error" >&2; exit 1 ;; esac\n' % dep_fails)
                    if dep_fails else "",
                    defined, os.path.join(d, "wrapper.out"), wrapper_says,
                    "exit 1" if wrapper_fails else "exit 0",
                    ('case "$*" in *%s*) exit 1 ;; esac\n' % compile_fails_on) if compile_fails_on else ""))
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
    def setUp(self):
        self.d = tempfile.TemporaryDirectory()
        self.old_path = os.environ["PATH"]

    def tearDown(self):
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

    def assert_void(self, rc, out, cause):
        self.assertEqual(rc, 7, out)
        lines = [line for line in out.splitlines() if line.startswith("VOID: ")]
        self.assertEqual(len(lines), 1, out)
        self.assertIn(cause, lines[0])
        self.assertIn("not its proofs", lines[0])
        self.assertNotRegex(out, r"(?m)^(?:proofs|projects)/\S+: (proves|refutes) ")
        self.assertNotRegex(out, r"(?m)^oft check: [1-9][0-9]* step\(s\) passed")

    def test_missing_facts_are_void_and_stop_before_the_next_unit(self):
        with tree() as t:
            t.write("toolchain/allowed-axioms.txt", "x\n")
            tl = self.tools()
            rc, out = run(check.run, t.root, [self.ZLIB, self.JSON], facts_from=self._facts_dir())
            self.assert_void(rc, out, "no facts file at " + check.facts_file(self._facts_dir(), self.ZLIB))
            self.assertNotIn("FAIL ", out)
            self.assertNotIn(self.JSON, out)
            self.assertEqual(tl.calls(), "")

    def test_wrong_facts_format_is_void(self):
        with tree() as t:
            t.write("toolchain/allowed-axioms.txt", "x\n")
            d = self._facts_dir()
            self.assertEqual(run(check.run, t.root, [self.ZLIB], facts_to=d)[0], 0)
            path = check.facts_file(d, self.ZLIB)
            data = yamlio.load_file(path)
            data["version"] = 1
            with open(path, "w") as f:
                f.write(yamlio.dump(data))
            rc, out = run(check.run, t.root, [self.ZLIB, self.JSON], facts_from=d)
            self.assert_void(rc, out, "format version 1, not 2")
            self.assertIn(path, out)
            self.assertNotIn("FAIL ", out)
            self.assertNotIn(self.JSON, out)

    def test_unparseable_facts_are_void_on_one_line(self):
        with tree() as t:
            t.write("toolchain/allowed-axioms.txt", "x\n")
            d = self._facts_dir()
            self.assertEqual(run(check.run, t.root, [self.ZLIB], facts_to=d)[0], 0)
            path = check.facts_file(d, self.ZLIB)
            with open(path, "w") as f:
                f.write("version: [\n")
            rc, out = run(check.run, t.root, [self.ZLIB, self.JSON], facts_from=d)
            self.assert_void(rc, out, "facts that do not read")
            self.assertIn(path, out)
            self.assertNotIn("FAIL ", out)
            self.assertNotIn(self.JSON, out)
            self.assertEqual(len(out.splitlines()), 2, out)  # stack measurement, then the one refusal line

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_nothing_compiled_for_statements_and_proofs_is_void(self):
        with tree() as t:
            self.ready(t)
            tl = self.tools()
            rc, out = run(check.run, t.root, [self.ZLIB], parts="statements,proofs")
            self.assert_void(rc, out, "COMPILED 0")
            self.assertIn("\nCOMPILED 0 file(s) with dune -j -\n", out)
            self.assertEqual(tl.calls(), "")

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_every_dune_build_gets_a_positive_j_and_the_count_is_recorded(self):
        """What the empty-affinity tests used to assert, now that main's _jobs (#2121) ends in
        max(1, ...) and can never answer below 1: this tool always passes an explicit positive -j, so there
        is no "no job count" case to void HERE. The case is real one layer out, in the n6 pod, which can run
        a job for which no width was ever determined; it keeps that rule and reads its own record (#2108).
        What this class adds is that the count is RECORDED, which is what a reader needs."""
        with tree() as t, mock.patch.object(check.os, "sched_getaffinity", return_value=set()):
            self.ready(t)
            self._proof(t)
            tl = self.tools()
            rc, out = run(check.run, t.root, [self.ZLIB], parts="statements,proofs")
            self.assertEqual(rc, 0, out)
            self.assertNotIn("VOID:", out)
            for line in [l for l in tl.calls().splitlines() if l.startswith("dune build")]:
                j = line.split(" -j ")[1].split()[0]
                self.assertGreaterEqual(int(j), 1, line)
            self.assertRegex(out, r"(?m)^COMPILED \d+ file\(s\) with dune -j [1-9]\d*$")

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_compilation_counts_targets_cache_hits_and_proof_compiles(self):
        with tree() as t, mock.patch.object(check.os, "sched_getaffinity", return_value={0, 1, 2, 3}):
            self.ready(t)
            self._two_proofs_and_a_library(t)
            tl = self.tools()
            rc, out = run(check.run, t.root, [self.ZLIB], parts="statements,proofs")
            self.assertEqual(rc, 0, out)
            self.assertNotIn("VOID:", out)
            # Three statement targets, Defined.v, two library targets, two proofs and two wrappers.
            # The dune stand-in emits no build-rule lines, as a wholly cached build may do.
            self.assertIn("oft check: 3 step(s) passed, 0 failed; work files in ", out)
            self.assertIn("\nCOMPILED 12 file(s) with dune -j 4\n", out)  # + one rocq dep per proof
            builds = [line for line in tl.calls().splitlines() if line.startswith("dune build")]
            self.assertEqual(len(builds), 2)
            for line in builds:
                self.assertIn(" -j 4 ", line)

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_a_real_proof_compile_failure_is_not_void(self):
        with tree() as t:
            self.ready(t)
            self._proof(t)
            tl = self.tools(compile_fails_on="/Proof.v")
            rc, out = run(check.run, t.root, [self.ZLIB], parts="proofs")
            self.assertEqual(rc, 1, out)
            self.assertNotIn("VOID:", out)
            self.assertIn("does not compile", out)
            self.assertIn("\nCOMPILED 2 file(s) with dune -j -\n", out)  # the proof's rocq dep, then its compile
            self.assertIn("rocq compile", tl.calls())

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_one_target_whose_cone_compiled_and_whose_target_failed_is_fail_never_void(self):
        """The inverted verdict LPS found in rocq-kit's `built 0 of N => VOID` rule (TOOLS, 2026-11-06): a
        round over ONE target with a real .v error compiles its cone, fails on the target, and builds 0 of 1.
        That is a FAIL. What this tool counts is the compiling work it ATTEMPTED -- every .vo target given to
        dune and every rocq compile started, failed ones included -- never the targets that succeeded, so a
        cone that compiled makes the count non-zero and no void rule can reach the round."""
        with tree() as t, mock.patch.object(check.os, "sched_getaffinity", return_value={0, 1, 2, 3}):
            self.ready(t)
            self._proof(t, body="Theorem plain_halts_holds : True. Proof. exact nonsense. Qed.\n")
            tl = self.tools(compile_fails_on="/Proof.v")
            rc, out = run(check.run, t.root, [self.ZLIB], parts="statements,proofs")
            self.assertEqual(rc, 1, "a real .v error is a failure, not VOID: %s" % out)
            self.assertNotIn("VOID:", out)
            self.assertIn("does not compile", out)
            # the cone was built: the statements and the proof library both went to dune
            self.assertNotIn("\nCOMPILED 0 ", out)
            self.assertIn(" -j 4 ", tl.calls())

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_the_oft_check_line_is_the_last_line_and_compiled_comes_before_it(self):
        """The check-of-record tool's build-service rule takes the LAST non-blank line of job.log and
        requires it to be the `oft check: ` summary; the pod prints nothing after a pass, so a COMPILED line
        printed after it would leave every passing check of record `unresolved` (the second non-author
        review of #2109, 2026-11-06).  The farm runner's RUN_SCRIPT and docs/check-of-record.md say the
        same.  So the counts go on the line BEFORE it, and that order is the contract."""
        with tree() as t, mock.patch.object(check.os, "sched_getaffinity", return_value={0, 1, 2, 3}):
            self.ready(t)
            self._proof(t)
            self.tools()
            rc, out = run(check.run, t.root, [self.ZLIB], parts="statements,proofs")
            self.assertEqual(rc, 0, out)
            lines = [l for l in out.splitlines() if l.strip()]
            self.assertTrue(lines[-1].startswith("oft check: "), lines[-3:])
            self.assertRegex(lines[-1], r"^oft check: \d+ step\(s\) passed, \d+ failed; work files in \S+$")
            self.assertRegex(lines[-2], r"^COMPILED \d+ file\(s\) with dune -j \S+$")

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_the_compile_helpers_keep_the_signatures_their_outside_callers_use(self):
        """The two gate-job scripts, under tools/publish/ and dev/stream/bin/, drive check_statements,
        compile_lib and
        check_proof themselves, positionally, from outside this module, and are not changed by this PR.  The
        compilation counter is therefore a KEYWORD parameter with a default on each, and a call that passes
        none compiles exactly as before, counting into a throwaway (the CI/CD lead, 2026-11-06 17:25Z)."""
        import inspect
        for fn, before in ((check.check_statements, ["root", "h", "allowed", "work", "out", "rocqchk"]),
                           (check.compile_lib, ["root", "h", "work", "libs", "out"]),
                           (check.check_proof,
                            ["root", "st", "pd", "allowed", "work", "out", "libs", "rocqchk"])):
            names = list(inspect.signature(fn).parameters)
            self.assertEqual(names[:len(before)], before,
                             "%s's old parameters must keep their places and their order" % fn.__name__)
            self.assertEqual(names[len(before):], ["compilation"])
            self.assertIsNone(inspect.signature(fn).parameters["compilation"].default)
        with tree() as t:
            self.ready(t)
            self._proof(t)
            self.tools()
            h = facts.load(t.root).projects["zlib"].harnesses["checksum_fuzzer"]
            work = tempfile.mkdtemp()
            self.addCleanup(shutil.rmtree, work, True)
            # the old call, with no counter at all: it runs and answers a -Q mapping, raising nothing
            self.assertIsInstance(check.compile_lib(t.root, h, work, {}, io.StringIO()), list)

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_a_split_job_of_a_library_less_unit_fails_on_a_broken_proof(self):
        """The route the sixth review of #2109 found. A unit too long for one job is checked one statement
        per job, as `--parts proofs --statements S`, which is the farm's split. With no proof library there
        is no dune build, so `rocq dep` is the FIRST thing that touches a .v file; uncounted, a proof it
        cannot parse left the round at COMPILED 0 and VOID, and the farm reruns a void unit for ever, so
        the broken proof would never be reported. `rocq dep` reads the proof's own files and is counted."""
        with tree() as t:
            self.ready(t)
            self._proof(t)
            # a proof `rocq dep` cannot parse: the case the review found, and the one that was voided
            tl = self.tools(dep_fails="/Proof.v")
            rc, out = run(check.run, t.root, [self.ZLIB], parts="proofs", statements=["plain_halts"])
            self.assertEqual(rc, 1, "a proof rocq dep cannot parse is a FAILED proof: %s" % out)
            self.assertNotIn("VOID:", out)
            self.assertIn("rocq dep failed", out)
            # the count is non-zero before any proof compiles, which is what keeps it a FAIL
            self.assertNotIn("\nCOMPILED 0 ", out)
            self.assertRegex(out, r"(?m)^COMPILED [1-9]\d* file\(s\) with dune -j -$")
            self.assertIn("rocq dep", tl.calls())

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_parallel_proof_compiles_count_without_a_library(self):
        with tree() as t:
            self.ready(t)
            self._proof(t)
            self._proof(t, self.SECOND, s="plain_halts_may_fail")
            self.tools()
            rc, out = run(check.run, t.root, [self.ZLIB], parts="proofs", proof_jobs=2)
            self.assertEqual(rc, 0, out)
            self.assertNotIn("VOID:", out)
            self.assertIn("oft check: 2 step(s) passed, 0 failed; work files in ", out)
            self.assertIn("\nCOMPILED 6 file(s) with dune -j -\n", out)  # two children, each a rocq dep and two compiles

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
            self.assert_void(rc, out, "COMPILED 0")
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
            self.assert_void(rc, out, "COMPILED 0")
            self.assertIn("is withheld or withdrawn, so Statements.v defines none: nothing to check", out)
            self.assertFalse(os.path.exists(tl.log) and "dune build" in tl.calls(), "nothing is built")

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_proofs_asked_of_a_unit_with_no_proof_fail(self):
        """--parts statements,proofs of a unit with no proof would pass on its statements alone."""
        with tree() as t:
            self.ready(t)
            self.tools()
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="statements,proofs")
            self.assert_void(rc, out, "COMPILED 0")
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
        fake_docker(tl, self.d.name)
        tools = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
        env = dict(os.environ, WORK=t.root, TOOLS=os.path.dirname(tools), PROJECTS="zlib", CX_UNITS="", FINDINGS="",
                   ASSETS=os.path.join(self.d.name, "assets"),  # ready() put the release asset here
                   PYDEPS=self.d.name, GITHUB_REPOSITORY="example/proofs",
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
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            self.assertIn("python3 -m oft.check --root /work --facts-to /facts zlib/api-driver zlib/checksum_fuzzer\n",
                          calls)
            self.assertIn("python3 -m oft.check --root /work --facts-from /facts zlib/checksum_fuzzer "
                          "--parts statements,proofs\n", calls)
            self.assertIn("python3 -m oft.check --root /work --facts-from /facts zlib/api-driver --parts statements\n",
                          calls)
            self.assertIn("2 step(s) passed, 0 failed", r.stdout)
            self.assertIn("1 step(s) passed, 0 failed", r.stdout)
            # the facts' run mounts the whole tree read-only; checksum_fuzzer's mounts its view and nothing else
            facts_run = next(l for l in calls.splitlines() if "--facts-to" in l)
            self.assertIn("-v %s:/work:ro " % os.path.realpath(t.root), facts_run)
            mounts = dict(reversed(m.split(":", 1)) for m in re.findall(r"-v (\S+)", next(
                l for l in calls.splitlines() if "zlib/checksum_fuzzer --parts" in l)))
            others = sorted(d for d in os.listdir(t.path("projects/zlib"))
                            if os.path.isfile(t.path("projects/zlib", d, "harness.yaml")) and d != "checksum_fuzzer")
            self.assertTrue(others)
            # the statement folder by its entries, its README.md left out (unitpaths.HARNESS_DROP)
            work = ["projects/zlib/checksum_fuzzer/" + e for e in os.listdir(t.path("projects/zlib/checksum_fuzzer"))
                    if e not in unitpaths.HARNESS_DROP]
            work += ["projects/zlib/project.yaml", "projects/zlib/bin/checksum_fuzzer", "proofs/zlib/checksum_fuzzer",
                     "theories", "toolchain/allowed-axioms.txt"]
            work += ["projects/zlib/%s/harness.yaml" % d for d in others]
            self.assertTrue(all(os.path.exists(t.path(rel)) for rel in work))
            want = {"/work/%s:ro" % rel for rel in work} | {
                "/work", "/work/dune-project:ro", "/facts/zlib/checksum_fuzzer.yaml:ro", "/tools:ro", "/pydeps:ro"}
            self.assertEqual(set(mounts), want)
            for dst, src in mounts.items():
                if dst.startswith("/work/") and dst != "/work/dune-project:ro":
                    self.assertEqual(src, os.path.join(os.path.realpath(t.root), dst[len("/work/"):-len(":ro")]))

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_check_units_fails_a_unit_whose_view_cannot_be_made_and_checks_the_rest(self):
        """A unit's binaries directory that is a symbolic link, which a mount would follow out of the view: that unit
        fails, the next unit is still checked, and the job fails."""
        with tree() as t:
            self.ready(t)
            tl = self.tools()
            outside = os.path.join(self.d.name, "outside-bin")
            shutil.move(t.path("projects/zlib/bin/checksum_fuzzer"), outside)
            os.symlink(outside, t.path("projects/zlib/bin/checksum_fuzzer"))
            r, calls = self._check_units(t, tl, UNITS="zlib/checksum_fuzzer zlib/api-driver", PROOF_UNITS='""')
            self.assertEqual(r.returncode, 1, r.stdout + r.stderr)
            self.assertIn("FAIL zlib/checksum_fuzzer: its build view could not be made", r.stderr)
            self.assertIn("symbolic link", r.stderr)
            self.assertNotIn("--facts-from /facts zlib/checksum_fuzzer", calls)
            self.assertIn("python3 -m oft.check --root /work --facts-from /facts zlib/api-driver --parts statements\n",
                          calls)
            self.assertIn("1 step(s) passed, 0 failed", r.stdout)

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_check_units_checks_a_unit_in_a_view_without_the_dropped_parts_of_its_build_record(self):
        """The two parts of a unit's build record that unitpaths.PROOFS_DROP names -- its prose
        (provenance/PROVENANCE.md) and its licence evidence (provenance/evidence/licence/: the made-from record and
        the script that writes it) -- are in no key, so check-units.sh mounts neither; the build check reads nothing
        there and passes without them."""
        with tree() as t:
            self.ready(t)
            tl = self.tools()
            self._proof(t)
            record = "proofs/zlib/checksum_fuzzer/provenance"
            licence = record + "/evidence/licence"
            t.write(licence + "/made-from.tsv", "path\tdecision\nlib/Common.v\tmade from lib/Other.v\n")
            t.write(licence + "/made_from.py", "# the script of record\n")
            t.write(licence + "/left-bare.tsv", "path\treason\nlib/Common.v\tours\n")
            t.write(record + "/PROVENANCE.md", "# Build record\n\nThe rule found 148 such files.\n")
            t.write(record + "/evidence/mutants/1/notes.md", "a mutant run\n")
            r, calls = self._check_units(t, tl, UNITS="zlib/checksum_fuzzer",
                                         PROOF_UNITS=json.dumps("zlib/checksum_fuzzer"))
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            self.assertIn("python3 -m oft.check --root /work --facts-from /facts zlib/checksum_fuzzer "
                          "--parts statements,proofs\n", calls)
            mounts = [m.split(":", 1)[0] for m in re.findall(r"-v (\S+)", next(
                l for l in calls.splitlines() if "zlib/checksum_fuzzer --parts" in l))]
            self.assertEqual([m for m in mounts if licence in m], [])
            self.assertEqual([m for m in mounts if m.endswith(record + "/PROVENANCE.md")], [])
            under = [m for m in mounts if "proofs/zlib/checksum_fuzzer" in m]
            self.assertTrue(under)
            # what is beside a dropped path is mounted, so the check still reads the rest of the proofs folder
            for rel in ("provenance/evidence/mutants", "plain_halts"):
                self.assertTrue(any(m.endswith("proofs/zlib/checksum_fuzzer/" + rel) for m in under), rel)

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
    def test_check_units_builds_a_per_project_proof_library_by_these_tools_rule(self):
        """The same in the per-project layout (review F2): the library is projects/<p>/<h>/proofs/lib/, and its view's
        proofs folder is a read-only mount too, so check-units.sh writes this tool's lib/dune there before the view;
        the check loads the unit's facts in its view (--facts-from) with that library (Tree.proof_libs, review F3)."""
        rel = "projects/zlib/checksum_fuzzer/proofs/lib/dune"
        with tree() as t:
            self.ready(t)
            self._two_proofs_and_a_library(t)
            self.assertEqual(port.port_worktree(t.root, out=io.StringIO()), 0)
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertFalse(os.path.lexists(t.path("proofs/zlib/checksum_fuzzer")))
            want = t.read(rel)
            t.write(rel, want + "(rule (targets Base.vo) (action (copy x Base.vo)))\n")
            tl = self.tools()
            r, calls = self._check_units(t, tl, UNITS="zlib/checksum_fuzzer", PROOF_UNITS='"zlib/checksum_fuzzer"')
            self.assertIn("%s: written as these tools render it, before the view is made" % rel, r.stdout,
                          r.stdout + r.stderr)
            self.assertEqual(t.read(rel), want)
            run = next(l for l in calls.splitlines() if "zlib/checksum_fuzzer --parts" in l)
            self.assertIn(":/work/projects/zlib/checksum_fuzzer/proofs:ro ", run)
            self.assertNotIn("/work/proofs/", run)
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            self.assertIn("python3 -m oft.check --root /work --facts-from /facts zlib/checksum_fuzzer "
                          "--parts statements,proofs\n", calls)
            self.assertIn("dune build", tl.calls())
            self.assertIn("projects/zlib/checksum_fuzzer/proofs/plain_halts: proves zlib/checksum_fuzzer/"
                          "plain_halts", r.stdout)

    def test_loadpath_maps_the_tree_s_core(self):
        """In a tree whose release.yaml names another namespace, the statements are loaded under it: the core as
        <namespace>.Core and the harness as harness.yaml's rocq, whether the check loads the tree or reads the unit's
        facts from --facts-to's file (which carries the release's names, as a view holds no release.yaml)."""
        unit = "zlib/checksum_fuzzer"
        want = ["-Q", "/b/theories", "OSSVerify.Core", "-Q", "/b/projects/zlib/checksum_fuzzer",
                "OSSVerify.zlib.checksum_fuzzer"]
        with tree(render=False) as t:
            rename_namespace(t)
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertEqual(check._loadpath("/b", facts.load(t.root).projects["zlib"].harnesses["checksum_fuzzer"]),
                             want)
            d = os.path.join(self.d.name, "facts")
            rc, out = run(check.run, t.root, [unit], facts_to=d)
            self.assertEqual(rc, 0, out)
            h = facts.load_unit(t.root, yamlio.load_file(check.facts_file(d, unit)), unit, ["statements", "proofs"])
            self.assertEqual(check._loadpath("/b", h), want)
            self.assertEqual((h.tree.namespace, h.tree.opam_stem), ("OSSVerify", "oss-verify"))

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_check_units_checks_a_renamed_per_project_unit(self):
        """check-units.sh on a tree whose release.yaml names another namespace: step 1b writes the proof library's
        dune in the new names, the view's dune-project keeps the new packages, the facts carry the names into the
        view, and every tool call names the new namespace and never the old one."""
        rel = "projects/zlib/checksum_fuzzer/proofs/lib/dune"
        with tree() as t:
            self.ready(t)
            rename_namespace(t)
            self.assertEqual(t.generate(), 0, t.last_output)
            self._two_proofs_and_a_library(t)
            self.assertEqual(port.port_worktree(t.root, out=io.StringIO()), 0)
            self.assertEqual(t.generate(), 0, t.last_output)
            want = t.read(rel)
            self.assertIn("(name OSSVerify.Proofs.zlib.checksum_fuzzer.lib)", want)
            self.assertIn("(package rocq-oss-verify-zlib-proofs)", want)
            t.write(rel, want + "(rule (targets Base.vo) (action (copy x Base.vo)))\n")
            tl = self.tools()
            r, calls = self._check_units(t, tl, UNITS="zlib/checksum_fuzzer", PROOF_UNITS='"zlib/checksum_fuzzer"')
            self.assertIn("%s: written as these tools render it, before the view is made" % rel, r.stdout,
                          r.stdout + r.stderr)
            self.assertEqual(t.read(rel), want)
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            self.assertIn("projects/zlib/checksum_fuzzer/proofs/plain_halts: proves zlib/checksum_fuzzer/"
                          "plain_halts", r.stdout)
            self.assertIn("OSSVerify.Core", tl.calls())
            self.assertNotIn("OssFuzzTheorems", tl.calls())

    def test_facts_from_loads_a_per_project_unit_with_its_proof_library(self):
        """load_unit takes the unit's layout from the view, which holds that unit alone, and its proof library from
        it (review F3): in a ported tree, the library is the per-project one, and the facts --facts-to wrote match."""
        with tree() as t:
            self._two_proofs_and_a_library(t)
            self.assertEqual(port.port_worktree(t.root, out=io.StringIO()), 0)
            self.assertEqual(t.generate(), 0, t.last_output)
            d = os.path.join(self.d.name, "facts")
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], facts_to=d)
            self.assertEqual(rc, 0, out)
            data = yamlio.load_file(os.path.join(d, "zlib", "checksum_fuzzer.yaml"))
            h = facts.load_unit(t.root, data, "zlib/checksum_fuzzer", ["statements", "proofs"])
            self.assertEqual(h.tree.unit_layout("zlib/checksum_fuzzer"), "new")
            self.assertEqual(h.tree.proof_libs, {"zlib/checksum_fuzzer": "projects/zlib/checksum_fuzzer/proofs/lib"})
            self.assertEqual(sorted(h.statements[s].proof.path for s in h.statements if h.statements[s].proof),
                             ["projects/zlib/checksum_fuzzer/proofs/plain_halts",
                              "projects/zlib/checksum_fuzzer/proofs/plain_halts_may_fail"])

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_check_units_builds_a_proof_library_by_these_tools_rule_in_a_read_only_view(self):
        """A tree whose lib/dune other tools rendered (a maintainer's change to the template), checked as a merge
        queue group or a push checks it, where pr.yml renders nothing first: the view mounts the unit's proofs/
        read-only, so check-units.sh writes these tools' lib/dune on the host before the view is made, and the proofs
        pass with this tool's rule.  A lib/dune that is a symbolic link is not written through: the check refuses it."""
        rel = "proofs/zlib/checksum_fuzzer/lib/dune"
        with tree() as t:
            self.ready(t)
            self._two_proofs_and_a_library(t)
            want = t.read(rel)
            t.write(rel, want + "(rule (targets Base.vo) (action (copy x Base.vo)))\n")
            tl = self.tools()
            r, calls = self._check_units(t, tl, UNITS="zlib/checksum_fuzzer", PROOF_UNITS='"zlib/checksum_fuzzer"')
            self.assertIn("%s: written as these tools render it, before the view is made" % rel, r.stdout,
                          r.stdout + r.stderr)
            self.assertEqual(t.read(rel), want)
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            self.assertIn("python3 -m oft.check --root /work --facts-from /facts zlib/checksum_fuzzer "
                          "--parts statements,proofs\n", calls)
            self.assertIn("dune build", tl.calls())
            self.assertNotIn("%s: written as this oft generate renders it" % rel, r.stdout)
        self.d.cleanup()
        self.d = tempfile.TemporaryDirectory()
        with tree() as t:
            self.ready(t)
            self._two_proofs_and_a_library(t)
            outside = os.path.join(self.d.name, "outside-dune")
            with open(outside, "w") as f:
                f.write("(rule)\n")
            os.remove(t.path(rel))
            os.symlink(outside, t.path(rel))
            tl = self.tools()
            r, calls = self._check_units(t, tl, UNITS="zlib/checksum_fuzzer", PROOF_UNITS='"zlib/checksum_fuzzer"')
            self.assertNotEqual(r.returncode, 0, r.stdout + r.stderr)
            with open(outside) as f:
                self.assertEqual(f.read(), "(rule)\n", "lib/dune written through its symbolic link")
            self.assertNotIn("written as these tools render it", r.stdout)
            self.assertIn("%s: a proof library holds no symbolic link" % rel, r.stdout, r.stdout + r.stderr)

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
            self.assert_void(rc, out, "COMPILED 0")
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

    def _lib_dir(self, t, ported=False):
        """Where compile_lib's dune build leaves the library (with ported, in the per-project layout): root's _build
        copy of it, on every proof's -Q path."""
        return t.path("_build", "default", self.NEW_LIB if ported else "proofs/zlib/checksum_fuzzer/lib")

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_proof_jobs_check_each_statement_in_a_process_of_its_own_after_one_library_build(self):
        with tree() as t:
            self.ready(t)
            self._two_proofs_and_a_library(t)
            tl = self.tools()
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="statements,proofs", proof_jobs=2)
            self.assertEqual(rc, 0, out)
            self.assertIn("zlib/checksum_fuzzer: 2 statement(s) with a proof, each in a process of its own, 2 at a "
                          "time", out)
            calls = tl.calls().splitlines()
            # dune runs twice, both in this process: the statements, then the library; a statement's process runs none
            self.assertEqual(len([c for c in calls if c.startswith("dune build")]), 2, calls)
            self.assertEqual(len([c for c in calls if c.startswith("dune build") and "/lib/" in c]), 1, calls)
            users = [c for c in calls if c.startswith("rocq compile") and c.endswith(("/Proof.v", "/Wrapper.v"))]
            self.assertEqual(len(users), 4, "two proofs and two wrappers compiled")
            for c in users:
                self.assertIn("-Q %s %s" % (self._lib_dir(t), self.LIB_MOD), c)
            lines = out.splitlines()
            for s in ("plain_halts", "plain_halts_may_fail"):
                # the statement's own line, at the start of a line of this run's output, not only inside its log
                self.assertIn("proofs/zlib/checksum_fuzzer/%s: proves zlib/checksum_fuzzer/%s; assumptions: 1 axioms, "
                              "all allowed" % (s, s), lines)
            self.assertIn("oft check: 3 step(s) passed, 0 failed", out)

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_proof_jobs_hand_each_process_the_build_of_a_new_layout_library(self):
        with tree() as t:
            self.ready(t)
            self._two_proofs_and_a_library(t)
            self._ported(t)
            tl = self.tools()
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="statements,proofs", proof_jobs=2)
            self.assertEqual(rc, 0, out)
            self.assertIn("zlib/checksum_fuzzer: 2 statement(s) with a proof, each in a process of its own, 2 at a "
                          "time", out)
            calls = tl.calls().splitlines()
            # dune runs twice, both in this process: the statements, then the library; a statement's process runs none
            self.assertEqual(len([c for c in calls if c.startswith("dune build")]), 2, calls)
            builds = [c for c in calls if c.startswith("dune build") and "/lib/" in c]
            self.assertEqual(len(builds), 1, calls)
            self.assertTrue(builds[0].endswith(" %s/Base.vo %s/Sub/Deep.vo" % (self.NEW_LIB, self.NEW_LIB)), builds[0])
            users = [c for c in calls if c.startswith("rocq compile") and c.endswith(("/Proof.v", "/Wrapper.v"))]
            self.assertEqual(len(users), 4, "two proofs and two wrappers compiled")
            for c in users:
                self.assertIn("-Q %s %s" % (self._lib_dir(t, ported=True), self.LIB_MOD), c)
            lines = out.splitlines()
            for s in ("plain_halts", "plain_halts_may_fail"):
                self.assertIn("projects/zlib/checksum_fuzzer/proofs/%s: proves zlib/checksum_fuzzer/%s; assumptions: 1 "
                              "axioms, all allowed" % (s, s), lines)
            self.assertIn("oft check: 3 step(s) passed, 0 failed", out)

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_proof_jobs_a_statement_whose_process_does_not_prove_it_fails(self):
        with tree() as t:
            self.ready(t)
            self._two_proofs_and_a_library(t)
            self.tools(wrapper_fails=True)
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="proofs", proof_jobs=2)
            self.assertEqual(rc, 1, out)
            for s in ("plain_halts", "plain_halts_may_fail"):
                self.assertRegex(out, r"(?m)^FAIL proofs/zlib/checksum_fuzzer/%s: its process exited 1 \(see " % s)
            self.assertIn("oft check: 0 step(s) passed, 2 failed", out)

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_proof_jobs_a_statement_passes_only_on_exit_0_and_its_own_line(self):
        """A statement's process stands in for `python3 -m oft.check`: it prints the statement's own line or not, then
        exits 0, exits 1 or is killed.  Only the line and exit 0 together pass it."""
        stub = os.path.join(self.d.name, "stub-python")
        with open(stub, "w") as f:
            f.write('#!/bin/sh\nunit="" s=""; prev=""\nfor a in "$@"; do\n'
                    '  case "$prev" in --statements) s="$a" ;; esac\n'
                    '  case "$a" in */*) [ -z "$unit" ] && [ "$prev" != --root ] && [ "$prev" != --lib ] && '
                    '[ "$prev" != --allowed ] && unit="$a" ;; esac; prev="$a"; done\n'
                    'line="proofs/$unit/$s: proves $unit/$s; assumptions: 1 axioms, all allowed"\n'
                    'case "$STUB_MODE" in\n'
                    '  pass) echo "$line"; exit 0 ;;\n  silent) echo "compiled"; exit 0 ;;\n'
                    '  line1) echo "$line"; exit 1 ;;\n  killed) echo "$line"; kill -9 $$ ;;\nesac\n')
        os.chmod(stub, 0o755)
        with tree() as t:
            self.ready(t)
            self._two_proofs_and_a_library(t)
            self.tools()
            for mode, rc_want, why in (("pass", 0, None), ("silent", 1, "its process exited 0 without check_proof's "
                                       "line for zlib/checksum_fuzzer/%s"), ("line1", 1, "its process exited 1"),
                                       ("killed", 1, "its process was ended by signal 9")):
                with self.subTest(mode=mode), mock.patch.object(check.sys, "executable", stub), \
                        mock.patch.dict(os.environ, {"STUB_MODE": mode}):
                    rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="proofs", proof_jobs=2)
                    self.assertEqual(rc, rc_want, out)
                    for s in ("plain_halts", "plain_halts_may_fail"):
                        claim = ("proofs/zlib/checksum_fuzzer/%s: proves zlib/checksum_fuzzer/%s; assumptions: 1 "
                                 "axioms, all allowed" % (s, s))
                        if why is None:
                            self.assertIn(claim, out.splitlines())
                        else:
                            self.assertNotIn(claim, out.splitlines(), "only inside the process's echoed log")
                            self.assertIn("FAIL proofs/zlib/checksum_fuzzer/%s: %s (see " % (s, why.replace(
                                "%s", s)), out)
                    self.assertIn("oft check: %s" % ("2 step(s) passed, 0 failed" if why is None else
                                                     "0 step(s) passed, 2 failed"), out)

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_proof_jobs_a_library_that_does_not_build_fails_each_proof_and_starts_no_process(self):
        with tree() as t:
            self.ready(t)
            self._two_proofs_and_a_library(t)
            tl = self.tools(dune_fails_on="/lib/")
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="proofs", proof_jobs=2)
            self.assertEqual(rc, 1)
            self.assertEqual(out.count("proofs/zlib/checksum_fuzzer/lib: does not compile"), 2, out)
            self.assertNotIn("each in a process of its own", out)
            self.assertNotIn("Wrapper.v", tl.calls())

    def test_a_claim_counts_only_for_its_own_statement_and_verb(self):
        st = types.SimpleNamespace(id="p/h/plain_halts", proof=types.SimpleNamespace(path="proofs/p/h/plain_halts",
                                                                                      refutes=False))
        line = "proofs/p/h/plain_halts: proves p/h/plain_halts; assumptions: 3 axioms, all allowed"
        self.assertEqual(check.proof_claim(st, "x\n%s\nok\n" % line), line)
        self.assertEqual(check.proof_claim(st, "proofs/p/h/plain_halts: proves p/h/plain_halts (1 # 2); assumptions: "
                                               "3 axioms, all allowed"), "proofs/p/h/plain_halts: proves "
                         "p/h/plain_halts (1 # 2); assumptions: 3 axioms, all allowed")
        # lines end only at "\n": a carriage return or U+2028 cannot cut a FAIL line into a claim
        for text in (line.replace("proves", "refutes"), "  | " + line, line + " but not", line.replace(
                "plain_halts;", "plain_halts_may_fail;"), "FAIL " + line, "", "FAIL x\r" + line, "FAIL x\u2028" + line):
            with self.subTest(text=text):
                self.assertIsNone(check.proof_claim(st, text))

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_statements_names_only_statements_with_a_proof(self):
        with tree() as t:
            self.ready(t)
            self._proof(t)
            self.tools()
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="proofs", statements=["plain_halts"])
            self.assertEqual(rc, 0, out)
            self.assertIn("oft check: 1 step(s) passed, 0 failed", out)
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="proofs",
                          statements=["plain_halts", "plain_halts_may_fail"])
            self.assert_void(rc, out, "COMPILED 0")
            self.assertIn("FAIL zlib/checksum_fuzzer: --statements names plain_halts_may_fail, which has no proof "
                          "here", out)
            for kw in ({"parts": "statements,proofs"}, {"units": ["zlib/checksum_fuzzer", "zlib/api-driver"]}):
                with self.subTest(kw=kw):
                    args = dict({"parts": "proofs", "units": ["zlib/checksum_fuzzer"]}, **kw)
                    rc, out = run(check.run, t.root, args["units"], parts=args["parts"], statements=["plain_halts"])
                    self.assertEqual(rc, 1, out)
                    self.assertIn("--statements and --lib check the proofs of one unit", out)

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_lib_is_used_only_when_it_holds_the_library_s_own_sources(self):
        with tree() as t:
            self.ready(t)
            self._two_proofs_and_a_library(t)
            tl = self.tools()
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="proofs")
            self.assertEqual(rc, 0, out)
            libdir = self._lib_dir(t)
            open(tl.log, "w").close()
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="proofs", statements=["plain_halts"],
                          lib=libdir)
            self.assertEqual(rc, 0, out)
            self.assertNotIn("dune build", tl.calls(), "a library given by --lib is not built again")
            self.assertIn("-Q %s %s" % (libdir, self.LIB_MOD), tl.calls())
            t.write("proofs/zlib/checksum_fuzzer/lib/Sub/Deep.v", "Definition two := 3.\n")
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="proofs", statements=["plain_halts"],
                          lib=libdir)
            self.assert_void(rc, out, "COMPILED 0")
            self.assertIn("FAIL proofs/zlib/checksum_fuzzer/plain_halts: --lib names %s, whose .v files are not those "
                          "of proofs/zlib/checksum_fuzzer/lib" % libdir, out)
            # the same sources in another directory are not this checkout's build of the library
            t.write("proofs/zlib/checksum_fuzzer/lib/Sub/Deep.v", "Definition two := 2.\n")
            other = os.path.join(self.d.name, "other-lib")
            shutil.copytree(libdir, other)
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="proofs", statements=["plain_halts"],
                          lib=other)
            self.assert_void(rc, out, "COMPILED 0")
            self.assertIn("--lib names %s, which is not this checkout's build of its proof library" % other, out)

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_lib_of_a_new_layout_harness_is_only_this_checkout_s_build_of_its_library(self):
        with tree() as t:
            self.ready(t)
            self._two_proofs_and_a_library(t)
            self._ported(t)
            tl = self.tools()
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="proofs")
            self.assertEqual(rc, 0, out)
            libdir = self._lib_dir(t, ported=True)
            open(tl.log, "w").close()
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="proofs", statements=["plain_halts"],
                          lib=libdir)
            self.assertEqual(rc, 0, out)
            self.assertNotIn("dune build", tl.calls(), "a library given by --lib is not built again")
            self.assertIn("-Q %s %s" % (libdir, self.LIB_MOD), tl.calls())
            # a build where the old layout kept the library (one made before the port) is not where this checkout
            # builds it
            old = self._lib_dir(t)
            shutil.copytree(libdir, old)
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="proofs", statements=["plain_halts"],
                          lib=old)
            self.assert_void(rc, out, "COMPILED 0")
            self.assertIn("FAIL projects/zlib/checksum_fuzzer/proofs/plain_halts: --lib names %s, which is not this "
                          "checkout's build of its proof library (%s)" % (old, libdir), out)
            t.write(self.NEW_LIB + "/Sub/Deep.v", "Definition two := 3.\n")
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="proofs", statements=["plain_halts"],
                          lib=libdir)
            self.assert_void(rc, out, "COMPILED 0")
            self.assertIn("FAIL projects/zlib/checksum_fuzzer/proofs/plain_halts: --lib names %s, whose .v files are "
                          "not those of %s" % (libdir, self.NEW_LIB), out)

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_lib_for_a_harness_with_no_library_names_where_its_layout_keeps_one(self):
        for ported, folder in ((False, "proofs/zlib/checksum_fuzzer"), (True, "projects/zlib/checksum_fuzzer/proofs")):
            with self.subTest(ported=ported), tree() as t:
                self.d.cleanup()
                self.d = tempfile.TemporaryDirectory()
                self.ready(t)
                self._proof(t)
                if ported:
                    self._ported(t)
                tl = self.tools()
                lib = os.path.join(self.d.name, "lib")
                os.makedirs(lib)
                rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="proofs", statements=["plain_halts"],
                              lib=lib)
                self.assert_void(rc, out, "COMPILED 0")
                self.assertIn("FAIL %s/plain_halts: --lib names %s, but projects/zlib/checksum_fuzzer has no proof "
                              "library (%s/lib)" % (folder, lib, folder), out)
                self.assertNotIn("rocq compile", tl.calls())

    def _ported(self, t):
        """Move t to the per-project layout, as `oft port-layout` does, and render it again: its proofs folder gets
        its barrier dune."""
        self.assertEqual(port.port_worktree(t.root, out=io.StringIO()), 0)
        self.assertEqual(t.generate(), 0, t.last_output)

    def _refused_with(self, rel, text, ported=False, mode="w"):
        """check's output for a harness library that also holds file rel (with ported, in the per-project layout),
        written with text (with mode "a", text added to the file there); nothing is built."""
        with tree() as t:
            self.ready(t)
            self._two_proofs_and_a_library(t)
            if ported:
                self._ported(t)
            t.write(rel, text, mode)
            tl = self.tools()
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="proofs")
            self.assert_void(rc, out, "COMPILED 0")
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

    NEW_LIB = "projects/zlib/checksum_fuzzer/proofs/lib"

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_a_new_layout_library_accepts_the_barrier_and_the_statement_dune_above_it(self):
        with tree() as t:
            self.ready(t)
            self._two_proofs_and_a_library(t)
            self._ported(t)
            self.assertEqual(t.read("projects/zlib/checksum_fuzzer/proofs/dune"), generate.barrier_dune())
            h = facts.load(t.root).projects["zlib"].harnesses["checksum_fuzzer"]
            self.assertEqual(t.read("projects/zlib/checksum_fuzzer/dune"), generate.harness_dune(h))
            tl = self.tools()
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="proofs")
            self.assertEqual(rc, 0, out)
            self.assertIn("%s: 2 files compiled or taken from dune's cache" % self.NEW_LIB, out)
            calls = tl.calls().splitlines()
            builds = [c for c in calls if c.startswith("dune build") and "/lib/" in c]
            self.assertEqual(len(builds), 1, "the library is built once for two proofs")
            self.assertTrue(builds[0].endswith(" %s/Base.vo %s/Sub/Deep.vo" % (self.NEW_LIB, self.NEW_LIB)), builds[0])
            mapping = "-Q %s %s" % (t.path("_build", "default", self.NEW_LIB), self.LIB_MOD)
            users = [c for c in calls if c.startswith("rocq compile") and c.endswith(("/Proof.v", "/Wrapper.v"))]
            self.assertEqual(len(users), 4, "two proofs and two wrappers compiled afresh")
            for c in users:
                self.assertIn(mapping, c)

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_a_new_layout_library_refuses_a_changed_barrier(self):
        # (subdir lib ...) added there would reach the library's rules
        rel = "projects/zlib/checksum_fuzzer/proofs/dune"
        out = self._refused_with(rel, "(subdir lib (rule (targets Base.vo) (action (copy x Base.vo))))\n", ported=True,
                                 mode="a")
        self.assertIn("%s: differs from its rendering (run ./oft generate)" % rel, out)

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_a_new_layout_library_refuses_a_changed_statement_dune(self):
        rel = "projects/zlib/checksum_fuzzer/dune"
        out = self._refused_with(rel, "(subdir proofs/lib (rule (targets Base.vo) (action (copy x Base.vo))))\n",
                                 ported=True, mode="a")
        self.assertIn("%s: differs from its rendering (run ./oft generate)" % rel, out)

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_a_new_layout_library_refuses_another_build_file_above_it(self):
        for rel in ("projects/zlib/checksum_fuzzer/proofs/dune-file", "projects/zlib/checksum_fuzzer/dune-project",
                    "projects/zlib/dune", "projects/dune-workspace", "dune"):
            with self.subTest(rel=rel):
                self.d.cleanup()
                self.d = tempfile.TemporaryDirectory()
                out = self._refused_with(rel, "(subdir lib (rule (targets Base.vo) (action (copy x Base.vo))))\n",
                                         ported=True)
                self.assertIn("%s: no directory above a proof library holds a build file" % rel, out)

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_with_rocqchk_a_new_layout_harness_is_named_by_its_proofs_folder(self):
        with tree() as t:
            self.ready(t)
            self._two_proofs_and_a_library(t)
            self._ported(t)
            self.tools()
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="proofs", rocqchk=True)
            self.assertEqual(rc, 0, out)
            self.assertIn("projects/zlib/checksum_fuzzer/proofs: rocqchk over the wrappers of 2 proof(s)", out)

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_a_symbolic_link_above_a_harness_library_is_refused(self):
        with tree() as t:
            self.ready(t)
            self._two_proofs_and_a_library(t)
            os.rename(t.path("proofs/zlib/checksum_fuzzer"), t.path("elsewhere"))
            os.symlink(t.path("elsewhere"), t.path("proofs/zlib/checksum_fuzzer"))
            tl = self.tools()
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="proofs")
            self.assert_void(rc, out, "COMPILED 0")
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
            self.assert_void(rc, out, "COMPILED 0")
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
    def test_a_library_that_does_not_compile_quotes_the_error_from_deep_in_a_large_log(self):
        """The Release lane's case of 2026-11-02: the one error of a 362,395-line dune log, at line 220,381, among the
        rules dune ran and the warnings it printed.  The FAIL line quotes its block, the error first, and no other."""
        with tree() as t:
            self.ready(t)
            self._two_proofs_and_a_library(t)
            error = ['File "proofs/zlib/checksum_fuzzer/lib/Sub/Deep.v", line 7, characters 2-9:',
                     "Error: The reference foo was not found in the current environment."]
            body = []   # what dune prints; the log's first line is check's own `$ dune build ...`
            for k in range(362395 - 1):
                body.append(error[0] if k == 220379 else error[1] if k == 220380 else
                            'File "proofs/zlib/checksum_fuzzer/lib/W%d.v", line 1, characters 0-4:' % k if k % 1000 == 0
                            else "Warning: Notation overridden. [notation-overridden,parsing,default]" if k % 1000 == 1
                            else "        rocq proofs/zlib/checksum_fuzzer/lib/A%d.vo" % k)
            dune_out = os.path.join(self.d.name, "dune-out.txt")
            with open(dune_out, "w") as f:
                f.write("\n".join(body) + "\n")
            self.tools(dune_fails_on="Deep.vo", dune_fail_output=dune_out)
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="proofs")
            self.assertEqual(rc, 1)
            log = re.search(r"lib: does not compile \(see (\S+\.lib\.dune\.log)\)", out).group(1)
            with open(log) as f:
                lines = f.read().split("\n")[:-1]
            self.assertEqual((len(lines), lines[220380:220382]), (362395, error), "line 220,381 of 362,395")
            head = ("FAIL proofs/zlib/checksum_fuzzer/plain_halts: proofs/zlib/checksum_fuzzer/lib: does not compile (see "
                    "%s)\nthe log holds 1 Error: block(s): 1 quoted here; the whole log is %s\n"
                    "  | %s\n  | %s\n  |         rocq proofs/zlib/checksum_fuzzer/lib/A220381.vo\n"
                    % (log, log, error[0], error[1]))
            self.assertEqual(out.count(head), 1, out)
            # the block is its header, its error and the 619 lines up to the next File header; what is not quoted is
            # counted
            message = out[out.index(head):].split("\nFAIL ")[0].split("\n")
            quoted = [l for l in message[2:] if l.startswith("  | ") and not l.startswith("  | [")]
            self.assertEqual(message[-1], "  | [%d more line(s) of this block left out]" % (621 - len(quoted)), out)
            self.assertLessEqual(sum(len(l) + 1 for l in quoted), check.ERROR_BYTES)
            self.assertNotIn("Warning: Notation overridden", out)
            # the other proof gets the first line alone: the log is quoted once
            self.assertIn("\nFAIL proofs/zlib/checksum_fuzzer/plain_halts_may_fail: proofs/zlib/checksum_fuzzer/lib: "
                          "does not compile (see %s) (its log is quoted above, at the first proof that failed on it)\n"
                          % log, out)
            self.assertLess(len(out), 2 * check.ERROR_BYTES)

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
            wrap_call = [l for l in tl.calls().splitlines() if "Wrapper.v" in l][0]
            self.assertTrue(wrap_call.startswith("rocq compile -w -all "), "the wrapper compiles with warnings on: "
                            + wrap_call)
            with open(wrap_call.split()[-1]) as f:
                text = f.read()
            self.assertIn("Definition certified : OssFuzzTheorems.zlib.checksum_fuzzer.Statements.plain_halts := "
                          "OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.plain_halts.Proof.plain_halts_holds.\n"
                          "Set Printing Fully Qualified.\nRedirect \"assumptions\" Print Assumptions certified.\n", text)

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_what_the_wrapper_compile_prints_is_not_read(self):
        """A note the proof makes Rocq print while the wrapper compiles (a #[deprecated] or #[warn] note on the theorem
        that prints "Closed under the global context") is not read: only what Print Assumptions wrote through Redirect
        is, so the axiom the proof rests on still fails it (the Verified Linux team's payload, 2026-10-29)."""
        with tree() as t:
            self.ready(t)
            self._proof(t)
            self.tools(extra_axiom="Top.cheat : False",
                       wrapper_says="Warning: Reference Top.plain_halts_holds is deprecated.\n"
                                    "Closed under the global context\n")
            rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="proofs")
            self.assertEqual(rc, 1, out)
            self.assertIn("axioms outside the allowlist: Top.cheat", out)
            self.assertNotIn("all allowed", out)

    def test_print_assumptions_that_wrote_no_file_is_refused(self):
        with tempfile.TemporaryDirectory() as d:
            with self.assertRaises(check.CheckError) as cm:
                check.read_assumptions(d, os.path.join(d, "wrapper.log"))
            self.assertIn("Print Assumptions wrote no assumptions.out", str(cm.exception))

    def test_print_assumptions_with_a_carriage_return_is_refused(self):
        # read as written, as tests/check.sh reads it: no newline translation turns "\r\n" into a list it would parse
        with tempfile.TemporaryDirectory() as d:
            with open(os.path.join(d, "assumptions.out"), "w", newline="") as f:
                f.write("Axioms:\r\nA.b : Prop\r\n")
            with self.assertRaises(check.CheckError):
                check.read_assumptions(d, os.path.join(d, "wrapper.log"))

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
        # large proof terms overflow the usual 8 MiB stack: rocq runs with soft = min(hard, 2 GiB), an unlimited hard
        # limit counted as infinite (the CI/CD lead, 2026-11-01), so 2097152 KiB unless the hard limit is lower
        with tree() as t:
            self.ready(t)
            self._proof(t)
            tl = self.tools()
            soft, hard = resource.getrlimit(resource.RLIMIT_STACK)
            try:
                resource.setrlimit(resource.RLIMIT_STACK, (min(8 << 20, hard), hard))   # the usual 8 MiB, or less
                rc, out = run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="proofs")
            finally:
                resource.setrlimit(resource.RLIMIT_STACK, (soft, hard))
            self.assertEqual(rc, 0, out)
            want = check.STACK_NEEDED if hard == resource.RLIM_INFINITY else min(hard, check.STACK_NEEDED)
            seen = {l for l in tl.calls().splitlines() if l == "unlimited" or l.isdigit()}
            self.assertEqual(seen, {str(want // 1024)})

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
        # the forms Rocq 9.2.0 prints (printing/printer.ml, pr_assumptionset), as Redirect writes them: nothing else
        self.assertEqual(check.wrapper_assumptions("Closed under the global context\n"), set())
        self.assertEqual(check.wrapper_assumptions("Axioms:\nA.b : forall P : Prop,\n  P\nC.d :\n  nat\n"),
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
            # the line that means "nothing assumed", anywhere but alone: printed by a note while the file compiled,
            "$ rocq compile x\nClosed under the global context\n": "neither",
            "Warning: Reference P.t is deprecated.\nClosed under the global context\n": "neither",
            # or by an axiom's type (a string literal with line breaks), the second payload of 2026-10-29
            'Axioms:\nTop.cheat : K "\nClosed under the global context\n"%pstring\n': "Closed under the global context",
            # an empty line, after which an older parser stopped reading
            "Axioms:\nA.b : Prop\n\nTop.c : False\n": "empty line",
            # a line a type printed that starts with a blank other than a space or a tab is an entry, not a continuation
            'Axioms:\nTop.cheat : K "\n\u00a0junk\n"%pstring\n': "\u00a0junk",
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
            self.assert_void(rc, out, "COMPILED 0")
            self.assertIn("nothing to check", out)

    def test_a_counterexample_reproduces(self):
        with tree() as t:
            t.write("projects/json/bin/fuzzer-parse_bjdata/fuzzer-parse_bjdata.plain", "stand-in")
            self.tools()
            rc, out = run(check.run, t.root, ["json/fuzzer-parse_bjdata"], parts="counterexamples")
            self.assertEqual(rc, 0, out)
            self.assertIn("reproduces (exit 134 SIGABRT); control exits 0", out)
            self.assertNotIn("VOID:", out)
            # a counterexamples run compiles nothing by design, so it says no COMPILED line at all
            # and is not voided for it (the void rule reads a run that wanted statements or proofs)
            self.assertNotIn("COMPILED", out)

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

    # --facts-to and --facts-from: the facts and rules of the whole tree once, then each unit in a view of its own

    ZLIB, JSON = "zlib/checksum_fuzzer", "json/fuzzer-parse_bjdata"
    SECOND = "Theorem plain_halts_may_fail_holds : True. Proof. exact I. Qed.\n"

    def _refutation(self, t, s):
        st = next(x for x in facts.load(t.root).statements() if x.id == "zlib/checksum_fuzzer/" + s)
        t.put_yaml("proofs/zlib/checksum_fuzzer/%s/proof.yaml" % s, {
            "schema": "oss-fuzz-theorems/proof/1", "refutes": st.id, "fingerprint": st.fingerprint})
        t.write("proofs/zlib/checksum_fuzzer/%s/Refutation.v" % s,
                "Theorem %s_refuted : True. Proof. exact I. Qed.\n" % s)
        self.assertEqual(t.generate(), 0, t.last_output)

    def _two_units(self, t):
        """zlib/checksum_fuzzer fetched, with two proofs and a refutation; json/fuzzer-parse_bjdata with the binary its
        counterexample runs on (and not its other binaries, so its statements fail)."""
        self.ready(t)
        self._proof(t)
        self._proof(t, self.SECOND, s="plain_halts_may_fail")
        self._refutation(t, "ubsan_halts")
        t.write("projects/json/bin/fuzzer-parse_bjdata/fuzzer-parse_bjdata.plain", "stand-in")

    def _facts_dir(self):
        return os.path.join(self.d.name, "facts")

    def _python(self, *args):
        """python3 args from tools/, as CI runs the checker."""
        return subprocess.run([sys.executable] + list(args),
                              cwd=os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))),
                              env=dict(os.environ, PYTHONDONTWRITEBYTECODE="1"), capture_output=True, text=True)

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_facts_to_then_facts_from_gives_the_steps_and_verdict_of_a_plain_run(self):
        """zlib/checksum_fuzzer's statements, two proofs and a refutation pass, in the order of harness.yaml;
        json/fuzzer-parse_bjdata's statements fail, and its counterexample runs once for its own statement and once
        for the agreement that the same run refutes."""
        with tree() as t:
            self._two_units(t)
            tl = self.tools()
            units = [self.ZLIB, self.JSON]
            rc, out = run(check.run, t.root, units, facts_to=self._facts_dir())
            self.assertEqual(rc, 0, out)
            self.assertEqual(len(out.splitlines()), 2, out)
            for f in ("zlib/checksum_fuzzer.yaml", "json/fuzzer-parse_bjdata.yaml"):
                self.assertTrue(os.path.isfile(os.path.join(self._facts_dir(), f)), f)
            self.assertFalse(os.path.exists(tl.log), "--facts-to builds nothing")
            self.assertFalse(os.path.exists(os.path.join(self.d.name, "qemu-core-limit.log")), "and runs nothing")
            plain = run(check.run, t.root, units)
            split = run(check.run, t.root, units, facts_from=self._facts_dir())
            self.assertEqual((split[0], same_run(split[1])), (plain[0], same_run(plain[1])))
            self.assertEqual(split[0], 1)
            proved = ["proofs/zlib/checksum_fuzzer/%s: %s zlib/checksum_fuzzer/%s; " % (s, how, s) for s, how in (
                ("plain_halts", "proves"), ("ubsan_halts", "refutes"), ("plain_halts_may_fail", "proves"))]
            self.assertEqual([line[:len(p)] for line in split[1].splitlines() for p in proved if line.startswith(p)],
                             proved)
            for line in ("projects/zlib/checksum_fuzzer: statements compiled, each of the 11 listed defined\n",
                         "FAIL statements: the binaries are missing or do not match (run ./oft fetch json)\n",
                         "oft check: 6 step(s) passed, 1 failed; "):
                self.assertIn(line, split[1])
            self.assertEqual(split[1].count("counterexamples/json/fuzzer-parse_bjdata/plain_halts: reproduces (exit "
                                            "134 SIGABRT); control exits 0\n"), 2, split[1])

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_facts_from_checks_a_unit_in_a_view_that_holds_only_its_files(self):
        """A plain run fails in the view: it loads the facts of the whole tree, and the view has no release.yaml.  With
        the facts --facts-to wrote from the whole tree, the same check passes there.  Both phases run by the command
        line, the first as `oft check`, the second as check-units.sh runs it."""
        with tree() as t:
            self._two_units(t)
            self.tools()
            d = self._facts_dir()
            r = self._python("-m", "oft", "--root", t.root, "check", self.ZLIB, self.JSON, "--facts-to", d)
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            for unit, parts, passed in ((self.ZLIB, "statements,proofs", 4), (self.JSON, "counterexamples", 2)):
                with self.subTest(unit=unit):
                    view = unit_view(t, unit, os.path.join(self.d.name, "view-" + unit.split("/")[0]))
                    self.assertFalse(os.path.exists(os.path.join(view, "release.yaml")))
                    r = self._python("-m", "oft.check", "--root", view, unit, "--parts", parts)
                    self.assertEqual(r.returncode, 1, r.stdout + r.stderr)
                    self.assertIn("error: release.yaml: missing", r.stdout)
                    r = self._python("-m", "oft.check", "--root", view, unit, "--parts", parts, "--facts-from", d)
                    self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
                    self.assertIn("oft check: %d step(s) passed, 0 failed" % passed, r.stdout)

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_facts_from_refuses_facts_it_cannot_use(self):
        """No facts file, one of another format version or of another unit, and unit files other than those the facts
        came from: one of them differs or is missing, for a part the run checks.  Each fails its unit before anything
        is built or run."""
        proof_yaml = "proofs/zlib/checksum_fuzzer/plain_halts/proof.yaml"
        expect_yaml = "counterexamples/json/fuzzer-parse_bjdata/plain_halts/expect.yaml"
        finding_yaml = FINDING + "/finding.yaml"
        sources = ("projects/zlib/project.yaml", "projects/zlib/checksum_fuzzer/harness.yaml", proof_yaml, expect_yaml,
                   finding_yaml, UNPATCHED)
        with tree() as t:
            self._two_units(t)
            add_findings(t)
            tl = self.tools()
            d = self._facts_dir()
            zlib_facts = os.path.join(d, "zlib", "checksum_fuzzer.yaml")
            saved = {rel: t.read(rel) for rel in sources}

            def version(n):
                y = yamlio.load_file(zlib_facts)
                y["version"] = n
                with open(zlib_facts, "w") as f:
                    f.write(yamlio.dump(y))

            def names_of(namespace):
                y = yamlio.load_file(zlib_facts)
                y["names"]["namespace"] = namespace
                with open(zlib_facts, "w") as f:
                    f.write(yamlio.dump(y))

            def append(rel):
                t.write(rel, "# changed after --facts-to\n", "a")

            cases = (("no facts file", self.ZLIB, None, lambda: os.remove(zlib_facts), "no facts file"),
                     ("another version", self.ZLIB, None, lambda: version(1), "version 1"),
                     ("another namespace", self.ZLIB, None, lambda: names_of("OSSVerify"),
                      "is not OSSVerify.zlib.checksum_fuzzer"),
                     ("another unit", self.ZLIB, None,
                      lambda: shutil.copy(os.path.join(d, "json", "fuzzer-parse_bjdata.yaml"), zlib_facts), self.JSON),
                     ("a changed project.yaml", self.ZLIB, None, lambda: append(sources[0]), sources[0]),
                     ("a changed harness.yaml", self.ZLIB, None, lambda: append(sources[1]), sources[1]),
                     ("a missing proof.yaml", self.ZLIB, None, lambda: os.remove(t.path(proof_yaml)), proof_yaml),
                     ("a changed expect.yaml", self.JSON, None, lambda: append(expect_yaml), expect_yaml),
                     ("a changed finding.yaml", self.ZLIB, "findings", lambda: append(finding_yaml), finding_yaml),
                     ("a changed unpatched.yaml", self.ZLIB, "findings", lambda: append(UNPATCHED), UNPATCHED))
            for why, unit, parts, change, said in cases:
                with self.subTest(why):
                    self.assertEqual(run(check.run, t.root, [self.ZLIB, self.JSON], facts_to=d)[0], 0)
                    change()
                    for log in (tl.log, os.path.join(self.d.name, "qemu-core-limit.log")):
                        if os.path.exists(log):
                            os.remove(log)
                    rc, out = run(check.run, t.root, [unit], parts=parts, facts_from=d)
                    for rel, text in saved.items():
                        t.write(rel, text)
                    self.assert_void(rc, out, said)
                    self.assertNotIn("FAIL ", out)
                    self.assertFalse(os.path.exists(tl.log), "nothing is built")
                    self.assertFalse(os.path.exists(os.path.join(self.d.name, "qemu-core-limit.log")), "nothing runs")

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_facts_from_refuses_a_unit_directory_the_facts_do_not_have(self):
        """A proof, a counterexample or a finding directory added after --facts-to is in no step the facts give, so the
        check would pass without examining it: here a proof that does not compile.  It fails the unit when the run
        checks its part, and names the directory."""
        proof = "proofs/zlib/checksum_fuzzer/plain_halts_may_fail"
        counterexample = "counterexamples/json/fuzzer-parse_bjdata/extra"
        finding = "findings/zlib/checksum_fuzzer/extra"
        with tree() as t:
            self.ready(t)
            self._proof(t)
            add_findings(t)
            t.write("projects/json/bin/fuzzer-parse_bjdata/fuzzer-parse_bjdata.plain", "stand-in")
            self.tools(compile_fails_on="plain_halts_may_fail")
            d = self._facts_dir()
            self.assertEqual(run(check.run, t.root, [self.ZLIB, self.JSON], facts_to=d)[0], 0)
            self._proof(t, self.SECOND, s="plain_halts_may_fail")
            rc, out = run(check.run, t.root, [self.ZLIB], parts="proofs")
            self.assertEqual(rc, 1, out)
            self.assertIn("FAIL %s: %s: does not compile" % (proof, proof), out)
            os.makedirs(t.path(counterexample))
            os.makedirs(t.path(finding))
            for unit, parts, added in ((self.ZLIB, "statements", proof), (self.ZLIB, "proofs", proof),
                                       (self.JSON, "counterexamples", counterexample),
                                       (self.ZLIB, "findings", finding)):
                with self.subTest(parts=parts):
                    rc, out = run(check.run, t.root, [unit], parts=parts, facts_from=d)
                    self.assert_void(rc, out, added)
                    self.assertNotIn("FAIL ", out)
                    for other in {proof, counterexample, finding} - {added}:
                        self.assertNotIn(other, out, "a directory of a part the run does not check")

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_facts_from_compares_the_view_s_files_of_the_parts_it_checks(self):
        """A view of the build part's key holds no findings/: its statements and proofs pass, and its findings fail.  A
        file the facts came from that differs in the view alone fails the unit: the files are read under --root."""
        with tree() as t:
            self.ready(t)
            self._proof(t)
            add_findings(t)
            self.tools()
            d = self._facts_dir()
            self.assertEqual(run(check.run, t.root, [self.ZLIB], facts_to=d)[0], 0)
            view = unit_view(t, self.ZLIB, os.path.join(self.d.name, "view"))
            shutil.rmtree(os.path.join(view, "findings"))
            rc, out = run(check.run, view, [self.ZLIB], parts="statements,proofs", facts_from=d)
            self.assertEqual(rc, 0, out)
            self.assertIn("oft check: 2 step(s) passed, 0 failed", out)
            rc, out = run(check.run, view, [self.ZLIB], parts="findings", facts_from=d)
            self.assert_void(rc, out, "findings/zlib/")
            self.assertNotIn("FAIL ", out)
            self.assertIn("findings/zlib/", out)
            with open(os.path.join(view, "projects/zlib/project.yaml"), "a") as f:
                f.write("# changed in the view alone\n")
            rc, out = run(check.run, view, [self.ZLIB], parts="statements,proofs", facts_from=d)
            self.assert_void(rc, out, "projects/zlib/project.yaml differs")
            self.assertNotIn("FAIL ", out)
            self.assertIn("projects/zlib/project.yaml differs", out)

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_facts_to_writes_only_the_unit_s_own_findings(self):
        """zlib/api-driver has no finding; zlib/checksum_fuzzer has one.  The facts of zlib/api-driver hold none, so a
        view of zlib/api-driver, which holds no file of zlib/checksum_fuzzer, passes with its findings part."""
        api = "zlib/api-driver"
        with tree() as t:
            self.ready(t)
            add_findings(t)
            self.tools()
            d = self._facts_dir()
            self.assertEqual(run(check.run, t.root, [self.ZLIB, api], facts_to=d)[0], 0)
            for unit, want in ((self.ZLIB, [FINDING]), (api, [])):
                written = yamlio.load_file(check.facts_file(d, unit))
                self.assertEqual([f["path"] for f in written["findings"]], want, unit)
            view = unit_view(t, api, os.path.join(self.d.name, "view"))
            self.assertFalse(os.path.exists(os.path.join(view, FINDING)))
            plain = run(check.run, t.root, [api], parts="statements,findings")
            rc, out = run(check.run, view, [api], parts="statements,findings", facts_from=d)
            self.assertEqual((rc, same_run(out)), (plain[0], same_run(plain[1])))
            self.assertEqual(rc, 0, out)

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_facts_from_voids_malformed_facts_and_stops_before_the_next_unit(self):
        """Keys missing, data of the wrong type, a statement's data that is not its harness.yaml's, and a proof's
        refutes that is not true or false: no unit receives a verdict from unreadable facts."""
        with tree() as t:
            self._two_units(t)
            self.tools()
            d = self._facts_dir()
            self.assertEqual(run(check.run, t.root, [self.ZLIB, self.JSON], facts_to=d)[0], 0)
            path = check.facts_file(d, self.ZLIB)
            good = yamlio.load_file(path)
            statements = [dict(s) for s in good["statements"]]
            statements[0]["data"] = {"kind": "halts"}
            refutes = [dict(s, proof=s["proof"] and dict(s["proof"], refutes="yes")) for s in good["statements"]]
            builds = dict(good["harness"], data=dict(good["harness"]["data"], builds="plain"))
            cases = (("keys missing", {"version": 1, "unit": self.ZLIB, "project": {}}),
                     ("a harness whose builds are not a mapping", dict(good, harness=builds)),
                     ("a statement's data that is not harness.yaml's", dict(good, statements=statements)),
                     ("a refutes that is not true or false", dict(good, statements=refutes)))
            for why, data in cases:
                with self.subTest(why):
                    with open(path, "w") as f:
                        f.write(yamlio.dump(data))
                    rc, out = run(check.run, t.root, [self.ZLIB, self.JSON], facts_from=d)
                    self.assert_void(rc, out, path)
                    self.assertNotIn("FAIL ", out)
                    self.assertNotIn(self.JSON, out)

    def test_facts_to_writes_nothing_for_a_tree_the_rules_refuse(self):
        with tree() as t:
            r = t.yaml("release.yaml")
            r["counts"]["binaries"] += 1
            t.put_yaml("release.yaml", r)
            self.assertEqual(facts.load(t.root).errors, [], "the loader takes the tree; the rules refuse it")
            rc, out = run(check.run, t.root, [self.ZLIB], facts_to=self._facts_dir())
            self.assertEqual(rc, 1, out)
            self.assertIn("error: release.yaml", out)
            self.assertFalse(os.path.exists(self._facts_dir()) and os.listdir(self._facts_dir()), "no file is written")

    def test_facts_to_names_a_unit_with_no_harness(self):
        with tree() as t:
            rc, out = run(check.run, t.root, [self.ZLIB, "zlib/no_such_fuzzer"], facts_to=self._facts_dir())
            self.assertEqual(rc, 1, out)
            self.assertIn("zlib/no_such_fuzzer: no such harness\n", out)
            self.assertEqual(os.listdir(os.path.join(self._facts_dir(), "zlib")), ["checksum_fuzzer.yaml"])

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_facts_from_never_loads_the_tree(self):
        """Neither the facts of the whole tree nor its rules: --facts-to ran them, and a view would fail them.  The
        statements' check of the binaries reads the unit's harness alone, not a fresh load of the tree."""
        with tree() as t:
            self._two_units(t)
            self.tools()
            d = self._facts_dir()
            self.assertEqual(run(check.run, t.root, [self.ZLIB], facts_to=d)[0], 0)
            with mock.patch.object(facts, "load", side_effect=AssertionError("facts.load ran")), \
                    mock.patch.object(rules, "check", side_effect=AssertionError("rules.check ran")):
                rc, out = run(check.run, t.root, [self.ZLIB], facts_from=d)
            self.assertEqual(rc, 0, out)
            self.assertIn("oft check: 4 step(s) passed, 0 failed", out)


class LogErrors(unittest.TestCase):
    """check.log_errors: what the CheckError of a failed build quotes from its log."""

    def errors(self, lines):
        with tempfile.TemporaryDirectory() as d:
            log = os.path.join(d, "x.lib.dune.log")
            with open(log, "w", newline="") as f:
                f.write("".join(l + "\n" for l in lines))
            return check.log_errors(log).replace(log, "LOG")

    @staticmethod
    def block(n, extra=()):
        return ['File "lib/F%d.v", line %d, characters 0-3:' % (n, n), "Error: error number %d" % n] + list(extra)

    def test_a_log_with_no_error_line_quotes_its_last_40_lines(self):
        got = self.errors(["line %d" % n for n in range(1, 101)])
        self.assertEqual(got, "\nthe log holds no Error: line; its last 40 line(s) are quoted here; the whole log is "
                              "LOG\n" + "\n".join("  | line %d" % n for n in range(61, 101)))
        # a File header with only a warning under it is no Error: block either
        got = self.errors(['File "lib/A.v", line 1, characters 0-4:', "Warning: notation overridden"])
        self.assertIn("no Error: line; its last 2 line(s) are quoted here", got)
        self.assertIn("  | Warning: notation overridden", got)

    def test_an_empty_or_missing_log_still_says_so(self):
        self.assertEqual(self.errors([]), "\nthe log holds no Error: line and is empty: LOG")
        self.assertEqual(check.log_errors("/nonexistent/x.log"),
                         "\nthe log /nonexistent/x.log cannot be read: [Errno 2] No such file or directory: "
                         "'/nonexistent/x.log'")

    def test_errors_past_the_block_cap_are_counted_and_left_out(self):
        lines = ["$ dune build", "        rocq lib/A.vo"]
        for n in range(1, 10):
            lines += self.block(n, ["        rocq lib/G%d.vo" % n])
        got = self.errors(lines)
        quoted = "".join("\n  | " + l for n in range(1, 6) for l in self.block(n, ["        rocq lib/G%d.vo" % n]))
        self.assertEqual(got, "\nthe log holds 9 Error: block(s): 5 quoted here, 4 left out; the whole log is LOG"
                              + quoted)
        self.assertNotIn("error number 6", got)

    def test_errors_past_the_byte_cap_are_cut_and_counted(self):
        long = ["x" * 99] * 70   # 7,000 bytes under each error
        got = self.errors(self.block(1, long) + self.block(2, long) + self.block(3, long))
        self.assertTrue(got.startswith("\nthe log holds 3 Error: block(s): 2 quoted here, 1 left out; the whole log "
                                       "is LOG\n  | File \"lib/F1.v\""), got)
        self.assertIn("  | Error: error number 2\n", got)
        self.assertRegex(got, r"\n  \| \[\d+ more line\(s\) of this block left out\]$")
        self.assertNotIn("error number 3", got)
        quoted = [l[len("  | "):] for l in got.split("\n")[2:] if not l.startswith("  | [")]
        self.assertLessEqual(sum(len(l.replace(" [cut]", "")) + 1 for l in quoted), check.ERROR_BYTES + 1)
        # one line longer than the cap is cut to what is left of it
        got = self.errors(['File "lib/A.v", line 1, characters 0-1:', "Error: " + "y" * 20000])
        self.assertIn("1 Error: block(s): 1 quoted here; the whole log is LOG\n", got)
        self.assertRegex(got, r"\n  \| Error: y{7000,8000} \[cut\]$")
        self.assertLess(len(got), check.ERROR_BYTES + 200)

    def test_an_error_with_no_file_header_before_it_opens_a_block_with_its_context(self):
        """dune prints some errors with no location (`Error: Don't know how to build ...`).  Such a line among the
        rules dune ran opens a block of its own, with the 5 lines before it, as the gate's pod script reads it with `grep -C 5`
        (the CI/CD lead's two probe logs of #918)."""
        rules = ["        rocq lib/A%d.vo" % n for n in range(1000)]
        got = self.errors(rules + ["Error: Can't find file lib/X.v on loadpath"] + rules)
        self.assertEqual(got.split("\n")[1:8], [
            "the log holds 1 Error: block(s): 1 quoted here; the whole log is LOG"]
            + ["  |         rocq lib/A%d.vo" % n for n in range(995, 1000)]
            + ["  | Error: Can't find file lib/X.v on loadpath"])
        # after a warning's block that its 100,000 rules filled long before
        got = self.errors(['File "lib/W.v", line 1, characters 0-4:', "Warning: notation overridden"]
                          + ["        rocq lib/A%d.vo" % n for n in range(100000)]
                          + ["Error: Don't know how to build lib/X.vo"])
        self.assertIn("the log holds 1 Error: block(s): 1 quoted here; the whole log is LOG\n", got)
        self.assertIn("\n  |         rocq lib/A99999.vo\n  | Error: Don't know how to build lib/X.vo", got)
        self.assertNotIn("Warning", got, "the warning's block holds no Error: line")

    def test_an_error_late_in_a_block_is_quoted_whole(self):
        """The CI/CD lead's sweeps of 5a85aa408c04: a warning's block, N lines, a headerless Error: line, 5 more lines.
        With ASCII lines of about 80 bytes and with lines of 3-byte characters (as Rocq prints goals), the Error:
        line is quoted whole for every N: one that would not fit whole in the open block opens its own."""
        err = "Error: Don't know how to build lib/X.vo"
        for filler, ns in (("x" * 76, range(80, 120)), ("\u22a2 \u2200 \u2192 \u220e " * 4, range(40, 120))):
            for n in ns:
                with self.subTest(filler=filler[:4], n=n):
                    got = self.errors(['File "lib/W.v", line 1, characters 0-4:', "Warning: notation overridden"]
                                      + ["%d %s" % (i, filler) for i in range(n)] + [err]
                                      + ["after %d" % i for i in range(5)])
                    self.assertIn("\n  | %s\n" % err, got + "\n")
                    self.assertIn("the log holds 1 Error: block(s): 1 quoted here;", got)

    def test_the_quoted_lines_are_bounded_in_bytes_and_lines_prefixes_included(self):
        """The CI/CD lead's probes of #918: a header and an error, then 20,000 empty lines; and one line of 20,000
        vertical tabs, which str.splitlines cuts into one piece each."""
        for extra in ([""] * 20000, ["\x0b" * 20000]):
            got = self.errors(['File "lib/A.v", line 1, characters 0-1:', "Error: x"] + extra)
            quoted = [l for l in got.split("\n")[2:] if not l.startswith("  | [")]
            self.assertLessEqual(len(quoted), check.ERROR_LINES)
            self.assertLessEqual(sum(len((l + "\n").encode()) for l in quoted), check.ERROR_BYTES)
            self.assertLessEqual(len(got.split("\n")) - 2 - len(quoted), 1, "at most one note")

    def test_a_log_with_no_line_end_is_read_in_bounded_pieces(self):
        """64 MiB with no newline: read whole, it took about 3 times its size in memory.  Here the peak grows by less
        than 16 MiB (measured in a process of its own), and the message is its cut end."""
        with tempfile.TemporaryDirectory() as d:
            log = os.path.join(d, "x.log")
            with open(log, "wb") as f:
                f.writelines(b"a" * (1 << 20) for _ in range(64))
            code = ("import resource, sys\nfrom oft import check\n"
                    "before = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss\n"
                    "msg = check.log_errors(sys.argv[1])\n"
                    "print(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss - before)\nprint(msg)\n")
            # from tools/, where `from oft import check` finds this checker
            r = subprocess.run([sys.executable, "-c", code, log], capture_output=True, text=True,
                               cwd=os.path.dirname(os.path.dirname(os.path.abspath(check.__file__))))
            self.assertEqual(r.returncode, 0, r.stderr)
            grown_kib, msg = r.stdout.split("\n", 1)
            self.assertLess(int(grown_kib), 16 << 10, "KiB")
            self.assertTrue(msg.startswith("\nthe log holds no Error: line; its last 1 line(s) are quoted here"), msg)
            self.assertRegex(msg, r"\n  \| a{7000,8000} \[cut\]\n$")

    def test_no_log_line_stands_as_a_line_of_the_check_s_output(self):
        """A log line with a carriage return or U+2028 in it, which str.splitlines ends a line at, is quoted as two
        lines, each with its "  | ": a reader of the check's output finds no summary or claim line of the log's."""
        forged = "oft check: 9 step(s) passed, 0 failed"
        got = self.errors(['File "lib/A.v", line 1, characters 0-1:', "Error: x\r" + forged, "y\u2028" + forged])
        rest = got.splitlines()[2:]
        self.assertEqual(rest, ['  | File "lib/A.v", line 1, characters 0-1:', "  | Error: x", "  | " + forged, "  | y",
                                "  | " + forged])
        self.assertEqual([l for l in got.splitlines() if l.startswith("oft check")], [])


class ReachStep(unittest.TestCase):
    def pr_reach_step(self, head_release, base_release, changed, routed="true", event="pull_request",
                      old_base_tools=False):
        """pr.yml's reach step, run as the workflow runs it for this event, with this text as the change's
        release.yaml and the base's (None: no such file), these changed paths and the base step's `routed`: (its
        exit, its output, the outputs it wrote).  With old_base_tools, the base's tools are an oft whose plan module
        has no images_differ."""
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
            with open(os.path.join(tmp, "changed.txt"), "w", encoding="utf-8", errors="surrogateescape") as f:
                f.write("".join(rel + "\n" for rel in changed))
            script = os.path.join(d, "reach.sh")
            step = next(s for s in yamlio.load_file(PR_YML)["jobs"]["plan"]["steps"] if s.get("id") == "reach")
            with open(script, "w") as f:
                f.write(step["run"])
            out = os.path.join(d, "output")
            # the step starts python itself, and -B of this process does not reach that child: without this the run
            # leaves tools/oft/__pycache__ behind, which the repository's own lint then refuses
            env = dict(os.environ, PATH=os.path.join(d, "bin") + os.pathsep + os.environ["PATH"], RUNNER_TEMP=tmp,
                       GITHUB_OUTPUT=out, GITHUB_STEP_SUMMARY=os.path.join(d, "summary"), ROUTED=routed,
                       GITHUB_EVENT_NAME=event, PYTHONDONTWRITEBYTECODE="1", LC_ALL="C.UTF-8")  # a runner's locale
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

    @unittest.skipUnless(HAVE_PR_YML, "no .github/workflows/pr.yml beside tools/oft")
    def test_the_reach_step_routes_every_event_by_its_change_alone(self):
        """A push to main and a merge queue group are routed by their changed paths as a pull request is.  Only a
        change to the workflows, a .gitattributes or a quoted path, and a run the base step could not route (no base
        to compare with), run the tools' tests and the controls whatever the paths, and all but the change to the
        workflows the tests' whole-tree lint too: the workflows are no code of the tools that lint, so that test would
        repeat the lint job's run of the base's lint.  The tools' tests read the facts review's skill, what that
        review checks (review.md) and the repository's release.yaml, so a change to any of them alone runs them."""
        with open(os.path.join(REPO, "tools", "oft", "tests", "fixtures", "tree", "release.yaml")) as f:
            release = f.read()
        cases = [
            # (case, changed, routed, (repository_lint, tests, controls))
            ("CHANGELOG.md only", ["CHANGELOG.md"], "true", ("false", "false", "false")),
            ("docs and a proof", ["docs/checking.md", "proofs/zlib/checksum_fuzzer/plain_halts/Proof.v"], "true",
             ("false", "false", "false")),
            ("a workflow", [".github/workflows/pr.yml"], "true", ("false", "true", "true")),
            ("a workflow and a tool", [".github/workflows/pr.yml", "tools/oft/plan.py"], "true",
             ("true", "true", "true")),
            ("a .gitattributes", ["proofs/.gitattributes"], "true", ("true", "true", "true")),
            ("a quoted path", ['"docs/a\\tb.md"'], "true", ("true", "true", "true")),
            ("the facts review's skill", [".claude/skills/review-facts/SKILL.md"], "true", ("false", "true", "false")),
            # test_facts_review_scripts.SkillTest and CodeOwnersTest read review.md at the repository's root
            ("what the facts review checks", ["review.md"], "true", ("false", "true", "false")),
            ("a file named review.md elsewhere", ["docs/review.md"], "true", ("false", "false", "false")),
            ("release.yaml, the same images", ["release.yaml"], "true", ("false", "true", "false")),
            ("a file named release.yaml elsewhere", ["docs/release.yaml"], "true", ("false", "false", "false")),
            ("test data only", ["tools/oft/tests/fixtures/tree/README.md"], "true", ("false", "true", "false")),
            ("a tool", ["tools/oft/lint.py"], "true", ("true", "true", "false")),
            ("theories", ["theories/Shapes.v"], "true", ("false", "false", "true")),
            ("not routed", ["CHANGELOG.md"], "false", ("true", "true", "true")),
            ("routed left unset", ["CHANGELOG.md"], "", ("true", "true", "true")),
        ]
        for event in ("pull_request", "merge_group", "push"):
            for name, changed, routed, want in cases:
                with self.subTest(event=event, case=name):
                    rc, output, got = self.pr_reach_step(release, release, changed, routed=routed, event=event)
                    self.assertEqual(rc, 0, output)
                    self.assertEqual((got.get("repository_lint"), got.get("tests"), got.get("controls")), want,
                                     output)

    @unittest.skipUnless(HAVE_PR_YML, "no .github/workflows/pr.yml beside tools/oft")
    def test_a_proof_s_generated_dune_file_alone_runs_no_controls(self):
        """A proof directory's dune file is generated (lint's `oft generate --check` holds it equal to its rendering)
        and declares that proof's theory alone: a proof pull request that adds one runs no controls, unless the
        renderer, tools/oft/, changes with it.  Any other dune file still runs them."""
        with open(os.path.join(REPO, "tools", "oft", "tests", "fixtures", "tree", "release.yaml")) as f:
            base = f.read()
        proof = ["proofs/zlib/checksum_fuzzer/plain_halts/Proof.v", "proofs/zlib/checksum_fuzzer/plain_halts/dune",
                 "proofs/zlib/checksum_fuzzer/plain_halts/proof.yaml"]
        cases = [
            ("a proof with its dune file", proof, "false"),
            ("a proof library's dune file", ["proofs/zlib/checksum_fuzzer/lib/dune"], "false"),
            ("with a change to the renderer", proof + ["tools/oft/templates/proof-dune.tmpl"], "true"),
            ("the shared proof library's dune file", ["proofs/lib/dune"], "true"),
            ("a hand-written dune file deep in the shared proof library", ["proofs/lib/a/b/dune"], "true"),
            ("a dune file deeper in a proof", ["proofs/zlib/checksum_fuzzer/plain_halts/sub/dune"], "true"),
            ("a harness's dune file", ["projects/zlib/checksum_fuzzer/dune"], "true"),
            # the per-project layout (tools/oft/layout.py): the same rule in the fuzz target's own folder
            ("a per-project proof with its dune file", [p.replace("proofs/zlib/checksum_fuzzer/",
                                                                  "projects/zlib/checksum_fuzzer/proofs/")
                                                        for p in proof], "false"),
            ("a per-project proof library's dune file", ["projects/zlib/checksum_fuzzer/proofs/lib/dune"], "false"),
            ("the barrier dune files", ["projects/zlib/checksum_fuzzer/proofs/dune",
                                        "projects/zlib/checksum_fuzzer/counterexamples/dune"], "false"),
            ("a per-project dune file deeper in a proof",
             ["projects/zlib/checksum_fuzzer/proofs/plain_halts/sub/dune"], "true"),
            ("a dune file in a counterexample", ["projects/zlib/checksum_fuzzer/counterexamples/plain_halts/dune"],
             "true"),
            ("a per-project proof with a change to the renderer",
             ["projects/zlib/checksum_fuzzer/proofs/plain_halts/dune", "tools/oft/generate.py"], "true"),
            ("tests/", proof + ["tests/check.sh"], "true"),
            ("dune-project", proof + ["dune-project"], "true"),
            # a name that is not valid UTF-8, under the runner's UTF-8 locale
            ("a non-UTF-8 name under tests/", proof + ["tests/a\udcffb/check.sh"], "true"),
        ]
        for name, changed, controls in cases:
            with self.subTest(case=name):
                rc, output, got = self.pr_reach_step(base, base, changed)
                self.assertEqual(rc, 0, output)
                self.assertEqual(got.get("controls"), controls, output)


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

    def ready(self, t, ported=False):
        """Fetch the unpatched binaries of t's findings; with ported, after moving the findings and unpatched.yaml to
        the per-project layout, as `oft port-layout` moves them."""
        add_findings(t)
        unpatched_release(t, self.assets)
        if ported:
            self.ported(t)
        rc, out = run(fetch.fetch, t.root, ["zlib"], source=self.assets, findings=True)
        self.assertEqual(rc, 0, out)

    def ported(self, t):
        """Move t to the per-project layout, as `oft port-layout` does, and render it again."""
        self.assertEqual(port.port_worktree(t.root, out=io.StringIO()), 0)
        self.assertEqual(t.generate(), 0, t.last_output)

    def check(self, t, **kw):
        return run(check.run, t.root, ["zlib/checksum_fuzzer"], parts="findings", **kw)

    def test_old_layout_findings_unpack_into_unpatched_bin(self):
        with tree() as t:
            add_findings(t)
            files = unpatched_release(t, self.assets)
            rc, out = run(fetch.fetch, t.root, ["zlib"], source=self.assets, findings=True)
            self.assertEqual(rc, 0, out)
            self.assertIn("zlib: zlib-unpatched-bin.tar.zst", out)
            self.assertIn("8 binaries, each SHA-256 checked", out)
            for name, data in files.items():
                with open(t.path("projects/zlib/unpatched-bin", name), "rb") as f:
                    self.assertEqual(f.read(), data)
            self.assertFalse(os.path.exists(t.path("projects/zlib/bin")), "the published binaries are not fetched")
            self.assertEqual([str(f) for f in t.lint()], [], "the fetched binaries are never tracked")

    def test_findings_unpack_into_unpatched_bin(self):
        with tree() as t:
            add_findings(t)
            files = unpatched_release(t, self.assets)
            self.ported(t)
            rc, out = run(fetch.fetch, t.root, ["zlib"], source=self.assets, findings=True)
            self.assertEqual(rc, 0, out)
            for name, data in files.items():
                p = t.path("projects/zlib/unpatched-bin", name)
                self.assertTrue(os.path.isfile(p), p)
                with open(p, "rb") as f:
                    self.assertEqual(f.read(), data)
            self.assertFalse(os.path.exists(t.path("findings")))

    def test_fetch_unpacks_the_licence_files_beside_the_unpatched_binaries(self):
        """The unpatched archive may carry the licence files of the components compiled into its binaries, as a
        published one does; they go to projects/<p>/unpatched-bin/LICENSES/."""
        lic = {"LICENSES/zlib/LICENSE": b"zlib licence\n"}
        with tree() as t:
            add_findings(t)
            unpatched_release(t, self.assets, tamper=lambda f: dict(f, **lic))
            rc, out = run(fetch.fetch, t.root, ["zlib"], source=self.assets, findings=True)
            self.assertEqual(rc, 0, out)
            self.assertIn("8 binaries, each SHA-256 checked; 1 licence files", out)
            with open(t.path("projects/zlib/unpatched-bin/LICENSES/zlib/LICENSE"), "rb") as f:
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
            plain = "projects/zlib/unpatched-bin/checksum_fuzzer/checksum_fuzzer.plain"
            self.assertFalse(os.path.exists(t.path(plain)), plain)

    def test_fetch_refuses_a_project_without_unpatched_binaries(self):
        with tree() as t:
            add_findings(t)
            rc, out = run(fetch.fetch, t.root, ["json"], source=self.assets, findings=True)
            self.assertEqual(rc, 1)
            self.assertIn("json: no findings/json/unpatched.yaml", out)

    def test_fetch_names_the_unpatched_yaml_a_new_layout_project_lacks(self):
        with tree() as t:
            add_findings(t)
            self.ported(t)
            rc, out = run(fetch.fetch, t.root, ["json"], source=self.assets, findings=True)
            self.assertEqual(rc, 1)
            self.assertIn("json: no projects/json/unpatched.yaml", out)

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
            with open(t.path("projects/zlib/unpatched-bin/checksum_fuzzer/checksum_fuzzer.asan"), "ab") as f:
                f.write(b"!")
            rc, out = self.check(t)
            self.assertEqual(rc, 1)
            self.assertIn("projects/zlib/unpatched-bin/checksum_fuzzer/checksum_fuzzer.asan does not match its SHA-256 "
                          "in findings/zlib/unpatched.yaml (run ./oft fetch --findings zlib)", out)

    def test_a_new_layout_finding_is_checked_against_its_unpatched_yaml(self):
        with tree() as t:
            self.ready(t, ported=True)
            rc, out = self.check(t)
            self.assertEqual(rc, 0, out)
            self.assertIn("projects/zlib/checksum_fuzzer/findings/stand-in-abort: 6 runs match the record", out)
            with open(t.path("projects/zlib/unpatched-bin/checksum_fuzzer/checksum_fuzzer.asan"), "ab") as f:
                f.write(b"!")
            rc, out = self.check(t)
            self.assertEqual(rc, 1)
            self.assertIn("projects/zlib/unpatched-bin/checksum_fuzzer/checksum_fuzzer.asan does not match its SHA-256 "
                          "in projects/zlib/unpatched.yaml (run ./oft fetch --findings zlib)", out)

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
            fake_docker(tl, self.d.name)
            assets = os.path.join(self.d.name, "ci-assets")
            os.makedirs(assets)
            tools = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
            script = os.path.join(tools, "ci", "check-units.sh")
            env = dict(os.environ, PATH=tl.bin + os.pathsep + self.old_path, WORK=t.root, TOOLS=os.path.dirname(tools),
                       UNITS="", PROOF_UNITS='""', PROJECTS="", CX_UNITS="", FINDINGS="zlib/checksum_fuzzer",
                       ASSETS=assets,
                       PYDEPS=self.d.name, GITHUB_REPOSITORY="example/proofs",
                       CHECK_UNITS_LOG=log, CHECK_UNITS_SOURCE=self.assets, CHECK_UNITS_DEST=assets,
                       PYTHONDONTWRITEBYTECODE="1")
            r = subprocess.run(["bash", script], env=env, capture_output=True, text=True)
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            self.assertIn("oft check: 1 step(s) passed, 0 failed", r.stdout)
            with open(log) as f:
                calls = f.read()
            self.assertIn("gh release download findings-zlib", calls)
            self.assertIn("python3 -m oft.check --root /work --facts-from /facts zlib/checksum_fuzzer --parts findings",
                          calls)
            self.assertNotIn("statements,proofs", calls)
            # in the runner image, the facts too, since no build is checked; the finding's view holds its unpatched
            # binaries and its records, and no proof
            self.assertNotIn("oss-fuzz-theorems-checker", calls)
            run = next(l for l in calls.splitlines() if "--parts findings" in l)
            for rel in ("projects/zlib/unpatched-bin/checksum_fuzzer", "findings/zlib/checksum_fuzzer",
                        "findings/zlib/unpatched.yaml", "projects/zlib/checksum_fuzzer/harness.yaml",
                        "projects/zlib/project.yaml"):
                self.assertIn(":/work/%s:ro " % rel, run)
            self.assertNotIn("/work/proofs", run)
            self.assertNotIn("/work/projects/zlib/bin", run)
            self.assertNotIn("/work/dune-project", run)

    def test_facts_from_checks_a_finding_in_a_view_of_its_unit(self):
        """The finding's record and its project's unpatched.yaml come from the facts --facts-to wrote from the whole
        tree.  In a view of the unit, where a plain run fails (no release.yaml), the finding is checked as a plain run
        on the whole tree checks it."""
        with tree() as t:
            self.ready(t)
            d = os.path.join(self.d.name, "facts")
            plain = self.check(t)
            self.assertEqual(self.check(t, facts_to=d)[0], 0)
            view = unit_view(t, "zlib/checksum_fuzzer", os.path.join(self.d.name, "view"))
            self.assertEqual(run(check.run, view, ["zlib/checksum_fuzzer"], parts="findings")[0], 1)
            rc, out = run(check.run, view, ["zlib/checksum_fuzzer"], parts="findings", facts_from=d)
            self.assertEqual((rc, same_run(out)), (plain[0], same_run(plain[1])))
            self.assertEqual(rc, 0, out)
            self.assertIn(FINDING + ": 6 runs match the record; the input shows asan_agrees and asan_ubsan_agrees "
                          "false\n", out)

    def test_record_goes_with_neither_facts_to_nor_facts_from(self):
        """--record loads a tree whose findings may have no runs yet, so that it can record them: --facts-to writes the
        facts of a tree the rules pass, and --facts-from loads no tree."""
        with tree() as t:
            self.ready(t)
            d = os.path.join(self.d.name, "facts")
            rc, out = self.check(t, record=True, facts_to=d)
            self.assertEqual(rc, 1, out)
            self.assertTrue(out.startswith("FAIL --record"), out)
            self.assertFalse(os.path.exists(d), "no facts are written")
            self.assertEqual(self.check(t, facts_to=d)[0], 0)
            rc, out = self.check(t, record=True, facts_from=d)
            self.assertEqual(rc, 1, out)
            self.assertTrue(out.startswith("FAIL --record"), out)
            self.assertNotIn("runs match", out)


if __name__ == "__main__":
    unittest.main()
