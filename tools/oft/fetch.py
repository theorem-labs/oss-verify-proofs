"""oft fetch and oft verify-sha: release assets, pinned by SHA-256.

A project's binaries are one release asset, <project>-bin.tar.zst, whose
SHA-256 project.yaml records; every ELF inside it is pinned again, by its own
SHA-256, in its harness.yaml.  `fetch` checks both: the archive before it is
unpacked, and each file before it is moved into projects/<p>/bin/<harness>/.
The archive may also hold the licence files of the copyleft components compiled
into the binaries, as LICENSES/<component>/<file>; they go to
projects/<p>/bin/LICENSES/.  Any other member is refused, so an archive can
never write anywhere else.  `fetch --findings` does the same for the unpatched
binaries a project's findings run on, which findings/<p>/unpatched.yaml pins,
into findings/<p>/bin/<harness>/ (and their licence files into
findings/<p>/bin/LICENSES/).
"""
import hashlib
import os
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
import urllib.request

from . import facts

RELEASES = "https://github.com/theorem-labs/oss-verify-proofs/releases/download"


class FetchError(RuntimeError):
    pass


def _project(tree, name):
    proj = tree.projects.get(name)
    if proj is None:
        raise FetchError("no project %r" % name)
    if proj.data["status"] != "available" or "assets" not in proj.data:
        raise FetchError("%s has no binaries in this release (status: %s)" % (name, proj.data["status"]))
    return proj


def _download(url_or_path, dest, want_bytes, want_sha, pins):
    h = hashlib.sha256()
    n = 0
    if "://" in url_or_path:
        src = urllib.request.urlopen(url_or_path, timeout=120)
    else:
        src = open(url_or_path, "rb")
    with src, open(dest, "wb") as out:
        for chunk in iter(lambda: src.read(1 << 20), b""):
            h.update(chunk)
            n += len(chunk)
            out.write(chunk)
    if n != want_bytes or h.hexdigest() != want_sha:
        raise FetchError("%s: got %d bytes with SHA-256 %s; %s pins %d bytes, %s"
                         % (url_or_path, n, h.hexdigest(), pins, want_bytes, want_sha))


def _expected(proj):
    """{member name: its pin (file, bytes, sha256)} for every published build."""
    return {"%s/%s" % (h.name, rec["file"]): rec for h in proj.harnesses.values() for _b, rec in h.builds()}


_LICENCE_PART = re.compile(r"[A-Za-z0-9][A-Za-z0-9._+-]*")


def _licence_member(name):
    """The path parts of a LICENSES/ member: () for LICENSES/ itself, (component,) or (component, file); None for any
    other name."""
    parts = name.rstrip("/").split("/")
    if parts[0] != "LICENSES" or len(parts) > 3 or not all(_LICENCE_PART.fullmatch(p) for p in parts[1:]):
        return None
    return tuple(parts[1:])


def _unpack(archive, want, bindir, pins):
    """Unpack the archive's binaries, each of which must be one of want ({member name: its pin}) with the bytes and
    SHA-256 it pins, into bindir/<harness>/, and its licence files into bindir/LICENSES/; pins names the file that
    pins the binaries.  The members are staged in a .fetch-* directory of bindir, which is removed whether or not the
    archive unpacks.  Returns the number of each."""
    if shutil.which("zstd") is None:
        raise FetchError("zstd is needed to unpack %s" % archive)
    stage = tempfile.mkdtemp(prefix=".fetch-", dir=bindir)
    try:
        got, licences = _stage(archive, want, stage, pins)
        missing = sorted(set(want) - set(got))
        if missing:
            raise FetchError("%s lacks %s" % (archive, ", ".join(missing)))
        for name in sorted(got):
            dest = os.path.join(bindir, name)
            os.makedirs(os.path.dirname(dest), exist_ok=True)
            os.replace(got[name], dest)
            os.chmod(dest, 0o755)
        # the licence files are those of this archive only: an earlier archive's go
        shutil.rmtree(os.path.join(bindir, "LICENSES"), ignore_errors=True)
        for comp, f in sorted(licences):
            dest = os.path.join(bindir, "LICENSES", comp, f)
            os.makedirs(os.path.dirname(dest), exist_ok=True)
            os.replace(licences[comp, f], dest)
            os.chmod(dest, 0o644)
    finally:
        shutil.rmtree(stage)
    return len(got), len(licences)


def _stage(archive, want, stage, pins):
    """({binary member name: its staged file}, {(component, file): its staged file}): each member of the archive is
    written into stage under its index in the archive, so no two share a file."""
    got, licences = {}, {}
    unreadable = None   # tarfile's error, reported unless zstd failed first
    dec = subprocess.Popen(["zstd", "-dc", "--", archive], stdout=subprocess.PIPE)
    try:
        try:
            with tarfile.open(fileobj=dec.stdout, mode="r|") as tf:
                for i, m in enumerate(tf):
                    name = m.name[2:] if m.name.startswith("./") else m.name
                    if m.isdir() and name.rstrip("/") in {k.split("/")[0] for k in want} | {""}:
                        continue
                    lic = _licence_member(name)
                    if lic is not None and m.isdir() and len(lic) < 2:
                        continue
                    out = os.path.join(stage, str(i))
                    if lic is not None and m.isfile() and len(lic) == 2 and lic not in licences:
                        with tf.extractfile(m) as src, open(out, "wb") as dst:
                            shutil.copyfileobj(src, dst)
                        licences[lic] = out
                        continue
                    if not m.isfile() or name not in want:
                        raise FetchError("%s: unexpected member %r" % (archive, m.name))
                    rec = want[name]
                    digest = hashlib.sha256()
                    with tf.extractfile(m) as src, open(out, "wb") as dst:
                        for chunk in iter(lambda: src.read(1 << 20), b""):
                            digest.update(chunk)
                            dst.write(chunk)
                    if digest.hexdigest() != rec["sha256"] or m.size != rec["bytes"]:
                        raise FetchError("%s: %s does not match its %s SHA-256" % (archive, name, pins))
                    got[name] = out
        except tarfile.TarError as e:
            unreadable = e
        # tarfile stops at the end-of-archive blocks, or at a block it cannot read, while zstd is still writing.  Read
        # the rest, or closing the pipe can kill zstd with SIGPIPE and a complete archive reads as a failed one.
        while dec.stdout.read(1 << 20):
            pass
    finally:
        dec.stdout.close()
        rc = dec.wait()
    if rc != 0:
        raise FetchError("zstd failed on %s" % archive)
    if unreadable is not None:
        raise FetchError("%s: not a readable tar archive: %s" % (archive, unreadable))
    return got, licences


def _where(source, asset):
    if source and "://" not in source:
        return os.path.join(source, asset["file"])
    return "%s/%s" % ((source or RELEASES + "/" + asset["release"]).rstrip("/"), asset["file"])


def _assets(tree, name, findings, every_kind):
    """(asset, bindir, members, pins) of each archive `oft fetch` takes for a project: its published binaries, or
    with every_kind every asset it attaches, or with findings the unpatched binaries its findings run on.  members:
    {member name: its pin}; pins: the files that pin the archive and its members."""
    if findings:
        u = tree.unpatched.get(name)
        if u is None:
            raise FetchError("no findings/%s/unpatched.yaml" % name)
        members = {"%s/%s" % (h, rec["file"]): rec for h, builds in u["harnesses"].items() for rec in builds.values()}
        return [(u["asset"], os.path.join("findings", name, "bin"), members,
                 ("unpatched.yaml", "unpatched.yaml"))]
    proj = _project(tree, name)
    assets = proj.data["assets"]
    return [(assets[k], os.path.join(proj.dir, "bin"), _expected(proj), ("project.yaml", "harness.yaml"))
            for k in (["bin", "src", "src_manifest", "port"] if every_kind else ["bin"]) if k in assets]


def fetch(root, projects, source=None, all_projects=False, only_check_assets=False, release=None, listing=False,
          findings=False, out=sys.stdout):
    """Fetch the named projects' binaries.  all_projects: every available
    project (with findings, every project with unpatched binaries); release:
    only those whose binaries are attached to that release tag;
    only_check_assets: download and check every asset (binaries and source,
    including a port archive), unpack nothing; listing: print
    `<release> <file> <sha256>` for each asset and download nothing (for CI,
    which downloads with gh); findings: the unpatched binaries each project's
    findings run on (findings/<p>/unpatched.yaml), instead of its published
    ones."""
    tree = facts.load(root)
    if all_projects or release:
        # an available project that withholds every build attaches nothing; one that publishes a build and
        # has no assets is still listed, and _project refuses it
        projects = (sorted(tree.unpatched) if findings else
                    sorted(p.name for p in tree.available()
                           if "assets" in p.data or any(h.builds() for h in p.harnesses.values())))
    bad = n_assets = 0
    recipes = {}  # (release, file) -> the recipe a fetched project's binary archive pins (assets.bin.recipe)
    for name in projects:
        try:
            for asset, bindir, members, pins in _assets(tree, name, findings, only_check_assets or listing):
                if release and asset["release"] != release:
                    continue
                n_assets += 1
                if listing:
                    print("%s %s %s" % (asset["release"], asset["file"], asset["sha256"]), file=out)
                    continue
                bindir = tree.path(bindir)
                os.makedirs(bindir, exist_ok=True)
                fd, tmp = tempfile.mkstemp(prefix=".asset-", suffix=".tar.zst", dir=bindir)
                os.close(fd)
                try:
                    _download(_where(source, asset), tmp, asset["bytes"], asset["sha256"], pins[0])
                    n = None if only_check_assets else _unpack(tmp, members, bindir, pins[1])
                finally:
                    os.unlink(tmp)
                if n is None:
                    what = "SHA-256 matches"
                else:
                    what = "%d binaries, each SHA-256 checked" % n[0] + ("; %d licence files" % n[1] if n[1] else "")
                print("%s: %s (%s), %s" % (name, asset["file"], asset["sha256"][:12], what), file=out)
            # the recipe the binaries were built with, in its own release, which may hold no other asset of the project;
            # the unpatched binaries come with none
            rc = None if findings else facts.bin_recipe(tree, tree.projects[name])
            if (only_check_assets or listing) and rc and not (release and rc["release"] != release):
                # the file that pins it: the archive's own project.yaml, or release.yaml's one recipe in the older shape
                named = "recipe" in ((tree.projects[name].data.get("assets") or {}).get("bin") or {})
                recipes.setdefault((rc["release"], rc["file"]),
                                   (rc, "projects/%s/project.yaml" % name if named else "release.yaml"))
        except (FetchError, OSError) as e:
            print("%s: %s" % (name, e), file=out)
            bad += 1
    # each build recipe once, beside the binaries it built and the source assets it completes
    for recipe, pinned_by in (recipes[k] for k in sorted(recipes)):
        n_assets += 1
        if listing:
            print("%s %s %s" % (recipe["release"], recipe["file"], recipe["sha256"]), file=out)
            continue
        fd, tmp = tempfile.mkstemp(prefix=".asset-", suffix=".tar.zst", dir=root)
        os.close(fd)
        try:
            _download(_where(source, recipe), tmp, recipe["bytes"], recipe["sha256"], pinned_by)
            print("%s: %s (%s), SHA-256 matches" % (recipe["release"], recipe["file"], recipe["sha256"][:12]), file=out)
        except (FetchError, OSError) as e:
            print("%s: %s" % (recipe["release"], e), file=out)
            bad += 1
        finally:
            os.unlink(tmp)
    if not n_assets and not bad:
        print("oft fetch: no asset to fetch (name a project, or --all, or a --release with assets)", file=out)
        return 1
    return 1 if bad else 0


def verify_sha(root, projects, harness=None, out=sys.stdout):
    """Every published build of every included harness (or of `harness`
    only) is present, and has the size and SHA-256 its harness.yaml records."""
    tree = facts.load(root)
    bad = n = 0
    for name in projects:
        try:
            proj = _project(tree, name)
        except FetchError as e:
            print(e, file=out)
            bad += 1
            continue
        for h in proj.harnesses.values():
            if harness is not None and h.name != harness:
                continue
            for b, rec in h.builds():
                n += 1
                p = tree.path(h.elf_path(b))
                if not os.path.isfile(p):
                    print("%s: missing (run ./oft fetch %s)" % (h.elf_path(b), name), file=out)
                    bad += 1
                elif os.path.getsize(p) != rec["bytes"] or facts.sha256_file(p) != rec["sha256"]:
                    print("%s: does not match its SHA-256 in harness.yaml" % h.elf_path(b), file=out)
                    bad += 1
    if not n:
        print("oft verify-sha: no binaries to check", file=out)
        return 1
    print("oft verify-sha: %d binaries, %d problem(s)" % (n, bad), file=out)
    return 1 if bad else 0


def add_arguments(f):
    """oft fetch's arguments, for `oft fetch` and for `python3 -m oft.fetch`."""
    f.add_argument("projects", nargs="*")
    f.add_argument("--all", action="store_true", help="every available project")
    f.add_argument("--source", help="a directory or URL prefix to take the release assets from")
    f.add_argument("--assets-only", action="store_true",
                   help="check every archive's SHA-256 (binaries and source) without unpacking")
    f.add_argument("--release", help="only the projects whose assets are attached to this release tag")
    f.add_argument("--list", action="store_true", help="print <release> <file> <sha256> per asset; fetch nothing")
    f.add_argument("--findings", action="store_true",
                   help="the unpatched binaries the projects' findings run on (findings/<p>/unpatched.yaml), into "
                        "findings/<p>/bin/")


def cli(root, a):
    return fetch(root, a.projects, source=a.source, all_projects=a.all, only_check_assets=a.assets_only,
                 release=a.release, listing=a.list, findings=a.findings)


if __name__ == "__main__":
    # `python3 -m oft.fetch`, as tools/oft/ci/check-units.sh runs it: the fetch without the modules of the other
    # commands, which are not part of the checker (keys.NOT_THE_CHECKER)
    import argparse
    p = argparse.ArgumentParser(prog="python3 -m oft.fetch", description="oft fetch")
    p.add_argument("--root", default=".", help="the repository root (default: .)")
    add_arguments(p)
    a = p.parse_args()
    sys.exit(cli(os.path.abspath(a.root), a))
