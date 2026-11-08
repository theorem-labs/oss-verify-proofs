"""oft fetch and oft verify-sha: release assets, pinned by SHA-256.

A project's binaries are one release asset, <project>-bin.tar.zst, whose
SHA-256 project.yaml records; every ELF inside it is pinned again, by its own
SHA-256, in its harness.yaml.  `fetch` checks both: the archive before it is
unpacked, and each file before it is moved into projects/<p>/bin/<harness>/.
The archive may also hold the licence files of the copyleft components compiled
into the binaries, as LICENSES/<component>/<file>; they go to
projects/<p>/bin/LICENSES/.  A release archive is built from the whole project,
so it also carries the binaries of the project's other harnesses when the tree
has a home for only some of them (a tree that vendors a subset of a project,
or a sparse checkout): a member of a harness that projects/<p>/project.yaml
lists and this tree holds no build record of is skipped, never extracted, and
counted in the line fetch prints (_other_harnesses).  Any other member is
refused, so an archive can never write anywhere else.  A harness whose builds
this tree records and withholds ships no binary, so its members are refused
too.  `fetch --findings` does the same for the unpatched
binaries a project's findings run on, which its unpatched.yaml pins
(findings/<p>/unpatched.yaml or projects/<p>/unpatched.yaml, by layout.py),
into projects/<p>/unpatched-bin/<harness>/ (and their licence files into
projects/<p>/unpatched-bin/LICENSES/), whichever layout the findings are in.
"""
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
import urllib.error
import urllib.parse
import urllib.request

from . import facts, layout

RELEASES = "https://github.com/theorem-labs/oss-verify-proofs/releases/download"
# A release that is not public (a draft, or a release of another repository) has no download URL.  With
# OFT_RELEASES_REPO set to <owner>/<repo> and a GitHub token in GH_TOKEN or GITHUB_TOKEN, fetch takes each asset from
# that repository's release of the same tag through the GitHub API instead, a draft included (reading a draft needs a
# token with push access).  The size and SHA-256 checks are the same.  OFT_GITHUB_API names another API host.
RELEASES_REPO = "OFT_RELEASES_REPO"


class FetchError(RuntimeError):
    pass


def _project(tree, name):
    proj = tree.projects.get(name)
    if proj is None:
        raise FetchError("no project %r" % name)
    if proj.data["status"] != "available" or "assets" not in proj.data:
        raise FetchError("%s has no binaries in this release (status: %s)" % (name, proj.data["status"]))
    return proj


def _api_base():
    return os.environ.get("OFT_GITHUB_API", "https://api.github.com").rstrip("/")


def _token():
    t = os.environ.get("GH_TOKEN") or os.environ.get("GITHUB_TOKEN")
    if not t:
        raise FetchError("%s is set, and neither GH_TOKEN nor GITHUB_TOKEN is" % RELEASES_REPO)
    return t


class _TokenStaysHome(urllib.request.HTTPRedirectHandler):
    """GitHub answers an asset's API URL with a redirect to its storage host, which must not receive the token (and
    refuses a request that carries a second credential), so the Authorization header is dropped on a redirect to
    another host or scheme (an https to http redirect would send it in clear).  urllib's own handler sends it on."""

    def redirect_request(self, req, fp, code, msg, headers, newurl):
        new = super().redirect_request(req, fp, code, msg, headers, newurl)
        if new is not None and urllib.parse.urlsplit(newurl)[:2] != urllib.parse.urlsplit(req.full_url)[:2]:
            new.remove_header("Authorization")
        return new


def _api_open(url, accept):
    req = urllib.request.Request(url, headers={"Accept": accept, "Authorization": "Bearer " + _token(),
                                               "X-GitHub-Api-Version": "2022-11-28"})
    return urllib.request.build_opener(_TokenStaysHome).open(req, timeout=120)


class _ApiUrl(str):
    """An asset's GitHub API URL (_api_asset), which _download opens with the token."""


class _PublicUrl(str):
    """An asset's public release URL (RELEASES), the default path, whose 404 _download explains."""


_listed = {}  # (API host, repository) -> its releases, drafts included: one listing serves a whole run


def _api_asset(repo, asset):
    """The API URL of asset["file"] in repo's release asset["release"], a draft included."""
    key = (_api_base(), repo)
    if key not in _listed:
        rels, page = [], 1
        while True:
            url = "%s/repos/%s/releases?per_page=100&page=%d" % (key[0], repo, page)
            with _api_open(url, "application/vnd.github+json") as r:
                try:
                    batch = json.load(r)
                except ValueError as e:
                    raise FetchError("%s: the answer is not JSON: %s" % (url, e)) from e
            if not isinstance(batch, list):
                raise FetchError("%s: the answer is not a list of releases" % url)
            rels += batch
            if len(batch) < 100:
                break
            page += 1
        _listed[key] = rels
    tagged = [r for r in _listed[key] if r.get("tag_name") == asset["release"]]
    if not tagged:
        raise FetchError("%s has no release %s that this token can read (reading a draft needs push access)"
                         % (repo, asset["release"]))
    found = [a for r in tagged for a in r.get("assets") or () if a.get("name") == asset["file"]]
    if not found:
        raise FetchError("%s's release %s has no asset %s" % (repo, asset["release"], asset["file"]))
    # two drafts may carry one tag name: the copy whose digest GitHub records as the pinned SHA-256 first; with no
    # digest recorded the listing's order stands, and a wrong copy fails _download's SHA-256 check
    found.sort(key=lambda a: a.get("digest") != "sha256:" + asset["sha256"])
    return _ApiUrl(found[0]["url"])


def _download(url_or_path, dest, want_bytes, want_sha, pins):
    h = hashlib.sha256()
    n = 0
    try:
        if isinstance(url_or_path, _ApiUrl):
            src = _api_open(url_or_path, "application/octet-stream")
        elif "://" in url_or_path:
            src = urllib.request.urlopen(url_or_path, timeout=120)
        else:
            src = open(url_or_path, "rb")
    except urllib.error.HTTPError as e:
        if e.code == 404 and isinstance(url_or_path, _PublicUrl):
            raise FetchError("%s: HTTP 404, no public release holds it.  A draft, or a release of another repository, "
                             "has no download URL: set %s=<owner>/<repo> and GH_TOKEN to read it through the GitHub "
                             "API, or pass --source DIR" % (url_or_path, RELEASES_REPO)) from e
        raise
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


def _other_harnesses(proj, want):
    """The names of the project's harnesses whose members the archive may carry and no pin names: every name its
    project.yaml lists and every harness folder this tree holds, less the harnesses `want` pins a build of and the
    harnesses this tree holds a build record of.  A harness whose every build is withheld ships no binary, so a
    member of it is a member the archive should not carry at all, and _stage refuses it as before; the harnesses
    this tree knows nothing of are the ones a partial tree leaves no home for, and _stage skips those members."""
    if proj is None:
        return set()
    named = {e["name"] for e in proj.entries() if isinstance(e.get("name"), str)}
    recorded = {h.name for h in proj.harnesses.values() if h.builds(published_only=False)}
    return (named | set(proj.harnesses)) - recorded - {k.split("/")[0] for k in want}


_LICENCE_PART = re.compile(r"[A-Za-z0-9][A-Za-z0-9._+-]*")


def _licence_member(name):
    """The path parts of a LICENSES/ member: () for LICENSES/ itself, (component,) or (component, file); None for any
    other name."""
    parts = name.rstrip("/").split("/")
    if parts[0] != "LICENSES" or len(parts) > 3 or not all(_LICENCE_PART.fullmatch(p) for p in parts[1:]):
        return None
    return tuple(parts[1:])


def _unpack(archive, want, bindir, pins, others):
    """Unpack the archive's binaries, each of which must be one of want ({member name: its pin}) with the bytes and
    SHA-256 it pins, into bindir/<harness>/, and its licence files into bindir/LICENSES/; pins names the file that
    pins the binaries.  A member of one of the harnesses `others` names is skipped, never extracted.  The members
    are staged in a .fetch-* directory of bindir, which is removed whether or not the archive unpacks.  Returns the
    number of binaries, the number of licence files, and {skipped harness: how many of its files were skipped}."""
    if shutil.which("zstd") is None:
        raise FetchError("zstd is needed to unpack %s" % archive)
    stage = tempfile.mkdtemp(prefix=".fetch-", dir=bindir)
    try:
        got, licences, skipped = _stage(archive, want, stage, pins, others)
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
    return len(got), len(licences), skipped


def _stage(archive, want, stage, pins, others):
    """({binary member name: its staged file}, {(component, file): its staged file}, {skipped harness: how many of
    its files were skipped}): each member of the archive that is kept is written into stage under its index in the
    archive, so no two share a file."""
    got, licences, skipped = {}, {}, {}
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
                    parts = name.rstrip("/").split("/")
                    if parts[0] in others and len(parts) <= 2 and (m.isfile() if len(parts) == 2 else m.isdir()):
                        # a harness of this project that the tree pins no build of: its bytes are never read, and
                        # nothing of it is written, so the archive still writes only where a pin names
                        if len(parts) == 2:
                            skipped[parts[0]] = skipped.get(parts[0], 0) + 1
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
    return got, licences, skipped


def _where(source, asset):
    if source and "://" not in source:
        return os.path.join(source, asset["file"])
    if source:
        return "%s/%s" % (source.rstrip("/"), asset["file"])
    if os.environ.get(RELEASES_REPO):
        return _api_asset(os.environ[RELEASES_REPO], asset)
    return _PublicUrl("%s/%s" % ((RELEASES + "/" + asset["release"]).rstrip("/"), asset["file"]))


def _assets(tree, name, findings, every_kind):
    """(asset, bindir, members, pins, others) of each archive `oft fetch` takes for a project: its published
    binaries, or with every_kind every asset it attaches, or with findings the unpatched binaries its findings run
    on.  members: {member name: its pin}; pins: the files that pin the archive and its members; others: the
    project's harnesses that members pins no build of, whose members the archive carries too (_other_harnesses)."""
    if findings:
        u = tree.unpatched.get(name)
        if u is None:
            # the unpatched.yaml the loader found and could not read, or where the tree's layout keeps one
            raise FetchError("no %s" % tree.unpatched_paths.get(name, layout.unpatched_path(name, tree.layout)))
        members = {"%s/%s" % (h, rec["file"]): rec for h, builds in u["harnesses"].items() for rec in builds.values()}
        return [(u["asset"], layout.unpatched_bin_dir(name), members, ("unpatched.yaml", "unpatched.yaml"),
                 _other_harnesses(tree.projects.get(name), members))]
    proj = _project(tree, name)
    assets = proj.data["assets"]
    members = _expected(proj)
    others = _other_harnesses(proj, members)
    return [(assets[k], os.path.join(proj.dir, "bin"), members, ("project.yaml", "harness.yaml"), others)
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
    findings run on (its unpatched.yaml, tree.unpatched_paths), instead of its
    published ones, into projects/<p>/unpatched-bin/."""
    tree = facts.load(root)
    if all_projects or release:
        # an available project that withholds every build attaches nothing; one that publishes a build and
        # has no assets is still listed, and _project refuses it
        projects = (sorted(tree.unpatched) if findings else
                    sorted(p.name for p in tree.available()
                           if "assets" in p.data or any(h.builds() for h in p.harnesses.values())))
    bad = n_assets = 0
    recipes = {}  # (release, file) -> [(recipe, the file that pins it)] of each fetched project's binary archive
    for name in projects:
        try:
            for asset, bindir, members, pins, others in _assets(tree, name, findings, only_check_assets or listing):
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
                    n = None if only_check_assets else _unpack(tmp, members, bindir, pins[1], others)
                finally:
                    os.unlink(tmp)
                if n is None:
                    what = "SHA-256 matches"
                else:
                    skipped = sum(n[2].values())
                    what = "%d binaries, each SHA-256 checked" % n[0] + ("; %d licence files" % n[1] if n[1] else "") \
                        + ("; %d file%s of %s skipped, which this tree has no home for"
                           % (skipped, "" if skipped == 1 else "s", ", ".join(sorted(n[2]))) if n[2] else "")
                print("%s: %s (%s), %s" % (name, asset["file"], asset["sha256"][:12], what), file=out)
            # the recipe the binaries were built with, in its own release, which may hold no other asset of the project;
            # the unpatched binaries come with none
            rc = None if findings else facts.bin_recipe(tree, tree.projects[name])
            if (only_check_assets or listing) and rc and not (release and rc["release"] != release):
                # the file that pins it: the archive's own project.yaml, or release.yaml's one recipe in the older shape
                named = "recipe" in ((tree.projects[name].data.get("assets") or {}).get("bin") or {})
                recipes.setdefault((rc["release"], rc["file"]), []).append(
                    (rc, "projects/%s/project.yaml" % name if named else "release.yaml"))
        except (FetchError, OSError) as e:
            print("%s: %s" % (name, e), file=out)
            bad += 1
    # each build recipe once, beside the binaries it built and the source assets it completes. Two pins of one file
    # of one release that differ (a private project's own recipe, say, beside another's: oft lint refuses such facts,
    # and fetch, which may run on a tree lint has not passed, refuses them too) name no recipe to check: neither is
    # listed or fetched, and each file that pins one is named
    for key in sorted(recipes):
        pins = recipes[key]
        if any(r != pins[0][0] for r, _ in pins):
            print("%s: %s is pinned differently: %s" % (key[0], key[1], "; ".join(
                "%s pins %d bytes, %s" % (by, r["bytes"], r["sha256"]) for r, by in pins)), file=out)
            bad += 1
            continue
        recipe, pinned_by = pins[0][0], ", ".join(sorted({by for _, by in pins}))
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


def verify_builds(root, h, out=sys.stdout):
    """(builds checked, problems) of harness h: each published build is present under root, with the size and SHA-256
    its harness.yaml records.  Prints a line for each problem."""
    n = bad = 0
    for b, rec in h.builds():
        n += 1
        rel = h.elf_path(b)
        p = os.path.join(root, rel)
        if not os.path.isfile(p):
            print("%s: missing (run ./oft fetch %s)" % (rel, h.project.name), file=out)
            bad += 1
        elif os.path.getsize(p) != rec["bytes"] or facts.sha256_file(p) != rec["sha256"]:
            print("%s: does not match its SHA-256 in harness.yaml" % rel, file=out)
            bad += 1
    return n, bad


def verify_sha(root, projects, out=sys.stdout):
    """Every published build of every included harness of the projects is present, and has the size and SHA-256 its
    harness.yaml records (verify_builds)."""
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
            built, problems = verify_builds(tree.root, h, out)
            n += built
            bad += problems
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
                   help="the unpatched binaries the projects' findings run on (projects/<p>/unpatched.yaml, or "
                        "findings/<p>/unpatched.yaml in the old layout), into projects/<p>/unpatched-bin/")


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
