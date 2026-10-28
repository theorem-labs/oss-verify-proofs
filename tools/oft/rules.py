"""The rules that relate one fact to another (part of lint rules `schema` and
`withheld`).  Each function appends to tree.errors."""
import hashlib
import os
import re
from fractions import Fraction

from . import facts, names, schema, shapes

PB = facts.PHRASEBOOK
PLACEHOLDER = re.compile(r"\{([a-z_0-9]+)\}")
# the (status, reason) sentences that say what OSS-Fuzz has for the project, so a project OSS-Fuzz does not have (no
# oss_fuzz) cannot take them
OSS_FUZZ_REASONS = {("no-harness", "none-at-commit"), ("excluded", "stub-harness")}
# the harness reasons that say a fuzz target was not built, which an oss-verify entry (a fuzz target OSS Verify builds)
# cannot take
UNBUILT_REASONS = {"not-attempted", "build-system", "harness-framework", "dependency"}


def check(tree):
    _release(tree)
    _records(tree)
    idents = {}
    for proj in tree.projects.values():
        _project(tree, proj)
        idents.setdefault(names.ident(proj.name), []).append(proj.name)
    for ident, ps in idents.items():
        if len(ps) > 1:
            tree.err("projects", "names %s all map to the Rocq identifier %s" % (ps, ident))
    for h in tree.harnesses():
        _harness(tree, h)
    for sid, pd in tree.proofs.items():
        _proof(tree, sid, pd)
    for sid, cx in tree.counterexamples.items():
        _counterexample(tree, sid, cx)
    _approvals(tree)
    _written_here(tree)
    patches = {}
    for f in sorted(tree.findings.values(), key=lambda f: f.path):
        _finding(tree, f, patches)
    _series(tree)
    _held(tree)
    return tree.errors


def _approvals(tree):
    """approvals.yaml: each entry names an included fuzz target, at most once per source (origin and record), of a
    project no finding holds back and not private (release: private), and statements of it, none of them refuted or
    held back by an open finding of an enrolled project (facts.hold), and each in one entry of its fuzz target only,
    once; a submission names the record of its review, and only a submission does."""
    if not tree.approvals:
        return
    harnesses = {"%s/%s" % (h.project.name, h.name): h for h in tree.harnesses()}
    held = facts.hold(tree)
    held_ids = held.ids
    seen, where_listed = {}, {}
    for i, e in enumerate(tree.approvals["fuzz_targets"]):
        where = "approvals.yaml: approvals.fuzz_targets[%d]" % i
        unit = e["fuzz_target"]
        p = unit.partition("/")[0]
        if unit not in harnesses:
            tree.err(where, "%s is not an included fuzz target" % unit)
        else:
            for s in sorted(set(e["statements"]) - set(harnesses[unit].statements)):
                tree.err(where, "%s is not a statement of %s" % (s, unit))
        if p in held.held:
            tree.err(where, "%s: a finding holds back project %s, so none of its proofs is published" % (unit, p))
        if p in held.private:
            tree.err(where, "%s: project %s is private (release: private in its project.yaml), so no public release "
                            "carries it" % (unit, p))
        for s in sorted(set(e["statements"])):
            if "%s/%s" % (unit, s) in held_ids:
                tree.err(where, "%s/%s is held back by an open finding, so no release lists it" % (unit, s))
            pd = tree.proofs.get("%s/%s" % (unit, s))
            if pd is not None and pd.refutes:
                tree.err(where, "%s/%s: its proof is a refutation, which is never listed" % (unit, s))
        for s in sorted({s for s in e["statements"] if e["statements"].count(s) > 1}):
            tree.err(where, "%s/%s is listed twice" % (unit, s))
        source = (unit, e["origin"], e.get("record"))
        if source in seen:
            tree.err(where, "%s is listed twice for one source (%s%s): approvals.fuzz_targets[%d] and [%d]"
                     % (unit, e["origin"], ", record " + e["record"] if "record" in e else "", seen[source], i))
        seen.setdefault(source, i)
        for s in sorted(set(e["statements"])):
            first = where_listed.setdefault((unit, s), i)
            if first != i:
                tree.err(where, "%s/%s is listed twice: approvals.fuzz_targets[%d] and [%d]" % (unit, s, first, i))
        if (e["origin"] == "submission") != ("record" in e):
            tree.err(where, "%s: a submission names the record of its review, and only a submission does" % unit)


PACKAGE_ORIGIN = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._-]* \(sha256 [0-9a-f]{64}\)")


def _written_here(tree):
    """The build record of a fuzz target whose proofs came from a package (proofs.origin names it and its sha256)
    lists in proofs.written_here the statements whose proofs were written in this repository, and only such a record
    has written_here.  approvals.yaml agrees with it: a this-repository entry lists only statements written here, and
    a submission entry lists none of them, so provenance/, which ships whole, never credits the package with a proof
    this repository wrote, nor this repository with a proof of the package."""
    for (p, h), rec in sorted(tree.record_proofs.items()):
        unit, where = "%s/%s" % (p, h), "proofs/%s/%s/provenance/PROVENANCE.yaml" % (p, h)
        here, from_package = rec["written_here"], bool(PACKAGE_ORIGIN.match(rec["origin"] or ""))
        if here is not None and not (isinstance(here, list) and all(isinstance(s, str) for s in here)):
            tree.err(where, "proofs.written_here must be a list of statement names")
            here = None
        elif here is not None and not from_package:
            tree.err(where, "proofs.written_here: proofs.origin names no package, so every proof of %s was written "
                     "here and none is singled out" % unit)
            here = None
        elif here is not None:
            har = tree.projects.get(p).harnesses.get(h) if tree.projects.get(p) else None
            for s in sorted(set(here) - set(har.statements if har else ())):
                tree.err(where, "proofs.written_here: %s is not a statement of %s" % (s, unit))
            for s in sorted({s for s in here if here.count(s) > 1}):
                tree.err(where, "proofs.written_here: %s is listed twice" % s)
        if not from_package:
            continue
        written = set(here or ())
        for i, e in enumerate(tree.approvals["fuzz_targets"] if tree.approvals else []):
            if e["fuzz_target"] != unit:
                continue
            aw = "approvals.yaml: approvals.fuzz_targets[%d]" % i
            mine = e["origin"] == "this-repository"
            for s in sorted(set(e["statements"]) - written if mine else set(e["statements"]) & written):
                tree.err(aw, "%s/%s: the build record says the proofs of this fuzz target came from a package and "
                         "proofs.written_here %s it, so a %s entry may not list it"
                         % (unit, s, "does not name" if mine else "names", e["origin"]))


def counts(tree):
    """release.yaml's counts, as the tree gives them: the cut's tree gives the release's (release_tree._public_release)."""
    harnesses = list(tree.harnesses())
    return {
        "projects": len(tree.projects),
        "available": len(tree.available()),
        "harnesses": len(harnesses),
        "binaries": sum(len(h.builds()) for h in harnesses),
    }


def _release(tree):
    r = tree.release
    if not r:
        return
    # counts describe the tree this file is in, so the rendered pages and the index agree with them; oft release-tree
    # writes the release's own counts into the cut (release_tree._public_release), which this rule then checks
    harnesses = list(tree.harnesses())
    for k, v in counts(tree).items():
        if r["counts"][k] != v:
            tree.err("release.yaml", "counts.%s is %d but the tree has %d" % (k, r["counts"][k], v))
    n_oss_fuzz = tree.oss_fuzz_project_count()
    if r["oss_fuzz"]["projects"] != n_oss_fuzz:
        tree.err("release.yaml", "oss_fuzz.projects is %d but projects/ has %d OSS-Fuzz projects (a project.yaml with "
                 "oss_fuzz)" % (r["oss_fuzz"]["projects"], n_oss_fuzz))
    builders = (r.get("images") or {}).get("builder") or []
    for proj in tree.projects.values():
        if "oss_fuzz" in proj.data and proj.data["oss_fuzz"]["commit"] != r["oss_fuzz"]["commit"]:
            tree.err(proj.dir, "oss_fuzz.commit differs from release.yaml's")
        # the image a project names as its builder is one the release pins
        b = (proj.data.get("build") or {}).get("builder")
        if b is not None and b not in builders:
            tree.err(os.path.join(proj.dir, "project.yaml"), "build.builder is not one of release.yaml's images.builder")

    # every library a build links from the build image has a release.yaml entry: its licence, whether it makes a
    # binary copyleft, and whether sources.sysroot holds its source; a copyleft binary that links one ships only once
    # that source is in it
    known = r.get("image_libraries") or {}
    linked = set()
    for h in harnesses:
        names_ = facts.image_libraries(h)
        linked.update(names_)
        where = os.path.join(h.dir, "harness.yaml")
        for n in names_:
            if n not in known:
                tree.err(where, "links %s from the build image, which release.yaml's image_libraries does not list" % n)
        if h.builds() and names_ and facts.copyleft(tree, h):
            if not r.get("sources"):
                tree.err("release.yaml", "%s/%s is copyleft and links libraries from the build image, so release.yaml "
                         "names sources (the toolchain and sysroot source archives)" % (h.project.name, h.name))
            missing = [n for n in names_ if n in known and not known[n]["in_sysroot_src"]]
            if missing:
                tree.err(where, "a copyleft binary links %s, whose source sources.sysroot does not hold: withhold its "
                         "builds (source-bundle) until it does" % ", ".join(missing))
    for n in sorted(set(known) - linked):
        tree.err("release.yaml", "image_libraries lists %s, which no build links" % n)
    # one shape at a time: recipes, or the shape before it, its one recipe
    if "recipe" in r and "recipes" in r:
        tree.err("release.yaml", "names both recipe and recipes: recipes lists every recipe, and replaces recipe")
    # a GitHub release carries at most one recipe; and each recipe has a file name of its own, since a download keeps
    # the assets of every release in one directory by file name
    for key, msg in (("release", "recipes lists more than one recipe in %s: a release carries at most one recipe"),
                     ("file", "recipes names the file %s more than once: each recipe has a file name of its own")):
        values = [x[key] for x in facts.release_recipes(tree)]
        for v in sorted({v for v in values if values.count(v) > 1}):
            tree.err("release.yaml", msg % v)


def _records(tree):
    """Every build record of a project cites (recipe.asset) the recipe its binary archive pins (assets.bin.recipe):
    the binaries of one archive were built with one recipe.  A port-built project's records cite none: the OSS Verify
    port built its binaries (facts.load lets them cite none)."""
    for (p, h), asset in sorted(tree.records.items()):
        proj = tree.projects.get(p)
        where = "proofs/%s/%s/provenance/PROVENANCE.yaml" % (p, h)
        if proj and facts.port(proj):
            tree.err(where, "recipe.asset, %s in %s: build.oss_verify says the OSS Verify port built projects/%s's "
                     "binaries, and no recipe did, so its build records cite none" % (asset["file"], asset["release"], p))
            continue
        pinned = facts.bin_recipe(tree, proj) if proj else None
        if pinned is None and proj and not tree.release:
            continue  # release.yaml did not load (its errors are reported), so an archive of its older shape has none
        if asset != pinned:
            b = ((proj.data.get("assets") or {}).get("bin") or {}) if proj else {}
            named = "release.yaml's recipe" if b and "recipe" not in b else "assets.bin.recipe"
            tree.err(where, "recipe.asset, %s in %s, is not the recipe of projects/%s's binary archive (%s: %s)"
                     % (asset["file"], asset["release"], p, named,
                        "%s in %s" % (pinned["file"], pinned["release"]) if pinned else "none"))


def _sentence_ok(tree, where, shape, args):
    missing = [k for k in PLACEHOLDER.findall(shape)
               if k not in args and k not in ("project", "commit8")]
    if missing:
        tree.err(where, "the phrasebook sentence needs reason_args %s" % ", ".join(missing))


def _project(tree, proj):
    d, where = proj.data, os.path.join(proj.dir, "project.yaml")
    if d["project"] != proj.name:
        tree.err(where, "project is %r but the directory is %r" % (d["project"], proj.name))
    if "oss_fuzz" in d and d["oss_fuzz"]["path"] != "projects/" + proj.name:
        tree.err(where, "oss_fuzz.path must be projects/%s" % proj.name)
    if facts.port(proj) and facts.port(proj)["path"] != "projects/" + proj.name:
        tree.err(where, "build.oss_verify.path must be projects/%s" % proj.name)
    # a Go project's binaries are built by the Go toolchain alone (no cgo, so no clang); every other language's C code
    # by clang
    build = d.get("build")
    if build is not None:
        if d["language"] == "go" and ("go" not in build or "clang" in build):
            tree.err(where, "a Go project names build.go, the Go toolchain, and no build.clang")
        if d["language"] != "go" and ("clang" not in build or "go" in build):
            tree.err(where, "build.clang names the clang that compiled the C code; only a Go project names build.go "
                            "instead")
        if (build["system"] == "go") != (d["language"] == "go"):
            tree.err(where, "build.system is go exactly for a Go project")
        # the release recipe published no Go binary, so the port built every one, in its Go toolchain image
        if d["language"] == "go" and "oss_verify" not in build:
            tree.err(where, "a Go project's binaries are built by the OSS Verify port: it names build.oss_verify")
        if (GO_BUILDER in build["builder"]) != (d["language"] == "go"):
            tree.err(where, "build.builder is the port's Go toolchain image (%s) exactly for a Go project"
                     % GO_BUILDER)
    for key in ((d.get("budgets") or {}).get("agrees") or {}):
        try:
            own = shapes.is_own_pair(key, shapes.project_pair(d, key))
        except shapes.PairError:
            continue                # facts.load reports it
        if own and not proj.notes:
            # the statements' text says that the project's notes give the reason
            tree.err(where, "budgets.agrees.%s is this project's own pair, so notes/%s.md says why" % (key, proj.name))
    status, reason = d["status"], d.get("reason")
    reasons = PB["projects"][status]["reasons"]
    if status == "available":
        if reason is not None or "reason_args" in d:
            tree.err(where, "an available project has no reason")
        for k in ("library", "harnesses", "build"):
            if k not in d:
                tree.err(where, "an available project needs %r" % k)
        published = any(h.builds() for h in proj.harnesses.values())
        if published and "assets" not in d:
            tree.err(where, "an available project with published binaries needs 'assets'")
        if not published and "assets" in d:
            tree.err(where, "'assets' with every binary withheld: there is nothing to attach")
    else:
        if reason not in reasons:
            tree.err(where, "reason %r is not a %s reason (%s)" % (reason, status, ", ".join(reasons)))
        else:
            _sentence_ok(tree, where, reasons[reason], d.get("reason_args") or {})
        if "oss_fuzz" not in d and (status, reason) in OSS_FUZZ_REASONS:
            tree.err(where, "reason %s says what OSS-Fuzz has for the project, and OSS-Fuzz has no such project (no "
                     "oss_fuzz)" % reason)
        for k in ("library", "patches", "assets", "build", "withheld"):
            if k in d:
                tree.err(where, "%r belongs to available projects only" % k)
        if proj.harnesses:
            tree.err(where, "a %s project has no harness directories" % status)
        if any(e["status"] == "included" for e in proj.entries()):
            tree.err(where, "a %s project includes no harness" % status)
    for f in (d.get("reason_args") or {}).get("features", []):
        if f not in PB["features"]:
            tree.err(where, "unknown feature %r" % f)
    seen, idents = set(), {}
    for e in proj.entries():
        n = e["name"]
        if n in seen:
            tree.err(where, "harness %r listed twice" % n)
        seen.add(n)
        idents.setdefault(names.ident(n), []).append(n)
        if e.get("origin") == "oss-verify" and not facts.port(proj):
            tree.err(where, "%s: origin oss-verify requires build.oss_verify" % n)
        if e.get("origin") == "oss-verify" and e.get("reason") in UNBUILT_REASONS:
            tree.err(where, "%s: origin oss-verify says OSS Verify builds it, and reason %s says it is not built"
                     % (n, e["reason"]))
        if n in names.RESERVED_HARNESS_NAMES:
            tree.err(where, "%r is a reserved name" % n)
        if (n == names.API_DRIVER) != (e.get("origin") == "this-repository"):
            tree.err(where, "%s: api-driver, and only api-driver, has origin this-repository" % n)
        if "oss_fuzz" not in d and e.get("origin", "oss-fuzz") == "oss-fuzz":
            tree.err(where, "%s: OSS-Fuzz has no such project (no oss_fuzz), so no fuzz target of it is OSS-Fuzz's file "
                     "(origin oss-fuzz; an entry with no origin is oss-fuzz)" % n)
        if e["status"] == "included":
            if "reason" in e:
                tree.err(where, "%s: an included harness has no reason" % n)
            if n not in proj.harnesses:
                tree.err(where, "%s is included but projects/%s/%s/harness.yaml is missing" % (n, proj.name, n))
        else:
            r = e.get("reason")
            if r not in PB["harnesses"]:
                tree.err(where, "%s: reason %r is not a harness reason" % (n, r))
            else:
                _sentence_ok(tree, where + ": " + n, PB["harnesses"][r], e.get("reason_args") or {})
            if n in proj.harnesses:
                tree.err(where, "%s is not included but has a directory" % n)
    for ident, hs in idents.items():
        if len(hs) > 1:
            tree.err(where, "harnesses %s all map to the Rocq identifier %s" % (hs, ident))
    for h in proj.harnesses:
        if h not in seen:
            tree.err(where, "projects/%s/%s is not listed under harnesses" % (proj.name, h))
    ids = [p["id"] for p in d.get("patches", [])]
    if len(set(ids)) != len(ids):
        tree.err(where, "a patch id is listed twice")
    lib = d.get("library") or {}
    if lib and ("commit" in lib) == ("archive_sha256" in lib):
        tree.err(where, "library names exactly one of commit and archive_sha256")
    if "patch_count" in lib and lib["patch_count"] < len(ids):
        tree.err(where, "library.patch_count is less than the patches listed")
    wh = d.get("withheld")
    if wh is not None and not (wh.get("source_bundle") or wh.get("unpublished")):
        tree.err(where, "withheld names no reason: source_bundle or unpublished")
    if (wh or {}).get("unpublished") and "patch_count" in lib:
        tree.err(where, "a project with unpublished builds does not count its patches")
    # A binary is GPL or LGPL if its own expression, its library's or a library it links from the build image binds it.
    copyleft = [h for h in proj.harnesses.values() if facts.copyleft(tree, h)]
    # the corresponding source: the upstream trees (assets.src) and where each goes (assets.src_manifest), in one
    # release, which may be a second one, v<release>-src (a GitHub release holds at most 1,000 files); and what built
    # the binaries: the build recipe the binary archive pins (assets.bin.recipe), one that release.yaml lists, in any
    # release, or for a port-built project (build.oss_verify) the port archive (assets.port), in the release of
    # assets.src, and no recipe
    a = d.get("assets") or {}
    port = facts.port(proj)
    if "port" in a and not port:
        tree.err(where, "assets.port requires build.oss_verify")
    if ("src" in a) != ("src_manifest" in a):
        tree.err(where, "assets.src and assets.src_manifest go together: the trees and where each is laid down")
    if port and "src" in a and "port" not in a:
        tree.err(where, "a project with build.oss_verify and assets.src also needs assets.port, the port archive")
    if "port" in a and "src" not in a:
        tree.err(where, "assets.port goes with assets.src: the port archive is attached as part of the corresponding "
                        "source, with the source trees and their manifest")
    # each archive is named for its project: the release workflows and fetch read the project from the name
    for k, suffix in (("bin", "-bin.tar.zst"), ("src", "-src.tar.zst"), ("src_manifest", "-src.MANIFEST.tsv"),
                      ("port", "-port.tar.zst")):
        if k in a and a[k]["file"] != proj.name + suffix:
            tree.err(where, "assets.%s.file must be %s%s" % (k, proj.name, suffix))
    if "src" in a and "src_manifest" in a and a["src"]["release"] != a["src_manifest"]["release"]:
        tree.err(where, "assets.src and assets.src_manifest are attached to different releases")
    if "src" in a and "port" in a and a["src"]["release"] != a["port"]["release"]:
        tree.err(where, "assets.port and assets.src are attached to different releases")
    pinned = facts.bin_recipe(tree, proj)
    if port and "recipe" in a.get("bin", {}):
        tree.err(where, "assets.bin.recipe: build.oss_verify says the OSS Verify port built every binary, and no recipe "
                        "did; the corresponding source is assets.src, assets.src_manifest and assets.port")
    elif "bin" in a and tree.release and not port and pinned is None:
        tree.err(where, "assets.bin.recipe is missing: each binary archive names the recipe it was built with, unless "
                        "release.yaml has the shape before recipes, whose one recipe stands for it")
    elif "bin" in a and tree.release and not port and pinned not in facts.release_recipes(tree):
        tree.err(where, "assets.bin.recipe, %s in %s, is not one of release.yaml's recipes"
                 % (pinned["file"], pinned["release"]))
    if "bin" in a and a["bin"]["release"].endswith("-src"):
        tree.err(where, "assets.bin is attached to %s, a release of source assets" % a["bin"]["release"])
    if any(h.builds() for h in copyleft):
        if "src" not in a:
            tree.err(where, "a GPL- or LGPL-licensed binary ships only with its source bundle (assets.src)")
        if "src_manifest" not in a:
            tree.err(where, "a GPL- or LGPL-licensed binary ships only with its source manifest (assets.src_manifest)")
        if not ((port and "port" in a) or (not port and pinned)):
            tree.err(where, "a GPL- or LGPL-licensed binary ships only with its build recipe or port archive")
    if (wh or {}).get("source_bundle"):
        if "src" in d.get("assets", {}):
            tree.err(where, "withheld.source_bundle, but the source bundle is attached")
        if not any(r.get("withheld") == "source-bundle" for h in proj.harnesses.values()
                   for r in h.data["builds"].values()):
            tree.err(where, "withheld.source_bundle, but no binary waits for its source bundle")


def _harness(tree, h):
    d, where = h.data, os.path.join(h.dir, "harness.yaml")
    if d["project"] != h.project.name or d["harness"] != h.name:
        tree.err(where, "project/harness do not match the directory")
    if d["rocq"] != names.rocq_harness(h.project.name, h.name):
        tree.err(where, "rocq must be %s" % names.rocq_harness(h.project.name, h.name))
    if (d["origin"] == "this-repository") != (h.name == names.API_DRIVER):
        tree.err(where, "api-driver, and only api-driver, has origin this-repository")
    entry = [e for e in h.project.entries() if e["name"] == h.name]
    if entry and entry[0].get("origin", "oss-fuzz") != d["origin"]:
        tree.err(where, "origin differs from project.yaml")
    # the port, by its name or by a GitHub URL in any case, with or without .git or a trailing slash. repo_label reads
    # the URL: these rules also run in `oft check` and `oft generate`, which need only PyYAML, and urls.parse needs idna
    repo = (d["source"].get("from") or {}).get("repository")
    if repo and facts.repo_label(repo.lower()) == "theorem-labs/oss-verify" and d["origin"] != "oss-verify":
        tree.err(where, "only an oss-verify target may name theorem-labs/oss-verify as source.from.repository")
    # a build record says what built the binaries: recipe/ (proofs/<p>/<h>/provenance/recipe/) a build recipe, port/
    # the OSS Verify port; build.oss_verify must say the same
    record = tree.path("proofs", h.project.name, h.name, "provenance")
    if facts.port(h.project) and os.path.isdir(os.path.join(record, "recipe")):
        tree.err(where, "build.oss_verify says the port built every binary, and %s's build record carries a build "
                 "recipe (proofs/%s/%s/provenance/recipe/)" % (h.name, h.project.name, h.name))
    if not facts.port(h.project) and os.path.isdir(os.path.join(record, "port")):
        tree.err(where, "%s's build record carries a port build (proofs/%s/%s/provenance/port/), and project.yaml's "
                 "build.oss_verify names no port" % (h.name, h.project.name, h.name))
    # sources: listed files exist, nothing unlisted, pending means none
    src = d["source"]
    held = src.get("pending")
    if held and src["files"]:
        tree.err(where, "a pending source lists no files")
    if not held and not src["files"]:
        tree.err(where, "source.files is empty")
    if held and (d["checks"] or d.get("rejects")):
        tree.err(where, "checks and rejects name lines of a source that is not published")
    lines = {}
    for f in src["files"]:
        p = h.tree.path(h.dir, f)
        if not os.path.isfile(p):
            tree.err(where, "source file %s is missing" % f)
        else:
            with open(p, "rb") as fh:
                lines[f] = fh.read().count(b"\n") + 1
    sdir = h.tree.path(h.dir, "source")
    if os.path.isdir(sdir):
        for dp, _, fs in os.walk(sdir):
            for f in fs:
                rel = os.path.relpath(os.path.join(dp, f), h.tree.path(h.dir))
                if rel not in src["files"]:
                    tree.err(where, "%s is not listed in source.files" % rel)
    sites = [("checks[%d]" % i, c) for i, c in enumerate(d["checks"])]
    sites += [("rejects[%d]" % i, r) for i, r in enumerate(d.get("rejects") or [])]
    for label, c in sites:
        f, _, rng = c["where"].rpartition(":")
        if f not in lines and f not in src["files"]:
            tree.err(where, "%s.where names %s, which is not a source file" % (label, f))
        elif f in lines and int(rng.split("-")[-1]) > lines[f]:
            tree.err(where, "%s.where runs past the end of %s" % (label, f))
    for i, c in enumerate(d["checks"]):
        for k in ("exit_status", "exit_reaches_guard"):
            if (c["stops_with"] == "exit") != (k in c):
                tree.err(where, "checks[%d]: %s goes with stops_with: exit, and only there" % (i, k))
    for name, s in d["statements"].items():
        ex = s.get("exits", "any")
        if s["kind"] != "halts" or ex == "any":
            continue
        if (shapes.REJECTED in ex) != bool(d.get("rejects")):
            tree.err(where, "statements.%s: exits include %d exactly when the harness lists rejects"
                     % (name, shapes.REJECTED))
    if ("commit" in d["library"]) == ("archive_sha256" in d["library"]):
        tree.err(where, "library names exactly one of commit and archive_sha256")
    for b, rec in d["builds"].items():
        if rec["file"] != names.build_file(h.name, b):
            tree.err(where, "builds.%s.file must be %s" % (b, names.build_file(h.name, b)))
    for f in d.get("model_gap", []):
        if f not in PB["features"]:
            tree.err(where, "unknown model_gap feature %r" % f)
    for b, rec in d["builds"].items():
        if not rec.get("withheld") and not all(k in rec for k in ("bytes", "sha256", "segments")):
            tree.err(where, "builds.%s: a published build has bytes, sha256 and segments" % b)
        un = rec.get("uninstrumented") or []
        if un and rec.get("withheld"):
            tree.err(where, "builds.%s: a withheld build shows no detail, so no uninstrumented list" % b)
        seen = set()
        for i, u in enumerate(un):
            k = (u["name"], u["kind"], u.get("source"), u.get("sha256"))
            if k in seen:
                tree.err(where, "builds.%s.uninstrumented[%d]: %s listed twice" % (b, i, u["name"]))
            seen.add(k)
            if u["kind"] in ("assembly", "fortran") and "source" not in u:
                tree.err(where, "builds.%s.uninstrumented[%d]: a library member names its source file" % (b, i))
    if ("distribution" in d) != os.path.isfile(h.tree.path(h.dir, "Distribution.v")):
        tree.err(where, "Distribution.v exists exactly when distribution is given")
    _distribution(tree, h, where)
    for st in h.statements.values():
        _statement(tree, h, st, where)
    if h.project.data["language"] == "go":
        _go_harness(tree, h, where)
    else:
        for i, c in enumerate(d["checks"]):
            if c["stops_with"] == "fail":
                tree.err(where, "checks[%d]: stops_with: fail is t.Fatal, t.Error or t.Fail in a Go fuzz test" % i)
    kinds = {(s.kind, tuple(s.data["builds"])) for s in h.statements.values()}
    for s in h.statements.values():
        if s.kind in ("bound", "decidability") and ("agreement", tuple(s.data["builds"])) not in kinds:
            tree.err(where, "%s: a bound or decidability statement goes with its pair's agreement statement"
                     % s.name)
    # A harness that publishes a build has a statement for `oft check` to check, or has withdrawn every one, on purpose
    # and with a reason: plan leaves such a harness out of every check, so a withheld statement must not be all it has.
    statuses = {s.data.get("status") for s in h.statements.values()}
    if h.builds() and not any(s.rendered() for s in h.statements.values()) and statuses != {"withdrawn"}:
        tree.err(where, "publishes a build, but every statement is withheld, so Statements.v carries none and no check "
                        "checks it: withhold the builds too, or withdraw the statements")


# the stops a Go check can have: a panic, t.Fatal/t.Error/t.Fail, os.Exit, or none (the C, C++ and Python kinds name
# mechanisms a Go program does not use)
GO_STOPS = ("panic", "fail", "exit", "print-only", "return-only")
# the repository of the port's Go toolchain image (the port's infra/toolchains.tsv, its row for language go)
GO_BUILDER = "ghcr.io/theorem-labs/oss-fuzz-theorems-toolchain-go@"


def _go_harness(tree, h, where):
    """A Go fuzz target has only the plain build (Go's -asan needs cgo, which the port's build turns off, and -msan
    does not target riscv64), so its one statement is plain_halts, reading budget, allowing exactly the statuses 0 and
    2: its driver gives no status 3, and every other status it ends with (79, 77, 80, 139) is a failure
    (docs/building.md, "Go fuzz targets").  It is OSS-Fuzz's or the project's Go fuzz target, never an API driver."""
    if h.data["origin"] == "this-repository":
        tree.err(where, "a Go project has no API driver: its driver_api header describes a C driver")
    for b in sorted(set(h.data["builds"]) - {"plain"}):
        tree.err(where, "builds.%s: a Go fuzz target has only the plain build" % b)
    for i, c in enumerate(h.data["checks"]):
        if c["stops_with"] not in GO_STOPS:
            tree.err(where, "checks[%d]: a Go check stops with one of %s, not %s"
                     % (i, ", ".join(GO_STOPS), c["stops_with"]))
    for st in h.statements.values():
        if st.kind != "halts" or st.data["reading"] != "budget":
            tree.err(where, "statements.%s: a Go fuzz target's one statement is plain_halts (reading budget), so no "
                            "%s statement" % (st.name, st.name))
        elif st.data.get("exits") == "any" or set(st.data.get("exits") or []) != {0, 2}:
            tree.err(where, "statements.%s: a Go fuzz target's halts statement allows exactly the statuses 0 and 2"
                     % st.name)


def _bytes_def(body, name, _depth=0):
    """The bytes of `Definition name : list byte := [...]`, of the same list
    under List.nodup (the alphabet), or of a concatenation of such definitions
    (a long header in chunks); None if the body has no such definition."""
    m = re.search(r"Definition %s : [\w.]+(?: [\w.]+)? :=\s*(?:List\.nodup \(fun x y => decide \(x = y\)\)\s*)?"
                  r"\[(.*?)\]\s*\." % name, body, re.S)
    if m:
        return bytes(int(x) for x in re.findall(r"Z_to_bv 8 (\d+)", m.group(1)))
    m = re.search(r"Definition %s : list byte :=\s*([()\w\s+]*?)(?:%%list)?\s*\.\s" % name, body, re.S)
    if not m or _depth > 2:
        return None
    parts = re.findall(r"\w+", m.group(1))
    got = [_bytes_def(body, p, _depth + 1) for p in parts]
    if not parts or any(g is None for g in got) or "++" not in m.group(1):
        return None
    return b"".join(got)


def _q_def(body, name):
    m = re.search(r"Definition %s : Q :=\s*\(?\s*(\d+)\s*#\s*(\d+)\s*\)?(?:%%Q)?\s*\." % name, body)
    return Fraction(int(m.group(1)), int(m.group(2))) if m else None


def _distribution(tree, h, where):
    """The header says what the body is: each typed field is compared with the
    definition in the body it describes, so the prose cannot drift from the
    Rocq (a second reading of the same distribution, not a copy of it)."""
    d = h.data.get("distribution")
    body = h.distribution_body()
    if d is None or body is None:
        return
    w = where + ": distribution"
    frac = lambda s: Fraction(*schema.fraction_value(s))
    if ("prefix_hex" in d) == ("prefix" in d):
        return tree.err(w, "exactly one of prefix_hex and prefix")
    hdr = _bytes_def(body, "hdr")
    if "prefix" in d:
        hdr_fact = hdr and (len(hdr), hashlib.sha256(hdr).hexdigest())
        hdr_want = (d["prefix"]["bytes"], d["prefix"]["sha256"])
    else:
        hdr_fact, hdr_want = hdr, bytes.fromhex(d["prefix_hex"])
    expect = [("prog", _bytes_def(body, "prog"), d["argv0"].encode()),
              ("path", _bytes_def(body, "path"), d["input_file"].encode()),
              ("hdr", hdr_fact, hdr_want),
              ("p", _q_def(body, "p"), frac(d["payload"]["p"])),
              ("m_payload", _q_def(body, "m_payload"), frac(d["components"]["payload"])),
              ("m_missing_file", _q_def(body, "m_missing_file"), frac(d["components"]["missing_file"])),
              ("m_base", _q_def(body, "m_base"), frac(d["components"]["full_support"])),
              ("M", _q_def(body, "M"), frac(d["mass"]))]
    each = _q_def(body, "m_argv_arity_each")
    expect.append(("m_argv_arity_each", each and each * body.count("m_argv_arity_each)"),
                   frac(d["components"]["wrong_argc"])))
    if "envp" in d["components"]:
        each = _q_def(body, "m_envp_each")
        expect.append(("m_envp_each", each and each * body.count("m_envp_each)"), frac(d["components"]["envp"])))
    alpha = _bytes_def(body, "alpha")
    if d["payload"]["alphabet"] == "bytes":
        expect.append(("alpha", alpha is None, True))
    else:
        expect.append(("alpha", alpha and len(alpha), d["payload"].get("alphabet_size")))
    for name, got, want in expect:
        if got is None:
            tree.err(w, "the body has no Definition %s to check the header against" % name)
        elif got != want:
            tree.err(w, "the header says %r but the body's %s is %r" % (want, name, got))
    p = frac(d["payload"]["p"])
    if p and d["payload"]["mean_bytes"] != round((1 - p) / p):
        tree.err(w, "mean_bytes is %d but p = %s gives %d" % (d["payload"]["mean_bytes"], p, round((1 - p) / p)))


def _statement(tree, h, st, where):
    d, w = st.data, "%s: statements.%s" % (where, st.name)
    try:
        expect = names.statement_name(d["kind"], d["builds"], d["reading"])
    except (KeyError, IndexError):
        return tree.err(w, "unknown builds %r" % (d["builds"],))
    if st.name != expect:
        tree.err(w, "its fields give the name %s" % expect)
    for b in d["builds"]:
        if b not in h.data["builds"]:
            tree.err(w, "names build %s, which harness.yaml does not list" % b)
    try:
        try:
            shapes.term(d, project=h.project.data)
        except shapes.PairError:
            pass    # reported once, against project.yaml (facts.load); term checks every other field before the pair
        if "shape" in d and d["shape"] != shapes.shape_name(d):
            tree.err(w, "shape is %s, but its fields give %s" % (d["shape"], shapes.shape_name(d)))
        if "env" in d and d["env"] != shapes.READING_ENV[d["reading"]]:
            tree.err(w, "env is %s, but reading %s gives %s" % (d["env"], d["reading"], shapes.READING_ENV[d["reading"]]))
    except shapes.ShapeError as e:
        tree.err(w, str(e))
    if d["kind"] == "halts" and "exits" not in d:
        tree.err(w, "a halts statement names its exits")
    if d["kind"] == "bound" and "distribution" not in h.data:
        tree.err(w, "a bound statement needs the harness's distribution")
    if d["kind"] != "halts" and "binds_checks" in d:
        tree.err(w, "binds_checks is for halts statements")
    if "binds_checks" in d:
        computed = any(shapes.binds(c, d, h.data) for c in h.data["checks"])
        if d["binds_checks"] != computed:
            tree.err(w, "binds_checks is %s, but the checks give %s" % (d["binds_checks"], computed))
    status = d["status"]
    need = {"suspected-false": {"basis", "reason"}, "withdrawn": {"reason"}, "witnessed-false": {"witness"},
            "withheld": {"withheld"}}.get(status, set())
    allowed = need | ({"gap"} if status == "model-gap" else set())
    for k in ("basis", "reason", "witness", "withheld", "gap"):
        if k in need and k not in d:
            tree.err(w, "a %s statement needs %r" % (status, k))
        if k in d and k not in allowed:
            tree.err(w, "%r does not go with status %s" % (k, status))
    if h.data.get("model_gap") and status not in ("model-gap", "withheld", "withdrawn"):
        tree.err(w, "the harness has a model gap, so every statement is model-gap")
    if h.data.get("model_gap") and "gap" in d:
        tree.err(w, "gap is for a statement whose harness has no model_gap")
    if status == "model-gap" and not h.data.get("model_gap") and not d.get("gap"):
        tree.err(w, "model-gap needs the harness's model_gap features or the statement's gap")
    for f in d.get("gap", []):
        if f not in PB["features"]:
            tree.err(w, "unknown gap feature %r" % f)
    held = {h.data["builds"].get(b, {}).get("withheld") for b in d["builds"]} - {None}
    if held and status not in ("withheld", "withdrawn"):
        tree.err(w, "names a withheld build, so it is withheld too")
    if held and status == "withheld" and d.get("withheld") not in held:
        tree.err(w, "withheld for %s, but its build is withheld for %s" % (d.get("withheld"), ", ".join(sorted(held))))
    wt = d.get("witness")
    if wt is not None:
        if wt["build"] not in d["builds"]:
            tree.err(w, "the witness ran build %s, which the statement does not name" % wt["build"])
        elif h.data["builds"].get(wt["build"], {}).get("withheld"):
            tree.err(w, "the witness ran a withheld build")
        if ("input_hex" in wt) == ("input" in wt):
            tree.err(w, "a witness gives exactly one of input_hex and input")
        if (wt["outcome"] == "exit") != ("exit" in wt):
            tree.err(w, "a witness gives an exit status exactly when it ends in an exit")
        if wt["outcome"] == "exit":
            # an exit refutes a halts statement that does not allow its status; an agreement is about two builds,
            # which one build's exit cannot show differ
            if d["kind"] != "halts":
                tree.err(w, "a witness that ends in an exit refutes only a halts statement")
            elif d.get("exits") == "any" or wt.get("exit") in (d.get("exits") or []):
                tree.err(w, "the witness exits with status %s, which the statement allows" % wt.get("exit"))
            if "after" in wt:
                tree.err(w, "`after` is for a witness that ends in a signal")


def _proof(tree, sid, pd):
    st = next((s for s in tree.statements() if s.id == sid), None)
    if st is None:
        return
    y = os.path.join(pd.path, "proof.yaml")
    if st.kind == "bound" and not pd.refutes and "bound" not in pd.data:
        tree.err(y, "a bound proof names its bound")
    if st.kind != "bound" and "bound" in pd.data:
        tree.err(y, "only a bound proof names a bound")
    if st.fingerprint and pd.data["fingerprint"] != st.fingerprint:
        tree.err(y, "fingerprint differs from the statement's current one (%s): re-check the proof; when only the "
                 "fingerprint's version changed, `./oft revisions PREVIOUS --write-pins` sets it (docs/versioning.md)"
                 % st.fingerprint)


def _counterexample(tree, sid, cx):
    st = next((s for s in tree.statements() if s.id == sid), None)
    if st is None:
        return
    y = os.path.join(cx.path, "expect.yaml")
    if st.kind != "halts":
        tree.err(y, "counterexamples are for halts statements")
        return
    obs = cx.data["observed"]
    if obs["build"] != st.data["builds"][0]:
        tree.err(y, "observed.build must be the statement's build")
    ex = st.data.get("exits", "any")
    if "signal" not in obs and (ex == "any" or obs["exit"] in ex):
        tree.err(y, "the observed exit %d is allowed by the statement: this is not a counterexample" % obs["exit"])
    if ex != "any" and cx.data["control"]["exit"] not in ex:
        tree.err(y, "the control input must exit with an allowed status")


# The shape of a run as `oft check --record` prints it and the finding schema's `run` allows it: an exit status from 0
# to 255, the signal that ended it if it is one of these, and the SHA-256 of its stdout and of its stderr.  `oft check
# --record` prints no run of another shape, and `oft ledger` anchors no record with one.  It is written out here rather
# than read from the schema, so that no later change to the schema turns a record that was evidence back into a draft;
# test_findings checks that the schema allows the same signals.
RUN_SIGNALS = ("SIGABRT", "SIGILL", "SIGSEGV", "SIGBUS", "SIGFPE", "SIGTRAP")
_SHA256 = re.compile(r"[0-9a-f]{64}")


def run_ok(run):
    """Whether run (one build's run, as finding.yaml records it) has the shape `oft check --record` prints."""
    if not isinstance(run, dict) or not {"exit", "stdout_sha256", "stderr_sha256"} <= set(run) <= set(facts.RUN_FIELDS):
        return False
    exit_ok = isinstance(run["exit"], int) and not isinstance(run["exit"], bool) and 0 <= run["exit"] <= 255
    return (exit_ok and run.get("signal", RUN_SIGNALS[0]) in RUN_SIGNALS
            and all(isinstance(run[k], str) and _SHA256.fullmatch(run[k]) for k in ("stdout_sha256", "stderr_sha256")))


# The statuses that record a statement as false: derived from a counterexample or a refutation, or exported.
FALSE_STATUSES = ("counterexample", "refuted", "witnessed-false", "suspected-false")


def _finding(tree, f, patches):
    """A finding's input shows each of its statements false, unless it is pruned, when it shows none false; its
    control shows none false; it runs only the builds its statements name; its patch has a name no other finding of
    its project has; and a not-a-defect finding's statements are recorded as false in the facts.  patches: (project,
    patch file name) -> the first finding that names it."""
    d, y = f.data, os.path.join(f.path, "finding.yaml")
    if d.get("patch"):
        first = patches.setdefault((f.project, d["patch"]), f.path)
        if first != f.path:
            tree.err(y, "its patch %s has the name of the patch of %s: each patch of a project has a name of its own"
                     % (d["patch"], first))
    h = f.project in tree.projects and tree.projects[f.project].harnesses.get(f.harness)
    if not h:
        return
    sts = [h.statements[s] for s in d["statements"] if s in h.statements
           and h.statements[s].kind in ("agreement", "halts")]
    if d["state"] == "not-a-defect":
        for st in sts:
            if st.status not in FALSE_STATUSES:
                tree.err(y, "not-a-defect, but %s is not recorded as false" % st.name)
    if "input" not in d or "control" not in d:
        return
    named = {b for st in sts for b in st.data["builds"]}
    for which in ("input", "control"):
        for b in sorted(set(d[which]) - named, key=schema.BUILDS.index):
            tree.err(y, "%s runs build %s, which none of its statements names" % (which, b))
    for st in sts:
        if any(b not in d["input"] or b not in d["control"] for b in st.data["builds"]):
            continue            # the loader names the missing run
        false = facts.shows_false(st, d["input"])
        if d["state"] == "pruned" and false:
            tree.err(y, "pruned, but its record shows %s false" % st.name)
        elif d["state"] != "pruned" and not false:
            tree.err(y, "the input does not show %s false" % st.name)
        if facts.shows_false(st, d["control"]):
            tree.err(y, "the control does not behave normally: it shows %s false" % st.name)


PATCH_NAME = re.compile(r"[A-Za-z0-9][A-Za-z0-9._+-]*\.patch")
# the states whose patch the patched build carries; a pruned or not-a-defect finding may keep its patch in the ledger
SERIES_STATES = ("patched", "reported", "public")


def _series(tree):
    """findings/<p>/<h>/series lists patch file names, one per line, in build order: exactly the patches of that
    harness's findings that are patched, reported or public."""
    units = {f.unit for f in tree.findings.values()} | set(tree.finding_series)
    for unit in sorted(units):
        rel = os.path.join("findings", unit, "series")
        listed = tree.finding_series.get(unit, "").split("\n")
        if listed and listed[-1] == "":
            listed.pop()
        mine = [f for f in tree.findings.values() if f.unit == unit]
        seen = set()
        for no, name in enumerate(listed, 1):
            if not PATCH_NAME.fullmatch(name):
                tree.err(rel, "line %d is not a patch file name" % no)
                continue
            if name in seen:
                tree.err(rel, "lists %s twice" % name)
                continue
            seen.add(name)
            n = sum(1 for f in mine if f.data.get("patch") == name and f.data["state"] in SERIES_STATES)
            if n != 1:
                tree.err(rel, "lists %s, which is the patch of %d findings that are patched, reported or public, not "
                         "exactly one" % (name, n))
        for f in sorted(mine, key=lambda f: f.path):
            if f.data["state"] in SERIES_STATES and f.data.get("patch") and f.data["patch"] not in seen:
                tree.err(os.path.join(f.path, "finding.yaml"), "a %s finding's patch %s is not listed in %s"
                         % (f.data["state"], f.data["patch"], rel))


def _held(tree):
    """Only a project a finding holds back whole builds from the port's internal
    copy, and only it attaches assets to a findings-<project>
    release, its own: no shipping release names either.  An enrolled project
    whose findings hold back only some of its statements ships its binaries,
    so it builds from the public port."""
    held = facts.hold(tree).held
    for proj in tree.projects.values():
        where = os.path.join(proj.dir, "project.yaml")
        port = facts.port(proj)
        if port and port["repository"] == schema.INTERNAL_PORT_REPOSITORY and proj.name not in held:
            tree.err(where, "build.oss_verify.repository is %s: only a project a finding holds back whole builds "
                            "from %s" % (schema.INTERNAL_PORT_REPOSITORY, schema.INTERNAL_PORT_REPOSITORY))
        assets = proj.data.get("assets") or {}
        for k in ("bin", "src", "src_manifest", "port"):
            release = (assets.get(k) or {}).get("release", "")
            if release.startswith("findings-") and (proj.name not in held or release != "findings-" + proj.name):
                tree.err(where, "assets.%s is attached to %s: only a project a finding holds back whole attaches to "
                                "findings-<project>, its own" % (k, release))

