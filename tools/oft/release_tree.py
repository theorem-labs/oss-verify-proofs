"""oft release-tree: turn a checkout into the files of a release.

approvals.yaml lists the proofs a release carries, by fuzz target and statement.  This
keeps the proof directory of each listed statement, with its fuzz target's whole lib/ and
build record (so a listed statement carries everything in that lib/), and removes every other
proof (a fuzz target's whole proofs folder when none of its proofs is listed).  An entry from
a project's enrollment merge (origin enrollment) is a ceiling: it lists the statements its
enrollment facts pull requests wrote, and of those this keeps only the proofs that exist, that
facts.hold does not hold back and that do not refute.  A fuzz target's
proofs folder is proofs/<project>/<harness>/ in the old layout and
projects/<project>/<harness>/proofs/ in the per-project one (layout.py); each fuzz target is
read in the layout its facts are in.

It leaves out what facts.hold holds back.  A project held whole (`release: private` in its
project.yaml, or a finding that holds it back) ships as a held project when OSS-Fuzz has it:
its project.yaml is rewritten to the held form (facts.held_form) and its page is rendered from
that, and everything else of it goes (the rest of projects/<p>/, its counterexamples,
patches/<p>/ or projects/<p>/patches/, notes/<p>.md; its proofs as unlisted ones).  A held
page says only that the project is held, so it tells a reader nothing the OSS-Fuzz issue does
not.  A project held whole that OSS-Fuzz does not have is removed whole.  An enrolled project
(`enrolled: true`) whose findings are all open keeps its page and its other statements, and
only the statements
those findings break are held back (with each held agreement's bound and decidability
statements), with their proofs and counterexamples.  Either way
release.yaml carries the counts and oss_fuzz.projects of the cut, and an image_libraries
entry no remaining build links goes.  It removes every finding entirely: findings/, and each
projects/<p>/<h>/findings/ and projects/<p>/unpatched.yaml (an undisclosed bug's record,
reproducer and patch never ship),
and what only this repository has (INTERNAL, paths.py's list and SKILLS written out, whose comment says
why each is there; a directory is removed whole, and never read for what is held back); it rewrites
tools/oft/lint-exceptions.yaml without each entry whose path, in either layout's form, is at or
under a path the cut removes (an entry left for it would be unused, and a lint finding in the
release), and without every licence-pending entry, so a release carries none (the lines above its
`exceptions` key stay as written), and renders
the generated files again, so the statuses in the pages and the index say what the release
holds.  It reports a listed statement that has no proof in the checkout (of enrollment entries,
only how many: a ceiling's normal state), and each fuzz target
whose lib/ it keeps while removing some of its statement directories (that lib/ may hold
their proofs).  Everything else (the facts, CHANGELOG.md among them, counterexamples) is left
as it is, so the release's CHANGELOG section must describe only what the release carries.

It refuses, and changes nothing, when the facts have an error; the checkout holds a symbolic
link outside an ignored path (proofs/, .github/, .claude/ and tools/ themselves among them, as
the cut would remove through them), or a path the cut removes is one (an ignored one, such as
a held project's bin/, among them); a fuzz target's proofs folder holds a file beside its statement
directories (its generated dune file aside), a file under the old layout's proofs/ is in no fuzz target's
proofs folder (proofs/lib/ among them, which no row admits), or a kept statement
directory holds a file other than Proof.v, proof.yaml and its generated dune; git tracks a
file at an ignored path; the facts as the release will have them have an error; a file the
release keeps or writes, the rewritten lint-exceptions.yaml included, discloses what is held
back (disclosure); or the generated files are not current, the shared ones apart (paths.SHARED:
the line's render owns them, and this run's final render writes them into the cut).  Every check
runs before the first change.  It rewrites the checkout in place: run it in a scratch checkout.
"""
import copy
import glob
import io
import os
import shutil
import subprocess
import sys

import yaml

from . import disclosure, facts, generate, layout, lint, paths, rules, yamlio

# What only this repository has, which the cut removes: the INTERNAL of paths.py (TABLE's internal rows, then its
# INTERNAL_FILES and INTERNAL_DIRS), then SKILLS (below), written out here as a literal tuple equal to them
# (test_release_tree.test_every_internal_path_is_one_the_cut_removes).  It is written out, not imported, because the
# release gate reads this file's INTERNAL from its syntax tree, as an assignment of a literal tuple of strings, and
# skips an import without a word (its R17 row: a published tree is a release-tree cut;
# test_the_release_gate_reads_every_internal_path_from_release_tree_py replays its reading).  An entry that ends in / is
# a directory, removed whole.  What each is: the list of the files that need judgement (CODEOWNERS), the automated
# facts review of a pull request and its criteria (the review runs on this repository's identity), and which proofs a
# release publishes; the pipeline that turns an enrollment into facts and its approvals (enroll.yml, enroll-build.yml,
# the workflows that start its redo runs, facts-refresh.yml and hold-state.yml, enroll-retry.yml, approvals-watch.yml
# and the tools/enroll/ directory they run), which a reader of a proof never needs; the released-proof index's workflow
# and builder, which push to this repository's branch proof-index, and the trigger that ossv/candidates carries to start
# that workflow; the render of the shared generated files after a merge (index.yml and regenerate-shared.sh), which
# only an internal line has: each publication renders its cut whole; the publishing workflows and the tools/publish/
# directory they run; the change ledgers (changes/: oft change-ledger), whose sessions, costs and journals are this
# repository's own records; the reference book (docs/reference/: the worker briefs and the rules a proof's author
# follows, docs/reference/README.md), which is written for the people and agents who prove, not for a reader of a
# proof; and dev/stream/, the OSS Verify stream's operational tools (dev/stream/README.md), which run the stream rather
# than check a proof and which name this company's machines, buckets and sessions.  That last cut is what lets
# lint.internal_only read dev/stream/ as text no reader outside this company sees: the two lists are held to each other
# by tools/oft/tests/test_lint.py; and the script of pr.yml's prove job (ci/prove-pr), which posts a check on this
# repository's pull requests: the public repository's pr.yml finds no such script in its base's tools, and so posts
# nothing.  The tests that run regenerate-shared.sh and prove-pr go with them (a released test finds every file it
# needs: test_release_tree.ReleasedTests).  Last come the two skill directories of SKILLS: the porting skill
# (.claude/skills/porting-released-proofs/), which tells a prover how to find the proof a new statement ports from
# through this repository's unreleased branches, its search tools and an outside delivery, none of which a release
# carries, and the clean-room skill (.claude/skills/clean-room-restatement/), the internal method of a clean-room
# rewrite, which a reader of a proof never needs.  paths.py does not name them: it is part of the checker, whose ids
# are in every key (keys.py), so lint admits their files alone (lint.LINT_ONLY_HAND)
INTERNAL = (
    "approvals.yaml",
    ".github/CODEOWNERS",
    ".github/workflows/facts-review.yml",
    ".claude/skills/review-facts/SKILL.md",
    "review.md",
    ".github/workflows/enroll.yml",
    ".github/workflows/enroll-build.yml",
    ".github/workflows/facts-refresh.yml",
    ".github/workflows/hold-state.yml",
    ".github/workflows/enroll-retry.yml",
    ".github/workflows/approvals-watch.yml",
    "tools/enroll/",
    ".github/workflows/proof-index.yml",
    ".github/proof-index.py",
    ".github/workflows/proof-index-trigger.yml",
    ".github/workflows/index.yml",
    ".github/workflows/publish-request.yml",
    ".github/workflows/publish.yml",
    ".github/workflows/publish-gate.yml",
    "tools/publish/",
    "tools/oft/ci/regenerate-shared.sh",
    "tools/oft/tests/test_regenerate_shared.py",
    "tools/oft/ci/prove-pr",
    "tools/oft/tests/test_prove_pr.py",
    "changes/",
    "docs/reference/",
    "dev/stream/",
    ".claude/skills/porting-released-proofs/",
    ".claude/skills/clean-room-restatement/",
)

# the directories of INTERNAL that paths.py does not name (lint.LINT_ONLY_HAND admits their files): the release gate
# reads only INTERNAL above, so these are written there too
SKILLS = (".claude/skills/porting-released-proofs/", ".claude/skills/clean-room-restatement/")

# the files a kept statement directory may hold: its proof, its record, and the generated dune (paths.py)
STATEMENT_FILES = ("Proof.v", "proof.yaml", "dune")

PARTIAL = "kept the lib/ of %s, while removing some of its statement directories: that lib/ may hold their proofs"


def _inside_a_cut(rel):
    """Whether `rel` is inside an INTERNAL entry this cut removes whole, rather than being that entry itself.

    The gate below exists so that no facts path the cut reads can point out of the checkout; it runs before
    `facts.load`, which is why it cannot wait for the cut.  A file inside `dev/stream/` or `tools/enroll/` is
    read by nothing here and is deleted whole by `shutil.rmtree`, which unlinks a child link rather than
    following it, so a link there can take the cut nowhere.  Gating it instead refuses the whole cut: with
    `dev/stream/lane/`'s three mirrored links in the tree, `oft release-tree` exited 1 and changed nothing, so
    the first release cut from a main carrying them would have failed (the review of pull request 669, B1).
    The entry itself is still gated: a link AT `dev/stream` is what rmtree would follow.

    The directories of INTERNAL meet that test, and all are meant: `dev/stream/`, `tools/enroll/`,
    `tools/publish/`, `changes/`, `docs/reference/` and the two skill directories of SKILLS.  None is read by
    `facts.load`, `rules.check` or any later step of the cut -- `tools/enroll/` is the enrollment scripts that
    enroll.yml runs, `tools/publish/` the publication's own tools, `changes/` the change ledgers,
    `docs/reference/` the reference book and the skill directories agents' instructions, which this
    tool only deletes -- and each is removed by one `shutil.rmtree`.  The one INTERNAL entry this tool reads is
    `approvals.yaml`, through `facts.load`; the rest, `.github/CODEOWNERS` and `review.md` among them, are only
    listed and deleted.  The other entries are files, not directories, so no path is ever "inside" them and the
    gate still covers every one of them; that is why this skip is of a path inside a cut entry rather than of
    INTERNAL itself, and why the cut cannot simply run before the gate.  A link under `tools/enroll/` is still
    refused by `oft lint`, whose LINKS_ALLOWED is `dev/stream/lane/` alone, so it cannot reach main in the first
    place: the two rules answer different questions and both are kept.  A directory entry of INTERNAL ends in `/`
    (as INTERNAL in paths.py writes it), and an entry is compared without it, so `dev/stream` and `dev/stream/` read
    alike.
    """
    return any(rel.startswith(entry.rstrip("/") + "/") for entry in INTERNAL)


def checkout_links(root):
    """Every symbolic link in root outside an ignored path (paths.ignored) and outside what the cut removes whole
    (_inside_a_cut), before facts.load can read through one."""
    found = []
    for d, dirs, files in os.walk(root):
        rd = os.path.relpath(d, root)
        rd = "" if rd == "." else rd + os.sep
        found += [rd + n for n in dirs + files
                  if os.path.islink(os.path.join(d, n))
                  and not paths.ignored((rd + n).replace(os.sep, "/"))
                  and not _inside_a_cut((rd + n).replace(os.sep, "/"))]
        dirs[:] = [x for x in dirs if not paths.ignored((rd + x).replace(os.sep, "/"))]
    return sorted(found)


def tracked_ignored(tree):
    """The files git tracks at an ignored path (paths.ignored), which the checks above do not read: [] when the
    checkout is not a git work tree."""
    if not os.path.exists(tree.path(".git")):
        return []
    r = subprocess.run(["git", "-C", tree.root, "ls-files", "-z"], capture_output=True)
    if r.returncode:
        return ["git ls-files failed: %s" % r.stderr.decode("utf-8", "replace").strip()]
    return sorted(rel for rel in r.stdout.decode("utf-8", "surrogateescape").split("\0") if rel and paths.ignored(rel))


def tools_problems(tree, checkout=None):
    """Why tools/oft may not be published on its own, ahead of a release, as the runner image publishes a copy of it
    (.github/workflows/images.yml): [] when it may.  These are the rules of `oft release-tree` that reach a file under
    tools/oft: facts with an error, which may hide what is held back; and a file under tools/oft that discloses what
    facts.hold holds back, by its bytes or its path (disclosure.search, the release's own search).  A file at an
    ignored path is a problem of its own here: the search does not read it, and a copy of the directory takes it
    whether or not git tracks it.  The facts are tree's; the tools/oft judged is checkout's (a directory, another
    checkout such as the public repository's), else tree's own."""
    rules.check(tree)
    if tree.errors:
        return ["the facts have an error, so what a release holds back is not known: %s" % e for e in tree.errors]
    root = tree.root if checkout is None else checkout
    tools = os.path.join(root, "tools")
    skip = [n for n in os.listdir(root) if n != "tools"]
    skip += ["tools/" + n for n in (os.listdir(tools) if os.path.isdir(tools) else []) if n != "oft"]
    try:
        needles = disclosure.needles(tree, facts.hold(tree))
    except facts.BoundedFileError as e:
        return ["a holding finding's evidence cannot be read within its cap, so what may not ship is not known: %s" % e]
    out = ["%s names %s" % (rel, label) for rel, label in disclosure.search(root, needles, skip, {})]
    for d, dirs, files in os.walk(os.path.join(tools, "oft")):
        for name in sorted(dirs + files):
            rel = os.path.relpath(os.path.join(d, name), root).replace(os.sep, "/")
            if paths.ignored(rel):
                out.append("%s: an ignored path, so it is not read, and a copy of tools/oft takes it" % rel)
    return out


LINT_EXCEPTIONS = os.path.join("tools", "oft", "lint-exceptions.yaml")


def _under(rel, tops):
    rel = rel.replace(os.sep, "/")
    return any(rel == t or rel.startswith(t + "/") for t in (t.replace(os.sep, "/").rstrip("/") for t in tops))


def _canonical(rel):
    """rel, a file or a folder, in the per-project layout: where layout.canonical moves it, an old-layout folder whose
    files move (proofs/<p>/<h>, counterexamples/<p>/<h>, patches/<p>) going where they go."""
    rel = rel.replace(os.sep, "/").rstrip("/")
    if layout.moved(rel):
        return layout.moved(rel)
    inside = layout.moved(rel + "/-")
    return inside[:-len("/-")] if inside else rel


def _cut_entry(e, goes):
    """Why the release does not carry lint-exceptions.yaml's entry e, as the text that names it, or None: it is a
    licence-pending entry (a release carries none: lint.apply_pending), or its path is at or under a path the cut
    removes (goes)."""
    if e.get("rule") == lint.PENDING:
        return "%s %s" % (lint.PENDING, e.get("unit"))
    if goes(e["path"]):
        return e["path"]
    return None


def cut_lint_exceptions(tree, cut):
    """(text, dropped entries): tools/oft/lint-exceptions.yaml without each entry for a file the cut removes
    (_cut_entry), in either layout (lint matches an entry through layout.canonical), which the
    release does not carry (an entry left for it would be unused, and a finding in the public tree), and which may
    name what is held back, and without every licence-pending entry.  Every line above the `exceptions` key (the
    leading comment, the schema) is kept as
    written; the list, and anything after it, is written again in the canonical form, so a comment among the entries
    is not kept (an entry's why belongs in its reason).  None when no entry is dropped."""
    p = tree.path(LINT_EXCEPTIONS)
    if not os.path.isfile(p):
        return None
    with open(p, encoding="utf-8") as f:
        text = f.read()
    data = yamlio.load(text, LINT_EXCEPTIONS)
    entries = data.get("exceptions") or []
    moved = [_canonical(c) for c in cut]

    def goes(path):
        return _under(path, cut) or _under(layout.canonical(path), moved)

    gone = [g for g in (_cut_entry(e, goes) for e in entries) if g is not None]
    if not gone:
        return None
    keys = yaml.compose(text, Loader=yamlio.StrictLoader).value
    line = next(k.start_mark.line for k, _ in keys if k.value == "exceptions")
    rest = {k.value: data[k.value] for k, _ in keys if k.start_mark.line >= line}
    rest["exceptions"] = [e for e in entries if _cut_entry(e, goes) is None]
    return "".join(text.splitlines(True)[:line]) + yamlio.dump(rest), gone


def _public_release(tree, public):
    """release.yaml as the release carries it, from the cut facts `public`: its counts and oss_fuzz.projects, and
    without an image_libraries entry no build of the cut links.  None when none of that changes anything."""
    r = copy.deepcopy(tree.release)
    if not r:
        return None
    harnesses = list(public.harnesses())
    r["counts"] = rules.counts(public)
    r["oss_fuzz"]["projects"] = public.oss_fuzz_project_count()

    known = r.get("image_libraries")
    if known is not None:
        linked = {n for h in harnesses for n in facts.image_libraries(h)}
        r["image_libraries"] = {n: v for n, v in known.items() if n in linked}
        if not r["image_libraries"]:
            del r["image_libraries"]
    return None if r == tree.release else r


def _files(tree, rel):
    """rel when it is a file, else every file under it, sorted."""
    if not os.path.isdir(tree.path(rel)):
        return [rel]
    return sorted(os.path.relpath(os.path.join(d, f), tree.root) for d, _, fs in os.walk(tree.path(rel)) for f in fs)


def _plan(tree, keep):
    """(kept, removed, partial, stray) for a checkout with no symbolic link (checkout_links).  keep is {fuzz target:
    approved statements}.  Each fuzz target's proofs folder is read through the facts, in the layout they are in: kept
    and removed list a statement's proof directory, or the whole proofs folder when none of its proofs is approved.
    partial lists each fuzz target whose lib/ is kept while some of its statement directories are removed.  stray lists
    every file where only a directory belongs: beside the statement directories (a generated file aside), and anywhere
    under the old layout's proofs/ outside a fuzz target's proofs folder (proofs/lib/ among it, which no row admits);
    and anything in a kept statement directory other than the files of STATEMENT_FILES."""
    kept, removed, partial, stray = [], [], [], []
    sids = {}   # fuzz target -> the ids of its proofs
    for sid in sorted(tree.proofs):
        sids.setdefault(sid.rsplit("/", 1)[0], []).append(sid)
    folders = set()
    for unit in sorted(u for u, kinds in tree.unit_kinds.items() if "proofs" in kinds):
        p, h = unit.split("/")
        d = layout.proofs_dir(p, h, tree.unit_layout(unit))
        folders.add(d)
        bad = [os.path.join(d, e) for e in sorted(os.listdir(tree.path(d)))
               if not os.path.isdir(tree.path(d, e)) and not paths.is_gen(os.path.join(d, e))]
        if bad:
            stray += bad
            continue
        approved = [sid for sid in sids.get(unit, ()) if sid.rsplit("/", 1)[1] in keep.get(unit, ())]
        if not approved:
            removed.append(d)
            continue
        for sid in approved:
            sd = tree.proofs[sid].path
            stray += [os.path.join(sd, f) for f in sorted(os.listdir(tree.path(sd)))
                      if f not in STATEMENT_FILES or not os.path.isfile(tree.path(sd, f))]
        kept += [tree.proofs[sid].path for sid in approved]
        cut = [tree.proofs[sid].path for sid in sids[unit] if sid not in approved]
        removed += cut
        if cut and unit in tree.proof_libs:
            partial.append(unit)
    # the old layout's proofs/ holds only fuzz targets' proofs folders, proofs/<project>/<harness>/
    base = tree.path("proofs")
    for p in sorted(os.listdir(base)) if os.path.isdir(base) else []:
        if not os.path.isdir(tree.path("proofs", p)):
            stray.append(os.path.join("proofs", p))
            continue
        for h in sorted(os.listdir(tree.path("proofs", p))):
            if os.path.join("proofs", p, h) not in folders:
                stray += _files(tree, os.path.join("proofs", p, h))
    return kept, removed, partial, stray


def _findings(tree):
    """Every finding's place in the checkout, which no release carries: findings/, each projects/<p>/<h>/findings/,
    each projects/<p>/unpatched.yaml, and each projects/<p>/unpatched-bin/ that `oft fetch --findings` filled (untracked,
    as findings/<p>/bin/ was, which went with findings/)."""
    found = glob.glob(tree.path(layout.findings_dir("*", "*", layout.NEW)))
    found += glob.glob(tree.path(layout.unpatched_path("*", layout.NEW)))
    found += glob.glob(tree.path(layout.unpatched_bin_dir("*")))
    return ((["findings"] if os.path.lexists(tree.path("findings")) else [])
            + sorted(os.path.relpath(f, tree.root) for f in found))


def _remove(tree, rel, out):
    """Remove rel, a file or a directory, and each parent below the top level that this leaves empty."""
    if os.path.isdir(tree.path(rel)):
        shutil.rmtree(tree.path(rel))
        print("removed %s/" % rel, file=out)
    else:
        os.remove(tree.path(rel))
        print("removed %s" % rel, file=out)
    parent = os.path.dirname(rel)
    while os.sep in parent and not os.listdir(tree.path(parent)):
        os.rmdir(tree.path(parent))
        parent = os.path.dirname(parent)


def run(root, out=sys.stdout):
    root = os.path.abspath(root)
    # A facts path is untrusted until this check says it cannot point outside root. facts.load and rules.check inspect
    # source/ and finding files, so this precedes every checkout read.
    links = checkout_links(root)
    if links:
        for rel in links:
            print("error: %s: a symbolic link, which the cut could follow out of the checkout" % rel, file=out)
        print("oft release-tree: %d path(s) that are not plain directories or expected files; nothing changed"
              % len(links), file=out)
        return 1
    tree = facts.load(root)
    rules.check(tree)
    if tree.errors:
        for e in tree.errors:
            print("error: " + e, file=out)
        print("oft release-tree: %d error(s) in the facts; nothing changed" % len(tree.errors), file=out)
        return 1
    if tree.approvals is None:
        print("oft release-tree: no approvals.yaml, so nothing says which proofs this release publishes; "
              "nothing changed", file=out)
        return 1
    held = facts.hold(tree)
    held_ids = held.ids
    keep = {}   # a fuzz target may have an entry per source: it keeps the union of their statements
    ceiling = set()   # the ids of the statements enrollment entries list
    for e in tree.approvals["fuzz_targets"]:
        unit, statements = e["fuzz_target"], set(e["statements"])
        if e["origin"] == "enrollment":
            ceiling.update("%s/%s" % (unit, s) for s in statements)
            # a ceiling (rules._approvals): none of a project held whole, nor a statement held back or whose proof
            # refutes; the rules refuse those in any other entry
            statements = {s for s in statements if unit.partition("/")[0] not in held.whole
                          and "%s/%s" % (unit, s) not in held_ids
                          and not getattr(tree.proofs.get("%s/%s" % (unit, s)), "refutes", False)}
        keep.setdefault(unit, set()).update(statements)
    kept, removed, partial, stray = _plan(tree, keep)
    problems = ["%s: a file a release cannot carry there" % rel for rel in stray]
    problems += ["%s (tracked by git at an ignored path): a file a release cannot carry" % rel
                 for rel in tracked_ignored(tree)]
    if problems:
        for p in problems:
            print("error: " + p, file=out)
        print("oft release-tree: %d path(s) that are not plain directories or expected files; nothing changed"
              % len(problems), file=out)
        return 1
    hidden = sorted(held.whole)
    # the facts as the release will have them, checked before the first change; the cut decides which projects held
    # whole keep a held page
    kept_dirs = set(kept)
    shipped = {sid for sid, pd in tree.proofs.items() if pd.path in kept_dirs}
    public = facts.load(root)
    held_page = facts.cut(public, shipped, held)
    # the one removal path: what a release leaves out of each project
    dropped = [os.path.join("projects", p) for p in hidden if p not in held_page]
    dropped += [os.path.join("projects", p, x) for p in held_page
                for x in sorted(os.listdir(tree.path("projects", p))) if x not in ("project.yaml", "README.md")]
    for p in hidden:
        # its counterexamples, in the layout of each fuzz target, and its patches in either layout
        dropped += [layout.counterexamples_dir(p, u.split("/")[1], lay)
                    for u, lay in sorted(tree.unit_layouts.items()) if u.split("/")[0] == p]
        dropped += [layout.patches_dir(p, layout.OLD), layout.patches_dir(p, layout.NEW),
                    os.path.join("notes", p + ".md")]
    # a statement an open finding holds back takes its counterexample with it
    dropped += [layout.counterexample_dir(p, h, s, tree.unit_layout("%s/%s" % (p, h)))
                for p, h, s in (sid.split("/") for sid in sorted(held_ids))]
    # each path once, and none inside another (a held project's own folder holds what it has in the per-project layout)
    dropped = [rel for i, rel in enumerate(dropped) if os.path.lexists(tree.path(rel)) and rel not in dropped[:i]
               and not any(rel.startswith(other + os.sep) for other in dropped)]
    # checkout_links reads no ignored path (projects/<p>/bin/, a _build/), and the cut removes such a path of a held
    # project: a symbolic link there would stop rmtree after the first change, or take the cut out of the checkout
    linked = [rel for rel in removed + dropped if os.path.islink(tree.path(rel))]
    if linked:
        for rel in linked:
            print("error: %s: a symbolic link, which the cut could follow out of the checkout" % rel, file=out)
        print("oft release-tree: %d path(s) that are not plain directories or expected files; nothing changed"
              % len(linked), file=out)
        return 1
    files = [f for f in INTERNAL if os.path.lexists(tree.path(f.rstrip("/")))]
    findings = _findings(tree)
    release_yaml = _public_release(tree, public)
    if release_yaml is not None:
        public.release = release_yaml
    rules.check(public)
    if public.errors:
        for e in public.errors:
            print("error: after the cut: %s" % e, file=out)
        print("oft release-tree: %d error(s) in the facts as the release would have them; nothing changed"
              % len(public.errors), file=out)
        return 1
    # every file the cut writes, in one place: the search reads it, the walk skips the old file, and the cut writes it
    writes = {os.path.join("projects", p, "project.yaml"): yamlio.dump(public.projects[p].data) for p in held_page}
    writes.update({os.path.join("projects", unit, "harness.yaml"): yamlio.dump(public.projects[p].harnesses[h].data)
                   for unit in {sid.rsplit("/", 1)[0] for sid in held_ids} for p, h in [unit.split("/")]})
    if release_yaml is not None:
        writes["release.yaml"] = yamlio.dump(release_yaml)
    # the rewritten lint-exceptions.yaml ships, so the search reads its text as the release will have it
    exceptions = cut_lint_exceptions(tree, removed + dropped + files + findings)
    if exceptions is not None:
        writes[LINT_EXCEPTIONS] = exceptions[0]
    rendered = generate.render_all(public)
    try:
        needles = disclosure.needles(tree, held)
    except facts.BoundedFileError as e:
        print("error: a holding finding's evidence cannot be read within its cap: %s" % e, file=out)
        print("oft release-tree: the evidence to search for is unreadable; nothing changed", file=out)
        return 1
    named = disclosure.search(root, needles, removed + dropped + files + list(writes) + findings,
                              {**rendered, **writes})
    if named:
        for rel, label in named:
            print("error: %s names %s" % (rel, label), file=out)
        print("oft release-tree: %d disclosure(s) of what is held back in files the release keeps; nothing changed"
              % len(named), file=out)
        return 1
    # a stale rendering would fail only after the cut: find it first.  Not the shared generated files
    # (paths.SHARED): the line's render owns them, so a line commit may carry a stale one, and this run's own final
    # render writes them into the cut.
    buf = io.StringIO()
    if generate.run(root, check=True, out=buf, shared=False):
        out.write(buf.getvalue())
        print("oft release-tree: the generated files are not current (run ./oft generate); nothing changed", file=out)
        return 1
    # every check has passed: only now does anything change
    # a statement of an exact entry with no proof is named; one of a ceiling, its normal state, only counted
    absent = sorted(sid for sid in ("%s/%s" % (u, s) for u, ss in keep.items() for s in ss)
                    if sid not in tree.proofs and sid not in ceiling)
    unproved = sum(1 for sid in ceiling if sid not in tree.proofs)
    for rel in removed + dropped:
        _remove(tree, rel, out)
    for rel, text in sorted(writes.items()):
        with open(tree.path(rel), "w", encoding="utf-8") as f:
            f.write(text)
        if rel == LINT_EXCEPTIONS:
            print("rewrote %s without the exception(s) for %s, which the release does not carry"
                  % (LINT_EXCEPTIONS, ", ".join(exceptions[1])), file=out)
        else:
            print("wrote %s as the release has it" % rel, file=out)
    # the generated files were current before the cut, so a generated file its facts no longer produce (the
    # Characterise.v of a harness whose agreements all went, say) is one the cut left behind; the final render writes
    # the rest
    for rel in generate.existing_generated(root):
        if rel not in rendered:
            _remove(tree, rel, out)
    # the facts were loaded, and checked, with the findings in place: only now are they cut
    for f in files:
        p = tree.path(f.rstrip("/"))
        if os.path.isdir(p) and not os.path.islink(p):
            shutil.rmtree(p)
        else:
            os.remove(p)
    gone = []
    for rel in findings:
        if not os.path.lexists(tree.path(rel)):
            continue   # a held project's own folder, removed above, held it
        if os.path.isdir(tree.path(rel)):
            shutil.rmtree(tree.path(rel))
            gone.append(rel + "/")
        else:
            os.remove(tree.path(rel))
            gone.append(rel)
    gone += files
    for p in sorted(held.held):
        print("held back by a finding that is not public: %s" % p, file=out)
    for sid in sorted(held_ids):
        print("held back by an open finding: %s" % sid, file=out)
    for sid in absent:
        print("listed, but no proof in this checkout: %s" % sid, file=out)
    if unproved:
        print("%d statement(s) that enrollment entries list have no proof in this checkout (an enrollment entry is a "
              "ceiling)" % unproved, file=out)
    for unit in partial:
        print(PARTIAL % unit, file=out)
    print("oft release-tree: kept %d proof(s) of %d fuzz target(s); removed %d path(s) of proofs folders; removed %s; "
          "%d listed statement(s) with no proof" % (len(kept), len({os.path.dirname(k) for k in kept}), len(removed),
                                                   " and ".join(gone), len(absent)), file=out)
    rc = generate.run(root, out=out)
    if rc == 0:
        print("the cut's statements, for its CHANGELOG.md section: %s" % generate.counts_sentence(public),
              file=out)
    return rc
