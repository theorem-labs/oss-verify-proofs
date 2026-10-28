"""oft release-tree: turn a checkout into the files of a release.

approvals.yaml lists the proofs a release carries, by fuzz target and statement.  This
keeps the proof directory of each listed statement, with its fuzz target's whole lib/ and
build record (so a listed statement carries everything in that lib/), and removes every other
proof (a whole proofs/<project>/<harness>/ when none of its proofs is listed).

It leaves out what facts.hold holds back.  A project held whole (`release: private` in its
project.yaml, or a finding that holds it back) ships as a held project when OSS-Fuzz has it:
its project.yaml is rewritten to the held form (facts.held_form) and its page is rendered from
that, and everything else of it goes (the rest of projects/<p>/, counterexamples/<p>/,
patches/<p>/, notes/<p>.md; its proofs as unlisted ones).  A held page says only that the
project is held, so it tells a reader nothing the OSS-Fuzz issue does not.  A project held
whole that OSS-Fuzz does not have is removed whole.  An enrolled project (`enrolled: true`)
whose findings are all open keeps its page and its other statements, and only the statements
those findings break are held back (with each held agreement's bound and decidability
statements), with their proofs and counterexamples.  Either way
release.yaml carries the counts and oss_fuzz.projects of the cut, and an image_libraries
entry no remaining build links goes.  It
removes findings/ entirely (an undisclosed bug's record, reproducer and patch never ship),
and the files only this repository has (INTERNAL: approvals.yaml, .github/CODEOWNERS, the
facts review's workflow and its criteria, the two enrollment workflows and the tools/enroll/
directory they run, and the released-proof index's workflow and builder); it rewrites
tools/oft/lint-exceptions.yaml without each entry whose path
is at or under a path the cut removes (an entry left for it would be unused, and a lint
finding in the release; the lines above its `exceptions` key stay as written), and renders
the generated files again, so the statuses in the pages and the index say what the release
holds.  It reports a listed statement that has no proof in the checkout, each fuzz target
whose lib/ it keeps while removing some of its statement directories (that lib/ may hold
their proofs), and each file under proofs/lib/, which ships unchecked.  Everything else (the
facts, CHANGELOG.md among them, proofs/lib/, counterexamples/) is left as it is, so the
release's CHANGELOG section must describe only what the release carries.

It refuses, and changes nothing, when the facts have an error; the checkout holds a symbolic
link outside an ignored path (proofs/, .github/, .claude/ and tools/ themselves among them, as
the cut would remove through them), or a path the cut removes is one (an ignored one, such as
a held project's bin/, among them); a path under proofs/ is a stray file, or a kept statement
directory holds a file other than Proof.v, proof.yaml and its generated dune; git tracks a
file at an ignored path; the facts as the release will have them have an error; a file the
release keeps or writes, the rewritten lint-exceptions.yaml included, discloses what is held
back (disclosure); or the generated files are not current.  Every check runs before the first
change.  It rewrites the checkout in place: run it in a scratch checkout.
"""
import copy
import io
import os
import shutil
import subprocess
import sys

import yaml

from . import disclosure, facts, generate, paths, rules, yamlio

# what only this repository has: the list of the files that need judgement (CODEOWNERS), the automated facts review of a
# pull request and its criteria (the review runs on this repository's identity), and which proofs a release publishes;
# the pipeline that turns an enrollment into facts (enroll.yml, enroll-build.yml and the tools/enroll/ directory they
# run), which a reader of a proof never needs; and the released-proof index's workflow and builder, which push to this
# repository's branch proof-index
INTERNAL = ("approvals.yaml", ".github/CODEOWNERS", ".github/workflows/facts-review.yml",
            ".claude/skills/review-facts/SKILL.md", "review.md", ".github/workflows/enroll.yml",
            ".github/workflows/enroll-build.yml", "tools/enroll", ".github/workflows/proof-index.yml",
            ".github/proof-index.py")

# the files a kept statement directory may hold: its proof, its record, and the generated dune (paths.py)
STATEMENT_FILES = ("Proof.v", "proof.yaml", "dune")

PARTIAL = "kept the lib/ of %s, while removing some of its statement directories: that lib/ may hold their proofs"


def checkout_links(root):
    """Every symbolic link in root outside an ignored path (paths.ignored), before facts.load can read through one."""
    found = []
    for d, dirs, files in os.walk(root):
        rd = os.path.relpath(d, root)
        rd = "" if rd == "." else rd + os.sep
        found += [rd + n for n in dirs + files
                  if os.path.islink(os.path.join(d, n)) and not paths.ignored((rd + n).replace(os.sep, "/"))]
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


def cut_lint_exceptions(tree, cut):
    """(text, dropped paths): tools/oft/lint-exceptions.yaml without each entry whose path is at or under a path in
    cut, which the release does not carry (an entry left for it would be unused, and a finding in the public tree), and
    which may name what is held back.  Every line above the `exceptions` key (the leading comment, the schema) is kept
    as written; the list, and anything after it, is written again in the canonical form, so a comment among the
    entries is not kept (an entry's why belongs in its reason).  None when no entry is dropped."""
    p = tree.path(LINT_EXCEPTIONS)
    if not os.path.isfile(p):
        return None
    with open(p, encoding="utf-8") as f:
        text = f.read()
    data = yamlio.load(text, LINT_EXCEPTIONS)
    entries = data.get("exceptions") or []
    gone = [e["path"] for e in entries if _under(e["path"], cut)]
    if not gone:
        return None
    keys = yaml.compose(text, Loader=yamlio.StrictLoader).value
    line = next(k.start_mark.line for k, _ in keys if k.value == "exceptions")
    rest = {k.value: data[k.value] for k, _ in keys if k.start_mark.line >= line}
    rest["exceptions"] = [e for e in entries if not _under(e["path"], cut)]
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


def _plan(tree, keep):
    """(kept, removed, partial, stray) for a checkout with no symbolic link (checkout_links).  keep is {fuzz target:
    approved statements}.  kept and removed list paths under proofs/: a statement's proof directory, or a whole
    proofs/<project>/<harness>/ when none of its proofs is approved.  partial lists each fuzz target whose lib/ is kept
    while some of its statement directories are removed.  stray lists every file where only a directory belongs, and
    anything in a kept statement directory other than the files of STATEMENT_FILES."""
    kept, removed, partial, stray = [], [], [], []
    base = tree.path("proofs")
    for p in sorted(os.listdir(base)) if os.path.isdir(base) else []:
        if not os.path.isdir(tree.path("proofs", p)):
            stray.append("proofs/%s" % p)
            continue
        if p == "lib":
            continue
        for h in sorted(os.listdir(tree.path("proofs", p))):
            hd = os.path.join("proofs", p, h)
            entries = sorted(os.listdir(tree.path(hd))) if os.path.isdir(tree.path(hd)) else []
            bad = [os.path.join(hd, s) for s in entries if not os.path.isdir(tree.path(hd, s))]
            if not os.path.isdir(tree.path(hd)) or bad:
                stray += bad or [hd]
                continue
            proofs = [s for s in entries if s not in facts.PROOF_HARNESS_DIRS]
            approved = [s for s in proofs if s in keep.get("%s/%s" % (p, h), ())]
            if not approved:
                removed.append(hd)
                continue
            for s in approved:
                sd = os.path.join(hd, s)
                stray += [os.path.join(sd, f) for f in sorted(os.listdir(tree.path(sd)))
                          if f not in STATEMENT_FILES or not os.path.isfile(tree.path(sd, f))]
            kept += [os.path.join(hd, s) for s in approved]
            cut = [os.path.join(hd, s) for s in proofs if s not in approved]
            removed += cut
            if cut and os.path.isdir(tree.path(hd, "lib")):
                partial.append("%s/%s" % (p, h))
    return kept, removed, partial, stray


def shared_files(tree):
    """Every file under proofs/lib/, which any release carries unchecked."""
    base = tree.path("proofs", "lib")
    return sorted(os.path.relpath(os.path.join(d, f), tree.root)
                  for d, _, fs in os.walk(base) for f in fs) if os.path.isdir(base) else []


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
    keep = {}   # a fuzz target may have an entry per source: it keeps the union of their statements
    for e in tree.approvals["fuzz_targets"]:
        keep.setdefault(e["fuzz_target"], set()).update(e["statements"])
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
    held = facts.hold(tree)
    hidden = sorted(held.whole)
    held_ids = held.ids
    # the facts as the release will have them, checked before the first change; the cut decides which projects held
    # whole keep a held page
    shipped = {os.path.relpath(k, "proofs").replace(os.sep, "/") for k in kept}
    public = facts.load(root)
    held_page = facts.cut(public, shipped, held)
    # the one removal path: what a release leaves out of each project
    dropped = [os.path.join("projects", p) for p in hidden if p not in held_page]
    dropped += [os.path.join("projects", p, x) for p in held_page
                for x in sorted(os.listdir(tree.path("projects", p))) if x not in ("project.yaml", "README.md")]
    dropped += [rel for p in hidden for rel in (os.path.join("counterexamples", p),
                os.path.join("patches", p), os.path.join("notes", p + ".md"))]
    # a statement an open finding holds back takes its counterexample with it
    dropped += [os.path.join("counterexamples", *sid.split("/")) for sid in sorted(held_ids)]
    dropped = [rel for rel in dropped if os.path.lexists(tree.path(rel))]
    # checkout_links reads no ignored path (projects/<p>/bin/, a _build/), and the cut removes such a path of a held
    # project: a symbolic link there would stop rmtree after the first change, or take the cut out of the checkout
    linked = [rel for rel in removed + dropped if os.path.islink(tree.path(rel))]
    if linked:
        for rel in linked:
            print("error: %s: a symbolic link, which the cut could follow out of the checkout" % rel, file=out)
        print("oft release-tree: %d path(s) that are not plain directories or expected files; nothing changed"
              % len(linked), file=out)
        return 1
    files = [f for f in INTERNAL if os.path.lexists(tree.path(f))]
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
    exceptions = cut_lint_exceptions(tree, removed + dropped + files + ["findings"])
    if exceptions is not None:
        writes[LINT_EXCEPTIONS] = exceptions[0]
    rendered = generate.render_all(public)
    try:
        needles = disclosure.needles(tree, held)
    except facts.BoundedFileError as e:
        print("error: a holding finding's evidence cannot be read within its cap: %s" % e, file=out)
        print("oft release-tree: the evidence to search for is unreadable; nothing changed", file=out)
        return 1
    named = disclosure.search(root, needles, removed + dropped + files + list(writes) + ["findings"],
                              {**rendered, **writes})
    if named:
        for rel, label in named:
            print("error: %s names %s" % (rel, label), file=out)
        print("oft release-tree: %d disclosure(s) of what is held back in files the release keeps; nothing changed"
              % len(named), file=out)
        return 1
    # a stale rendering would fail only after the cut: find it first
    buf = io.StringIO()
    if generate.run(root, check=True, out=buf):
        out.write(buf.getvalue())
        print("oft release-tree: the generated files are not current (run ./oft generate); nothing changed", file=out)
        return 1
    # every check has passed: only now does anything change
    absent = sorted("%s/%s" % (u, s) for u, ss in keep.items() for s in ss if "%s/%s" % (u, s) not in tree.proofs)
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
    # the facts were loaded, and checked, with findings/ in place: only now is it cut
    for f in files:
        if os.path.isdir(tree.path(f)) and not os.path.islink(tree.path(f)):
            shutil.rmtree(tree.path(f))
        else:
            os.remove(tree.path(f))
    gone = files
    if os.path.isdir(tree.path("findings")):
        shutil.rmtree(tree.path("findings"))
        gone = ["findings/"] + files
    for p in sorted(held.held):
        print("held back by a finding that is not public: %s" % p, file=out)
    for sid in sorted(held_ids):
        print("held back by an open finding: %s" % sid, file=out)
    for sid in absent:
        print("listed, but no proof in this checkout: %s" % sid, file=out)
    for unit in partial:
        print(PARTIAL % unit, file=out)
    for f in shared_files(tree):
        print("carried unchecked, as every release carries proofs/lib/: %s" % f, file=out)
    print("oft release-tree: kept %d proof(s) of %d fuzz target(s); removed %d path(s) under proofs/; removed %s; "
          "%d listed statement(s) with no proof" % (len(kept), len({os.path.dirname(k) for k in kept}), len(removed),
                                                   " and ".join(gone), len(absent)), file=out)
    rc = generate.run(root, out=out)
    if rc == 0:
        print("the cut's statements, for its CHANGELOG.md section: %s" % generate.counts_sentence(public),
              file=out)
    return rc
