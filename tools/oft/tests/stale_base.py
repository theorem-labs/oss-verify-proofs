"""Whether the base branch moved, since this run was built, by a change the run's own checks read from it.

    PYTHONPATH=<tools> GH_TOKEN=<read token>
    python3 -m oft.tests.stale_base --repo <owner/name> --base-ref <branch> [--root <dir>]

pr.yml's required job runs the BASE's copy of it (its step for a base that moved under a run), as every other
judging step of that workflow runs the base's tools: a change's own copy must not decide whether that change may
merge.  It is under tools/oft/tests/, beside parallel.py, which is a runner and no test either, because
keys.NOT_THE_CHECKER names oft/tests/ and nothing else would hold it: a file anywhere else under tools/ is the checker,
whose id is in every unit's key, and a new file under .github/ needs a row in paths.py, which is the checker too.
So this file, and a change to it, re-check no fuzz target.

It imports layout.py and nothing else of the package.  It cannot import keys.py, although that is where the facts
it mirrors are defined: keys.py imports yaml, and the required job installs no dependency -- it is a bare python3
over a sparse checkout of tools/oft, unlike plan, lint and tests, which each run `pip install --require-hashes`.
Where a constant of keys.py is restated here (the dune file names), test_stale_base measures that the two agree.

A pull request run of pr.yml checks the merge commit GitHub built when the run started, refs/pull/<n>/merge, and
judges it with what that merge's first parent -- the base as it was then -- holds: the base's tools run the plan, the
lint and the check, the base's .github/actions/ run inside the jobs, and the base's facts are the statements a proof
is checked against.  (pr.yml itself is the merge commit's copy, as GitHub runs a pull request's workflow; a base
change to it is in the merge that lands and in the next run.)  When the base then takes such a change, the run's
green says nothing about what merging now would do: measured on this repository's pull request #438, whose tools'
tests passed on the base before #416 and failed on the line after it.  Nothing re-runs the checks: a pull request
into a branch with no merge queue merges on the verdict of its own run.

So this script compares two commits:

  the base the verdict was made on  the first parent of HEAD (the merge commit of a pull request)
  the tip of the base branch now    repos/<owner/name>/git/ref/heads/<branch>, read through gh

and names every path they differ in that the checks read from the base (FEEDS_THE_CHECKS and THE_FACTS, below).
It prints what it found, appends it to $GITHUB_STEP_SUMMARY when that is set, and exits

  0  the base has not moved, or moved only in paths no check of this run reads: the files another change brings
     (layout.is_change: its proofs, counterexamples, findings and unpatched pins, in both layouts), the facts of
     another fuzz target or project (THE_FACTS) -- both only for fuzz targets and projects this change does not
     touch, and the facts only while this run did not read the whole tree (--whole-tree) -- and the pages
     `oft generate` renders
  1  the base moved in a path the checks read: this run's verdict is about a base that is gone
  2  it could not tell: gh could not answer, the answer was not what it must be, or the base branch no longer holds
     the commit the verdict was made on (a force push).  A run that cannot tell fails: a silent pass here would be
     the very green this script exists to refuse.

It reads the two trees with git, not through the compare API, whose file list stops at 300 files: a render of the
shared generated files touches more than that, and a truncated list would hide the one tools/ file after it.  The
commits themselves are named from the compare API, which this script needs anyway to see that the base branch still
holds the commit the run was built on.
"""
import argparse
import json
import os
import re
import subprocess
import sys

from .. import layout

# What a run of pr.yml takes from its base to judge a change.  Each row is a path pattern, anchored at the start of
# the path, and the name this script calls it by.  The set is pr.yml's own: the plan, lint and check jobs run
# `PYTHONPATH=base/tools` and the base's tools/oft/ci scripts, and each job runs the base's copy of
# .github/actions/; the reach step runs the tools' tests for a change under tools/ or .github/ and the controls for
# one under theories/, tests/ or toolchain/, for any dune file, or for a release.yaml that names another image;
# the tools' tests themselves open .claude/skills/review-facts/SKILL.md (test_facts_review_scripts); and keys.py
# holds the facts (projects/, theories/, toolchain/allowed-axioms.txt, dune-project), the images release.yaml
# pins, the checker (tools/) and the checkout attributes of every file it keys.
# CHANGELOG.md and NOTICE are the only files paths.py calls facts that no row below names: no job of a run reads
# either, while lint.read_by_every_verdict takes every facts path, "wider on purpose, a margin".
FEEDS_THE_CHECKS = (
    # the tools every job runs from the base: `oft plan`, `oft lint`, `oft check` and the ci scripts the check job runs
    (r"tools/", "the tools"),
    # the enrollment scripts, whose tests the tools' tests job runs (test_enroll_tools) and whose check.sh the
    # enrollment's facts job runs against this base: tools/enroll/ until they moved (OSSV-276)
    (r"dev/enroll/", "the tools"),
    # the shared actions each job runs from the base, and this workflow, which a pull request runs as its merge
    # commit has it: a base change to it is in the merge that lands and in every run after this one
    (r"\.github/", "the workflows"),
    # the skills the tools' tests read (pr.yml's reach step)
    (r"\.claude/", "the tools"),
    # the checker and runner Dockerfiles, lps-core.paths, and the axiom allowlist every proof is judged against
    (r"toolchain/", "the toolchain"),
    # the Rocq core every statement and every proof compiles against
    (r"theories/", "the statements"),
    # the controls: tests/check.sh and the theories they build
    (r"tests/", "the controls"),
    # the checker and runner images every check runs in (keys.images)
    (r"release\.yaml\Z", "the pinned images"),
    # every dune file a build reads (layout.DUNE_FILES): dune-project, dune-workspace, dune-file, and the dune of a
    # directory a check compiles
    (r"(?:.*/)?dune(?:-project|-workspace|-file)?\Z", "the statements"),
    # (a .gitattributes is read before these: ATTRIBUTES, below; a fuzz target's facts and a project's own files
    # after them: THE_FACTS)
)

# The facts of one fuzz target -- its Statements.v, Characterise.v, Distribution.v, Images.v, Symbols.v, source/ and
# symbols/ -- and the files of one project -- project.yaml, every fuzz target's harness.yaml, unpatched.yaml and
# patches/.  These are not read by every run: the check of fuzz target X reads X's own facts and its project's files,
# and nothing of fuzz target Y but Y's harness.yaml, which keys._project digests with the project (PROJECT_LEVEL).  So
# a move of the base that brings them is read only when
#
#   they belong to a fuzz target or a project this change itself touches (owned_by_this_change), where the merged
#   tree would carry a key neither run checked; or
#
#   this run read the whole tree: the tools' tests, and with them the whole-tree lint, ran (pr.yml's reach step,
#   repository_lint and tests), and then a change anywhere in the base's facts can change what they found.
#
# Counted as read by every run instead, one statements pull request would fail `required` on every open pull
# request: #427 brought the statements of five projects, and #461 is to touch 159 fuzz targets.
# One coupling it passes over: `oft lint` judges every file's links against the URLs of EVERY project's facts and
# findings (lint.fact_urls, which scan_file takes as `known`), so a base move that REMOVES a URL from another
# project's facts could turn a link in this change's own file from accepted to refused in the merged tree.  It is
# accepted: the move this narrowing is about adds facts, which only widens `known`; a contrib file's links outside
# its own project's facts are public repositories the tools' own lists accept, not `known`; and the next pull
# request's whole-tree lint finds it.
THE_FACTS = (r"projects/", r"patches/")

# What a move of the base may touch while this run's verdict still holds, read before FEEDS_THE_CHECKS:
#
#   the files a change brings, which layout.is_change names in both layouts -- another change's proofs,
#   counterexamples, findings and a project's unpatched pins -- for a fuzz target this change does not itself touch.
#   Its own run checked them, and they are in no key of this change's parts.  Where the two meet, they are not: a
#   part's key holds the unit's whole proofs folder (keys.py), so a base that took another change to a fuzz target
#   this one also changes leaves the merged tree with a key neither run checked, and that is a failure
#   (owned_by_this_change, below).  The repository's own definition is used, and not a pattern of this file, so that
#   a layout move cannot leave the two disagreeing (test_stale_base.TheRule measures the agreement);
#
#   a project's page and a fuzz target's page, which `oft generate` renders and no check opens
#   (test_keys.Checker measures that: no file of a check's reads is a README.md under projects/).  Every merge of a
#   proof renders them, so without this row the step would fail every pull request open while a proof lands.  The
#   project page is also one of the shared generated files (paths.SHARED) that .github/workflows/index.yml renders
#   after each merge; the other shared generated files (README.md, index/, analyses/) match no row of
#   FEEDS_THE_CHECKS, and so need no row here.
RENDERED_PAGES = re.compile(r"projects/[^/]+(?:/[^/]+)?/README\.md\Z")

# A .gitattributes decides the bytes git checks out for every file under it (line ends, encoding, filters), which
# every key holds (keys.CHECKOUT_ATTRIBUTES) and which `oft lint` reads for every file's verdict
# (lint.read_by_every_verdict).  One inside a change's own folders -- proofs/.gitattributes -- changes what a check
# compiles just as a root one does, so it is read before the files a change brings.
ATTRIBUTES = re.compile(r"(?:.*/)?\.gitattributes\Z")

_FEEDS = tuple((re.compile(p), what) for p, what in FEEDS_THE_CHECKS)
_THE_FACTS = re.compile("|".join(THE_FACTS))
# How many paths, and how many commits, the message names before it counts the rest: the error line is read in one
# glance beside a red check, the step summary carries every path the rule matched.
SHOWN = 10
SHOWN_COMMITS = 5


class CannotTell(Exception):
    """Neither answer can be given: the script exits 2 and the run fails."""


def feeds_the_checks(path, units=(), projects=(), whole_tree=False):
    """What the checks read the path as, or None when a change to it leaves this run's verdict standing.

    units and projects are what this change itself brings files for (own_units): a file of one of those fuzz
    targets or projects is read, whoever brought it.  whole_tree says this run read every file of the tree (the
    tools' tests and the whole-tree lint ran: pr.yml's reach step), and then the facts of any fuzz target are read
    as well.
    """
    if ATTRIBUTES.match(path):
        return "the checkout attributes"
    if layout.is_change(path):
        return owned_by_this_change(path, units, projects)
    if RENDERED_PAGES.match(path):
        return None
    for pattern, what in _FEEDS:
        if pattern.match(path):
            return what
    if _THE_FACTS.match(path):
        return owned_by_this_change(path, units, projects) or ("the statements" if whole_tree else None)
    return None


# The top-level folders under which a path belongs to one project: everything else (tools/, .github/, theories/)
# names no project, and must not give one its second segment.
OF_A_PROJECT = ("projects", "proofs", "counterexamples", "findings", "patches")

# The files of a project that every fuzz target of it is checked with, by their name.  keys._project digests
# projects/<p>/project.yaml and every projects/<p>/<h>/harness.yaml into one id, and that id is a component of
# every part of every unit of the project, so a sibling fuzz target's harness.yaml is read by them all.  A
# project's unpatched pins are the same: the findings part of each unit holds them.
# test_stale_base discovers what keys._project digests from keys itself and holds this list to it.
PROJECT_LEVEL = ("project.yaml", "harness.yaml", "unpatched.yaml")


def unit_and_project(path):
    """(the fuzz target, the project) a path belongs to, either None.  layout.unit_of reads both layouts and every
    file of a fuzz target: its proofs, counterexamples and findings, and its statement folder.  A file every fuzz
    target of the project is checked with -- PROJECT_LEVEL, and the project's patches -- has a project and no fuzz
    target, so that it is read whichever of them the change touches."""
    parts = path.split("/")
    if len(parts) < 2 or parts[0] not in OF_A_PROJECT:
        return None, None
    if parts[-1] in PROJECT_LEVEL:
        return None, parts[1]
    return layout.unit_of(path), parts[1]


def owned_by_this_change(path, units, projects):
    """What this change reads a file another change brings as, or None when the two touch no fuzz target and no
    project in common.  `units` are the fuzz targets this change brings files for; `projects` are the projects
    whose own files it brings -- project.yaml, unpatched.yaml, patches/ -- which every fuzz target of the project
    is checked with (keys.py: the findings key of a unit holds its project's files).  So:

      a file of a fuzz target   is read when that fuzz target is one of this change's, or when this change carries
                                its project's own files
      a project's own file      is read when this change carries that project's own files, or any file of one of
                                its fuzz targets
    """
    unit, project = unit_and_project(path)
    if unit is not None:
        if unit in units:
            return "this change's own fuzz target %s" % unit
        return "this change's own project %s" % project if project in projects else None
    if project is None:
        return None
    if project in projects or project in {u.split("/")[0] for u in units}:
        return "this change's own project %s" % project
    return None


def own_units(root, base):
    """(the fuzz targets, the projects) this change itself brings files for: the diff from the base the verdict was
    made on to the merge commit, which is this pull request's own diff.  Every path counts, not only the ones
    layout.is_change names: a change that carries a fuzz target's facts (its harness.yaml, Statements.v or source/)
    owns that fuzz target as surely as one that carries its proofs, since a part's key holds both.  A path with no
    fuzz target of its own gives its project, which stands for every fuzz target of it."""
    units, projects = set(), set()
    for path in changed_paths(root, base, "HEAD"):
        unit, project = unit_and_project(path)
        if unit is not None:
            units.add(unit)
        elif project is not None:
            projects.add(project)
    return units, projects


def git(root, *args, check=True):
    done = subprocess.run(["git", "-C", root, *args], capture_output=True, text=True)
    if check and done.returncode != 0:
        raise CannotTell("git %s: %s" % (" ".join(args), done.stderr.strip() or done.stdout.strip()))
    return done


def gh_json(endpoint, what):
    """`gh api <endpoint>`, parsed.  Any failure is a CannotTell naming the endpoint and what it was for."""
    done = subprocess.run(["gh", "api", endpoint], capture_output=True, text=True)
    if done.returncode != 0:
        raise CannotTell("gh api %s (%s) failed: %s" % (endpoint, what, done.stderr.strip() or done.stdout.strip()))
    try:
        return json.loads(done.stdout)
    except ValueError as e:
        raise CannotTell("gh api %s (%s) answered no JSON: %s" % (endpoint, what, e))


SHA = re.compile(r"[0-9a-f]{40}\Z")


def base_of_the_run(root):
    """The commit the run was built on: the first parent of HEAD, which must be the merge commit GitHub builds for a
    pull request.  It is read from the commit object itself, as pr.yml's base steps read it: a commit names its
    parents even in a clone one commit deep, while `git rev-parse HEAD^1` there answers nothing, since .git/shallow
    hides a shallow commit's parents (measured on a --depth=1 fetch of refs/pull/<n>/merge).  The parent's own
    object is not in such a clone, which is what fetch() is for."""
    body = git(root, "cat-file", "-p", "HEAD").stdout
    parents = [line.split(None, 1)[1].strip() for line in body.splitlines() if line.startswith("parent ")]
    if len(parents) != 2 or not all(SHA.match(p) for p in parents):
        raise CannotTell("HEAD has %d parent(s), not 2: it is not the merge commit GitHub builds for a pull request"
                         % len(parents))
    return parents[0]


def tip_of(repo, base_ref):
    """The commit the base branch is at now."""
    ref = gh_json("repos/%s/git/ref/heads/%s" % (repo, base_ref), "the tip of %s" % base_ref)
    tip = ref.get("object", {}).get("sha") if isinstance(ref, dict) else None
    if not isinstance(tip, str) or not SHA.match(tip):
        raise CannotTell("repos/%s/git/ref/heads/%s named no commit (%r)" % (repo, base_ref, tip))
    return tip


def commits_between(repo, base, tip):
    """[(sha, subject)] of the commits the base branch took after base, and how many there are.  It refuses a base
    branch that no longer holds base: then this run was built on a commit the branch has dropped."""
    cmp = gh_json("repos/%s/compare/%s...%s?per_page=%d" % (repo, base, tip, SHOWN * 10),
                  "the commits %s took after %s" % (repo, base[:7]))
    status = cmp.get("status") if isinstance(cmp, dict) else None
    if status not in ("identical", "ahead"):
        raise CannotTell("the base branch is %r against %s, the commit this run was built on: it no longer holds that "
                         "commit (a force push), so nothing can say what moved" % (status, base[:7]))
    total = cmp.get("total_commits", 0)
    named = [(c.get("sha", "?"), (c.get("commit", {}).get("message") or "").splitlines()[:1])
             for c in cmp.get("commits", [])]
    return [(sha, line[0] if line else "") for sha, line in named], total


def changed_paths(root, base, tip):
    """Every path the two commits differ in, read from the trees themselves."""
    out = git(root, "-c", "core.quotePath=false", "diff", "--no-renames", "--name-only", "-z", base, tip).stdout
    return [p for p in out.split("\0") if p]


def have_locally(root, commit):
    """Whether the commit and its tree are both here already (a checkout that needs no fetch: the tests')."""
    return git(root, "cat-file", "-e", commit + "^{tree}", check=False).returncode == 0


def fetch(root, *commits):
    """Bring the commits, with their trees and no blob: the diff below reads the trees alone.  A shallow checkout
    (what actions/checkout makes) takes each as its own root, so no history of the base branch is downloaded.  A
    repository with no origin to fetch from is fine as long as it already holds what is wanted."""
    shallow = git(root, "rev-parse", "--is-shallow-repository").stdout.strip() == "true"
    depth = ["--depth=1"] if shallow else []
    if git(root, "fetch", "--no-tags", "--filter=blob:none", *depth, "origin", *commits,
           check=False).returncode == 0:
        return
    missing = [c for c in commits if not have_locally(root, c)]
    if missing:
        raise CannotTell("%s could not be fetched, and %s is not in this checkout"
                         % (", ".join(c[:7] for c in commits), ", ".join(c[:7] for c in missing)))


def say(message, summary=True):
    print(message, flush=True)
    path = os.environ.get("GITHUB_STEP_SUMMARY")
    if summary and path:
        with open(path, "a", encoding="utf-8") as f:
            f.write(message + "\n")


def named(items, most=SHOWN, total=None):
    """The first `most` of items, then a count of the rest.  `total` says how many there are when `items` is itself
    a page of them: a compare answers at most 100 commits a page, while it counts them all."""
    whole = len(items) if total is None else max(total, len(items))
    shown = ", ".join(items[:most])
    return shown if whole <= most else "%s and %d more" % (shown, whole - min(most, len(items)))


def judge(root, repo, base_ref, base, tip, units, projects, when, whole_tree):
    """(exit code, [(message, to the step summary)]) for one comparison of base with tip.  It prints nothing: a
    pass is only told once the base has been read again and is still at tip (run, below).  `when` names the moment
    the verdict belongs to, for the message."""
    if tip == base:
        return 0, [("the base %s is still at %s, the commit the verdict was made on" % (base_ref, base[:7]), False)]
    commits, total = commits_between(repo, base, tip)
    fetch(root, base, tip)
    paths = changed_paths(root, base, tip)
    read = [(p, what) for p, what in ((p, feeds_the_checks(p, units, projects, whole_tree)) for p in paths) if what]
    if not read:
        return 0, [("the base %s moved from %s to %s (%d commit(s), %d path(s)), and no check of this run reads any "
                    "of those paths: other fuzz targets' contributions, the pages a merge renders, and files no job "
                    "opens" % (base_ref, base[:7], tip[:7], total, len(paths)), False)]
    moved = named(["%s %s" % (sha[:7], subject) for sha, subject in commits], SHOWN_COMMITS, total)
    # the classes of path it read, in the order FEEDS_THE_CHECKS names them, so that the error line says what moved
    order = [what for _p, what in FEEDS_THE_CHECKS] + ["the checkout attributes"]
    kinds = sorted({what for _p, what in read}, key=lambda w: (order.index(w) if w in order else len(order), w))
    return 1, [
        ("::error::the base moved by a change to %s since %s: %d commit(s) on %s after %s (%s); "
         "push or re-run" % (" and ".join(kinds), when, total, base_ref, base[:7], moved), False),
        ("the base %s moved from %s to %s and the checks read %d of the path(s) it changed: %s. The verdict was "
         "made against %s, which the base no longer is, so its green says nothing about merging now. "
         "Push to the pull request, or re-run all jobs, to judge this head against %s."
         % (base_ref, base[:7], tip[:7], len(read), ", ".join("%s (%s)" % (p, what) for p, what in read), base[:7],
            tip[:7]), True)]


# How many times the comparison is made again when the base moves while it runs.  A pass must rest on a tip the base
# still had when the comparison ended: the ref is read again after it, and a comparison of a tip the base has already
# left could pass over a change the new tip brings.  A failure needs no such care -- the base moved under this run
# either way.
ROUNDS = 3


def run(root, repo, base_ref, whole_tree=False):
    base = base_of_the_run(root)
    fetch(root, base)
    units, projects = own_units(root, base)
    tip = tip_of(repo, base_ref)
    when = "this run started"
    for _ in range(ROUNDS):
        code, lines = judge(root, repo, base_ref, base, tip, units, projects, when, whole_tree)
        after = tip if code else tip_of(repo, base_ref)
        if after == tip:
            for message, summary in lines:
                say(message, summary=summary)
            return code
        tip = after
    raise CannotTell("the base %s moved again every time this step compared it (%d times, last to %s): nothing it "
                     "read is the base this change would merge into" % (base_ref, ROUNDS, tip[:7]))


def main(argv=None):
    p = argparse.ArgumentParser(prog="python3 -m oft.tests.stale_base", description=__doc__.splitlines()[0])
    p.add_argument("--root", default=".", help="the checkout of the merge commit this run was built on (default: .)")
    p.add_argument("--repo", required=True, help="owner/name of the repository")
    p.add_argument("--base-ref", required=True, help="the branch the pull request is into")
    p.add_argument("--whole-tree", action="store_true",
                   help="this run read every file of the tree (the tools' tests and the whole-tree lint ran: "
                        "pr.yml's reach step), so the facts of any fuzz target are read, not only this change's")
    args = p.parse_args(argv)
    try:
        return run(args.root, args.repo, args.base_ref, args.whole_tree)
    except CannotTell as e:
        say("::error::whether the base moved since this run started cannot be told, so this run cannot be trusted: "
            "%s" % e, summary=False)
        return 2


if __name__ == "__main__":
    sys.exit(main())
