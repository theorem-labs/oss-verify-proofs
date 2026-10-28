"""./oft <command> ...  (see tools/oft/README.md)"""
import argparse
import os
import sys

from . import approvals, check, fetch, generate, ledger, lint, plan, release_tree, revisions


def _root(a):
    return os.path.abspath(a.root)


def _processes(s):
    """--jobs: a number of processes, 1 or more."""
    try:
        n = int(s)
    except ValueError:
        n = 0
    if n < 1:
        raise argparse.ArgumentTypeError("%r is not a number of processes (1 or more)" % s)
    return n


def cmd_generate(a):
    return generate.run(_root(a), check=a.check)


def cmd_lint(a):
    changed = None
    if a.changed:
        with open(a.changed, encoding="utf-8") as f:
            changed = [l.strip() for l in f if l.strip()]
    try:
        found = lint.run(_root(a), changed=changed, pr_kind=a.pr_kind, base=a.base, skeleton=a.skeleton,
                         release=a.release, changed_only=a.changed_only, jobs=a.jobs)
    except lint.ChangedOnlyError as e:
        print("FAIL oft lint --changed-only: %s" % e)
        return 1
    for f in found:
        print(f)
    print("oft lint: %d finding(s)" % len(found))
    return 1 if found else 0


def cmd_ledger(a):
    try:
        found = ledger.run(_root(a), a.base, a.tip)
    except ledger.LedgerError as e:
        print("FAIL %s" % e)
        return 1
    for f in found:
        print(f)
    print("oft ledger: %d finding(s)" % len(found))
    return 1 if found else 0


def cmd_fetch(a):
    return fetch.cli(_root(a), a)


def cmd_verify_sha(a):
    return fetch.verify_sha(_root(a), a.projects)


def cmd_check(a):
    return check.cli(_root(a), a)


def cmd_plan(a):
    units = None
    if a.units:
        with open(a.units, encoding="utf-8") as f:
            units = {l.strip() for l in f if l.strip()}
    if a.explain:
        return plan.explain(_root(a), a.explain, change=a.change, base=a.base, kind=a.pr_kind, tools=a.tools,
                            store=a.store, rocqchk=a.rocqchk)
    return plan.plan(_root(a), change=a.change, base=a.base, kind=a.pr_kind, tools=a.tools, store=a.store,
                     units=units, max_jobs=a.max_jobs, rocqchk=a.rocqchk)


def cmd_release_tree(a):
    return release_tree.run(_root(a))


def cmd_approvals(a):
    return approvals.write(_root(a), a.list, approved_by=a.approved_by, date=a.date)


def cmd_revisions(a):
    return revisions.run(_root(a), os.path.abspath(a.previous), write_pins=a.write_pins,
                         earlier=[os.path.abspath(p) for p in a.earlier])


def main(argv=None):
    p = argparse.ArgumentParser(prog="oft", description="the tools of oss-fuzz-theorems")
    p.add_argument("--root", default=".", help="the repository root (default: .)")
    sub = p.add_subparsers(dest="cmd", required=True)

    g = sub.add_parser("generate", help="render every generated file from the facts")
    g.add_argument("--check", action="store_true", help="compare instead of writing")
    g.set_defaults(fn=cmd_generate)

    li = sub.add_parser("lint", help="the repository's rules (tools/oft/README.md)")
    li.add_argument("--changed", help="a file listing the paths a pull request changes")
    li.add_argument("--base",
                    help="trusted base tree for finding-ledger deletions in a pull-request change")
    li.add_argument("--pr-kind", choices=["release", "maintainer", "contributor"], default="maintainer")
    li.add_argument("--skeleton", action="store_true",
                    help="accept a tree with no facts yet (no release.yaml, no projects/)")
    li.add_argument("--release", action="store_true",
                    help="what only a release must satisfy: no placeholder digest or commit (all zeros)")
    li.add_argument("--changed-only", metavar="BASE",
                    help="run the per-file text rules only over the files that differ from commit BASE, or over "
                         "every file when a fact (a file tools/oft/paths.py classes as facts), a finding's "
                         "finding.yaml, a .gitattributes, tools/oft/lint-exceptions.yaml or the running tools "
                         "differ from it (the rules over the whole tree still run); --root must be the top of a "
                         "git checkout")
    li.add_argument("--jobs", type=_processes,
                    help="processes for the per-file text rules, 1 or more (default: every CPU this process may "
                         "run on, for %d files or more to read)" % lint.PARALLEL_FILES)
    li.set_defaults(fn=cmd_lint)

    le = sub.add_parser("ledger", help="the findings ledger over a change's history: every record a commit had from "
                                       "its anchor on is in the tip, with its anchor's evidence")
    le.add_argument("--base", required=True, help="the commit the change is judged from (its history is BASE..TIP)")
    le.add_argument("--tip", default="HEAD", help="the commit judged (default: HEAD)")
    le.set_defaults(fn=cmd_ledger)

    f = sub.add_parser("fetch", help="download a project's binaries and check every SHA-256")
    fetch.add_arguments(f)
    f.set_defaults(fn=cmd_fetch)

    v = sub.add_parser("verify-sha", help="check fetched binaries against harness.yaml")
    v.add_argument("projects", nargs="+")
    v.set_defaults(fn=cmd_verify_sha)

    c = sub.add_parser("check", help="build and check statements, proofs and counterexamples")
    check.add_arguments(c)
    c.set_defaults(fn=cmd_check)

    pl = sub.add_parser("plan", help="the parts of units a CI run checks, as JSON for its job matrix")
    pl.add_argument("--change", default="HEAD",
                    help="the commit whose proofs/, counterexamples/ and findings/ are checked (default: HEAD)")
    pl.add_argument("--base", help="the commit the change is judged against: a part whose key is the base's is not "
                                   "checked (default: none, every part with no recorded pass is)")
    pl.add_argument("--pr-kind", choices=plan.KINDS, default="release",
                    help="the kind of change (pr.yml's KIND): for maintainer and contributor the statements are the "
                         "base's, as pr.yml's check job takes them (default: release, the change's own)")
    pl.add_argument("--tools", help="the commit of the tools the check jobs run (default: --base, else --change)")
    pl.add_argument("--store", help="a commit of the branch check-results; without it nothing is recorded")
    pl.add_argument("--units", metavar="FILE", help="only the units FILE lists, one per line")
    pl.add_argument("--max-jobs", type=int, default=20)
    pl.add_argument("--rocqchk", action="store_true", help="the check jobs run rocqchk")
    pl.add_argument("--explain", metavar="PROJECT/HARNESS",
                    help="print each part of one unit, whether it is checked and why, and every input of its key")
    pl.set_defaults(fn=cmd_plan)

    rt = sub.add_parser("release-tree", help="keep only the proofs approvals.yaml lists, in place, and render again")
    rt.set_defaults(fn=cmd_release_tree)

    ap = sub.add_parser("approvals", help="write approvals.yaml from the proofs of the fuzz targets a file lists")
    ap.add_argument("list", metavar="FILE",
                    help="one <project>/<harness> per line, then a tab and the review record for a submission")
    ap.add_argument("--approved-by", required=True, help="the GitHub login of who approves the entries")
    ap.add_argument("--date", required=True, help="the date of the approval, YYYY-MM-DD")
    ap.set_defaults(fn=cmd_approvals)

    r = sub.add_parser("revisions", help="each statement's revision and proof against the previous release")
    r.add_argument("previous", help="a checkout of the previous release")
    r.add_argument("--write-pins", action="store_true",
                   help="set the pin of each proof that carries forward to its statement's fingerprint here")
    r.add_argument("--earlier", nargs="+", default=[], metavar="OLDER",
                   help="checkouts of the releases before the previous one, strictly newest first (by date, then by "
                        "release): a statement the previous release left out (held or private) is compared with the "
                        "newest of them that has it")
    r.set_defaults(fn=cmd_revisions)

    a = p.parse_args(argv)
    return a.fn(a)


if __name__ == "__main__":
    # `oft check` reports each step as it finishes, and a CI job cut off at its time limit keeps only what was written
    # out by then. With no terminal (a container, a pipe) Python buffers output in blocks, so every line is written as
    # it is printed instead.
    sys.stdout.reconfigure(line_buffering=True)
    sys.stderr.reconfigure(line_buffering=True)
    sys.exit(main())
