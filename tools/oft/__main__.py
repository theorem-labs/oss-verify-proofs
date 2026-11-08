"""./oft <command> ...  (see tools/oft/README.md)"""
import argparse
import os
import re
import sys

# The packages tools/oft/requirements.txt pins are no part of the interpreter: ./oft runs with the ones the
# environment has, else in a virtual environment of its own that it builds once from that file (./oft, and
# tools/oft/README.md).  Where it reaches a missing one anyway, the run must say which requirement it is and
# where it was looked for.  `oft lint` imports idna only to map a host, and does it in a worker process
# (lint.forked_map), which re-raises it here: a bare ModuleNotFoundError there named neither.
# {import name: the distribution requirements.txt pins}; tools/oft/tests/test_wrapper.py holds it to that file.
REQUIREMENTS = {"idna": "idna", "yaml": "PyYAML"}


def _missing_requirement(e):
    """The message for a ModuleNotFoundError about a pinned requirement: the requirement, the line of
    requirements.txt that pins it, every directory that was looked in, and the two ways to install it.  None for an
    error about anything else, which is a fault of the tools and must keep its traceback."""
    named = e.name
    if not named:
        # an exception that came back from a worker process without its name attribute (concurrent.futures)
        found = re.search(r"No module named '([^']+)'", str(e))
        named = found.group(1) if found else ""
    top = named.split(".")[0]
    if top not in REQUIREMENTS:
        return None
    dist = REQUIREMENTS[top]
    req = os.path.join(os.path.dirname(os.path.abspath(__file__)), "requirements.txt")
    pin = None
    try:
        with open(req, encoding="utf-8") as f:
            pin = next((l.rstrip().rstrip("\\").rstrip() for l in f
                        if re.match(r"%s\s*==" % re.escape(dist), l, re.I)), None)
    except OSError:
        pass
    said = ["oft: the pinned requirement %s is not installed: `import %s` found nothing." % (dist, top)]
    if pin:
        said.append("%s pins it as `%s`." % (req, pin))
    said.append("Looked in:")
    said += ["  %s%s" % (p or os.getcwd(), "" if os.path.isdir(p or os.getcwd()) else "   (no such directory)")
             for p in sys.path]
    said += ["Install it in one of the two ways ./oft reads (tools/oft/README.md):",
             "  - have `uv` on PATH and run ./oft again: it builds the pinned environment once, under "
             "${OFT_VENV_ROOT:-${XDG_CACHE_HOME:-$HOME/.cache}/oft-venv}, and every later run reuses it with no "
             "network. Building it needs a network once.",
             "  - or install the pinned packages yourself and put them on PYTHONPATH:",
             '      python3 -m pip install --require-hashes --target "$HOME/oft-pydeps" -r '
             "tools/oft/requirements.txt",
             '      PYTHONPATH="$HOME/oft-pydeps" ./oft ...']
    return "\n".join(said)


try:
    from . import (approvals, change_ledger, check, check_run, classify, contracts, fetch, generate, ledger, lint,
                   lps_impact, nsrename, plan, port, prove, release_tree, revisions, schema, symbols)
except ModuleNotFoundError as _e:
    _said = _missing_requirement(_e)
    if _said is None:
        raise
    sys.exit(_said)


def _root(a):
    return os.path.abspath(a.root)


# --jobs: a number of processes, 1 or more.  One definition, in lps_impact, which every subcommand's --jobs and
# --proof-jobs take their type from.
_processes = lps_impact.positive("number of processes")


def _gib(s):
    """--max-rss-gib: a number of GiB above 0."""
    try:
        n = float(s)
    except ValueError:
        n = 0
    if not n > 0:
        raise argparse.ArgumentTypeError("%r is not a number of GiB above 0" % s)
    return n


def _post_check(s):
    """--post-check and --post-check-optional: OWNER/REPO@SHA, a GitHub repository and the full id of a commit of it,
    as (repository, id)."""
    got = check_run.target(s)
    if got is None:
        raise argparse.ArgumentTypeError("not OWNER/REPO@SHA, a GitHub repository and the full commit id (40 "
                                         "lower-case hex digits) of its pull request's head: %r" % s)
    return got


def _pull_request(s):
    """--pull-request: the URL of a pull request on GitHub (check_run.PULL_REQUEST)."""
    if check_run.PULL_REQUEST.fullmatch(s) is None:
        raise argparse.ArgumentTypeError("not https://github.com/OWNER/REPO/pull/N: %r" % s)
    return s


def cmd_generate(a):
    return generate.run(_root(a), check=a.check, shared=a.shared)


def cmd_lint(a):
    changed = None
    if a.changed:
        with open(a.changed, encoding="utf-8") as f:
            changed = [l.strip() for l in f if l.strip()]
    pending, expired = [], []
    try:
        found = lint.run(_root(a), changed=changed, pr_kind=a.pr_kind, base=a.base, skeleton=a.skeleton,
                         release=a.release, changed_only=a.changed_only, jobs=a.jobs, pending=pending,
                         max_rss_gib=a.max_rss_gib, pending_base=a.pending_base, expired=expired)
    except lint.ChangedOnlyError as e:
        print("FAIL oft lint --changed-only: %s" % e)
        return 1
    except lint.ResourceStop as e:
        print("FAIL %s" % e)
        return lint.MAX_RSS_EXIT
    for f in found:
        print(f)
    # the licence findings of the fuzz targets that lint-exceptions.yaml lists as licence-pending: reported, not
    # failed; one line per fuzz target with its count (a whole tree has tens of thousands), each one with --list-pending
    if a.list_pending:
        for f in pending:
            print("pending %s" % f)
    else:
        for unit, n in lint.pending_by_unit(pending):
            print("pending %s: %d licence finding(s) (--list-pending prints each)" % (unit, n))
    # an expired licence-pending entry that this change does not touch: a warning, here and on GitHub's checks page
    for f in expired:
        print("expired %s" % f)
        print("::warning file=%s::%s" % (f.where, f.msg))
    summary = "oft lint: %d finding(s)" % len(found)
    if pending:
        summary += "; %d pending licence finding(s) in %d unit(s) that %s lists, which do not fail" % (
            len(pending), len({lint.finding_unit(f) for f in pending}), lint.EXCEPTIONS)
    if expired:
        summary += ("; %d expired licence-pending entr(ies) that this change does not touch, which do not fail"
                    % len(expired))
    print(summary)
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
    if a.contracts:
        ignored = [flag for flag, given in (("--pr-kind", a.pr_kind != "release"), ("--tools", a.tools),
                                            ("--store", a.store), ("--units", a.units), ("--rocqchk", a.rocqchk))
                   if given]
        if ignored:
            print("oft plan: --contracts reads only --change and --base, not %s" % ", ".join(ignored),
                  file=sys.stderr)
            return 2
        return contracts.run(_root(a), a.contracts, change=a.change, base=a.base)
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


def cmd_port_layout(a):
    return port.layout_cli(_root(a), commit=a.commit, dry_run=a.dry_run, out=sys.stdout)


def cmd_port_branch(a):
    return port.port_branch(_root(a), a.branch, os.path.abspath(a.worktree), layout_commit=a.layout_commit,
                            namespace_commit=a.namespace_commit, onto=a.onto, out=sys.stdout)


def cmd_rename_namespace(a):
    if a.verify:
        if a.to or a.opam_stem or a.check:
            print("oft rename-namespace: --verify takes no --to, --opam-stem or --check", file=sys.stderr)
            return 1
        try:
            return nsrename.verify_cli(_root(a), a.verify[0], a.verify[1], jobs=a.jobs, out=sys.stdout)
        except nsrename.Error as e:
            print("oft rename-namespace --verify: %s" % e, file=sys.stderr)
            return 1
    if not a.to or not a.opam_stem:
        print("oft rename-namespace: --to NAME and --opam-stem STEM, or --verify A B", file=sys.stderr)
        return 1
    return nsrename.rename_tree(_root(a), a.to, a.opam_stem, check=a.check, jobs=a.jobs, out=sys.stdout)


def cmd_approvals(a):
    return approvals.write(_root(a), a.list, approved_by=a.approved_by, date=a.date)


def cmd_lps_impact(a):
    return lps_impact.cli(_root(a), a)


def cmd_revisions(a):
    return revisions.run(_root(a), os.path.abspath(a.previous), write_pins=a.write_pins,
                         earlier=[os.path.abspath(p) for p in a.earlier], out=sys.stdout,
                         write_revisions=a.write_revisions, repin_changed=a.repin_changed)


def cmd_symbols(a):
    return symbols.run(_root(a), a.unstripped, a.stripped, a.lines, a.harness, a.build, out=sys.stdout)


def cmd_classify(a):
    return classify.run(a.base, a.head, a.json, out=sys.stdout)


def cmd_prove(a):
    posts = ([(repo, sha, False) for repo, sha in a.post_check]
             + [(repo, sha, True) for repo, sha in a.post_check_optional])
    token = None
    if posts:
        if not os.environ.get("GH_TOKEN"):
            print("FAIL oft prove: %s needs a token in GH_TOKEN" % ("--post-check" if a.post_check
                                                                    else "--post-check-optional"))
            return 1
        try:
            token = check_run.Token(os.environ["GH_TOKEN"])
        except ValueError:
            print("FAIL oft prove: GH_TOKEN holds whitespace, a control character or a non-ASCII character; it is not "
                  "shown")
            return 1
    r = prove.run(_root(a), a.unit, a.base, a.head, a.json, out=sys.stdout)
    if r is None:
        return 1
    if not posts:
        return 0
    sys.stdout.flush()   # the report comes before the lines about its check runs, in a log that holds both
    return check_run.run(r, posts, token, os.environ.get("GITHUB_API_URL") or check_run.API, err=sys.stderr,
                         pull_request=a.pull_request)


def cmd_change_ledger(a):
    return change_ledger.cli(_root(a), a, out=sys.stdout)


def main(argv=None):
    p = argparse.ArgumentParser(prog="oft", description="the tools of oss-fuzz-theorems")
    p.add_argument("--root", default=".", help="the repository root (default: .)")
    sub = p.add_subparsers(dest="cmd", required=True)

    g = sub.add_parser("generate", help="render every generated file from the facts")
    g.add_argument("--check", action="store_true", help="compare instead of writing")
    # the shared generated files (tools/oft/paths.py SHARED) are rendered from the whole tree: the line's render
    # after each merge owns them, so a pull request neither carries nor compares them
    scope = g.add_mutually_exclusive_group()
    scope.add_argument("--skip-shared", dest="shared", action="store_const", const=False, default=None,
                       help="leave the shared generated files (tools/oft/paths.py SHARED) to the line's render")
    scope.add_argument("--shared-only", dest="shared", action="store_const", const=True,
                       help="render the shared generated files alone, as the line's render after a merge does")
    g.set_defaults(fn=cmd_generate)

    li = sub.add_parser("lint", help="the repository's rules (tools/oft/README.md)")
    li.add_argument("--changed", help="a file listing the paths a pull request changes")
    li.add_argument("--base",
                    help="trusted base tree for finding-ledger deletions in a pull-request change")
    li.add_argument("--pr-kind", choices=["release", "maintainer", "contributor"], default="maintainer")
    li.add_argument("--skeleton", action="store_true",
                    help="accept a tree with no facts yet (no release.yaml, no projects/)")
    li.add_argument("--release", action="store_true",
                    help="what only a release must satisfy: no placeholder digest or commit (all zeros), complete "
                         "build records (rule records), and, read from GitHub, the model the checker image pins "
                         "(model) and every pinned commit on a branch or tag of its public repository (pins)")
    li.add_argument("--changed-only", metavar="BASE",
                    help="run the per-file text rules only over the files that differ from commit BASE, or over "
                         "every file when a fact (a file tools/oft/paths.py classes as facts), a finding's "
                         "finding.yaml, a build record, a .gitattributes, tools/oft/lint-exceptions.yaml or the "
                         "running tools differ from it (the rules over the whole tree still run); --root must be "
                         "the top of a git checkout")
    li.add_argument("--jobs", type=_processes,
                    help="processes for the per-file text rules, 1 or more (default: every CPU this process may "
                         "run on, but no more than the available memory holds at %g GiB each, "
                         "for %d files or more to read)" % (lint.WORKER_GIB, lint.PARALLEL_FILES))
    li.add_argument("--max-rss-gib", type=_gib, default=lint.MAX_RSS_GIB,
                    help="the resident memory each process may hold, in GiB (default %g): a process that holds "
                         "more stops the run, which exits %d" % (lint.MAX_RSS_GIB, lint.MAX_RSS_EXIT))
    li.add_argument("--pending-base", metavar="DIR",
                    help="a git checkout of the base commit, which may be sparse (with --changed): the "
                         "licence-pending entries of its HEAD's tools/oft/lint-exceptions.yaml, read through git, are "
                         "the ones a pull request that changes proof files may have")
    li.add_argument("--list-pending", action="store_true",
                    help="print each pending licence finding, not one line per fuzz target with its count")
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
                    help="the commit whose proofs, counterexamples and findings are checked (default: HEAD)")
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
    what = pl.add_mutually_exclusive_group()
    what.add_argument("--explain", metavar="PROJECT/HARNESS",
                      help="print each part of one unit, whether it is checked and why, and every input of its key")
    what.add_argument("--contracts", metavar="PROJECT/HARNESS",
                      help="print the work key of each contract file of one unit at --change, as JSON: which "
                           "contracts need an agent; never a basis for verdict reuse. It holds the contract, the "
                           "files of the proof library it requires, the proof environment, the masked bytes or size "
                           "of what it names from Symbols.v and, for a function, the targets of the symbol fact "
                           "(what the immediates its mask zeroed point at, so that a call or a read of another "
                           "symbol changes the key), and no address; with --base, which inputs differ")
    pl.set_defaults(fn=cmd_plan)

    rt = sub.add_parser("release-tree", help="keep only the proofs approvals.yaml lists, in place, and render again")
    rt.set_defaults(fn=cmd_release_tree)

    po = sub.add_parser("port-layout", help="move an old-layout tree (proofs/, counterexamples/, findings/, patches/) "
                                            "to the per-project layout, or refuse it whole and move nothing")
    how = po.add_mutually_exclusive_group()
    how.add_argument("--dry-run", action="store_true", help="print each move and move nothing")
    how.add_argument("--commit", metavar="REV",
                     help="port the tree of commit REV of --root's repository instead, in a temporary index, and print "
                          "the id of the ported tree (no checkout, no blob read)")
    po.set_defaults(fn=cmd_port_layout)

    pb = sub.add_parser("port-branch", help="port a branch made on the old layout onto the per-project layout, or "
                                            "made before the Rocq namespace rename onto the renamed tree, or both, "
                                            "in a worktree; pushes nothing, prints the commands that would")
    pb.add_argument("branch", help="the branch: a local one, else origin's")
    pb.add_argument("--layout-commit", metavar="LC",
                    help="the commit that moved the base to the per-project layout: its tree is its first parent's "
                         "ported (port-layout --commit)")
    pb.add_argument("--namespace-commit", metavar="NC",
                    help="the commit that renamed the base's Rocq namespace: its tree is its first parent's renamed "
                         "(rename-namespace); with --layout-commit too, the layout is ported first")
    pb.add_argument("--onto", default=port.ONTO, metavar="REF",
                    help="the base merged after the port, which holds LC and NC (default: %(default)s)")
    pb.add_argument("--worktree", required=True, metavar="DIR",
                    help="where the port happens: a new worktree of the branch's tip when DIR does not exist or is "
                         "empty, else the worktree an earlier run left, which goes on from its HEAD")
    pb.set_defaults(fn=cmd_port_branch)

    rn = sub.add_parser("rename-namespace", help="rename the Rocq namespace and the opam stem in every file, the "
                                                 "stored proof encodings among them (tools/oft/nsrename.py), or "
                                                 "compare a commit with the rename of another")
    rn.add_argument("--to", metavar="NAME", help="the new namespace")
    rn.add_argument("--opam-stem", metavar="STEM", help="the new opam stem (packages rocq-STEM-<project>)")
    rn.add_argument("--check", action="store_true", help="run the refusals and the before-gate; write nothing")
    rn.add_argument("--verify", nargs=2, metavar=("A", "B"),
                    help="compare commit B of --root's repository with the rename of commit A, each by its "
                         "release.yaml's names; exit 0 only with no problem")
    rn.add_argument("--jobs", type=_processes, help="processes (default: every CPU)")
    rn.set_defaults(fn=cmd_rename_namespace)

    ap = sub.add_parser("approvals", help="write approvals.yaml from the proofs of the fuzz targets a file lists")
    ap.add_argument("list", metavar="FILE",
                    help="one <project>/<harness> per line, then a tab and the review record for a submission")
    ap.add_argument("--approved-by", required=True, help="the GitHub login of who approves the entries")
    ap.add_argument("--date", required=True, help="the date of the approval, YYYY-MM-DD")
    ap.set_defaults(fn=cmd_approvals)

    lx = sub.add_parser("lps-impact", help="check every unit in a checker image built from an LPS commit, and say "
                                           "what each unit's first error is")
    lps_impact.add_arguments(lx)
    lx.set_defaults(fn=cmd_lps_impact)

    r = sub.add_parser("revisions", help="each statement's revision and proof against the previous release")
    r.add_argument("previous", help="a checkout of the previous release")
    r.add_argument("--write-pins", action="store_true",
                   help="set the pin of each proof that carries forward to its statement's fingerprint here")
    r.add_argument("--repin-changed", action="store_true",
                   help="as --write-pins, and also set the pin of each re-checked or new proof that holds its "
                        "statement's fingerprint in the previous release to its fingerprint here: only for a change "
                        "whose re-check is the next corpus run (a change to the code of Shapes.v), never to silence a "
                        "proof that failed.  Against a commit that is not a release (a proof branch's base before "
                        "that change), only the pins count: the revision errors and the exit status compare with that "
                        "commit, not with a release, so ignore them and never add --write-revisions there")
    r.add_argument("--write-revisions", action="store_true",
                   help="set each statement's revision in harness.yaml to the one it must have, then name the "
                        "render to run next.  The previous checkout and each OLDER must be releases: one that holds a "
                        "file `oft release-tree` removes (approvals.yaml, review.md, ...) is refused.  A new "
                        "statement's revision is never lowered: name with --earlier the release that has it, or, if no "
                        "release has it, remove its revision: line")
    r.add_argument("--earlier", nargs="+", default=[], metavar="OLDER",
                   help="checkouts of the releases before the previous one, strictly newest first (by date, then by "
                        "release): a statement the previous release left out (held or private) is compared with the "
                        "newest of them that has it")
    r.set_defaults(fn=cmd_revisions)

    sy = sub.add_parser("symbols", help="write a build's symbol fact, projects/<p>/<h>/symbols/<build>.tsv, from its "
                                        "unstripped twin")
    sy.add_argument("--unstripped", required=True, metavar="U",
                    help="the build's unstripped twin, the same link without --strip-all, which has the symbol table")
    sy.add_argument("--stripped", required=True, metavar="S",
                    help="the build's published binary, whose sha256 harness.yaml pins")
    sy.add_argument("--lines", required=True, metavar="L",
                    help="the output of `llvm-dwarfdump --debug-line U`, run in the toolchain image of release.yaml")
    sy.add_argument("--harness", required=True, metavar="PROJECT/HARNESS")
    sy.add_argument("--build", required=True, choices=schema.BUILDS)
    sy.set_defaults(fn=cmd_symbols)

    cl = sub.add_parser("classify", help="the class of each function between two builds' symbol facts: identical, "
                                         "moved, changed, added or removed")
    cl.add_argument("base", metavar="BASE.tsv", help="the symbol fact of the base build")
    cl.add_argument("head", metavar="HEAD.tsv", help="the symbol fact of the head build")
    cl.add_argument("--json", action="store_true", help="print the rows and the counts as JSON")
    cl.set_defaults(fn=cmd_classify)

    pv = sub.add_parser("prove", help="a change's functions, contracts and source lines in one report: the class of "
                                      "each function of each build between --base and --head, the state of each "
                                      "contract (changed contract, removed, needs work, unknown, data changed or "
                                      "unchanged) and why, and the source lines of each changed function")
    pv.add_argument("unit", metavar="PROJECT/HARNESS")
    pv.add_argument("--base", required=True, metavar="REF", help="the commit the change is judged against")
    pv.add_argument("--head", default="HEAD", metavar="REF", help="the commit of the change (default: HEAD)")
    pv.add_argument("--json", action="store_true",
                    help="print the report as JSON: every function with its class, every contract with its state, "
                         "why, the work-key components that differ and the class and source lines of each function "
                         "it names")
    pv.add_argument("--post-check", type=_post_check, metavar="OWNER/REPO@SHA", action="append", default=[],
                    help="also post the report as the check run 'theorem/prove: PROJECT/HARNESS' on commit SHA of the "
                         "GitHub repository OWNER/REPO, the head of its pull request: action_required when a contract "
                         "needs work, is a changed contract, is removed or is unknown, neutral when the others are all "
                         "data changed, else success.  May be given more than once: each is posted, and a refusal "
                         "stops no other.  The token is GH_TOKEN, a GitHub App installation token with checks: write "
                         "on OWNER/REPO; the API is GITHUB_API_URL (default %s)" % check_run.API)
    pv.add_argument("--post-check-optional", type=_post_check, metavar="OWNER/REPO@SHA", action="append", default=[],
                    help="as --post-check, after every --post-check, except that GitHub's refusal with 403 or 404 (the "
                         "App is not installed on OWNER/REPO, or may not write its checks) is a warning, not a "
                         "failure")
    pv.add_argument("--pull-request", type=_pull_request, metavar="URL",
                    help="the pull request whose head --head is, when the check goes on another commit (its code "
                         "repository's): the summary says first that the report is of the head of that unmerged pull "
                         "request")
    pv.set_defaults(fn=cmd_prove)

    cg = sub.add_parser("change-ledger", help="what one change cost, from the records that hold it: its agent "
                                              "sessions' tokens, cost and hours, its VM time and check time, and its "
                                              "proof edits (changes/<change>/, tools/oft/change_ledger.py)")
    cgs = cg.add_subparsers(dest="ledger_cmd", required=True)
    ct = cgs.add_parser("tag", help="record an agent session that worked on a step of CHANGE in "
                                    "changes/CHANGE/sessions.tsv; a session counts in one step of one change, unless "
                                    "each of its tags gives a window (--from, --until) and no two windows overlap")
    ct.add_argument("change", metavar="CHANGE")
    ct.add_argument("--step", required=True, help="the step of the change the session worked on")
    ct.add_argument("--session", required=True, metavar="ID", help="the omp session id, as its transcript records it")
    ct.add_argument("--host", required=True, help="the machine the session ran on")
    ct.add_argument("--transcript", required=True, metavar="PATH", help="the session's omp transcript (.jsonl)")
    ct.add_argument("--vm", action="append", default=[], metavar="NAME",
                    help="a VM the session drove, whose samples count in its time span (repeat for each)")
    ct.add_argument("--from", dest="since", metavar="TIME",
                    help="count only the transcript's entries at or after TIME (ISO 8601 with a time zone): with "
                         "--until, the window of a session that worked on several steps or changes, tagged once for "
                         "each")
    ct.add_argument("--until", metavar="TIME",
                    help="count only the transcript's entries before TIME (ISO 8601 with a time zone)")
    cc = cgs.add_parser("check", help="record the GNU time -v log of a check run for a step of CHANGE in "
                                      "changes/CHANGE/checks.tsv")
    cc.add_argument("change", metavar="CHANGE")
    cc.add_argument("--step", required=True, help="the step of the change the check belongs to")
    cc.add_argument("--time-log", required=True, metavar="PATH", help="the check's `time -v` output")
    cn = cgs.add_parser("no-work", help="record in changes/CHANGE/no-work.tsv that a step of CHANGE needed no work, "
                                        "so its row reads 0 rather than not measured")
    cn.add_argument("change", metavar="CHANGE")
    cn.add_argument("--step", required=True, help="the step of the change that needed no work")
    cn.add_argument("--why", required=True, metavar="TEXT",
                    help="what shows it needed no work, on one line (such as: oft prove finds no function changed)")
    cs = cgs.add_parser("sum", help="write changes/CHANGE/ledger.tsv, session-totals.tsv, gaps.tsv, inputs.tsv and, "
                                    "with a saved prediction (prove.json), contracts.tsv, from the records; create "
                                    "journal.md when it is missing")
    cs.add_argument("change", metavar="CHANGE")
    cs.add_argument("--unit", metavar="PROJECT/HARNESS",
                    help="the fuzz target whose proof lines, function classes, contracts and proof edits count")
    cs.add_argument("--base", metavar="REF", help="the commit the change started from (with --unit)")
    cs.add_argument("--head", default="HEAD", metavar="REF", help="the commit of the change (default: HEAD)")
    cs.add_argument("--vm-samples", action="append", default=[], metavar="FILE",
                    help="a TSV of VM samples with the columns vm, time (or run_ts) and type (or machine_type), such "
                         "as notes/compute-ledger.tsv or notes/idle-stop.tsv (repeat for each); without one, "
                         "vcpu_hours is not measured")
    cs.add_argument("--vm-deletions", action="append", default=[], metavar="FILE",
                    help="a compute inventory that records each VM deletion as gone=MM-DDTHH:MMZ in its labels, such "
                         "as the one bin/ossv-vm keeps (repeat for each): a deletion less than 45 minutes after a VM "
                         "life's last sample ends the life there; without one, the time after a life's last sample "
                         "is not measured")
    cg.set_defaults(fn=cmd_change_ledger)

    a = p.parse_args(argv)
    return a.fn(a)


def run(argv=None):
    """main(), with a requirement a command imports only when it needs it reported as the install it is: idna,
    which `oft lint` imports to map a host, is imported in one of lint.forked_map's worker processes, and the pool
    re-raises it here.  SystemExit then carries the message instead of a traceback through concurrent.futures."""
    try:
        return main(argv)
    except ModuleNotFoundError as e:
        said = _missing_requirement(e)
        if said is None:
            raise
        raise SystemExit(said) from None


if __name__ == "__main__":
    # `oft check` reports each step as it finishes, and a CI job cut off at its time limit keeps only what was written
    # out by then. With no terminal (a container, a pipe) Python buffers output in blocks, so every line is written as
    # it is printed instead.
    sys.stdout.reconfigure(line_buffering=True)
    sys.stderr.reconfigure(line_buffering=True)
    sys.exit(run())
