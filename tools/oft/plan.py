"""oft plan: which parts of which units a CI run checks, as JSON for its job matrix.

A part is checked when its key (keys.py) has no recorded pass on the branch check-results, and, for a run that
judges a change against a base, when the key differs from the base's: a change is checked on what it changes.  Each
part's row says why it is or is not checked.  `oft plan --contracts` gives the work key of each contract file of one
unit instead (contracts.py)."""
import json
import re
import sys

import yaml

from . import facts, keys, layout, pack

KINDS = ("release", "maintainer", "contributor")
# The files of keys.NOT_THE_CHECKER a plan runs: `python -m oft plan` goes through __main__.py's cmd_plan, whose
# arguments and defaults decide what plan() gets, and this file and pack.py decide which parts are checked and how
# they are packed.  release-check.yml's same_tools keeps them in its comparison, so a push that changes the planner
# is planned with its own planner rather than credited by a merge queue run that planned with its parent's.  The
# list is here, not in keys.py, because keys.py is the checker: a change to it would re-key every unit.  This file
# is in the list, so a change to the list loses the credit too; same_tools also keeps this file by name, so a push
# that drops it from the list (and changes it) cannot keep the credit either.
PLANNER = ("tools/oft/__main__.py", "tools/oft/plan.py", "tools/oft/pack.py")
# The enrollment scripts' place outside tools/ (OSSV-276: tools/enroll/ moves to dev/enroll/): enroll.yml and
# enroll-build.yml run them and no check opens them.  Under tools/ keys.NOT_THE_CHECKER names them; outside it no
# key holds them, so paths_a_check_reads names them here.
ENROLLMENT_SCRIPTS = "dev/enroll/"
# The model gateway's formal model (OSSV-498) and the workflow that builds it: no check opens either.
GATEWAY_MODEL = "dev/gateway-model/"
GATEWAY_MODEL_WORKFLOW = ".github/workflows/gateway-model.yml"
# The tools that run this repository's evals (OSSV-643: dev/evals/paired-run/) and the workflow that runs the paired
# run's tests: no check opens either.
EVALS = "dev/evals/"
EVALS_WORKFLOW = ".github/workflows/paired-run.yml"
# The shared Rocq build service (OSSV-299): its release-test workflow, and its table of memory classes, which the
# service's client `theorem check` (OSSV-654) reads.  `oft check` opens neither, so paths_a_check_reads names them
# here.  The one caller of paths_a_check_reads, pr.yml's elsewhere step, is deleted when the proof checks move to the
# build service, and this list goes with it.
BUILD_SERVICE_FILES = (".github/workflows/rocq-release.yml", ".github/theorem-rule-classes.tsv")
# The shared licence-record generator (OSSV-400) and its tests: each unit's provenance/evidence/licence/made_from.py
# holds only that unit's data and calls it.  pr.yml's made_from job runs it over each unit's licence evidence, which
# unitpaths.PROOFS_DROP keeps out of every key; no check of a proof opens it, and outside tools/ no key holds it
# (keys.checker lists tools/ alone), so paths_a_check_reads names it here.
LICENCE_GENERATOR = "dev/licence/"
# The OSS Verify stream's operational tools (dev/stream/README.md), which the stream's boxes run and pr.yml's
# stream_tools and farm_tests jobs check.  No check of a proof opens them, and outside tools/ no key holds them
# (keys.checker lists tools/ alone), so paths_a_check_reads names them here.
STREAM_TOOLS = "dev/stream/"


def rows(root, wanted, change="HEAD", base=None, kind="release", tools=None, store=None, rocqchk=False):
    """[(row, components, the base's components or None)] for each (unit, part) of wanted.  root is the tree a check
    job checks, inside a git repository that holds the commits named here.

    change   the commit whose proofs, counterexamples and findings are checked
    base     the commit the change is judged against, or None to check every part with no recorded pass
    kind     pr.yml's KIND: for maintainer and contributor the statements are the base's, as pr.yml's check job takes
             them; for release they are the change's own
    tools    the commit of the tools the check jobs run (default: base, else change)
    store    a commit of the branch check-results, or None when nothing is recorded"""
    if kind not in KINDS:
        raise ValueError("no kind %r" % kind)
    if kind != "release" and base is None:
        raise ValueError("a %s change is judged against a base" % kind)
    tools = tools or base or change
    if kind != "release":
        # the check runs the base's tests/, theories/ and sources, but the change's own hand-written dune files are on
        # main once it merges: refuse one that could shadow a theory here, not in every later plan
        keys.check_hand_dune(root, change)
    now = keys.keys(root, wanted, change if kind == "release" else base, change, tools, rocqchk)
    # A unit the change enrols has no key at the base, which does not have its statement folder: keys() refuses a
    # unit at neither of its commits (keys.no_unit), and before OSSV-457 that call answered a key of "-" components
    # for it.  So the base's keys are asked only of the units the base has, and the row of one it has not says so
    # and is checked, as a row with no base key already was.
    at_base = keys.have_unit(root, base, {u for u, _p in wanted}) if base else set()
    before = keys.keys(root, [up for up in wanted if up[0] in at_base], base, base, tools, rocqchk) if base else {}
    recorded = keys.recorded(root, store) if store else {}
    out = []
    for unit, part in wanted:
        key, comp = now[(unit, part)]
        old = before.get((unit, part))
        row = {"unit": unit, "part": part, "key": key, "check": False}
        if key in recorded.get((unit, part), ()):
            row["why"] = "recorded pass"
        elif old and old[0] == key:
            row["why"] = "unchanged from the base"
        else:
            row["check"] = True
            if old:
                row["why"] = "changed: " + ", ".join(n for n in sorted(comp) if old[1].get(n) != comp[n])
            elif base and unit not in at_base:
                row["why"] = "the base has not this unit"
            else:
                row["why"] = "no recorded pass"
        out.append((row, comp, old[1] if old else None))
    return out


def hosted_skips(skipped, rows, checks, cap=pack.HOSTED_CAP):
    """One sentence per unit of `skipped`, in name order, for the run summary of a hosted sweep: what the sweep
    measured for it, that no hosted job can check it, the words `not checked this week`, and the last passing farm
    check of record `checks` holds for it with the day it ran, so a standing check that has gone stale shows as
    stale.  A unit `checks` has none for says `no farm check found`, which is a different thing from an old one
    and never written as one."""
    out = []
    for unit in skipped:
        minutes, outcome = rows[unit]
        took = "%d minutes" % minutes if outcome == "finished" else "at least %d minutes" % minutes
        run, date = checks.get(unit, ("", ""))
        had = "last passing farm check of record %s (%s)" % (run, date) if run else "no farm check found"
        out.append("%s: not checked this week -- %s on a 16-core runner, over the %d-minute hosted cap; %s."
                   % (unit, took, cap, had))
    return out


def plan(root, change="HEAD", base=None, kind="release", tools=None, store=None, units=None, max_jobs=20,
         rocqchk=False, hosted=False, out=sys.stdout):
    """Print {"all", "units", "check_units", "parts", "jobs"} for the parts rows() checks; units, if given, limits
    the plan to those units (the units named in weekly.yml's dispatch).  parts holds every part's row with its key and
    components.  Each job lists its units, the units whose build it checks (check_units) and those of them with a proof
    of one of their statements (proof_units, which check-units.sh checks with their proofs and the rest on their
    statements), the projects whose binaries those and the counterexamples need, the units whose counterexamples and
    findings it runs, and `cpus`, the CPUs its check may give dune (pack.job_cpus of its proof_units: a unit checked
    on its statements alone never needs fewer; 0 for every CPU); pack.shards deals the units whose proofs it builds
    by their measured time.  A job carries no keys (the parts do): the workflows pass
    the jobs as one job output, which grows with the tree, and weekly.yml's determinism job takes them as one
    environment variable, which Linux caps at 131,072 bytes (with a key per part, a plan of every
    harness at 132,809 bytes).  With `hosted`, the units no hosted job can check (pack.too_long_for_hosted) are
    left out of the plan altogether, and `skipped` holds one sentence about each for the run's summary
    (hosted_skips); without it the plan carries every unit and `skipped` is empty."""
    tree = facts.load(root)
    proved = {st.harness.project.name + "/" + st.harness.name for st in tree.statements() if st.proof}
    wanted = keys.wanted(tree)
    if units is not None:
        wanted = [(u, p) for u, p in wanted if u in units]
    parts = [dict(r, components=c) for r, c, _o in rows(root, wanted, change, base, kind, tools, store, rocqchk)]
    of = {}
    for r in parts:
        if r["check"]:
            of.setdefault(r["unit"], set()).add(r["part"])
    chosen = sorted(of)
    rows_ = pack.sweep()
    skipped = [u for u in pack.too_long_for_hosted(rows_) if u in of] if hosted else []
    if skipped:
        chosen = [u for u in chosen if u not in skipped]
        parts = [r for r in parts if r["unit"] not in skipped]
        of = {u: p for u, p in of.items() if u not in skipped}
    said = hosted_skips(skipped, rows_, pack.farm_checks())
    for line in said:
        print("plan: " + line, file=sys.stderr)
    n = max(1, min(max_jobs, len(chosen)))
    # the units whose proofs this run builds, dealt by the minutes the sweep measured for each (pack.py), then the
    # rest.  A proved unit the sweep has not timed is named here and dealt a job of its own: a silent middling
    # weight for one is what cancelled shard 29 of run 42556340137 (pack.py's docstring).
    table, measured = pack.load(), {u: m for u, (m, o) in rows_.items() if o == "finished" and u not in skipped}
    building = proved & {u for u in chosen if "build" in of[u]}
    untimed = pack.unmeasured(chosen, building, measured)
    if untimed:
        print("plan: %s with proofs and no measured sweep time in %s, so each is planned a job of its own: %s"
              % ("1 unit" if len(untimed) == 1 else "%d units" % len(untimed),
                 "tools/oft/pack.py's SWEEP_TIMES", " ".join(untimed)),
              file=sys.stderr)
    jobs = []
    for i, shard in enumerate(pack.shards(chosen, n, building, table, measured) if chosen else []):
        build = [u for u in shard if "build" in of[u]]
        cx = [u for u in shard if "counterexamples" in of[u]]
        jobs.append({"index": i, "units": " ".join(shard), "check_units": " ".join(build),
                     "proof_units": " ".join(u for u in build if u in proved),
                     "projects": " ".join(sorted({u.split("/")[0] for u in build + cx})),
                     "counterexamples": " ".join(cx),
                     "findings": " ".join(u for u in shard if "findings" in of[u]),
                     "cpus": pack.job_cpus([u for u in build if u in proved], table)})
    json.dump({"all": bool(parts) and all(r["check"] for r in parts), "units": chosen,
               "check_units": [u for u in chosen if "build" in of[u]], "parts": parts, "jobs": jobs,
               "skipped": said}, out)
    out.write("\n")
    return 0


def explain(root, unit, change="HEAD", base=None, kind="release", tools=None, store=None, rocqchk=False,
            out=sys.stdout):
    """Each part of unit: its key, whether a run would check it and why, and every component's id; a component that
    differs from the base's is marked *."""
    wanted = [(u, p) for u, p in keys.wanted(facts.load(root)) if u == unit]
    if not wanted:
        print("%s: nothing to check (no such harness, or no published build, counterexample or finding)" % unit,
              file=out)
        return 1
    for row, comp, old in rows(root, wanted, change, base, kind, tools, store, rocqchk):
        print("%s %s %s: %s, %s" % (row["unit"], row["part"], row["key"], "checked" if row["check"] else "not checked",
                                     row["why"]), file=out)
        for name in sorted(comp):
            print("  %s %-15s %s" % ("*" if old and old.get(name) != comp[name] else " ", name, comp[name]), file=out)
    return 0


# The keys of release.yaml that name the containers a check runs in: tools/oft/ci/check-units.sh's image() reads
# images.checker (the statements are built and the proofs compiled in it) and images.runner (the counterexamples and
# the findings run in it).
IMAGE_KEYS = (("images", "checker"), ("images", "runner"))


def _images(path):
    """The value of each of IMAGE_KEYS in the release.yaml at path, as check-units.sh's image() reads it
    (yaml.safe_load, then printed), or None when the file cannot be read or parsed or lacks one of them."""
    try:
        with open(path, encoding="utf-8") as f:
            v = yaml.safe_load(f)
    except (OSError, ValueError, yaml.YAMLError):
        return None
    values = []
    for key in IMAGE_KEYS:
        x = v
        for k in key:
            if not isinstance(x, dict) or k not in x:
                return None
            x = x[k]
        values.append(str(x))
    return values


def images_differ(head_release, base_release):
    """Whether the release.yaml at the path head_release names another checker or runner image than the one at
    base_release (a path, or None).  No base_release, a file that cannot be read or parsed and a missing key all
    count as a difference, so that no caller takes a release.yaml it could not compare for the same images.

    pr.yml's reach step asks it, with the base's tools, whether a changed release.yaml makes the controls run.  It is
    here and not in check.py or keys.py because keys.NOT_THE_CHECKER leaves plan.py out of every key: a change to it
    re-checks no fuzz target."""
    if base_release is None:
        return True
    base = _images(base_release)
    return base is None or _images(head_release) != base


# pr.yml's checked-elsewhere step: a merge queue group whose every pull request carries merge-pr.sh's VM evidence
# comment runs no check job when nothing a planned part's check reads moved between the tree its check of record ran
# on and the group head.  These answer that, with the base's tools, as the reach step asks images_differ, and they
# are here for the same reason: keys.NOT_THE_CHECKER leaves plan.py out of every key, so a change to them re-checks
# no fuzz target.
KEY_LINE = re.compile(r"(?P<unit>[^/\s]+/[^/\s]+) (?P<key>[0-9a-f]{64})")
# The parts of a unit an evidence line can record, and so the parts a pull request may have checked elsewhere.
# This tuple is the ONE place that set is written: vm_evidence_keys below refuses a plan that marks any other part
# to check, and the queue check that measures a pull request before it is enqueued asks the base's tools for it
# (its evidence_names) before it sends the first farm job, so the set that queue check spends farm time under and
# the set the gate accepts are one.
#   `findings` is not in it.  No plan has carried a findings part to this route, and a part whose key no evidence
# line records can only end in the refusal below; naming it costs a word here when one appears.  Until 2026-11-11
# `counterexamples` was not in it either, and #2479's plan -- 2,175 units with the parts [build] and the eight
# FFmpeg decoder targets of OSSV-367 with [build, counterexamples] -- was refused after 41,043 s and 2,042 farm
# jobs, with nothing enqueued (the report on OSSV-373, 2026-11-11 06:33Z).
HANDLED_PARTS = ("build", "counterexamples")
# The id of a checker, as keys.checker gives it and as a marker's `<!-- vm-evidence-checker id=<64 hex> -->` line
# carries it (vm_evidence_checker).
CHECKER_ID = re.compile(r"[0-9a-f]{64}")
# Ruling 16 (OSS Verify, 2026-11-01): main's checker at 87c4b944683b, under which the VM checks of record ran, and
# at dd31239f2de (keys.checker of each).
ONLY_CHECKER = ("6d15b1f1a2bd82ec4dc93752b90672434f1e5658f5fbdac8184de52595a5334b",
                "416c41fb27ae28c1701639ba9ca83898fdecb78b26faa0dd744ba0b8575ef544")
# Ruling 20 (OSS Verify, 2026-11-01, amended the same day and on 2026-11-02, when the train dropped the reading
# change and with it the one-reading-per-pair rule of rules.py): what the W2 train moves in every unit's key and
# nothing else.  keys.VERSION, which the train raises to 3; the dune-path component, which it adds; the checker
# id, since the train changes 9 files of the checker (keys.checker of the train's tools, and main's before it,
# which is ONLY_CHECKER[1]); and the theories id, since the train adds theories/Premises.v.  Each is pinned, so a
# later change to the checker or to theories/ gives an id these do not name and ends ruling 20 by itself
# (_before_the_train returns None).  Never re-pin these to extend it: a new pair needs the OSS Verify lead's
# ruling.  test_keys.VmEvidence reads them back at the commit that wrote them, so such a change fails nothing.
BEFORE_THE_TRAIN = "2"
AFTER_THE_TRAIN_CHECKER = "f1800c27cab27dded55e606b4f2a99f33b7d7a0bc873e25fde0ca176356b10c1"
AFTER_THE_TRAIN_THEORIES = ("dff080d6cdccfdb3e9c481ed95ddeead6e386b734e1fcda96fa810071f0e4adc"
                            " 613a5ee83381ddf6fd5239404cb75c65641a85f50f5416e91578101b90ba607c")
BEFORE_THE_TRAIN_THEORIES = ("e2114ed52f49c4031474bd34d719b0ce02a0723acca8851559f189a939124e3a"
                             " 6ceebc312f26592ba54bab60eb6dd0abe8a334c0a925b6f5e5a6d8c9f7c3a52d")


def _before_the_train(comp):
    """The components comp as they were before the W2 train, or None when they are not this train's: its version
    component back at BEFORE_THE_TRAIN, no dune-path component, the checker id back at main's (ONLY_CHECKER[1])
    and the theories id back at BEFORE_THE_TRAIN_THEORIES (ruling 20).

    A part whose checker or theories id is not the train's is no part this ruling knows,
    and gets None: the two ids are pinned exactly, so only the tree the ruling was granted for is read back, and
    the first later change to the checker or to theories/ ends it.  Every other component is comp's own.  The
    difference lives here, in the file the pull request after N6 removes, and keys.py knows of no formula but
    today's."""
    if comp.get("checker") != AFTER_THE_TRAIN_CHECKER or comp.get("theories") != AFTER_THE_TRAIN_THEORIES:
        return None
    was = {"version": BEFORE_THE_TRAIN, "checker": ONLY_CHECKER[1], "theories": BEFORE_THE_TRAIN_THEORIES}
    return {name: was.get(name, value) for name, value in comp.items() if name != "dune-path"}


def ruling_16_allows(comp, recorded):
    """Whether a part whose key here differs from the key `recorded` may still be skipped: ruling 16 allows one
    difference, the checker component alone, and only from ONLY_CHECKER[0] to ONLY_CHECKER[1].  True exactly when
    this part's checker is the second and the key of these components with the first is the recorded one, which no
    other difference survives.

    The exception ends with the event it was granted for: it is removed, with this function and its callers' lines,
    by the pull request that follows the VM corpus run N6 passing on post-train main (the CI/CD lead tracks it).
    Its callers are rulings_allow below, which vm_evidence_keys and the plan job's elsewhere step in
    .github/workflows/pr.yml call over the same parts to find the key that takes a queue entry out.
    Until then a unit checked of record under the older checker is not re-checked for the checker alone."""
    old, new = ONLY_CHECKER
    return comp.get("checker") == new and keys.key_of(dict(comp, checker=old)) == recorded


def ruling_20_allows(comp, recorded):
    """Whether a part whose key here differs from the key `recorded` may still be skipped under ruling 20 (the OSS
    Verify lead, 2026-11-01, amended the same day; it mirrors ruling 16): the recorded key is the key these very
    components give as they stood before the W2 train.  A check of record that ran before the train measured the
    same tree, and the train moves three things in every unit's key without touching what any check reads: the
    key's formula (keys.VERSION 3 and the dune-path component), the checker id (the train changes 9 files of the
    checker), and the theories id (the train adds theories/Premises.v, a pure addition: no existing theory moves,
    so no proof of a merged unit reads anything new).  _before_the_train takes those three back, pinned, and
    nothing of what a check reads is forgiven: one changed proof file, statement, image, axiom list, project row or
    dune-project moves a component, and no ruling brings the two keys together again.

    Ruling 16 holds inside it, for a check of record that ran under main's older checker as well: it is asked of
    the same pre-train components, so the two exceptions meet in one place and neither repeats the other's rule.

    One thing the keys do not carry: until N6 passes, a hand-written dune file of a unit's build path merged after
    the train is not built with the proofs a pre-train marker covers, since that marker's check of record ran
    before it; check_hand_dune bounds such a file to one that can only fail a build, and N6 is the backstop.

    What stands behind it is N6: the farm corpus run of record on post-train main re-checks every unit merged
    under this ruling, so a key this accepts is a check deferred to N6, never a check dropped.  It ends as ruling
    16 does, and with it: the pull request that follows N6 passing (the CI/CD lead tracks it) removes both, these
    functions, the table below and its callers' lines.  Nothing of either is in keys.py."""
    pre = _before_the_train(comp)
    return pre is not None and (keys.key_of(pre) == recorded or ruling_16_allows(pre, recorded))


# The exceptions a key that differs from its evidence line may still stand under, in the order they are asked: each
# a name for the message vm_evidence_keys writes and the predicate that answers.  Ruling 16 comes first, since it
# forgives the checker alone and so says the less of the two.
RULINGS = (("ruling 16's checker pair", ruling_16_allows), ("ruling 20's pre-train tree", ruling_20_allows))


def rulings_allow(comp, recorded):
    """The name RULINGS gives the first exception that lets a part whose key differs from `recorded` be skipped, or
    "" when none does, so one call answers for every ruling and the step that reports names the one it used."""
    return next((name for name, allows in RULINGS if allows(comp, recorded)), "")


def _generated_readme(path):
    """Whether path is a README.md `oft generate` renders and no check reads: a fuzz target's,
    projects/<p>/<h>/README.md (the statement folder is the same in both layouts, layout.statement_dir, so there is
    nothing for layout.canonical to move), or its project's, projects/<p>/README.md.  No key holds either: the
    statement folder's component drops its README.md (unitpaths.HARNESS_DROP, "generated, and no check reads it"),
    and a project's component is its project.yaml and its fuzz targets' harness.yaml alone
    (unitpaths.project_files: "The other files directly in projects/<p>/, its README.md and its .opam file, are
    generated, and no check reads them"; keys._project: "a proof re-renders the README, which no check reads").
    A folder of projects/<p>/ that is no fuzz target's (layout.NOT_A_HARNESS) has no README of this kind."""
    parts = path.split("/")
    if parts[0] != "projects" or parts[-1] != "README.md":
        return False
    return len(parts) == 3 or (len(parts) == 4 and parts[2] not in layout.NOT_A_HARNESS)


def paths_a_check_reads(changed):
    """Of the paths changed, those whose change can move a verdict the keys do not already hold.  Ten kinds cannot:
    a file of a unit's own proofs folder in either layout (layout.is_change and layout.canonical), which only that
    unit's build reads -- a check reads no file of another unit, so every proof library a unit's check may read is in
    that folder (tools/oft/unitpaths.py) -- and whose id that unit's build key holds, so vm_evidence_keys catches any
    change to it, but for what unitpaths.PROOFS_DROP leaves out of that key (the build record's prose and its licence
    evidence), which no rule a check runs and no build opens, so a change there can move no verdict either;
    CHANGELOG.md, which no check opens; a file of tools/ that no check opens
    (keys.not_the_checker); a file of dev/enroll/, the enrollment scripts (ENROLLMENT_SCRIPTS), which enroll.yml and
    enroll-build.yml run and no check opens; a file of dev/licence/, the shared licence-record generator
    (LICENCE_GENERATOR), which no check opens; a file of dev/stream/, the stream's operational tools (STREAM_TOOLS),
    which the stream's boxes run, pr.yml's stream_tools and farm_tests jobs check, and no check of a proof opens; a
    file of dev/gateway-model/, the gateway's formal model (GATEWAY_MODEL), or its workflow (GATEWAY_MODEL_WORKFLOW),
    which no check opens; a file of dev/evals/, the tools
    that run the evals (EVALS), or the paired run's workflow (EVALS_WORKFLOW), which no check opens; the build
    service's release-test workflow or its table of
    memory classes (BUILD_SERVICE_FILES), which `oft check` does not open; and a fuzz target's or a project's generated
    README.md, which no key holds and no check opens (_generated_readme), and which a proof re-renders with its
    statement's new status.
    Everything else counts, a statement, theories/,
    toolchain/, .github/, release.yaml, dune-project, a counterexample, a finding and a projects/<p>/unpatched.yaml
    among them: a counterexamples or findings part is checked in CI, and no VM evidence line records its key.

    An empty path (a trailing newline of the changed list) is no path and counts for nothing."""
    out = []
    for path in changed:
        if not path or path == "CHANGELOG.md" or path in (GATEWAY_MODEL_WORKFLOW, EVALS_WORKFLOW) \
                or path in BUILD_SERVICE_FILES or keys.not_the_checker(path) \
                or path.startswith((ENROLLMENT_SCRIPTS, LICENCE_GENERATOR, STREAM_TOOLS, GATEWAY_MODEL, EVALS)) \
                or _generated_readme(path):
            continue
        parts = layout.canonical(path).split("/") if layout.is_change(path) else []
        if len(parts) > 4 and parts[0] == "projects" and parts[3] == "proofs":
            continue
        out.append(path)
    return out


def vm_evidence_checker(checker, lines):
    """Why the group's evidence markers do not stand for runs under the checker `checker`, or "" when each marker
    names exactly it.  `checker` is keys.checker of the merge tree this group checks, read with the base's tools;
    `lines` are `<pull request> <id>...` lines, one per pull request of the group, carrying the ids that pull
    request's marker gave on its `<!-- vm-evidence-checker id=<64 hex> -->` lines, in the marker's own order.

    A key says nothing about the tools that computed it.  On 2026-11-06 a lane posted markers whose keys were
    computed with main's tools while its farm runs had executed the pull request heads' older tools, from before
    #2109 moved keys.checker (main's was 7e50363e1a34, the runs' were 924ec654, ec73f922 and 746226f8): the keys
    matched although no run had used main's checker.  So a marker names the checker its run actually used, and a
    marker with no such line, with more than one, or with another id leaves the group its checks (the OSS Verify
    lead, 2026-11-06 18:10Z).  Reading no pull request at all refuses too, so that a group whose markers were
    never read cannot pass here."""
    if not CHECKER_ID.fullmatch(checker or ""):
        return "the checker of the tree this group checks is no checker id: %r" % checker
    seen = 0
    for line in lines:
        fields = line.split()
        if not fields or not fields[0].isdigit() or not all(CHECKER_ID.fullmatch(f) for f in fields[1:]):
            return "a checker line is not one pull request and the ids its marker named: %r" % line.strip()
        pull, ids = fields[0], fields[1:]
        if len(ids) != 1:
            return ("pull request %s's evidence comment names %d checker ids%s, and the tree this group checks "
                    "has checker %s" % (pull, len(ids), (": " + " ".join(ids)) if ids else "", checker))
        if ids[0] != checker:
            return ("pull request %s's evidence comment names checker %s and the tree this group checks has "
                    "checker %s" % (pull, ids[0], checker))
        seen += 1
    if not seen:
        return "no pull request of this group was read for the checker its marker names"
    return ""


def evidence_unit(unit, part):
    """The name an evidence key line carries for PART of UNIT.

    A unit's `build` is named by the unit alone, which is what every marker written before 2026-11-11 carries and
    what `<!-- vm-evidence-key unit=<p>/<h> key=<64 hex> -->` has always meant; any other handled part is
    `<unit>:<part>`.  A unit id holds no `:` (the check-of-record reader's UNIT_ID), so no part name can be read
    as a unit, and `<unit>:<part>` still matches KEY_LINE here and the `unit=(?<unit>[^ ]+)` capture pr.yml's
    elsewhere step takes the key lines with, so the marker's shape and the workflow that reads it are unchanged.

    Rule 3a's own reading is unchanged too: it dates a unit's proofs from the sentence of a check-of-record
    paragraph that names the unit, and the queue check's marker writes no check-of-record sentence for a part
    that is not a build (its marker_text)."""
    return unit if part == "build" else "%s:%s" % (unit, part)


def vm_evidence_keys(planned, lines, checker, checker_lines):
    """(True, what was measured) when every part planned marks for checking is of a kind an evidence line can
    record and carries here the key an evidence line recorded for it, and every marker names the checker the
    group's tree holds, else
    (False, why).  planned is `oft plan`'s parts, lines the `<name> <key>` lines of the group's evidence comments,
    checker keys.checker of the merge tree this group checks and checker_lines the `<pull request> <id>...` lines
    vm_evidence_checker reads.

    The checker is asked first, since a key alone does not say which tools computed it (vm_evidence_checker).
    A part's content key holds everything its check reads (keys.py), so equal keys say that nothing moved between
    the tree the check of record ran on and this one.  An evidence line records ONE PART's key, under the name
    evidence_unit gives it, so a plan that marks a part of a kind no evidence line can record (HANDLED_PARTS)
    leaves the group its checks, and so does a planned part with no line of its own, or two
    lines for one part that disagree (two pull requests of one group touching it).  A key that differs is false
    here too, but the workflow answers it before this function, except for a unit two pull requests recorded,
    which it leaves here: the plan step fails for the group's last entry, whose pull request recorded that key, so
    the queue takes that entry out instead of checking a tree its owner never measured
    (.github/workflows/pr.yml, the plan job's elsewhere step)."""
    refused = vm_evidence_checker(checker, checker_lines)
    if refused:
        return False, refused
    recorded = {}
    for line in lines:
        m = KEY_LINE.fullmatch(line.strip())
        if not m:
            return False, "an evidence line is not one unit and one key: %r" % line.strip()
        if recorded.setdefault(m.group("unit"), m.group("key")) != m.group("key"):
            return False, "%s has two evidence lines of its own, with different keys" % m.group("unit")
    parts = [p for p in planned if p.get("check")]
    if not parts:
        return False, "the plan marks no part to check"
    other = sorted({p["part"] for p in parts} - set(HANDLED_PARTS))
    if other:
        return False, "the plan marks %s to check, which no evidence line records" % ", ".join(other)
    by_ruling = {name: [] for name, _allows in RULINGS}
    for part in parts:
        unit, key, comp = part["unit"], part["key"], part["components"]
        named = evidence_unit(unit, part["part"])
        was = recorded.get(named)
        if was is None:
            return False, "%s has no key line in its pull request's evidence comment" % named
        if was == key:
            continue
        ruling = rulings_allow(comp, was)
        if ruling:
            by_ruling[ruling].append(named)
            continue
        return False, "%s: its key at this group head is %s and its evidence comment recorded %s" % (named, key, was)
    return True, ("%d part(s), each with the key its check of record ran on" % len(parts)
                  + "".join("; %d by %s: %s" % (len(units), name, " ".join(units))
                            for name, units in by_ruling.items() if units))
