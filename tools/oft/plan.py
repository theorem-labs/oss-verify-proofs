"""oft plan: which parts of which units a CI run checks, as JSON for its job matrix.

A part is checked when its key (keys.py) has no recorded pass on the branch check-results, and, for a run that
judges a change against a base, when the key differs from the base's: a change is checked on what it changes.  Each
part's row says why it is or is not checked."""
import json
import math
import os
import sys

import yaml

from . import facts, keys

KINDS = ("release", "maintainer", "contributor")

# Each check job's runner.  A job runs on GitHub's standard runner (4 CPUs, 16 GB; free on a public repository) when
# every unit in it peaked under PEAK_GIB on the 16-core runner and its units' minutes there sum to at most
# SUM_MINUTES; otherwise on the 16-core runner (64 GB).  PEAK_GIB leaves 2 GiB of the 16 GB for the checker image and
# dune's tree beside the check.  SUM_MINUTES: most of a check is serial (each proof and each wrapper is one
# `rocq compile` after another, and the counterexamples run one by one), but the proof library's `dune build -j` and
# the statements' `dune build` use every CPU, so a job runs longer on 4 CPUs; 150 minutes leaves the job room under
# GitHub's 6-hour cap even if it takes twice as long.  The measurements are TIMES; a unit missing from it counts as
# over both thresholds.
STANDARD = "ubuntu-24.04"
LARGE = "ubuntu-24.04-16core"
PEAK_GIB = 14
SUM_MINUTES = 150
TIMES = os.path.join(os.path.dirname(os.path.abspath(__file__)), "check-times.tsv")
# Each check job's time limit, in minutes: MARGIN times the job's measured minutes on its runner (its units' minutes in
# TIMES, times SLOWER on the standard runner), at least FLOOR and at most CAP; CAP when a unit has no measured minutes.
#   SLOWER  cgif/cgif_file_fuzzer, the one unit checked on both runners at one commit: 302.8 minutes on ubuntu-24.04
#           (release-check run 41335592258) against 137.9 and 159.7 on the 16-core runner (runs 41299366541,
#           41335509469): 2.2 and 1.9 times; the larger is taken.
#   MARGIN  the minutes in TIMES are each unit's longest run, and for 41 units that run is release-check run
#           40665207695, which took a median 1.35 times (at most 1.56) the time of run 41299366541 on the same units;
#           half as much again over the longest run covers a run as slow as that one, of a unit measured on a fast day.
#   FLOOR   the shortest unit's longest job took 13.9 minutes; 30 leaves room for a slow pull of the images and the
#           binaries.
#   CAP     the longest successful check job, zstd/simple_decompress (324.5 minutes, run 40665207695), with 15 minutes
#           to spare, under GitHub's 360.
SLOWER = 2.2
MARGIN = 1.5
FLOOR = 30
CAP = 340


def check_times(path=TIMES):
    """{unit: (minutes or None, peak_gib or None)}: the measured checks of TIMES on the 16-core runner."""
    out = {}
    with open(path, encoding="utf-8") as f:
        lines = [line.rstrip("\n") for line in f if not line.startswith("#")]
    if not lines or lines[0].split("\t") != ["unit", "minutes", "peak_gib"]:
        raise ValueError("%s: the header must be unit, minutes, peak_gib" % path)
    for line in lines[1:]:
        unit, minutes, peak = line.split("\t")
        out[unit] = (float(minutes) if minutes else None, float(peak) if peak else None)
    return out


def runner(units, times):
    """The runner of a check job of units, by the rule above."""
    measured = [times.get(u, (None, None)) for u in units]
    if all(m is not None and p is not None and p < PEAK_GIB for m, p in measured) \
            and sum(m for m, _p in measured) <= SUM_MINUTES:
        return STANDARD
    return LARGE


def timeout_minutes(units, times, on):
    """The time limit of a check job of units on the runner on, by the rule above."""
    minutes = [times.get(u, (None, None))[0] for u in units]
    if any(m is None for m in minutes):
        return CAP
    expected = sum(minutes) * (SLOWER if on == STANDARD else 1)
    # rounded first, so that a product such as 40 x 2.2 x 1.5 is the 132 it is and not 132.00000000000003
    return min(CAP, max(FLOOR, math.ceil(round(MARGIN * expected, 6))))


# How the units are packed into check jobs.  A job may hold measured minutes up to what its time limit allows below
# CAP: CAP / MARGIN on the 16-core runner (226.7), and on the standard runner CAP / MARGIN / SLOWER (103.0), which is
# also under SUM_MINUTES.  The units runner() puts on the standard runner, each within that, are packed into jobs of
# their own, so that a long unit never pulls a short one onto the 16-core runner; the rest are packed into 16-core
# jobs.  Each kind is packed first-fit decreasing: longest unit first, into the first job it fits in.  A unit with no
# measured minutes, and one whose own minutes are over its runner's room (openssl/hashtable, zstd/simple_decompress,
# cgif/cgif_rgb_fuzzer), gets a job of its own, at CAP.  The jobs are listed longest first, so that the matrix starts
# them first.  MATRIX is the most jobs GitHub runs in one matrix.
ROOM = {LARGE: CAP / MARGIN, STANDARD: CAP / MARGIN / SLOWER}
MATRIX = 256


def pack(units, times):
    """[(runner, [unit, ...]), ...]: the check jobs of units, by the rule above.  Every unit is in exactly one job."""
    alone, by = [], {STANDARD: [], LARGE: []}
    for u in units:
        m = times.get(u, (None, None))[0]
        on = runner([u], times)
        if on == STANDARD and m > ROOM[STANDARD]:
            on = LARGE
        if m is None or m > ROOM[on]:
            alone.append((LARGE, [u]))
        else:
            by[on].append(u)
    jobs = alone
    for on, members in by.items():
        bins = []
        for u in sorted(members, key=lambda u: (-times[u][0], u)):
            b = next((b for b in bins if b[0] + times[u][0] <= ROOM[on]), None)
            if b is None:
                bins.append([times[u][0], [u]])
            else:
                b[0] += times[u][0]
                b[1].append(u)
        jobs += [(on, b[1]) for b in bins]

    def length(job):
        minutes = [times.get(u, (None, None))[0] for u in job[1]]
        return math.inf if None in minutes else sum(minutes) * (SLOWER if job[0] == STANDARD else 1)
    jobs = [(on, sorted(us)) for on, us in sorted(jobs, key=lambda j: (-length(j), sorted(j[1])))]
    if len(jobs) > MATRIX:
        raise ValueError("%d check jobs: more than the %d a matrix runs" % (len(jobs), MATRIX))
    return jobs


def rows(root, wanted, change="HEAD", base=None, kind="release", tools=None, store=None, rocqchk=False):
    """[(row, components, the base's components or None)] for each (unit, part) of wanted.  root is the tree a check
    job checks, inside a git repository that holds the commits named here.

    change   the commit whose proofs/, counterexamples/ and findings/ are checked
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
    before = keys.keys(root, wanted, base, base, tools, rocqchk) if base else {}
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
            row["why"] = ("changed: " + ", ".join(n for n in sorted(comp) if old[1].get(n) != comp[n]) if old
                          else "no recorded pass")
        out.append((row, comp, old[1] if old else None))
    return out


def plan(root, change="HEAD", base=None, kind="release", tools=None, store=None, units=None, rocqchk=False,
         times=None, out=sys.stdout):
    """Print {"all", "units", "check_units", "parts", "jobs"} for the parts rows() checks; units, if given, limits
    the plan to those units (weekly's rotating third).  parts holds every part's row with its key and components.
    The jobs are pack()'s, from times (check_times() when None).  Each job lists its units, the units whose build it
    checks (check_units) and those of them with a proof of one of their statements (proof_units, which check-units.sh
    checks with their proofs and the rest on their statements), the projects whose binaries those and the
    counterexamples need, the units whose counterexamples and findings it runs, the runner it runs on and its time
    limit in minutes (timeout_minutes()).  A job carries no keys (the parts do): the workflows pass the jobs as one job
    output, which grows with the tree, and weekly.yml's determinism job takes them as one environment variable, which
    Linux caps at 131,072 bytes (with a key per part, #170 measured a plan of every harness at 132,809 bytes)."""
    times = check_times() if times is None else times
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
    jobs = []
    for i, (on, shard) in enumerate(pack(chosen, times)):
        build = [u for u in shard if "build" in of[u]]
        cx = [u for u in shard if "counterexamples" in of[u]]
        jobs.append({"index": i, "units": " ".join(shard), "check_units": " ".join(build),
                     "proof_units": " ".join(u for u in build if u in proved),
                     "projects": " ".join(sorted({u.split("/")[0] for u in build + cx})),
                     "counterexamples": " ".join(cx),
                     "findings": " ".join(u for u in shard if "findings" in of[u]),
                     "runner": on, "timeout_minutes": timeout_minutes(shard, times, on)})
    json.dump({"all": bool(parts) and all(r["check"] for r in parts), "units": chosen,
               "check_units": [u for u in chosen if "build" in of[u]], "parts": parts, "jobs": jobs}, out)
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
