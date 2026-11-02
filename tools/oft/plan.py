"""oft plan: which parts of which units a CI run checks, as JSON for its job matrix.

A part is checked when its key (keys.py) has no recorded pass on the branch check-results, and, for a run that
judges a change against a base, when the key differs from the base's: a change is checked on what it changes.  Each
part's row says why it is or is not checked."""
import datetime
import json
import math
import os
import re
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
# measured minutes (in TIMES: the 61 with a committed proof; the tree has some 2,150 harnesses, most checked on their
# statements alone) is packed on the 16-core runner as UNMEASURED minutes, and its job's limit is CAP.  UNMEASURED is
# the largest minutes per harness of a sweep job with no proved harness in the measured weekly runs of 24 and 26
# October 2026 (five such 16-core jobs: 9 or 26 harnesses each, 4.2 to 75.9 minutes; the 75.9-minute job of 26
# harnesses is 2.92 a harness, and the median is 0.54), rounded up.  A unit whose own minutes are over the 16-core
# room (offloaded()) is in no job: it is checked on the build service (builds-ossv), and the plan takes a citation of
# that check instead (OFFLOADED).  The jobs are listed longest first, so that the matrix starts them first.  MATRIX is
# the most jobs GitHub runs in one matrix.
ROOM = {LARGE: CAP / MARGIN, STANDARD: CAP / MARGIN / SLOWER}
UNMEASURED = 3.0
MATRIX = 256


def offloaded(unit, times):
    """Whether unit is too long for a check job even alone: its measured minutes are over the 16-core room."""
    m = times.get(unit, (None, None))[0]
    return m is not None and m > ROOM[LARGE]


def pack(units, times):
    """([(runner, [unit, ...]), ...], [unit, ...]): the check jobs of units, by the rule above, and the units that are
    in no job because offloaded() says so.  Every unit is in exactly one job or in the second list."""
    by, away, size = {STANDARD: [], LARGE: []}, [], {}
    for u in units:
        m = times.get(u, (None, None))[0]
        on = runner([u], times)
        if on == STANDARD and m > ROOM[STANDARD]:
            on = LARGE
        if offloaded(u, times):
            away.append(u)
        else:
            size[u] = UNMEASURED if m is None else m
            by[on].append(u)
    jobs = []
    for on, members in by.items():
        bins = []
        for u in sorted(members, key=lambda u: (-size[u], u)):
            b = next((b for b in bins if b[0] + size[u] <= ROOM[on]), None)
            if b is None:
                bins.append([size[u], [u]])
            else:
                b[0] += size[u]
                b[1].append(u)
        jobs += [(on, b[1]) for b in bins]

    def length(job):
        return sum(size[u] for u in job[1]) * (SLOWER if job[0] == STANDARD else 1)
    jobs = [(on, sorted(us)) for on, us in sorted(jobs, key=lambda j: (-length(j), sorted(j[1])))]
    if len(jobs) > MATRIX:
        raise ValueError("%d check jobs: more than the %d a matrix runs" % (len(jobs), MATRIX))
    return jobs, sorted(away)


# The checks of offloaded units, done on the build service: one row per unit and part, naming the key it was checked
# at, the build-service job that checked it, the SHA-256 of the job's result.json, and the date (YYYY-MM-DD); a newer
# check replaces the row.  It is the file at this path in the tree a plan judges, and citations() refuses a malformed
# row.  A plan that checks a part of an offloaded unit takes that part's row at the part's key in place of a check job,
# and fails, naming the unit, the part and the key, when there is none: a row of another key is a check of other
# bytes.  keys.NOT_THE_CHECKER names the file, so a new row re-keys nothing.
OFFLOADED = os.path.join("tools", "oft", "offloaded-checks.tsv")
OFFLOADED_COLUMNS = ["unit", "part", "key", "job", "result_sha256", "date"]
_HEX64 = re.compile(r"[0-9a-f]{64}")
_DATE = re.compile(r"\d{4}-\d{2}-\d{2}")


def citations(path, harnesses, wanted):
    """{(unit, part, key): row}: the rows of the OFFLOADED file at path; {} when there is no such file.  harnesses is
    the set of the tree's units, wanted the (unit, part) pairs it has to check.  Raises ValueError, naming each bad
    row, for a row whose key or result_sha256 is not 64 lowercase hex digits, whose date is not a real YYYY-MM-DD,
    whose part is not one of keys.PARTS, whose unit is no harness of the tree or has no such part to check, or that
    repeats the unit and part of an earlier row (a part's row names its one current check; a newer check replaces
    the row)."""
    if not os.path.isfile(path):
        return {}
    with open(path, encoding="utf-8") as f:
        lines = [(n, line.rstrip("\n")) for n, line in enumerate(f, 1) if not line.startswith("#") and line.strip()]
    if not lines or lines[0][1].split("\t") != OFFLOADED_COLUMNS:
        raise ValueError("%s: the header must be %s" % (path, ", ".join(OFFLOADED_COLUMNS)))
    out, seen, bad = {}, {}, []
    for n, line in lines[1:]:
        fields = line.split("\t")
        if len(fields) != len(OFFLOADED_COLUMNS) or not all(fields):
            bad.append("line %d: a row has %d non-empty columns, tab-separated: %r" % (n, len(OFFLOADED_COLUMNS), line))
            continue
        row = dict(zip(OFFLOADED_COLUMNS, fields))
        why = []
        for column in ("key", "result_sha256"):
            if not _HEX64.fullmatch(row[column]):
                why.append("%s %r is not 64 lowercase hex digits" % (column, row[column]))
        try:
            valid_date = bool(_DATE.fullmatch(row["date"])) and datetime.date.fromisoformat(row["date"])
        except ValueError:
            valid_date = False
        if not valid_date:
            why.append("date %r is not a date YYYY-MM-DD" % row["date"])
        if row["part"] not in keys.PARTS:
            why.append("part %r is not one of %s" % (row["part"], ", ".join(keys.PARTS)))
        elif row["unit"] not in harnesses:
            why.append("unit %r is no harness of this tree" % row["unit"])
        elif (row["unit"], row["part"]) not in wanted:
            why.append("%s has no %s part to check" % (row["unit"], row["part"]))
        if (row["unit"], row["part"]) in seen:
            why.append("line %d already has a row for %s %s" % (seen[(row["unit"], row["part"])], row["unit"],
                                                                 row["part"]))
        seen.setdefault((row["unit"], row["part"]), n)
        if why:
            bad.append("line %d: %s" % (n, "; ".join(why)))
        else:
            out[(row["unit"], row["part"], row["key"])] = row
    if bad:
        raise ValueError("%s: %d bad row(s):\n  %s" % (path, len(bad), "\n  ".join(bad)))
    return out


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
         times=None, out=sys.stdout, err=sys.stderr):
    """Print {"all", "units", "check_units", "offloaded", "parts", "jobs"} for the parts rows() checks; units, if
    given, limits the plan to those units (weekly's rotating third).  parts holds every part's row with its key and
    components.  The jobs are pack()'s, from times (check_times() when None); units and check_units name the units the
    jobs check.  offloaded holds, for each checked part of a unit pack() leaves out, the row of root's OFFLOADED file
    at the part's key; when a part has none, nothing is printed, each such part is named on err with its key, and the
    plan returns 1.  Each job lists its units, the units whose build it checks (check_units) and those of them with a
    proof of one of their statements (proof_units, which check-units.sh checks with their proofs and the rest on their
    statements), the projects whose binaries those and the counterexamples need, the units whose counterexamples and
    findings it runs, the runner it runs on and its time limit in minutes (timeout_minutes()).  A job carries no keys
    (the parts do): the workflows pass the jobs as one job output, which grows with the tree, and weekly.yml's
    determinism job takes them as one environment variable, which Linux caps at 131,072 bytes (with a key per part,
    #170 measured a plan of every harness at 132,809 bytes)."""
    times = check_times() if times is None else times
    tree = facts.load(root)
    proved = {st.harness.project.name + "/" + st.harness.name for st in tree.statements() if st.proof}
    wanted = keys.wanted(tree)
    try:
        cited = citations(os.path.join(root, OFFLOADED),
                          {h.project.name + "/" + h.name for h in tree.harnesses()}, set(wanted))
    except ValueError as e:
        print("oft plan: %s" % e, file=err)
        return 1
    if units is not None:
        wanted = [(u, p) for u, p in wanted if u in units]
    parts = [dict(r, components=c) for r, c, _o in rows(root, wanted, change, base, kind, tools, store, rocqchk)]
    of = {}
    for r in parts:
        if r["check"]:
            of.setdefault(r["unit"], set()).add(r["part"])
    packed, away = pack(sorted(of), times)
    found, missing = [], []
    for r in parts:
        if r["check"] and r["unit"] in away:
            row = cited.get((r["unit"], r["part"], r["key"]))
            if row:
                found.append(row)
            else:
                other = [k for u, p, k in cited if (u, p) == (r["unit"], r["part"])]
                missing.append("%s %s: key %s has no check on the build service (builds-ossv) in %s%s" % (
                    r["unit"], r["part"], r["key"], OFFLOADED,
                    "; its row is for key %s, a check of other bytes: replace it" % other[0] if other else ""))
    if missing:
        print("oft plan: %d part(s) too long for a check job and not checked on the build service at their key; "
              "check each there and add or replace its row:" % len(missing), file=err)
        for m in missing:
            print("  " + m, file=err)
        return 1
    chosen = sorted(u for _on, shard in packed for u in shard)
    jobs = []
    for i, (on, shard) in enumerate(packed):
        build = [u for u in shard if "build" in of[u]]
        cx = [u for u in shard if "counterexamples" in of[u]]
        jobs.append({"index": i, "units": " ".join(shard), "check_units": " ".join(build),
                     "proof_units": " ".join(u for u in build if u in proved),
                     "projects": " ".join(sorted({u.split("/")[0] for u in build + cx})),
                     "counterexamples": " ".join(cx),
                     "findings": " ".join(u for u in shard if "findings" in of[u]),
                     "runner": on, "timeout_minutes": timeout_minutes(shard, times, on)})
    json.dump({"all": bool(parts) and all(r["check"] for r in parts), "units": chosen,
               "check_units": [u for u in chosen if "build" in of[u]], "offloaded": found, "parts": parts,
               "jobs": jobs}, out)
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
