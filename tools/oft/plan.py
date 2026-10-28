"""oft plan: which parts of which units a CI run checks, as JSON for its job matrix.

A part is checked when its key (keys.py) has no recorded pass on the branch check-results, and, for a run that
judges a change against a base, when the key differs from the base's: a change is checked on what it changes.  Each
part's row says why it is or is not checked."""
import json
import sys

import yaml

from . import facts, keys

KINDS = ("release", "maintainer", "contributor")


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


def plan(root, change="HEAD", base=None, kind="release", tools=None, store=None, units=None, max_jobs=20,
         rocqchk=False, out=sys.stdout):
    """Print {"all", "units", "check_units", "parts", "jobs"} for the parts rows() checks; units, if given, limits
    the plan to those units (weekly's rotating third).  parts holds every part's row with its key and components.
    Each job lists its units, the units whose build it checks (check_units) and those of them with a proof of one of
    their statements (proof_units, which check-units.sh checks with their proofs and the rest on their statements),
    the projects whose binaries those and the counterexamples need, and the units whose counterexamples and findings
    it runs.  A job carries no keys (the parts do): the workflows pass the jobs as one job output, which grows with
    the tree, and weekly.yml's determinism job takes them as one environment variable, which Linux caps at 131,072
    bytes (with a key per part, #170 measured a plan of every harness at 132,809 bytes)."""
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
    n = max(1, min(max_jobs, len(chosen)))
    jobs = []
    for i, shard in enumerate([chosen[i::n] for i in range(n)] if chosen else []):
        build = [u for u in shard if "build" in of[u]]
        cx = [u for u in shard if "counterexamples" in of[u]]
        jobs.append({"index": i, "units": " ".join(shard), "check_units": " ".join(build),
                     "proof_units": " ".join(u for u in build if u in proved),
                     "projects": " ".join(sorted({u.split("/")[0] for u in build + cx})),
                     "counterexamples": " ".join(cx),
                     "findings": " ".join(u for u in shard if "findings" in of[u])})
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
