#!/usr/bin/env python3
"""Generate and compare farm About probes for discharged twin statements.

Use `budgetwit probe --twin FILE --r1-module MODULE --out FILE --map JSON`,
then build on the farm and use `budgetwit about --map JSON --log LOG`.
Only printed types and Arguments are compared, not definition bodies.
The complete comparison limitations are in README.md.
"""
import json
import os
import re

from . import gen_v
from .rocqparse import QID, parse_file

MARK = "ossv_about_mark_"
#: the module qualifier `About` may put in front of a constant
QID_DOT = QID + r"\."


# ------------------------------------------------------------------ probe

def scan_twin(path, module):
    """Read a generated twin and return [(twin name, line)] of its declarations."""
    vf = parse_file(path, module)
    return [(it.name, it.line) for it in vf.decls() if it.name]


def r1_of(twin_module, twin_name, r1_module, pairs):
    for a, b in pairs:
        if b == twin_name:
            return a
    return None


def write_probe(twin_path, out_path, map_path, r1_module, pairs,
                extra_renames=None, census=None, package=None, twin_dir="BudgetWit"):
    """Write the probe .v and the map `check` reads back."""
    if not package:
        raise ValueError("write_probe needs the unit's logical package")
    tmod_short = os.path.basename(twin_path)[:-2]
    r1_short = r1_module.rsplit(".", 1)[1]
    r1_pre = r1_module.rsplit(".", 1)[0]
    lines = [
        "(* Copyright 2026 Anthropic PBC *)",
        "(* SPDX-License-Identifier: Apache-2.0 OR MIT *)",
        "(* Modified by Theorem Labs, 2026-11: a probe, not part of the proof: it "
        "prints the discharged statement of each twin and of its released original "
        "so that about_check.py can compare them. *)",
        "From %s Require Import %s." % (r1_pre, r1_short),
        "From %s.%s Require Import %s." % (package, twin_dir, tmod_short),
        "Set Printing Width 500.",
    ]
    entries = []
    k = 0
    tag = re.sub(r"[^A-Za-z0-9_]", "_", tmod_short)
    for r1_name, twin_name in pairs:
        for side, mod, nm in (("r1", r1_short, r1_name),
                              ("twin", tmod_short, twin_name)):
            mark = "%s%s_%03d" % (MARK, tag, k)
            lines.append("Definition %s : unit := tt." % mark)
            lines.append("Print %s." % mark)
            lines.append("About %s.%s." % (mod, nm))
            entries.append({"mark": mark, "side": side, "name": nm,
                            "qualified": mod + "." + nm,
                            "r1_name": r1_name, "twin_name": twin_name})
            k += 1
    end = "%s%s_%03d" % (MARK, tag, k)
    lines.append("Definition %s : unit := tt." % end)
    lines.append("Print %s." % end)
    entries.append({"mark": end, "side": "end", "name": "", "qualified": "",
                    "r1_name": "", "twin_name": ""})
    with open(out_path, "w", encoding="utf8") as fh:
        fh.write("\n".join(lines) + "\n")
    meta = {"probe": os.path.basename(out_path), "twin": os.path.basename(twin_path),
            "twin_module": tmod_short, "r1_module": r1_module,
            "pairs": pairs, "entries": entries,
            "census_renames": dict(census or {}),
            "extra_renames": dict(extra_renames or {})}
    with open(map_path, "w", encoding="utf8") as fh:
        json.dump(meta, fh, indent=1)
    return meta


# ------------------------------------------------------------------ check

def split_blocks(log, entries):
    """Cut the build log into the `About` block that follows each marker.

    A mark that answers twice in one log means two probes of the same job used the
    same marks: refuse, rather than read the other probe's answers as this one's.
    """
    text = log
    pos = {}
    ambiguous = []
    for e in entries:
        hits = list(re.finditer(r"^%s\s*=\s*tt" % re.escape(e["mark"]), text, re.M))
        if len(hits) > 1:
            ambiguous.append(e["mark"])
        m = hits[0] if hits else re.search(re.escape(e["mark"]), text)
        pos[e["mark"]] = m.start() if m else None
    if ambiguous:
        raise SystemExit(
            "this log answers %d mark(s) more than once, so the blocks cannot be told "
            "apart: %s.\nTwo probes of one job used the same mark names; re-probe with "
            "the current about_check.py, which puts the twin module in every mark."
            % (len(ambiguous), ", ".join(ambiguous[:4])))
    out = {}
    marks = [e["mark"] for e in entries]
    for i, e in enumerate(entries[:-1]):
        a = pos[e["mark"]]
        b = pos[marks[i + 1]]
        if a is None or b is None or b <= a:
            out[e["mark"]] = None
            continue
        chunk = text[a:b]
        # drop the `Print` answer of the marker itself
        chunk = re.sub(r"^%s\s*=\s*tt\s*\n?\s*:\s*unit\s*" % re.escape(e["mark"]),
                       "", chunk)
        out[e["mark"]] = chunk.strip()
    return out


ARGS_RE = re.compile(r"^Arguments\s+(\S+)\s*(.*)$", re.M)


def parse_about(block, qualified):
    """Return (type, Arguments line) of one `About` answer."""
    if not block:
        return None, None
    lines = block.split("\n")
    # `About` prints the shortest unambiguous name, which for the twin is often the
    # bare one: take whatever name opens the answer.
    short = qualified.split(".")[-1]
    start = None
    for i, ln in enumerate(lines):
        if re.match(r"^\s*(?:" + re.escape(qualified) + r"|" + re.escape(short)
                    + r")\s*:", ln):
            start = i
            break
    if start is None:
        return None, None
    ty = [re.sub(r"^\s*\S+\s*:", "", lines[start])]
    i = start + 1
    while i < len(lines):
        ln = lines[i]
        if re.match(r"^\s*\S+\s+is\s+", ln) or ln.startswith("Arguments") \
                or ln.startswith("Expanded"):
            break
        ty.append(ln)
        i += 1
    args = None
    m = ARGS_RE.search(block)
    if m:
        args = m.group(2)
    return norm(" ".join(ty)), norm(args or "")


def norm(s):
    s = re.sub(r"\(\*.*?\*\)", " ", s, flags=re.S)
    return re.sub(r"\s+", " ", s).strip()


def census_renames(tsv, overrides, pkg, profile, twin_path=None):
    """{R1 short name: twin short name} from the census and the overrides.

    So a correct twin does not read DIFF only because its statement names
    `KnodeB.mreal_b` where the released one names `YO0d.mreal`.
    """
    out = {}
    for full, (_tm, tn) in gen_v.load_twins(tsv, pkg).items():
        out[full.rsplit(".", 1)[1]] = tn
    omaps, _skips, _omods = gen_v.load_overrides(overrides, pkg)
    for full, (_tm, tn, _ex) in omaps.items():
        short = full.rsplit(".", 1)[1]
        out[short] = tn or profile.twin_name(short)
    if twin_path and os.path.exists(twin_path):
        # Only the names THIS twin really restates: a file that keeps the released
        # `malloc_realizes` must not have the census rename applied to its R1 side,
        # or a correct twin reads DIFF.
        with open(twin_path, encoding="utf8", errors="replace") as fh:
            have = set(re.findall(r"[A-Za-z_][A-Za-z0-9_']*", fh.read()))
        out = dict((k, v) for k, v in out.items() if v in have)
    return out


def args_ok(want, got):
    """Compare two `Arguments` lines, allowing a renamed binder name.

    A section hypothesis whose type names a twinned declaration is renamed by the
    generator (`HMm` -> `HMm_b`), and that name shows in the `Arguments` line without
    changing the statement.
    """
    a, b = want.split(), got.split()
    if len(a) != len(b):
        return False
    for x, y in zip(a, b):
        if x == y or y == x + "_b":
            continue
        return False
    return True


def rename_text(text, renames):
    """Rewrite the R1 names of a printed statement to the twin's names.

    `About` prints each constant with as much of its module path as it needs, so a
    renamed name is matched with or without a qualifier and comes out unqualified;
    `strip_quals` does the same on the twin's side.  Everything that is not renamed
    keeps its qualifier, so a twin that names a different module is still a DIFF.
    """
    if not renames:
        return text
    pat = re.compile(r"(?<![A-Za-z0-9_'])(?:" + QID_DOT + r")?(" +
                     "|".join(sorted((re.escape(k) for k in renames), key=len,
                                     reverse=True)) + r")(?![A-Za-z0-9_'])")
    return pat.sub(lambda m: renames[m.group(1)], text)


def strip_quals(text, names):
    """Drop the module qualifier of each of `names` in a printed statement."""
    if not names:
        return text
    pat = re.compile(r"(?<![A-Za-z0-9_'])(?:" + QID_DOT + r")?(" +
                     "|".join(sorted((re.escape(n) for n in names), key=len,
                                     reverse=True)) + r")(?![A-Za-z0-9_'])")
    return pat.sub(lambda m: m.group(1), text)


def check(meta, log, allow=()):
    entries = meta["entries"]
    blocks = split_blocks(log, entries)
    renames = {a: b for a, b in meta["pairs"] if a != b}
    renames.update(meta.get("census_renames", {}))
    renames.update(meta.get("extra_renames", {}))
    targets = set(renames.values()) | {b for _, b in meta["pairs"]}
    by_pair = {}
    for e in entries:
        if e["side"] == "end":
            continue
        ty, args = parse_about(blocks.get(e["mark"]), e["qualified"])
        by_pair.setdefault((e["r1_name"], e["twin_name"]), {})[e["side"]] = (ty, args)
    rows = []
    for (r1n, twn), sides in by_pair.items():
        r1 = sides.get("r1", (None, None))
        tw = sides.get("twin", (None, None))
        if r1[0] is None or tw[0] is None:
            rows.append(("NOREAD", r1n, twn, "no About answer in the log"))
            continue
        want_ty = strip_quals(rename_text(r1[0], renames), targets)
        want_ar = strip_quals(rename_text(r1[1], renames), targets)
        got_ty = strip_quals(tw[0], targets)
        got_ar = strip_quals(tw[1], targets)
        if want_ty == got_ty and (want_ar == got_ar or args_ok(want_ar, got_ar)):
            rows.append(("SAME", r1n, twn, ""))
            continue
        why = []
        if want_ty != got_ty:
            why.append("type: " + first_diff(want_ty, got_ty))
        if want_ar != got_ar and not args_ok(want_ar, got_ar):
            why.append("Arguments: %r vs %r" % (want_ar, got_ar))
        msg = "; ".join(why)
        if any(re.search(p, msg) for p in allow):
            rows.append(("ALLOWED", r1n, twn, msg))
        else:
            rows.append(("DIFF", r1n, twn, msg))
    return rows


def first_diff(a, b):
    ta, tb = a.split(), b.split()
    for i, (x, y) in enumerate(zip(ta, tb)):
        if x != y:
            return "at word %d, R1 %r vs twin %r (... %s | %s ...)" % (
                i, x, y, " ".join(ta[max(0, i - 4):i + 4]),
                " ".join(tb[max(0, i - 4):i + 4]))
    if len(ta) != len(tb):
        longer = ta if len(ta) > len(tb) else tb
        side = "R1" if len(ta) > len(tb) else "twin"
        return "%s has %d extra word(s): %s" % (side, abs(len(ta) - len(tb)),
                                                " ".join(longer[min(len(ta), len(tb)):]))
    return "equal after normalisation"


