#!/usr/bin/env python3
"""DRV_TRACES as af0m.py derives them from a YCej.universe.json (af0m's --universe input).

    drv_check.py UNIVERSE.json --af0m AF0M.py --af0m-sha SHA12 (--expect '[[..]; ..]' | --expect-from FILE)
                 [--same-order]

The derivation is NOT re-implemented: the lines of af0m's own `if a.universe:` block, from `drv = ` through
`body = `, are read out of the given af0m source (whose sha256 must start with --af0m-sha), printed, and executed
on the json (start-up bundle 8cd71d3a4bb: af0m.py 238598b380f1, af0m.py:1598-1608). The resulting rows are
compared with --expect (a Coq list literal) or with `Definition DRV_TRACES ... .` of --expect-from.
Gate: equal as sets, no row twice; with --same-order also equal list for list. The order is always reported.
Exit 0 on PASS, 1 on FAIL.
"""
import argparse
import hashlib
import json
import re
import sys
import textwrap


def coq_list(text):
    return [tuple(int(x, 0) for x in t.split(";") if x.strip()) for t in re.findall(r"\[([^\[\]]*)\]", text)]


def fmt(t):
    return "[" + "; ".join("%#x" % z for z in t) + "]"


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("universe")
    ap.add_argument("--af0m", required=True)
    ap.add_argument("--af0m-sha", required=True)
    ap.add_argument("--expect")
    ap.add_argument("--expect-from")
    ap.add_argument("--same-order", action="store_true")
    a = ap.parse_args()

    src = open(a.af0m).read()
    h = hashlib.sha256(src.encode()).hexdigest()
    print("af0m %s sha256 %s" % (a.af0m, h))
    if not h.startswith(a.af0m_sha):
        print("FAIL af0m sha256 does not start with %s" % a.af0m_sha)
        return 1
    lines = src.split("\n")
    i = [k for k, l in enumerate(lines) if l.strip() == "if a.universe:"]
    if len(i) != 1:
        print("FAIL af0m: %d `if a.universe:` blocks (want 1)" % len(i))
        return 1
    j0 = next(k for k in range(i[0], len(lines)) if lines[k].strip().startswith("drv = "))
    j1 = next(k for k in range(j0, len(lines)) if lines[k].strip().startswith("body = "))
    block = textwrap.dedent("\n".join(lines[j0:j1 + 1]))
    print("af0m lines %d-%d executed on %s:" % (j0 + 1, j1 + 1, a.universe))
    for l in block.split("\n"):
        print("    " + l)
    env = {"U": json.load(open(a.universe))}
    exec(block, env)
    drv = [tuple(int(x, 0) for x in t) for t in env["drv"]]
    print("af0m would write  Definition DRV_TRACES : list (list Z) :=\n[%s]." % env["body"])

    if a.expect_from:
        m = re.search(r"Definition DRV_TRACES : list \(list Z\) :=\s*(\[.*?\])\.", open(a.expect_from).read(), re.S)
        want = coq_list(m.group(1)[1:-1])
        src_w = a.expect_from
    else:
        want = coq_list(a.expect.strip()[1:-1])
        src_w = "--expect"
    print("derived %d rows; expected (%s) %d rows" % (len(drv), src_w, len(want)))
    for t in drv:
        print("    %s %s" % ("ok  " if t in want else "XTRA", fmt(t)))
    for t in want:
        if t not in drv:
            print("    MISS %s" % fmt(t))
    nodup = len(set(drv)) == len(drv) and len(set(want)) == len(want)
    same_set = set(drv) == set(want)
    same_list = drv == want
    print("equal as sets %s; no row twice %s; same order %s" % (same_set, nodup, same_list))
    ok = same_set and nodup and (same_list or not a.same_order)
    print("DRV PASS" if ok else "DRV FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
