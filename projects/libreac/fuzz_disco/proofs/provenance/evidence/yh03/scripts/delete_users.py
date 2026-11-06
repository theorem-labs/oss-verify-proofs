#!/usr/bin/env python3
"""delete_users.py [--skip SUBDIR ...] PROOFS_DIR TABLE.tsv [TABLE.tsv ...]

For every DELETE row of the YH03 fix tables, count the .v files under PROOFS_DIR that name the cell
(`src0_<name>` as a whole identifier, comments included) and the total number of such names. A deleted cell must
have 0 uses in the fixed tree. Prints one line per distinct name (sorted), then a summary; exit 1 if any count is
not 0. One pass over the tree: every identifier token is looked up in the set of deleted names. --skip SUBDIR
(relative to PROOFS_DIR, repeatable) leaves a subtree out, e.g. this evidence slice's own copies of the old files."""
import os
import re
import sys


def main(argv):
    args, skip = list(argv[1:]), []
    while args and args[0] == "--skip":
        skip.append(args[1].strip("/"))
        args = args[2:]
    if len(args) < 2:
        sys.exit(__doc__)
    root = args[0]
    names = set()
    for t in args[1:]:
        with open(t) as f:
            rows = f.read().splitlines()
        hdr = rows[0].split("\t")
        for raw in rows[1:]:
            r = dict(zip(hdr, raw.split("\t")))
            if r["action"] == "DELETE":
                names.add(r["name"] if r["name"].startswith("src0_") else "src0_" + r["name"])
    files = {n: 0 for n in names}
    uses = {n: 0 for n in names}
    ident = re.compile(r"[A-Za-z0-9_']+")
    nfiles = 0
    for d, _, fs in os.walk(root):
        rel = os.path.relpath(d, root)
        if any(rel == s or rel.startswith(s + os.sep) for s in skip):
            continue
        for fn in fs:
            if not fn.endswith(".v"):
                continue
            nfiles += 1
            with open(os.path.join(d, fn), errors="replace") as f:
                seen = set()
                for tok in ident.findall(f.read()):
                    if tok in uses:
                        uses[tok] += 1
                        seen.add(tok)
            for n in seen:
                files[n] += 1
    bad = 0
    for n in sorted(names):
        bad += uses[n] != 0
        print("%s files %d uses %d" % (n, files[n], uses[n]))
    print("# %d deleted names, %d .v files scanned (skipped: %s), %d names with uses" % (len(names), nfiles, " ".join(skip) or "none", bad))
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main(sys.argv)
