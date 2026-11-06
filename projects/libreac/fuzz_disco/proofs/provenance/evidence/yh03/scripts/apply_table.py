#!/usr/bin/env python3
"""apply_table.py OLD.v TABLE.tsv HEADER.txt AFTER_LINE > NEW.v

Apply a YH03 fix table (columns action, file, line, name, committed, correct, ...) to the address table it was
measured on, and insert the fix's one comment line.
- FIX rows replace `committed` by `correct` in their `Definition src0_<name> : Z := <committed>.`;
- DELETE rows remove their Definition (a line the deletions leave empty is dropped);
- KEEP rows change nothing.
A row whose Definition is not on its line with its committed value stops the run (exit 1).
HEADER.txt (one line) is inserted after line AFTER_LINE of the result. No other change is made."""
import re
import sys


def main(argv):
    if len(argv) != 5:
        sys.exit(__doc__)
    old_path, table_path, header_path, after = argv[1], argv[2], argv[3], int(argv[4])
    with open(old_path) as f:
        old = f.read().splitlines(True)
    with open(table_path) as f:
        rows = f.read().splitlines()
    with open(header_path) as f:
        header = f.read()
    hdr = rows[0].split("\t")
    lines = list(old)
    for raw in rows[1:]:
        r = dict(zip(hdr, raw.split("\t")))
        i = int(r["line"]) - 1
        name = r["name"] if r["name"].startswith("src0_") else "src0_" + r["name"]
        pat = re.compile(r"Definition\s+" + re.escape(name) + r"\s*:\s*Z\s*:=\s*" + re.escape(r["committed"]) +
                         r"\s*\.\s*")
        m = pat.search(lines[i])
        if not m:
            sys.exit("line %s: no `Definition %s : Z := %s.`" % (r["line"], name, r["committed"]))
        if r["action"] == "FIX":
            lines[i] = lines[i][:m.start()] + m.group(0).replace(r["committed"], r["correct"], 1) + lines[i][m.end():]
        elif r["action"] == "DELETE":
            lines[i] = lines[i][:m.start()] + lines[i][m.end():]
        elif r["action"] != "KEEP":
            sys.exit("line %s: unknown action %r" % (r["line"], r["action"]))
    out = [l for l, o in zip(lines, old) if not (l.strip() == "" and o.strip() != "")]
    out.insert(after, header if header.endswith("\n") else header + "\n")
    sys.stdout.write("".join(out))


if __name__ == "__main__":
    main(sys.argv)
