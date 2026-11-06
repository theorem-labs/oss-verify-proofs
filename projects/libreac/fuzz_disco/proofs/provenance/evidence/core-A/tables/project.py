#!/usr/bin/env python3
"""project.py SRC OUT [--drop-comments] [--drop-col NAME]... [--neutral]

Writes a shipped table from its working table. The values are not changed: the script only
  --drop-comments   drops the lines that start with '#' (header notes; the MANIFEST role text carries their facts),
  --drop-col NAME   drops the tab-separated column whose header cell is NAME (a column of people's names),
  --neutral         removes the attribution clauses in free text that name a person or a working session
                    (`per <name> <hh:mm>Z`, `, <name> 0 MISMATCH`, `<name>'s GENERATED`) and writes the old name of
                    the address-map tool as `the address map`.
It prints how many lines and substitutions it changed, so a reader can compare with the source.
"""
import re, sys

NAME = r"[a-z]-[a-z]+(?:-[a-z0-9]+)*"
RULES = [
    (re.compile(rf" per {NAME} \d\d:\d\dZ"), ""),
    (re.compile(rf", {NAME} 0 MISMATCH"), ", 0 MISMATCH"),
    (re.compile(rf"in {NAME}'s GENERATED"), "in the GENERATED"),
    (re.compile(r"was [a-z]+ big (\.text run mispairing)"), r"was a big \1 of the address map"),
]


def main():
    a = sys.argv[1:]
    src, out, opts = a[0], a[1], a[2:]
    drop_comments = '--drop-comments' in opts
    neutral = '--neutral' in opts
    drop = [opts[i + 1] for i, o in enumerate(opts) if o == '--drop-col']
    lines = open(src).read().split('\n')
    dropped = subs = 0
    if drop_comments:
        keep = [l for l in lines if not l.startswith('#')]
        dropped, lines = len(lines) - len(keep), keep
    if drop:
        head = lines[0].split('\t')
        idx = [head.index(c) for c in drop]
        lines = ['\t'.join(c for i, c in enumerate(l.split('\t')) if i not in idx) if l else l for l in lines]
    if neutral:
        new = []
        for l in lines:
            for rx, rep in RULES:
                l, n = rx.subn(rep, l)
                subs += n
            new.append(l)
        lines = new
    open(out, 'w').write('\n'.join(lines))
    print(f'project: {out}: {dropped} comment lines dropped, columns dropped {drop or "none"}, {subs} substitutions')


if __name__ == '__main__':
    main()
