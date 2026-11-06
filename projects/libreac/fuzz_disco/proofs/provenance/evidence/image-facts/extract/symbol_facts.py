#!/usr/bin/env python3
"""symbol_facts.py -- two facts the listing commands take from a symbol table extract (symbol_table.py output).

  range FIRST LAST   prints `LO HI` (hex without 0x): the address of function FIRST and the end (address + size)
                     of function LAST; function symbols are types t, T, w, W. This is the program code range the
                     listing covers.
  addr NAME          prints the address (hex without 0x) of symbol NAME.
A name that is missing or has more than one address is an error (exit 1).

Usage: symbol_facts.py SYMS range FIRST LAST
       symbol_facts.py SYMS addr NAME
"""
import sys


def table(path, names, kinds):
    found = {}
    for line in open(path):
        f = line.split()
        if len(f) == 4 and f[3] in names and (kinds is None or f[2] in kinds):
            found.setdefault(f[3], set()).add((int(f[0], 16), int(f[1], 16)))
    for n in names:
        if len(found.get(n, ())) != 1:
            sys.exit("%s: %d addresses for %s" % (path, len(found.get(n, ())), n))
    return {n: next(iter(v)) for n, v in found.items()}


def main():
    a = sys.argv[1:]
    if len(a) == 4 and a[1] == "range":
        t = table(a[0], (a[2], a[3]), "tTwW")
        print("%x %x" % (t[a[2]][0], t[a[3]][0] + t[a[3]][1]))
    elif len(a) == 3 and a[1] == "addr":
        print("%x" % table(a[0], (a[2],), None)[a[2]][0])
    else:
        sys.exit(__doc__)


if __name__ == "__main__":
    main()
