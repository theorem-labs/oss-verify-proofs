"""The class of each function between two builds (`oft classify`), from their symbol facts (symbols.py).

A function is the names of a fact that share an address and a size: a name and its aliases.  A fact's data objects
(kind object) and its functions of size 0 (musl's _start), which have no bytes to compare, are not classified: no row
names one.  The two builds' functions are matched through their names, in order:

  * a name with one function in each build matches those two;
  * then a name with more functions in either build (static functions of different files) matches each of its
    functions first with the one an alias of that function already matched it with, so that aliases stay together,
    then with one at the same address with the same exact bytes, then with one of the same masked bytes, in address
    order; each match it makes holds for the names after it.

The names that match one pair of functions are one row, whose class is

    identical   the same bytes at the same address
    moved       the same masked bytes: only an address immediate, or the address, differs
    changed     other masked bytes
    added       a name only the head has, or a head function of a duplicate name that no base function matched
    removed     a name only the base has, or a base function of a duplicate name that no head function matched

So a name that leaves a function whose other names stay is a removed row of its own: a contract that names it has no
function in the head.  Classification is a hint for who updates a proof; Rocq checks every proof.

This module is not the checker (keys.NOT_THE_CHECKER): no check reads a symbol fact."""
import collections
import json

from . import facts, symbols

CLASSES = ("identical", "moved", "changed", "added", "removed")


class Row(collections.namedtuple("Row", "cls names base head")):
    """One function of two builds: its class (CLASSES), its names, sorted (for a function of both builds, the names
    they share), and the symbols.Sym of the first of them in the base and in the head (None in a build without it)."""


def _class(base, head):
    if base.exact == head.exact and base.address == head.address:
        return "identical"
    return "moved" if base.masked == head.masked else "changed"


def _functions(syms):
    """({name: [function]}, {(function, name): Sym}) of the functions of syms with a size (kind func; a data object is
    none, and a function of size 0 has no bytes to compare), where a function is (address, size): each name's
    functions by address, a row repeated at the same address and size once."""
    rows, of = {}, collections.defaultdict(list)
    for s in syms:
        if s.kind != "func" or s.size == 0:
            continue
        f = (s.address, s.size)
        if (f, s.name) not in rows:
            rows[f, s.name] = s
            of[s.name].append(f)
    return {name: sorted(fs) for name, fs in of.items()}, rows


def classify(base, head):
    """[Row] of every function of two builds' symbol facts, base and head ([symbols.Sym]): by base address, then the
    added functions by head address."""
    (old, old_rows), (new, new_rows) = _functions(base), _functions(head)
    # the bytes of a function: aliases share them, so any of its names' Sym holds them
    old_body = {f: s for (f, _name), s in old_rows.items()}
    new_body = {f: s for (f, _name), s in new_rows.items()}
    pairs = collections.defaultdict(list)   # (base function, head function) -> names
    gone = collections.defaultdict(list)    # base function -> names
    came = collections.defaultdict(list)    # head function -> names
    names = sorted(old.keys() | new.keys())
    unique = {n for n in names if len(old.get(n, ())) == 1 and len(new.get(n, ())) == 1}
    for n in unique:
        pairs[old[n][0], new[n][0]].append(n)
    matches = (lambda b, h: (b, h) in pairs,
               lambda b, h: b[0] == h[0] and old_body[b].exact == new_body[h].exact,
               lambda b, h: old_body[b].masked == new_body[h].masked)
    for n in names:
        if n in unique:
            continue
        bs, hs = list(old.get(n, ())), list(new.get(n, ()))
        for same in matches:
            for b in list(bs):
                h = next((h for h in hs if same(b, h)), None)
                if h is not None:
                    pairs[b, h].append(n)
                    bs.remove(b)
                    hs.remove(h)
        for b in bs:
            gone[b].append(n)
        for h in hs:
            came[h].append(n)
    rows = []
    for (b, h), ns in pairs.items():
        ns = tuple(sorted(ns))
        first_b, first_h = old_rows[b, ns[0]], new_rows[h, ns[0]]
        rows.append(Row(_class(first_b, first_h), ns, first_b, first_h))
    rows += [Row("removed", tuple(ns), old_rows[b, ns[0]], None) for b, ns in gone.items()]
    rows += [Row("added", tuple(ns), None, new_rows[h, ns[0]]) for h, ns in came.items()]
    return sorted(rows, key=lambda r: (r.base is None, (r.base or r.head).address, r.names))


def _json(s):
    """A Sym as JSON, its address written as a symbol fact writes it."""
    return None if s is None else dict(s._asdict(), address="0x%x" % s.address)


def _place(s):
    """A Sym's address and size, as columns of the table; `-` in a build without it."""
    return ("-", "-") if s is None else ("0x%x" % s.address, str(s.size))


def run(base, head, as_json, out):
    """`oft classify`: the rows of classify() between the symbol facts at the paths base and head, and a count per
    class, to out, as a table or, with as_json, as JSON; or which fact did not load, and why.  The exit status."""
    loaded = []
    for path in (base, head):
        try:
            loaded.append(symbols.load(path)[1])
        except (OSError, ValueError, facts.BoundedFileError) as e:
            print("FAIL oft classify: %s: %s" % (path, e), file=out)
            return 1
    rows = classify(*loaded)
    counts = dict.fromkeys(CLASSES, 0)
    for r in rows:
        counts[r.cls] += 1
    if as_json:
        json.dump({"rows": [{"class": r.cls, "names": list(r.names), "base": _json(r.base), "head": _json(r.head)}
                            for r in rows], "counts": counts}, out)
        out.write("\n")
        return 0
    print("class\tnames\tbase_address\tbase_size\thead_address\thead_size", file=out)
    for r in rows:
        # a name holds no white space (symbols._row), so a space joins aliases without ambiguity
        print("\t".join((r.cls, " ".join(r.names), *_place(r.base), *_place(r.head))), file=out)
    print("%d functions: %s" % (len(rows), ", ".join("%d %s" % (counts[c], c) for c in CLASSES)), file=out)
    return 0
