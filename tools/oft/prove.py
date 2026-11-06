"""A change's functions, contracts and source lines in one report (`oft prove`, `./theorem prove`).

Between a base commit and a head commit of one fuzz target (a unit, <project>/<harness>), the report holds

    rows        (build, classify.Row) of each function of each build with a symbol fact at either commit: its class
                between the build's fact at the base and at the head (a build with a fact at one commit only has every
                function added, or removed)
    counts      the number of rows of each class (classify.CLASSES), over every build
    contracts   each contract file of the unit at the head (lint.CONTRACT_FILE) with its state, the first that holds:

        changed contract   its own file changed: it is new, its blob differs, or its work key's contract component
        needs work         a function it names from Symbols.v is changed, added or removed
        unknown            its work key (contracts.contract_keys) cannot be computed, at the head or at the base
        needs work         its work key differs from the base's in another component: a file it requires, the proof
                           environment, a function's kind or size, a data symbol's kind or size (why names them)
        data changed       its work key differs from the base's only in the bytes of data objects or sections it names,
                           each of the same kind and size at both commits (Ruling 22): Rocq decides, no agent is
                           predicted; the bytes may hold addresses that a relink moved
        unchanged          its work key is the base's

                then each contract file of the base that the head lacks, with the state removed.

The state is a prediction of which proofs need an agent, never a verdict: Rocq checks every proof.  A reference the
head's symbol fact cannot resolve (contracts.contract_keys: status "unresolved") is resolved through the base's
identifiers, so a contract on a removed function needs work; an identifier is never read as a symbol's name.  The
source lines of a function are the head's symbol fact's (the base's for a removed function).

Report, with rows as a list of (build, classify.Row) pairs (a Row names no build; a unit has up to four), markdown()
and markdown_parts() are the interface the pull request check consumes (OSSV-267 Task 7, check_run.payload): it reads
the counts, each contract's state and the rows, and posts the Markdown, or, past GitHub's limit, its parts with the
rows that fit.

This module is not the checker (keys.NOT_THE_CHECKER): no check reads a symbol fact or a contract key."""
import collections
import json

from . import classify, contracts, keys, layout, names, symbols

STATES = ("changed contract", "removed", "needs work", "unknown", "data changed", "unchanged")
# the states that predict an agent's work: the check's title counts them as contracts that need work (check_run)
PREDICTS_WORK = ("changed contract", "removed", "needs work")
# the states whose contract file itself differs from the base's: change_ledger counts them as contracts changed
EDITED = ("changed contract", "removed")
# the states whose rows a summary cut to GitHub's limit keeps before every other row (check_run._summary)
FIRST = PREDICTS_WORK + ("unknown",)
# the kinds of a symbol a contract may name whose bytes alone may change with no work predicted
DATA = ("object", "section")
# the classes of a function whose proofs need an agent: its instructions are other, new or gone
CHANGED_CLASSES = ("changed", "added", "removed")


class Report(collections.namedtuple("Report", "unit base head rows contracts counts")):
    """unit; the base and head commits, as full object ids; rows, [(build, classify.Row)], by build
    (names.BUILD_MODULE's order), then as classify orders them; contracts, one dict per contract file, by path (the
    removed ones last), with

        file        its path
        state       STATES
        why         what gives the state, joined by `; `
        base        contracts.contract_keys's base: how the base's key compares (None for a removed contract)
        changed     contracts.contract_keys's changed: the components of its work key that differ from the base's, as
                    data, or None when either key cannot be computed, the base has no such contract or the head has
                    none
        references  contracts.contract_keys's references: what it names from Symbols.v, resolved at the head or not
                    ([] for a removed contract)
        functions   {"build", "name", "class", "lines"} of each classified function it names, in the order of its
                    references: the head's function of that name, else the base's; for an unresolved reference, the
                    function the base's identifiers give it; lines from the head's fact (a removed function's from
                    the base's)

    and counts, {class: number of rows}."""


def _data_only(changed):
    """Whether each component of changed (contracts.contract_keys) is a data object or section of the same kind and size
    at the base and at the head, so that its bytes alone differ."""
    return all(c["type"] == "symbol" and c["before"] is not None and c["before"] == c["after"]
               and c["before"]["kind"] in DATA for c in changed)


def _commit(repo, ref):
    """The object id of the commit ref names."""
    try:
        return keys.git(repo, "rev-parse", "--verify", "--end-of-options", ref + "^{commit}").strip()
    except keys.NoKey:
        raise keys.NoKey("no commit %r" % ref)


def _functions(references, of, base_tables):
    """{"build", "name", "class", "lines"} of each classified function that references (contracts.contract_keys) name,
    once each: a resolved reference's symbol, and an unresolved one's identifier resolved through the base's identifiers
    (base_tables(), contracts.symbol_tables), never read as a name.  of is {(build, name): classify.Row}."""
    out, seen = [], set()
    for ref in references:
        name = ref["name"]
        if ref["status"] == "unresolved":
            row, _sized = symbols.resolve(base_tables().get(ref["build"]), ref["written"])
            name = None if row is None else row.name
        r = of.get((ref["build"], name))
        if r is not None and (ref["build"], name) not in seen:
            seen.add((ref["build"], name))
            out.append({"build": ref["build"], "name": name, "class": r.cls, "lines": (r.head or r.base).lines})
    return out


def _state(new, own, work, unknown, other):
    """(state, why) of a contract file the head has: new, whether the file is new; own, whether it or its work key's
    contract component changed; work, the classified functions it names whose class is in CHANGED_CLASSES; unknown,
    why its work key is unknown at the head or at the base, or None; other, the components of its key that differ
    from the base's beside its file and those functions.  One return per state, the first that holds as the module
    says."""
    why = ((["the contract file is new" if new else "the contract file changed"] if own else [])
           + ["%s:%s %s" % (fn["build"], fn["name"], fn["class"]) for fn in work] + ([unknown] if unknown else [])
           + (["changed: " + ", ".join(c["component"] for c in other)] if other else []))
    why = "; ".join(why) or "unchanged from the base"
    if own:
        return "changed contract", why
    if work or (other and not unknown and not _data_only(other)):
        return "needs work", why
    if unknown:
        return "unknown", why
    if other:
        return "data changed", why
    return "unchanged", why


def report(root, unit, base, head):
    """The Report of unit between the commits base and head of the repository at root.  ValueError for a unit that is
    not <project>/<harness>, or that has no symbol fact at either commit and no contract file at either; keys.NoKey for
    a commit or a file git cannot give, and a symbol fact that does not parse."""
    layout.split_unit(unit)
    base, head = _commit(root, base), _commit(root, head)
    ids = contracts.fact_ids(root, [unit], (base, head))
    before, after = contracts.load_facts(root, base, ids[unit, base]), contracts.load_facts(root, head, ids[unit, head])
    rows = [(b, r) for b in names.BUILD_MODULE if b in before or b in after
            for r in classify.classify(before[b][2] if b in before else [], after[b][2] if b in after else [])]
    counts = dict.fromkeys(classify.CLASSES, 0)
    for _b, r in rows:
        counts[r.cls] += 1
    got = contracts.contract_keys(root, unit, head, base)
    gone = sorted(set(contracts.contract_files(root, unit, base)) - set(got))
    if not got and not gone and not before and not after:
        raise ValueError("%s has no symbol fact and no contract file at %s or %s" % (unit, base, head))
    # each function by (build, name): the one the head has under that name, else the base's
    of = {}
    for b, r in rows:
        for n in r.names:
            if r.head is not None or (b, n) not in of:
                of[b, n] = r
    blob = keys.object_ids(root, ["%s:%s" % (c, f) for f in got for c in (base, head)])
    lazy = {}

    def base_tables():
        if "tables" not in lazy:
            lazy["tables"] = contracts.symbol_tables(before, base)
        return lazy["tables"]

    judged = []
    for f, k in sorted(got.items()):
        functions = _functions(k["references"], of, base_tables)
        work = [fn for fn in functions if fn["class"] in CHANGED_CLASSES]
        changed = k["changed"]
        new = blob["%s:%s" % (base, f)] == "-"
        own = (new or blob["%s:%s" % (base, f)] != blob["%s:%s" % (head, f)]
               or any(c["type"] == "contract" for c in changed or ()))
        unknown = k["unknown"] or ("at the base: " + k["base_unknown"] if k["base_unknown"] else None)
        named = {(fn["build"], fn["name"]) for fn in work}
        other = [c for c in changed or () if c["type"] != "contract" and (c["build"], c["name"]) not in named]
        state, why = _state(new, own, work, unknown, other)
        judged.append({"file": f, "state": state, "why": why,
                       "base": k["base"], "changed": changed, "references": k["references"],
                       "functions": functions})
    judged += [{"file": f, "state": "removed", "why": "the contract file is gone", "base": None, "changed": None,
                "references": [], "functions": []} for f in gone]
    return Report(unit, base, head, rows, judged, counts)


def _cell(text):
    """text in a cell of a Markdown table."""
    return text.replace("|", "\\|")


def _lines(lines):
    """A function's source lines, each file's span as code."""
    return "-" if lines == "-" else ", ".join("`%s`" % span for span in lines.split(","))


def markdown(r):
    """The Report r as Markdown: the count of contracts in each state, the count of functions in each class by build,
    each changed, added or removed function with its source lines, and each contract with its state and why."""
    head, (above_functions, functions), (above_contracts, contracts) = markdown_parts(r)
    return "\n".join(head + above_functions + functions + above_contracts + [line for _s, line in contracts]) + "\n"


def markdown_parts(r):
    """markdown(r) in parts, for a reader that keeps some rows only (check_run): the lines above its list of functions,
    then that list and the list of contracts, each as (its lines above its rows, its rows).  A function's row is its
    line; a contract's row is (its state, its line)."""
    p, h = r.unit.split("/")
    libs = [layout.proof_lib_dir(p, h, where) + "/" for where in layout.LAYOUTS]
    lib = next((d for d in libs if any(c["file"].startswith(d) for c in r.contracts)), None)
    states = collections.Counter(c["state"] for c in r.contracts)
    head = ["## theorem prove %s" % r.unit, "", "Base `%s`, head `%s`." % (r.base[:12], r.head[:12]), "",
            "| contracts | number |", "|---|---|"]
    head += ["| %s | %d |" % (s, states[s]) for s in STATES]
    per = collections.Counter((b, row.cls) for b, row in r.rows)
    head += ["", "| functions | %s |" % " | ".join(classify.CLASSES), "|---|%s" % ("---|" * len(classify.CLASSES))]
    head += ["| %s | %s |" % (b, " | ".join(str(per[b, c]) for c in classify.CLASSES))
             for b in dict.fromkeys(b for b, _row in r.rows)]
    head.append("| all | %s |" % " | ".join(str(r.counts[c]) for c in classify.CLASSES))
    above, rows = ["", "### Functions whose instructions changed", ""], []
    work = [(b, row) for b, row in r.rows if row.cls in CHANGED_CLASSES]
    if work:
        above += ["| build | class | function | source lines |", "|---|---|---|---|"]
        rows = ["| %s | %s | %s | %s |" % (b, row.cls, ", ".join("`%s`" % _cell(n) for n in row.names),
                                           _cell(_lines((row.head or row.base).lines))) for b, row in work]
    else:
        above.append("No function changed, was added or was removed.")
    functions = (above, rows)
    above, rows = ["", "### Contracts", ""], []
    if r.contracts:
        if lib:
            above += ["Paths are in `%s`." % lib.rstrip("/"), ""]
        above += ["| contract | state | why |", "|---|---|---|"]
        rows = [(c["state"], "| `%s` | %s | %s |" % (
            _cell(c["file"][len(lib):] if lib and c["file"].startswith(lib) else c["file"]), c["state"],
            _cell(c["why"]))) for c in sorted(r.contracts, key=lambda c: (STATES.index(c["state"]), c["file"]))]
    else:
        above.append("No contract file.")
    return head, functions, (above, rows)


def _place(s):
    return None if s is None else {"address": "0x%x" % s.address, "size": s.size}


def as_json(r):
    """The Report r as JSON data: every function of every build with its class, names, source lines and address and
    size in each build, and each contract as Report says."""
    return {"unit": r.unit, "base": r.base, "head": r.head, "counts": r.counts, "contracts": r.contracts,
            "functions": [{"build": b, "class": row.cls, "names": list(row.names),
                           "lines": (row.head or row.base).lines, "base": _place(row.base), "head": _place(row.head)}
                          for b, row in r.rows]}


def with_symbol_facts(root, units, base, head):
    """[(unit, whether it has a symbol fact at the commit base or at head)] of each of units, in their order: pr.yml's
    prove job reports only on a unit that has one.  ValueError for a name that is not <project>/<harness>; keys.NoKey
    for a commit git cannot give."""
    for unit in units:
        layout.split_unit(unit)
    base, head = _commit(root, base), _commit(root, head)
    ids = contracts.fact_ids(root, units, (base, head)) if units else {}
    return [(u, any(ids[u, c] for c in (base, head))) for u in units]


def run(root, unit, base, head, as_json_, out):
    """`oft prove`: the report of unit between base and head to out, as Markdown or, with as_json_, as JSON, or why
    there is none: the Report, whatever the states it holds, or None."""
    try:
        r = report(root, unit, base, head)
    except (ValueError, keys.NoKey) as e:
        print("FAIL oft prove: %s" % e, file=out)
        return None
    if as_json_:
        json.dump(as_json(r), out, sort_keys=True)
        out.write("\n")
    else:
        out.write(markdown(r))
    return r
