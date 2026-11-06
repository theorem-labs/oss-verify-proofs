"""oft approvals: write approvals.yaml from the proofs a checkout holds.

FILE lists fuzz targets, one per line: `<project>/<harness>`; for proofs that began as a submission, a tab, the
record of the review that cleared them, a tab and the statements that record covers, separated by commas (a record
always names them).  Blank lines and lines that start with # are skipped.  Each line becomes an entry, one per source:
a record line names the statements of its fuzz target that have a proof in its proofs folder and that the
record covers; a bare line (no record) is this repository's entry and names every statement with a proof no
record line of the same fuzz target covers, so a bare line alone names every proof.  A fuzz target may be on several
lines: at most one bare line, and record lines with different records whose statements do not overlap.  It refuses a
name that is not an included fuzz target or a covered name that is not a statement of its fuzz target.  A refutation
is never listed, nor a fuzz target of a project a finding holds back: each is reported, as are a line whose
statements have no proof, a proof no line of its fuzz target covers, and a fuzz target whose lib/ the release will
keep while some of its proofs are not listed.  An entry already in approvals.yaml for the same fuzz target, origin
and record, with the same statements, keeps its approved_by and date; only a new or changed entry takes
--approved-by and --date.  An enrollment entry (origin enrollment) comes from the merge of its project's enrollment
pull request, not from FILE: each one in approvals.yaml is kept as written, and a bare line of its fuzz target names
only the proofs it does not list; nothing is written when approvals.yaml is there but cannot be read, or holds an
enrollment entry that does not match the schema.  The entries are sorted by fuzz target, origin and record, so the
same checkout and list give the same file.  The file is checked against its schema and the rules before it is written.
"""
import os
import sys

from . import facts, release_tree, rules, schema, yamlio

SCHEMA = "oss-fuzz-theorems/approvals/1"


def _read_list(listing, out):
    """{fuzz target: {record or None: covered statements or None}}, or None after printing why the list is refused."""
    wanted = {}
    try:
        with open(listing, encoding="utf-8") as f:
            lines = f.read().splitlines()
    except OSError as e:
        print("%s: %s" % (listing, e.strerror or e), file=out)
        return None
    for n, line in enumerate(lines, 1):
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        cols = line.split("\t")
        why = None
        if len(cols) > 3:
            why = "more than three fields"
        elif any(c != c.strip() or not c for c in cols):
            why = "an empty field, or spaces around one: %r" % line
        elif len(cols) == 2:
            why = "a record must name the statements it covers, in a third field: %r" % line
        record = cols[1] if len(cols) > 1 else None
        covers = set(cols[2].split(",")) if len(cols) > 2 else None
        lines_of = wanted.setdefault(cols[0], {})
        if not why and record in lines_of:
            why = ("%s is listed twice" % cols[0]) if record is None \
                else "%s is listed twice with record %s" % (cols[0], record)
        if not why and covers is not None:
            both = sorted(s for other in lines_of.values() if other is not None for s in covers & other)
            if both:
                why = "%s: %s covered by two records" % (cols[0], ", ".join(both))
        if why:
            print("%s:%d: %s" % (listing, n, why), file=out)
            return None
        lines_of[record] = covers
    return wanted


def _previous(tree):
    """{(fuzz target, origin, record): entry} of the approvals.yaml already in the checkout, as far as it can be read."""
    try:
        doc = yamlio.load_file(tree.path("approvals.yaml")) if os.path.isfile(tree.path("approvals.yaml")) else None
    except Exception:
        return {}
    old = doc.get("fuzz_targets") if isinstance(doc, dict) else None
    return {(e["fuzz_target"], e.get("origin"), e.get("record")): e
            for e in old if isinstance(e, dict) and isinstance(e.get("fuzz_target"), str)} \
        if isinstance(old, list) else {}


def _enrolled(tree):
    """{index in fuzz_targets: entry} of the enrollment entries of the approvals.yaml in the checkout, as written ({}
    when it has none), or None when the file is there but cannot be read."""
    if not os.path.isfile(tree.path("approvals.yaml")):
        return {}
    try:
        doc = yamlio.load_file(tree.path("approvals.yaml"))
    except Exception:
        return None
    old = doc.get("fuzz_targets") if isinstance(doc, dict) else None
    return {i: e for i, e in enumerate(old) if isinstance(e, dict) and e.get("origin") == "enrollment"} \
        if isinstance(old, list) else {}


def write(root, listing, approved_by, date, out=sys.stdout):
    wanted = _read_list(listing, out)
    if wanted is None:
        print("oft approvals: the list is malformed; nothing written", file=out)
        return 1
    tree = facts.load(root)
    previous = _previous(tree)
    enrolled = _enrolled(tree)
    if enrolled is None:
        print("oft approvals: approvals.yaml cannot be read, so its enrollment entries cannot be kept; nothing "
              "written: repair it, or remove it when it holds no enrollment entry, and run oft approvals again",
              file=out)
        return 1
    bad = [p for i, e in enrolled.items()
           for p in schema.validate_def("approvals", "approval", e, "approvals.yaml: approvals.fuzz_targets[%d]" % i)]
    if bad:
        for p in bad:
            print("error: " + p, file=out)
        print("oft approvals: %d problem(s) in the enrollment entries it keeps as written; nothing written" % len(bad),
              file=out)
        return 1
    # the statements each fuzz target's enrollment entries list
    ceiling = {}
    for e in enrolled.values():
        ceiling.setdefault(e["fuzz_target"], set()).update(e["statements"])
    # the file this writes is not an input, but for its enrollment entries: an outdated one must not stop it
    tree.approvals = None
    tree.errors = [e for e in tree.errors if not e.startswith("approvals.yaml")]
    rules.check(tree)
    if tree.errors:
        for e in tree.errors:
            print("error: " + e, file=out)
        print("oft approvals: %d error(s) in the facts; nothing written" % len(tree.errors), file=out)
        return 1
    harnesses = {"%s/%s" % (h.project.name, h.name): h for h in tree.harnesses()}
    unknown = ["%r is not an included fuzz target" % u for u in sorted(wanted) if u not in harnesses]
    unknown += ["%r is not a statement of %s" % (s, u) for u in sorted(wanted) if u in harnesses
                for s in sorted(set().union(*(c for c in wanted[u].values() if c)) - set(harnesses[u].statements))]
    if unknown:
        for u in unknown:
            print("error: %s" % u, file=out)
        print("oft approvals: %d name(s) that are not included fuzz targets or their statements; nothing written"
              % len(unknown), file=out)
        return 1
    held = facts.hold(tree)
    held_ids = held.ids
    proved, refuted, dirs = {}, [], {}
    for sid, pd in tree.proofs.items():
        p, h, s = sid.split("/")
        dirs.setdefault("%s/%s" % (p, h), set()).add(s)
        if pd.refutes:
            refuted.append(sid)
        else:
            proved.setdefault("%s/%s" % (p, h), set()).add(s)
    entries, missing, uncovered, withheld, partial, held_out = [], [], [], [], [], []
    for unit in sorted(wanted):
        p = unit.partition("/")[0]
        if p in held.whole:
            withheld.append(unit)
            continue
        proofs = proved.get(unit, set())
        # what the record lines and the enrollment entries of the fuzz target cover; a bare line names the other proofs
        recorded = set().union(ceiling.get(unit, set()), *(c for c in wanted[unit].values() if c is not None))
        if None not in wanted[unit]:
            uncovered += ["%s/%s" % (unit, s) for s in sorted(proofs - recorded)]
        # the proofs of its enrollment entries that the release keeps
        listed = {s for s in ceiling.get(unit, ()) if s in proofs and "%s/%s" % (unit, s) not in held_ids}
        # submission sorts before this-repository, then by record: the order of the entries in the file
        for record in sorted(wanted[unit], key=lambda r: (r is None, r or "")):
            covers = wanted[unit][record]
            statements = proofs & covers if covers is not None else proofs - recorded
            cut = {s for s in statements if "%s/%s" % (unit, s) in held_ids}
            held_out += ["%s/%s" % (unit, s) for s in sorted(cut)]
            statements -= cut
            if not statements:
                # a line whose every proof is held has proofs: its held lines say why it is not listed; so has a bare
                # line whose proofs its fuzz target's enrollment entries list
                if not cut and not (covers is None and proofs & ceiling.get(unit, set())):
                    missing.append("%s, record %s" % (unit, record) if record else unit)
                continue
            listed |= statements
            e = {"fuzz_target": unit, "statements": sorted(statements), "approved_by": approved_by, "date": date,
                 "origin": "submission" if record else "this-repository"}
            if record:
                e["record"] = record
            old = previous.get((unit, e["origin"], record), {})
            if old.get("statements") == e["statements"] \
                    and isinstance(old.get("approved_by"), str) and isinstance(old.get("date"), str):
                e["approved_by"], e["date"] = old["approved_by"], old["date"]
            entries.append(e)
        if listed and dirs.get(unit, set()) - listed and unit in tree.proof_libs:
            partial.append(unit)
    for unit in withheld:
        if unit.split("/")[0] in held.held:
            print("held by a finding that is not public: %s" % unit, file=out)
        else:
            print("its project is private (release: private), not listed: %s" % unit, file=out)
    for sid in held_out:
        print("held by an open finding: %s" % sid, file=out)
    for unit in missing:
        print("listed, no proof yet: %s" % unit, file=out)
    for sid in uncovered:
        print("a proof its record does not cover, not listed: %s" % sid, file=out)
    for sid in sorted(s for s in refuted if s.rsplit("/", 1)[0] in wanted):
        print("a refutation, not listed: %s" % sid, file=out)
    for unit in partial:
        print("the release will have " + release_tree.PARTIAL % unit, file=out)
    # the enrollment entries as written, among the entries this writes, by fuzz target, origin and record
    entries = sorted(entries + list(enrolled.values()),
                     key=lambda e: (e["fuzz_target"], e["origin"], e.get("record", "")))
    doc = {"schema": SCHEMA, "fuzz_targets": entries}
    problems = schema.validate("approvals", doc)
    if not problems:
        tree.approvals = doc
        rules.check(tree)
        problems = tree.errors
    if problems:
        for p in problems:
            print("error: " + p, file=out)
        print("oft approvals: %d problem(s); nothing written" % len(problems), file=out)
        return 1
    with open(tree.path("approvals.yaml"), "w", encoding="utf-8") as f:
        f.write(yamlio.dump(doc))
    print("oft approvals: %d fuzz target(s) in %d entries, %d statement(s) written to approvals.yaml; %d line(s) "
          "with no proof yet, %d proof(s) outside their record"
          % (len({e["fuzz_target"] for e in entries}), len(entries),
             sum(len(e["statements"]) for e in entries), len(missing), len(uncovered)), file=out)
    return 0
