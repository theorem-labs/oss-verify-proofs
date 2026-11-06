"""oft revisions PREVIOUS [--earlier OLDER...] [--write-pins] [--repin-changed] [--write-revisions]: each statement of
this tree beside the same statement in PREVIOUS, a checkout of the previous release (docs/versioning.md).

These tools fingerprint both trees, so a change to how a fingerprint is computed (facts.FINGERPRINT_TAG) changes no
statement, and a statement whose two fingerprints differ changed its meaning.  Taking PREVIOUS's facts through these
tools would also hide a change to how a statement is rendered (shapes.py, templates/): so a statement of PREVIOUS whose
generated code, written by that release's own tools, is not what these tools render from the same facts is
re-rendered, and its meaning changed too.  So does every statement's when the model (its name, version or commit) or
the Rocq package or version differs (model-changed): the fingerprint hashes only the model's version, which reads
`unreleased` until the model is released.  Withheld in either tree, a statement has no fingerprint to compare and no
expected revision.  A statement whose meaning changed has the previous revision plus one; any
other keeps its revision; a statement new in this tree has revision 1.  A proof whose statement kept its meaning
carries forward; one whose statement changed is re-checked; one that is gone is retired.  With write_pins, the pin of
each proof that carries forward is set to its statement's fingerprint here, when it still holds the pin it had in
PREVIOUS; with repin_changed, also the pin of each proof that holds its statement's fingerprint in PREVIOUS when that
fingerprint changed (stale_pins).  With write_revisions, each statement whose revision is not the one it must have is
given that one in harness.yaml (revised).

A release leaves out what a finding or `release: private` holds back, so a statement can be missing from PREVIOUS and
back in this tree.  Its identifier is never reused (docs/versioning.md), so it is compared with the newest of the
earlier releases (OLDER, checkouts of the releases before PREVIOUS, newest first) that has it, as with PREVIOUS: it
keeps that release's revision, or adds one if its meaning changed since.  A statement none of them has is new.  The
releases must come strictly newest first, by date and, on one date, by release (release_order), or nothing is compared:
two candidates of one day named oldest first would compare with the older one, and reuse a revision.
"""
import os
import re
import sys

import yaml

from . import facts, generate, port, release_tree, rocq, yamlio

COLUMNS = ("id", "previous_revision", "revision", "expected_revision", "statement", "proof")
STATEMENT = ("same", "changed", "re-rendered", "model-changed", "new", "gone", "unfingerprinted")
PROOF = ("carried-forward", "re-check", "retired", "new")
# a Rocq sentence ends at a period followed by a blank; rocq.code leaves one space or the end of the text
_SENTENCE_END = re.compile(r"\.(?: |$)")
_DEFINITION = re.compile(r"Definition ([^\s(]+)")


def model(tree):
    """What a statement's meaning rests on beside its fingerprint: the model's name, version and commit and the Rocq
    package and version of tree's release.yaml.  The fingerprint hashes only the model's version, which reads
    `unreleased` until the model is released."""
    r = tree.release or {}
    sem, rq = r.get("semantics") or {}, r.get("rocq") or {}
    return tuple((k, sem.get(k)) for k in ("name", "version", "commit")) + tuple(
        ("rocq " + k, rq.get(k)) for k in ("package", "version"))


def _code(path):
    """The code (rocq.code) of the Rocq file at path, read with no newline translation, or None if there is none."""
    return rocq.code(facts.read_raw(path)) if os.path.isfile(path) else None


def _definitions(code, names):
    """(every other sentence, {name: its Definition} for each of names) of the code of a Statements.v, or (None, {})
    for no file.  A Definition of another name, which a statement may use, is one of the other sentences.  The other
    sentences keep a marker where each statement's Definition stood, so a sentence that moves across a Definition (a
    scope opened before it instead of after it, say) changes the rest: it can change how the Definition parses."""
    if code is None:
        return None, {}
    rest, defs = [], {}
    for s in _SENTENCE_END.split(code):
        m = _DEFINITION.match(s)
        if m and m.group(1) in names:
            defs[m.group(1)] = s
            rest.append("Definition " + m.group(1))
        else:
            rest.append(s)
    return rest, defs


def rerendered(tree):
    """The ids of tree's statements whose generated code in tree is not what these tools render from tree's facts:
    the code of their Definition in Statements.v, of the rest of Statements.v or of the harness's Images.v, or, for a
    bound, of Distribution.v.  Comments and layout do not count."""
    ids = set()
    for h in tree.harnesses():
        if not h.builds():
            continue
        names = {st.name for st in h.statements.values()}
        rest, defs = _definitions(_code(tree.path(h.dir, "Statements.v")), names)
        new_rest, new_defs = _definitions(rocq.code(generate.statements_v(h)), names)
        whole = rest != new_rest or _code(tree.path(h.dir, "Images.v")) != rocq.code(generate.images_v(h))
        bounds = "distribution" in h.data and (
            _code(tree.path(h.dir, "Distribution.v")) != rocq.code(generate.distribution_v(h)))
        for st in h.statements.values():
            if whole or defs.get(st.name) != new_defs.get(st.name) or (bounds and st.kind == "bound"):
                ids.add(st.id)
    return ids


def release_order(tree):
    """The order releases come out in, as a sort key of a checkout: its release.yaml's date, then its release, where a
    candidate `-rc.N` comes by N, before the release it is a candidate of."""
    base, _, rc = tree.release["release"].partition("-rc.")
    return str(tree.release["date"]), tuple(int(n) for n in base.split(".")), (0, int(rc)) if rc else (1, 0)


def compare(cur, releases):
    """One row per statement of cur or of the previous release: (id, its Statement in the release it is compared with or
    None, in cur or None, expected revision or None, statement, proof).  releases: (tree, its rerendered ids
    (rerendered), whether its model() differs from cur's) for the previous release and each before it, newest first;
    a statement of cur is compared with the newest of them that has it.  statement is one of STATEMENT: re-rendered
    when its fingerprints are the same but its id is in that release's rerendered ids; model-changed when its
    fingerprints are the same but that release's model differs; unfingerprinted when it is withheld in a tree, so that
    there is nothing to compare and no revision is expected.  proof is one of PROOF, or "-"."""
    old = {}
    for tree, ids, changed in releases:
        for s in tree.statements():
            old.setdefault(s.id, (s, ids, changed))
    in_prev = {s.id for s in releases[0][0].statements()}
    new = {s.id: s for s in cur.statements()}
    rows = []
    for sid in sorted(in_prev | set(new)):
        a, ids, changed = old.get(sid, (None, frozenset(), False))
        b = new.get(sid)
        if b is None:
            what, expected = "gone", None
        elif a is None:
            what, expected = "new", 1
        elif not (a.fingerprint and b.fingerprint):
            what, expected = "unfingerprinted", None
        elif a.fingerprint != b.fingerprint:
            what, expected = "changed", a.revision + 1
        elif sid in ids:
            what, expected = "re-rendered", a.revision + 1
        elif changed:
            what, expected = "model-changed", a.revision + 1
        else:
            what, expected = "same", a.revision
        had, has = bool(a and a.proof), bool(b and b.proof)
        if had and has:
            proof = "carried-forward" if what == "same" else "re-check"
        else:
            proof = "retired" if had else "new" if has else "-"
        rows.append((sid, a, b, expected, what, proof))
    return rows


def stale_pins(rows, changed=False):
    """The statement, in this tree, of each proof that carries forward and still holds the pin it had in PREVIOUS,
    when that pin is not the statement's fingerprint here.

    With changed, also of each proof that is re-checked or new and holds its statement's fingerprint in PREVIOUS, when
    the statement's fingerprint here is another: the proof was written for the statement as PREVIOUS states it.  Use it
    only for a change whose re-check is the next corpus run, such as a change to the code of Shapes.v, which moves every
    fingerprint; never to silence a proof that failed, since the new pin says nothing of whether the proof still checks.
    A new proof counts so that a proof branch made before such a change, once it has merged the base that has the
    change, is re-pinned when compared with that base's commit before the change, which has none of the branch's
    proofs.  That commit is not a release, so the revisions expected against it are not a release's: write none then
    (write_revisions).  A re-checked or new proof whose pin is neither fingerprint is never rewritten."""
    out = []
    for _sid, a, b, _e, _w, proof in rows:
        if proof == "carried-forward":
            pin = b.proof.data["fingerprint"]
            if pin == a.proof.data["fingerprint"] and pin != b.fingerprint:
                out.append(b)
        elif changed and proof in ("re-check", "new") and a is not None and a.fingerprint and b.fingerprint:
            if b.proof.data["fingerprint"] == a.fingerprint and a.fingerprint != b.fingerprint:
                out.append(b)
    return out


def repinned(text, fingerprint, where):
    """text, a proof.yaml's, with the value of its top-level fingerprint set to fingerprint and nothing else changed:
    its quotes, its comments and its line ends stay."""
    node = yaml.compose(text, Loader=yamlio.StrictLoader)
    pins = [v for k, v in (node.value if isinstance(node, yaml.MappingNode) else ()) if k.value == "fingerprint"]
    # a plain scalar's style is "" from the C loader (yamlio.StrictLoader is a CSafeLoader), None from the Python one
    if len(pins) != 1 or not isinstance(pins[0], yaml.ScalarNode) or pins[0].style not in (None, "", '"', "'"):
        raise ValueError("%s: no plain or quoted top-level fingerprint" % where)
    v, quote = pins[0], pins[0].style or ""
    return text[:v.start_mark.index] + quote + fingerprint + quote + text[v.end_mark.index:]


def pinned_files(tree, statements):
    """[(path, its text)] of each statement's proof.yaml with its pin set to the statement's fingerprint (repinned)."""
    out = []
    for st in statements:
        path = tree.path(st.proof.path, "proof.yaml")
        out.append((path, repinned(facts.read_raw(path), st.fingerprint, path)))
    return out


def revised(text, revisions, where):
    """text, a harness.yaml's, with the revision of each statement {name: revision} set and nothing else changed: a
    revision other than 1 is the value of the statement's `revision:`, a line added after its `status:` line when it has
    none; revision 1, the default, is no line.  Its comments and line ends stay.  A statement must be a block mapping
    whose `status:` and `revision:` are each one line of their own, as yamlio.dump writes them."""
    statements = yamlio.mapping_value(yamlio.compose(text), "statements")
    lines = text.splitlines(True)
    for name, revision in revisions.items():
        st = yamlio.mapping_value(statements, name)
        if not isinstance(st, yaml.MappingNode) or st.flow_style:
            raise ValueError("%s: statement %s is not a block mapping" % (where, name))
        keys = {k.value: (k, v) for k, v in st.value}
        key, value = keys["revision"] if "revision" in keys else keys["status"]
        n, line = key.start_mark.line, lines[key.start_mark.line]
        if line[:key.start_mark.column].strip() or not isinstance(value, yaml.ScalarNode) or value.end_mark.line != n:
            raise ValueError("%s: statement %s: its %s is not one line of its own" % (where, name, key.value))
        if key.value == "status":
            body = line.rstrip("\r\n")
            eol = line[len(body):]
            lines[n] = body + (eol or "\n") + line[:key.start_mark.column] + "revision: %d" % revision + eol
        elif revision == 1:
            lines[n] = ""
        else:
            lines[n] = line[:value.start_mark.column] + str(revision) + line[value.end_mark.column:]
    return "".join(lines)


def revised_files(tree, rows):
    """[(path, its text)] of each harness.yaml that has a statement whose revision is not the one it must have, with
    each such revision set (revised).  A new statement's revision is never lowered: a statement that a release before
    the previous one has, and that the previous release held back, is new when that release is not named, and its
    revision 2 there is not wrong.  So a new statement above revision 1 is refused (ValueError), before any file."""
    above = [(sid, b.revision) for sid, _a, b, expected, what, _p in rows if what == "new" and b.revision > expected]
    if above:
        (sid, revision), more = above[0], len(above) - 1
        raise ValueError("%s: revision %d, and it is new%s: --write-revisions never lowers a new statement's revision; "
                         "if a release before the previous one has it, name that release with --earlier; if no release "
                         "has it, remove its revision: line"
                         % (sid, revision, " (and %d more new statements like it)" % more if more else ""))
    by_file = {}
    for _sid, _a, b, expected, _w, _p in rows:
        if expected is not None and b.revision != expected:
            by_file.setdefault(tree.path(b.harness.dir, "harness.yaml"), {})[b.name] = expected
    return [(path, revised(facts.read_raw(path), names, path)) for path, names in by_file.items()]


def not_released(tree):
    """The files of release_tree.INTERNAL that tree holds.  A release is a tree `oft release-tree` cut, and it removes
    every one of them, so a tree that holds one is a commit of this repository, not a release: compared with it, a
    statement's revision is not the one a release needs."""
    return [f for f in release_tree.INTERNAL if os.path.lexists(tree.path(f))]


def render_command(root):
    """The command that renders root's generated files again, as root's own tools spell it: `./oft generate`, with
    --skip-shared when they offer it (port.offers_skip_shared, the one reading of the flag; the shared files, the index
    among them, are then rendered after the merge)."""
    return "./oft generate --skip-shared" if port.offers_skip_shared(root) else "./oft generate"


WHY = {"same": "its meaning is the same as in the previous release",
       "changed": "its meaning changed since the previous release",
       "re-rendered": "these tools render it otherwise than the previous release's did",
       "model-changed": "the model it is stated in changed since the previous release",
       "new": "it is new"}


def run(root, previous, write_pins=False, earlier=(), out=sys.stdout, write_revisions=False, repin_changed=False):
    """earlier: checkouts of the releases before previous, newest first (compare).  write_revisions: give each
    statement the revision it must have; previous and earlier must then be checkouts of releases (not_released), since
    against any other commit that revision is wrong, and a new statement's revision is never lowered (revised_files).
    repin_changed: write_pins, and stale_pins with changed.  Every file is computed before any is written."""
    prev, cur = facts.load(previous), facts.load(root)
    older = [facts.load(p) for p in earlier]
    named = [("previous", prev), ("this tree", cur)] + [("earlier %s" % p, t) for p, t in zip(earlier, older)]
    for name, t in named:
        for e in t.errors:
            print("error: %s: %s" % (name, e), file=out)
    if any(t.errors for _name, t in named):
        print("oft revisions: a tree does not load cleanly with these tools: nothing compared", file=out)
        return 1
    # each release is older than the one before it in the list, so that a statement is compared with the newest release
    # that has it
    trees = [prev] + older
    late = [i for i in range(1, len(trees)) if release_order(trees[i]) >= release_order(trees[i - 1])]
    for i in late:
        print("error: earlier %s is %s of %s, not older than %s of %s before it in the list: name them newest first"
              % (earlier[i - 1], trees[i].release["release"], trees[i].release["date"],
                 trees[i - 1].release["release"], trees[i - 1].release["date"]), file=out)
    if late:
        print("oft revisions: the earlier releases are not newest first: nothing compared", file=out)
        return 1
    if write_revisions:
        held = [("previous %s" % previous, not_released(prev))] + [
            ("earlier %s" % p, not_released(t)) for p, t in zip(earlier, older)]
        for name, files in held:
            if files:
                print("error: %s is not a release: it holds %s, which `oft release-tree` removes from every release"
                      % (name, ", ".join(files)), file=out)
        if any(files for _name, files in held):
            print("oft revisions: --write-revisions needs checkouts of releases: nothing compared", file=out)
            return 1
    models, new_model = [model(t) for t in trees], model(cur)
    rows = compare(cur, [(t, rerendered(t), m != new_model) for t, m in zip(trees, models)])
    print("\t".join(COLUMNS), file=out)
    for sid, a, b, expected, what, proof in rows:
        print("\t".join(str(v) for v in (sid, a.revision if a else "-", b.revision if b else "-",
                                         "-" if expected is None else expected, what, proof)), file=out)
    for (k, v), (_k, w) in zip(models[0], new_model):
        if v != w:
            print("note: the model changed: %s is %s, was %s, so every statement's meaning may have changed" % (
                k, w, v), file=out)
    wrong = [r for r in rows if r[3] is not None and r[2].revision != r[3]]
    stale = stale_pins(rows, changed=repin_changed)
    repin = write_pins or repin_changed
    try:
        files = (pinned_files(cur, stale) if repin else []) + (revised_files(cur, rows) if write_revisions else [])
    except ValueError as e:
        failed = "%s: %s" % (e, "nothing written" if repin and write_revisions else
                             "no pin written" if repin else "no revision written")
    else:
        failed = None
        for path, text in files:
            with open(path, "w", encoding="utf-8", newline="") as f:
                f.write(text)
    for sid, _a, b, expected, what, _p in wrong:
        if write_revisions and not failed:
            print("written: %s: revision %d, was %d: %s" % (sid, expected, b.revision, WHY[what]), file=out)
        else:
            print("error: %s: revision %d, expected %d: %s" % (sid, b.revision, expected, WHY[what]), file=out)
    if failed:
        print("error: %s" % failed, file=out)
        return 1
    if write_revisions and wrong:
        print("oft revisions: harness.yaml changed: now run %s" % render_command(root), file=out)
    print("oft revisions: %d statements (%s), %d with a wrong revision; proofs: %s; %d pins %s%s" % (
        len(rows), ", ".join("%d %s" % (sum(r[4] == w for r in rows), w) for w in STATEMENT), len(wrong),
        ", ".join("%d %s" % (sum(r[5] == p for r in rows), p) for p in PROOF),
        len(stale), "rewritten" if repin else "to rewrite (--write-pins)",
        "; %d revisions written" % len(wrong) if write_revisions else ""), file=out)
    return 1 if wrong and not write_revisions else 0
