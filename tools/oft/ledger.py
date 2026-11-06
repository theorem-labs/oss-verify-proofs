"""oft ledger: the findings ledger over a change's history.

lint's paths rule compares the proposed tree with its base.  A proof branch
takes direct pushes and merges, not pull requests, so a finding can be added
there and then removed or rewritten before any two trees CI compares, and
neither tree shows it.  `run` holds every commit of BASE..TIP, and every parent
of one, to the rule instead.

A record is a folder with finding.yaml: findings/<project>/<harness>/<slug>/
in the old layout, projects/<project>/<harness>/findings/<slug>/ in the
per-project one (layout.py).  The two are the same record, as
findings/<project>/unpatched.yaml and projects/<project>/unpatched.yaml are the
same pins, so the move `oft port-layout` makes deletes and renames nothing.  A
commit of BASE..TIP that holds one record, or one project's pins, in both
layouts is refused, since which of the two is the record is not known; only
the per-project one is read there.  Its
anchor is its first version that is evidence, which is decided by the record's
own files alone: its input.bin and control.bin are regular files of at most the
finding input cap that begin with a complete driver header; each of its
statements is an agreement or halts statement by its name, which gives its
builds (names.statement_builds); and its input and control each hold a run of
every build its statements name, each of the shape `oft check --record` prints
(an exit status from 0 to 255, an optional signal, and two SHA-256s).  Any
recorded runs of that shape anchor a record, whether or not they show its
statements false, so a record's runs must come only from `oft check --record`,
which prints them only when the input shows each statement false and the
control none.  No schema, harness.yaml or unpatched.yaml is consulted, so
neither another file nor a change to the tools can turn evidence back into a
draft.  Before its anchor a record is a draft, which CI never re-ran, so it may
change in any way and may be renamed or deleted.  Anchors are found by ancestry
over TIP's whole history, not by the order of a walk: the anchors of a record
are its versions that are evidence at commits none of whose ancestors had a
version of it that was evidence.  Two anchors that differ in input.bin,
control.bin, statements or recorded runs are refused, when one of them is in
BASE..TIP: two branches that each recorded the slug, merged in either order or
with either tree kept.

From its anchor on, a record is never deleted or renamed: every file of it
that a commit at or after its anchor had is in TIP, among the commits of
BASE..TIP and their parents.  Its state never moves back to `open` from one
whose patch the pinned build carries (`patched`, `reported` or `public`,
rules.SERIES_STATES), whether or not the base has the record, since an
enrolled project's binaries keep that patch; from `pruned` or `not-a-defect`
it may, since those carry no patch.  Its input.bin and control.bin are the anchor's,
and its statements include the anchor's (a longer list makes a stronger claim,
and CI checks each).  The unpatched pin of each build the anchor's statements
name is frozen at the pin's own anchor: its first value in its project's
unpatched.yaml at or after the record's anchor, found by
ancestry in the same way, and two such anchors that differ are refused.  A pin
for a build no anchored record names may be added or changed.

Its recorded runs are the anchor's too, for every build its statements name.
A push to a proof branch runs no check, so neither the anchor's runs nor the
pins of the anchor's commit were ever re-run: a pin in that very commit may
name the fixed binary, and runs recorded on it would prune the finding.  The
same binaries in the same runner give the same runs, so an honest record never
needs new ones; only a new runner image can change them, and a finding holds
only as far as qemu agrees.  A record anchored outside BASE..TIP was checked
where TIP's history meets BASE.  For each merge base m of BASE and TIP (git
merge-base --all; more than one only after a criss-cross merge), c is the
oldest commit of BASE's first-parent line that has m: m itself when m is on
that line, else the merge that brought m into BASE.  Each commit of that line
passed CI as long as BASE takes changes only through checked pull requests (a
branch rule on BASE enforces that, not this tool), but m alone may be a
proof-branch commit no check judged, whose runs or runner were put right
before the merge.  When c has m's runner and m's recorded runs (its input and
control; its text may differ), c vouches for them, and the reference is m.
Otherwise c holds main's changes as well as m's,
which a branch that lags main never had, and the reference is n, the newest
commit of that line that TIP has.  In a pull request m = c = BASE; on a push
to a proof branch, a branch that lags main is held to what it has.  TIP's runs
agree with each reference that has the record, except one whose images.runner
in release.yaml (the image CI re-runs findings in) differs from TIP's: the same
test lint's base comparison makes, for a pull request.  A record anchored only
in BASE..TIP keeps its anchor's runs
whatever the runner, since that commit's
release.yaml is as unchecked as its pins.  If a new runner changes such a
record's runs, CI's re-run fails, so its branch cannot merge and its project
stays held.  A record's state, summary, upstream and patch text may change.

The rule is net: only TIP is judged against what the history had.  A file of a
record that paths.py does not list (an old run.sh beside it) may go, and
restoring what was deleted or changed clears the finding, since a proof branch
is never rewritten (ledger.yml fails a forced push to one) and its history has to
be able to come right.  The history is read as git has it, with no replace ref
or graft: either could hide a commit.

Only git objects are read: commits and trees (each commit's files of findings
are its first parent's with what git diff-tree finds changed between the two),
the finding.yaml, input.bin and control.bin of each version and the
unpatched.yaml of each commit at or after an anchor, each within its cap in the
finding (facts.FINDING_INPUT_CAP for input.bin and control.bin,
facts.FINDING_FILE_CAP for the others), and the release.yaml of TIP and of each
reference commit above, within its own cap (facts.file_cap).  In a clone fetched
without blobs, git fetches those on demand.
"""
import os
import re
import subprocess

from . import facts, layout, names, rules, schema, yamlio
from .lint import Finding

# A file of a record that paths.py lists, in the per-project layout (layout.canonical of its path in either layout);
# the record is the folder with finding.yaml.
RECORD_FILE = re.compile(r"projects/([^/]+)/([^/]+)/findings/([^/]+)/"
                         r"(finding\.yaml|input\.bin|control\.bin|[^/]+\.patch)")
# A project's unpatched pins, in the per-project layout.
UNPATCHED_FILE = re.compile(r"projects/([^/]+)/unpatched\.yaml")
# The files of findings in a commit's tree in either layout, as git pathspecs from the top of the tree: findings/ in
# the old layout, and in the per-project one each fuzz target's projects/<p>/<h>/findings/ and each project's
# projects/<p>/unpatched.yaml.
FINDINGS_FILES = (":(top,glob)findings/**", ":(top,glob)projects/*/*/findings/**",
                  ":(top,glob)projects/*/unpatched.yaml")
# What a finding's runs are of, compared by git object: CI re-runs its record against these.
FIXED_FILES = ("input.bin", "control.bin")
REGULAR = ("100644", "100755")
# git reads no replace ref (GIT_NO_REPLACE_OBJECTS) and no info/grafts (GIT_GRAFT_FILE): either rewrites parents.
GIT_ENV = {"GIT_NO_REPLACE_OBJECTS": "1", "GIT_GRAFT_FILE": os.devnull}


class LedgerError(Exception):
    pass


class _Git:
    """git in one repository, with the YAML blobs it has read."""

    def __init__(self, root):
        self.root = root
        self.env = dict(os.environ, **GIT_ENV)
        self.docs = {}      # object id -> its YAML, or None
        self.headers = {}   # object id -> the driver calls its header gives, or None

    def out(self, *args, stdin=None):
        r = subprocess.run(["git", "-C", self.root, "-c", "advice.graftFileDeprecated=false"] + list(args),
                           input=stdin, capture_output=True, env=self.env)
        if r.returncode != 0:
            raise LedgerError("git %s failed: %s" % (args[0], r.stderr.decode(errors="replace").strip()))
        return r.stdout

    def commit(self, rev):
        try:
            return self.out("rev-parse", "--verify", "--end-of-options", rev + "^{commit}").decode().strip()
        except LedgerError:
            raise LedgerError("not a commit: %s" % rev) from None

    def yaml(self, obj, cap=facts.FINDING_FILE_CAP):
        """The YAML in a regular file's blob, or None if it is not a regular file of at most cap, or does not parse."""
        mode, oid = obj
        if mode not in REGULAR:
            return None
        if oid not in self.docs:
            doc = None
            if int(self.out("cat-file", "-s", oid)) <= cap:
                try:
                    doc = yamlio.load(self.out("cat-file", "blob", oid).decode(), where=oid)
                except (UnicodeDecodeError, yamlio.YamlError):
                    pass
            self.docs[oid] = doc
        return self.docs[oid]

    def header(self, obj):
        mode, oid = obj
        if mode not in REGULAR:
            return None
        if oid not in self.headers:
            fits = int(self.out("cat-file", "-s", oid)) <= facts.FINDING_INPUT_CAP
            self.headers[oid] = facts.driver_calls(self.out("cat-file", "blob", oid)) if fits else None
        return self.headers[oid]


def _statements(doc):
    s = doc.get("statements") if isinstance(doc, dict) else None
    return sorted(s) if isinstance(s, list) and all(isinstance(x, str) for x in s) else None


def _pins(doc, harness):
    harnesses = doc.get("harnesses") if isinstance(doc, dict) else None
    pins = harnesses.get(harness) if isinstance(harnesses, dict) else None
    return pins if isinstance(pins, dict) else {}


def _build_order(b):
    return (schema.BUILDS.index(b) if b in schema.BUILDS else len(schema.BUILDS), str(b))


def _state(git, rec):
    """The state a version of a record gives it, or None when it has none to read."""
    doc = git.yaml(rec["finding.yaml"]) if "finding.yaml" in rec else None
    state = doc.get("state") if isinstance(doc, dict) else None
    return state if isinstance(state, str) else None


def _runner(git, commit):
    """images.runner in release.yaml at commit, the image CI re-runs findings in, or None."""
    listed = git.out("ls-tree", "-z", commit, "release.yaml").split(b"\0")[0]
    if not listed:
        return None
    mode, _, oid = listed.partition(b"\t")[0].decode().split(" ")
    doc = git.yaml((mode, oid), cap=facts.file_cap("release.yaml"))
    images = doc.get("images") if isinstance(doc, dict) else None
    runner = images.get("runner") if isinstance(images, dict) else None
    return runner if isinstance(runner, str) else None


def _root_trees(git, commits):
    """commit -> its tree id, all in one git call."""
    return dict(zip(commits, git.out("cat-file", "--batch-check=%(objectname)",
                                     stdin="".join("%s^{tree}\n" % c for c in commits).encode()).decode().split()))


def _findings_files(git, pairs, known):
    """Add to known the files of findings (FINDINGS_FILES) of each tree of pairs, [(a commit's tree id, the tree id it
    is read against, which known has or an earlier pair adds, or None for the empty tree)]: known[tree] = (since,
    {path: (mode, object id)}), the files of the tree it is read against with git diff-tree's changes from that one
    applied, and since the tree id where those files last changed (None for no files).  All pairs are one git call,
    and git reads only the folders that differ."""
    if not pairs:
        return
    known.setdefault(None, (None, {}))
    empty = git.out("hash-object", "-t", "tree", "--stdin", stdin=b"").decode().strip()
    data = git.out("diff-tree", "--stdin", "-r", "-z", "--no-renames", "--", *FINDINGS_FILES,
                   stdin="".join("%s %s\n" % (base or empty, tree) for tree, base in pairs).encode())
    at = 0
    for tree, base in pairs:
        # diff-tree echoes each pair, then lists each change as ":<mode> <mode> <id> <id> <status>\0<path>\0"
        end = data.index(b"\n", at)
        if data[at:end] != ("%s %s" % (base or empty, tree)).encode():
            raise LedgerError("git diff-tree did not echo %s %s" % (base or empty, tree))
        at = end + 1
        since, files = known[base]
        if data[at:at + 1] == b":":
            since, files = tree, dict(files)
        while data[at:at + 1] == b":":
            meta = data.index(b"\0", at)
            end = data.index(b"\0", meta + 1)
            _, mode, _, oid, status = data[at + 1:meta].decode().split(" ")
            path = data[meta + 1:end].decode(errors="surrogateescape")
            if status == "D":
                del files[path]
            else:
                files[path] = (mode, oid)
            at = end + 1
        known[tree] = (since, files)


class _Findings:
    """The records and unpatched pins of one commit, read from both layouts.  records: "<p>/<h>/<slug>" -> {file
    name: (mode, object id)} of each record (a folder with finding.yaml); dirs: the folder of each record; unpatched:
    project -> (mode, object id) of its unpatched.yaml; unpatched_at: that file's path; both: the per-project path of
    each record and unpatched.yaml the commit holds in both layouts, of which only the per-project one is read."""

    def __init__(self, *layouts):
        """layouts: {path: (mode, object id)} of the files of each layout, the old one first."""
        self.records, self.dirs, self.unpatched, self.unpatched_at, self.both = {}, {}, {}, {}, []
        for files in layouts:
            records, dirs, unpatched, unpatched_at = {}, {}, {}, {}
            for path, obj in files.items():
                canonical = layout.canonical(path)
                m = RECORD_FILE.fullmatch(canonical)
                if m and layout.unit_of(path):   # no fuzz target's: projects/<p>/bin/ and the like
                    key = "/".join(m.group(1, 2, 3))
                    records.setdefault(key, {})[m.group(4)] = obj
                    dirs[key] = path.rsplit("/", 1)[0]
                m = UNPATCHED_FILE.fullmatch(canonical)
                if m:
                    unpatched[m.group(1)], unpatched_at[m.group(1)] = obj, path
            records = {k: v for k, v in records.items() if "finding.yaml" in v}
            self.both += [dirs[k] for k in records if k in self.records]
            self.both += [unpatched_at[p] for p in unpatched if p in self.unpatched]
            self.records.update(records)
            self.dirs.update((k, dirs[k]) for k in records)
            self.unpatched.update(unpatched)
            self.unpatched_at.update(unpatched_at)
        self.both.sort()


def _records(files, memo):
    """_Findings of a commit's files of findings, (since, {path: (mode, object id)}) as _findings_files reads them;
    memo holds each by since."""
    since, files = files
    if since not in memo:
        memo[since] = _Findings(*({path: obj for path, obj in files.items() if layout.of_path(path) == which}
                                  for which in layout.LAYOUTS))
    return memo[since]


class _Evidence:
    """What a version of a record that is evidence fixes: its input.bin and control.bin (by object id), its
    statements, the builds they name, whose unpatched pins are frozen in turn, and its recorded runs of those builds."""

    def __init__(self, input_bin, control_bin, statements, builds, runs):
        self.input_bin, self.control_bin, self.statements, self.builds = input_bin, control_bin, statements, builds
        self.runs = runs   # "input" | "control" -> build -> run

    def differences(self, other):
        return [what for what, a, b in (("input.bin", self.input_bin, other.input_bin),
                                        ("control.bin", self.control_bin, other.control_bin),
                                        ("statements", self.statements, other.statements),
                                        ("recorded runs", self.runs, other.runs)) if a != b]



def _anchor(git, rec):
    if any(name not in rec or git.header(rec[name]) is None for name in FIXED_FILES):
        return None
    doc = git.yaml(rec["finding.yaml"])
    statements = _statements(doc)
    named = [names.statement_builds(s) for s in statements or ()]
    if not named or None in named:
        return None
    builds = frozenset(b for bs in named for b in bs)
    runs = {}
    for which in ("input", "control"):
        got = doc.get(which)
        if not isinstance(got, dict) or not all(b in got and rules.run_ok(got[b]) for b in builds):
            return None
        runs[which] = {b: got[b] for b in builds}
    return _Evidence(rec["input.bin"][1], rec["control.bin"][1], statements, builds, runs)


def _first_once(anchors, new, differ):
    """(the first anchor, [(a later anchor, how it differs from the first)]), counting only a pair with one of them in
    new: the base's own disagreement is not this change's.  differ(a, b): how b differs from a, a list."""
    (first, value), rest = anchors[0], anchors[1:]
    split = [(c, differ(value, other)) for c, other in rest if first in new or c in new]
    return (first, value), [(c, how) for c, how in split if how]


def run(root, base, tip="HEAD"):
    """The findings of the history BASE..TIP of the git repository at root (see the module's docstring)."""
    git = _Git(root)
    if git.out("rev-parse", "--is-shallow-repository").strip() != b"false":
        raise LedgerError("a shallow clone holds only part of the history: fetch it with --unshallow")
    base, tip = git.commit(base), git.commit(tip)
    # the commits judged: base..tip, and its boundary (the parents of those commits outside it, which base has), whose
    # records the change must keep
    listed = git.out("rev-list", "--boundary", "%s..%s" % (base, tip)).decode().split()
    new = {c for c in listed if not c.startswith("-")}
    scope = new | {c[1:] for c in listed if c.startswith("-")}
    if not new:
        return []
    # anchors are found over the whole history of tip, parents first, so that one is never a version a commit outside
    # BASE..TIP already had evidence before
    parents, commits = {}, []
    for line in git.out("rev-list", "--parents", "--topo-order", "--reverse", tip).decode().splitlines():
        c, *ps = line.split()
        commits.append(c)
        parents[c] = ps
    # each commit's files of findings in either layout, read against its first parent's
    trees, pairs, queued, known = _root_trees(git, commits), [], set(), {}
    for c in commits:
        if trees[c] not in queued:
            queued.add(trees[c])
            pairs.append((trees[c], trees[parents[c][0]] if parents[c] else None))
    _findings_files(git, pairs, known)
    memo, versions = {}, {}
    reach = {}        # record -> {a commit at or after one of its anchors: the builds those anchors ran}
    anchors = {}      # record -> [(commit, _Evidence)], parents first
    anchored_at = {}  # record -> its folder at its first anchor
    pin_reach = {}    # (project, harness, build) -> the commits at or after one of its pin's anchors
    pin_anchors = {}  # (project, harness, build) -> [(commit, the pin)], parents first
    pinned_at = {}    # project -> its unpatched.yaml at the first anchor of one of its pins
    had = {}          # (record, file name) -> (the first commit judged that had it at or after an anchor, its path there)
    states_had = {}   # record -> [(a commit judged, the state it gave the record)], parents first
    unpatched = {}    # project -> (the first commit judged with an anchored record of it and its unpatched.yaml, its path)
    both = {}         # the per-project path of a record or unpatched.yaml a commit of BASE..TIP had in both layouts ->
                      # the first such commit
    for c in commits:
        for seen in reach.values():
            builds = [seen[p] for p in parents[c] if p in seen]
            if builds:
                seen[c] = frozenset().union(*builds)
        for seen in pin_reach.values():
            if any(p in seen for p in parents[c]):
                seen.add(c)
        at = _records(known[trees[c]], memo)
        if not at.records and not at.unpatched:
            continue
        if c in new:
            for path in at.both:
                both.setdefault(path, c)
        for key, rec in sorted(at.records.items()):
            if c not in reach.get(key, ()):
                version = tuple(sorted(rec.items()))
                if version not in versions:
                    versions[version] = _anchor(git, rec)
                if versions[version] is None:
                    continue   # a draft
                reach.setdefault(key, {})[c] = versions[version].builds
                anchors.setdefault(key, []).append((c, versions[version]))
                anchored_at.setdefault(key, at.dirs[key])
            if c in scope:
                for name in rec:
                    had.setdefault((key, name), (c, "%s/%s" % (at.dirs[key], name)))
                st = _state(git, rec)
                if st is not None:
                    states_had.setdefault(key, []).append((c, st))
                p = key.split("/")[0]
                if p in at.unpatched:
                    unpatched.setdefault(p, (c, at.unpatched_at[p]))
        # the pins of the builds that the anchored records of each harness ran, from those anchors on
        frozen = {}
        for key, seen in reach.items():
            if c in seen:
                p, h, _ = key.split("/")
                frozen.setdefault((p, h), set()).update(seen[c])
        for (p, h), builds in sorted(frozen.items()):
            u = at.unpatched.get(p)
            pins = _pins(git.yaml(u), h) if u is not None else {}
            for b in sorted(builds):
                k = (p, h, b)
                if b in pins and c not in pin_reach.get(k, ()):
                    pin_reach.setdefault(k, set()).add(c)
                    pin_anchors.setdefault(k, []).append((c, pins[b]))
                    pinned_at.setdefault(p, at.unpatched_at[p])
    now = _records(known[trees[tip]], memo)
    states = {}    # commit -> (its runner, its records), read once a record needs them
    meeting = []   # [[(m, c) for each merge base m of BASE and TIP], n], computed once a record needs them

    def state(commit):
        if commit not in states:
            tree = _root_trees(git, [commit])[commit]
            if tree not in known:
                _findings_files(git, [(tree, trees[tip])], known)
            states[commit] = (_runner(git, commit), _records(known[tree], memo).records)
        return states[commit]

    def recorded(files):
        """The input and control a record's finding.yaml records, or None if it has none."""
        doc = git.yaml(files["finding.yaml"]) if files and "finding.yaml" in files else None
        return (doc.get("input"), doc.get("control")) if isinstance(doc, dict) else None

    def references(key):
        """The (runner, record files) that TIP's history vouches for key, one for each merge base m of BASE and TIP.
        c, the oldest commit of BASE's first-parent line that has m (m itself when m is on that line), is where m
        entered BASE and passed CI, as long as BASE takes changes only through checked pull requests; m alone may be a
        proof-branch commit no check judged.  When c has m's runner and m's recorded runs of key, c vouches for them,
        so m's are read; a record's state, summary, upstream and patch text may differ, since they may change.
        Otherwise c's are main's changes as much as m's, which a branch that lags main never had, so those of n are
        read: the newest commit of that line that TIP has, which passed CI and all of which TIP has."""
        if not meeting:
            line = git.out("rev-list", "--first-parent", base).decode().split()   # newest first
            on_line = set(line)
            pairs = []
            for m in git.out("merge-base", "--all", base, tip).decode().split():
                if m in on_line:
                    pairs.append((m, m))
                else:
                    has_m = set(git.out("rev-list", "--ancestry-path", "%s..%s" % (m, base)).decode().split())
                    pairs.append((m, next(x for x in reversed(line) if x in has_m)))
            lacks = set(git.out("rev-list", base, "--not", tip).decode().split())
            meeting.extend([pairs, next((x for x in line if x not in lacks), None)])
        pairs, n = meeting
        out = []
        for m, c in pairs:
            (m_runner, m_records), (c_runner, c_records) = state(m), state(c)
            if (m_runner, recorded(m_records.get(key))) == (c_runner, recorded(c_records.get(key))):
                ref = (m_runner, m_records.get(key))
            elif n is not None:
                ref = (state(n)[0], state(n)[1].get(key))
            else:
                continue   # TIP has no commit of that line: the anchor's runs hold
            if ref not in out:
                out.append(ref)
        return out
    tip_runner = _runner(git, tip)
    out = []
    for path, c in sorted(both.items()):
        out.append(Finding("paths", path, "in both layouts at %s" % c[:10]))
    for (key, name), (c, rel) in sorted(had.items()):
        if name not in now.records.get(key, {}):
            out.append(Finding("paths", rel, "a finding is never deleted: %s, which %s had" % (rel, c[:10])))
    for p, (c, rel) in sorted(unpatched.items()):
        if p not in now.unpatched:
            out.append(Finding("paths", rel, "a finding's unpatched pins are never deleted: %s, which %s had"
                               % (rel, c[:10])))
    # a state only moves forward from one whose patch the pinned build carries (rules.SERIES_STATES), over the whole
    # history judged: the base alone does not show a finding that a commit of this change added as patched and a later
    # one set back to open, which would release a hold its binaries keep
    for key, seq in sorted(states_had.items()):
        if key in now.records and _state(git, now.records[key]) == "open":
            rel = now.dirs[key] + "/finding.yaml"
            was = [(c, s) for c, s in seq if s in rules.SERIES_STATES]
            if was:
                out.append(Finding("paths", rel, "a finding's state never returns to open: %s was %s at %s"
                                   % (rel, was[0][1], was[0][0][:10])))
    for key, found in sorted(anchors.items()):
        rel = now.dirs.get(key, anchored_at[key])
        (first, ev), split = _first_once(found, new, _Evidence.differences)
        for c, what in split:
            out.append(Finding("paths", rel, "a finding is first recorded once: %s was first recorded by %s and by %s, "
                               "which differ in its %s" % (rel, first[:10], c[:10], " and ".join(what))))
        if split or key not in now.records:
            continue   # its anchors disagree, or it is deleted: reported above
        rec = now.records[key]
        for name in FIXED_FILES:
            if name in rec and rec[name][1] != (ev.input_bin if name == "input.bin" else ev.control_bin):
                out.append(Finding("paths", "%s/%s" % (rel, name), "a finding's %s is never changed: %s/%s, since %s"
                                   % (name, rel, name, first[:10])))
        doc = git.yaml(rec["finding.yaml"])
        current = _statements(doc)
        dropped = sorted(set(ev.statements) - set(current)) if current is not None else []
        if dropped:
            out.append(Finding("paths", rel + "/finding.yaml", "a finding's statements only grow: %s/finding.yaml no "
                               "longer names %s, which %s recorded" % (rel, ", ".join(dropped), first[:10])))
        if not isinstance(doc, dict):
            continue   # not YAML: lint's loader refuses it in the tree
        # a record anchored outside BASE..TIP was checked where TIP's history meets BASE (references): in a pull
        # request BASE itself; on a push, what the branch last has of main; more than one only after a criss-cross
        # merge, and each re-ran its runs in its own runner.  TIP's runs agree with each of those that has the record
        # and pins TIP's runner image; one that pins another constrains nothing.  A record anchored only in BASE..TIP
        # keeps its anchor's runs.
        refs = [ev.runs]
        if any(c not in new for c, _ in found):
            had_it = []
            for runner, files in references(key):
                was = git.yaml(files["finding.yaml"]) if files else None
                if isinstance(was, dict):
                    builds = {b for s in _statements(was) or () for b in names.statement_builds(s) or ()}
                    runs = {which: was.get(which) if isinstance(was.get(which), dict) else {}
                            for which in ("input", "control")}
                    had_it.append((runner, {which: {b: r for b, r in rs.items() if b in builds}
                                            for which, rs in runs.items()}))
            if had_it:
                refs = [runs for runner, runs in had_it if None in (runner, tip_runner) or runner == tip_runner]
        changed_runs = set()
        for want in refs:
            for which in ("input", "control"):
                runs = doc.get(which) if isinstance(doc.get(which), dict) else {}
                changed_runs.update((which, b) for b, run in want[which].items() if runs.get(b) != run)
        for which, b in sorted(changed_runs, key=lambda wb: (wb[0] != "input", _build_order(wb[1]))):
            out.append(Finding("paths", rel + "/finding.yaml", "a finding's recorded runs are never changed: "
                               "%s/finding.yaml %s.%s, since %s" % (rel, which, b, first[:10])))
    for (p, h, b), found in sorted(pin_anchors.items(), key=lambda kv: (kv[0][:2], _build_order(kv[0][2]))):
        urel = now.unpatched_at.get(p, pinned_at[p])
        (first, pin), split = _first_once(found, new, lambda a, b: ["pin"] if a != b else [])
        for c, _ in split:
            out.append(Finding("paths", urel, "a finding's unpatched pins are first recorded once: %s harnesses.%s.%s "
                               "was first pinned by %s and by %s, which differ" % (urel, h, b, first[:10], c[:10])))
        u = now.unpatched.get(p)
        doc = git.yaml(u) if u is not None else None
        if split or not isinstance(doc, dict):
            continue   # its anchors disagree, or deleted (above), or not YAML: lint's loader refuses it in the tree
        if _pins(doc, h).get(b) != pin:
            out.append(Finding("paths", urel, "a finding's unpatched pins are never changed: %s harnesses.%s.%s, "
                               "since %s" % (urel, h, b, first[:10])))
    return out
