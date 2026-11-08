"""oft change-ledger: what one change cost, summed from the records that hold it.

A change is one named piece of work, with its folder changes/<change>/ (only this repository has it: `oft
release-tree` removes changes/).  What it holds as input:

    sessions.tsv   step, session, host, vms, transcript, from, until: each agent session that worked on it (`oft
                   change-ledger tag`), the machine it ran on, the VMs it drove, and the window of the session that
                   counts here (from, until: `-` is no bound).  A session counts in one step of one change, but a
                   session that worked on several (a walk over upstream commits, one change each) is tagged once for
                   each, each tag with its own window, no two of one session overlapping: each entry of its
                   transcript then counts in the one tag whose window holds its timestamp, [from, until), and in no
                   change when none does.  A resumed agent's transcript, X-2.jsonl beside X.jsonl, is a fragment of
                   the same session, under a new session id or its first: its row goes in the same step (or has a
                   window apart from the others'), `sessions` counts the session once, and an entry a fragment repeats
                   (by its id: a resume may copy the history) counts once.
    checks.tsv     step, log: the GNU `time -v` log of each check run for it (`oft change-ledger check`).
    no-work.tsv    step, why: each step recorded as needing no work (`oft change-ledger no-work`), such as upstream
                   commits that change no binary.  Such a step has no session and no check log, and its row reads 0
                   (agent, VM and check figures) where a step with no record reads `not measured`.
    prove.json     optional: `oft prove UNIT --base BASE --head H --json`, saved when the change was made and before
                   any contract was edited: which contracts the work key predicted would need an agent.

`oft change-ledger sum` reads them and writes

    ledger.tsv          one row per step, in the order the steps were first recorded, then the row `total` (COLUMNS)
    session-totals.tsv  one row per tag of a session, with the model it asked for and the models that answered
    contracts.tsv       with prove.json: each contract's predicted state, its state at HEAD and whether its file was
                        edited (the work key's precision, measured)
    gaps.tsv            each figure that could not be read in full, and why
    inputs.tsv          what the sum read: the unit, the base and head commits, the VM sample files, and when
    journal.md          from templates/journal.md.tmpl when it is missing; people and agents write it

Each figure comes from a record that was read, never from a typed number:

    input_tokens, output_tokens, cache_read, cache_write, cost_usd
                        each transcript's assistant turns' message.usage (input, output, cacheRead, cacheWrite,
                        cost.total: omp's price of the call), and the usage of omp's own calls for the session
                        (model_usage entries, such as its task-completion probes)
    agent_hours         the sum of each assistant turn's time, from the transcript entry before it to its own
                        timestamp, counting only the turns of 10 minutes or less: the cost of the work
    waiting_hours       the same sum over the turns longer than 10 minutes, where the agent waited (a build, a farm
                        run, a person).  Every turn counts in exactly one of the two, so agent_hours +
                        waiting_hours is all turn time
    tool_hours          the time the session's tool calls took: from each assistant turn that asked for tool calls
                        to the last result of those calls, one interval per turn, so calls that ran together count
                        once.  A turn's own time ends where its tool calls begin, so no second is in two columns.
                        This is where a build or a farm run shows up: on libreac#35's proof step it is 37.61 hours
                        against 14.07 of turn time.  None of the three is the span: wall_end - wall_start also
                        holds the time in no turn and no tool call, and parallel sessions make it shorter than
                        their sum
    waiting_clock_hours in ledger.tsv only, and not a sum: the time with at least one of the row's sessions
                        waiting on a tool, so a wait that two of them share counts once.  tool_hours is what
                        the sessions spent; this is how long the step itself waited
    wall_start, wall_end the first and the last timestamp of the row's transcripts
    vcpu_hours          the VM samples given with --vm-samples (bin/ossv-sweep's notes/compute-ledger.tsv,
                        ossv-idle-shutdown's notes/idle-stop.tsv) of each session's host and of each VM it drove, inside
                        the union of the spans of the row's sessions that name that machine: each interval between two
                        samples of a machine under 45 minutes apart, times the vCPUs its machine type names
                        (bin/ossv-stream-numbers counts VM time the same way).  idle-stop.tsv also names each
                        sample's life (the VM's created and last_start, from GCE): two samples of different lives never
                        make an interval, and a life counts from its last start.  A deletion the compute inventory
                        records (--vm-deletions: gone=, from bin/ossv-vm) ends the life it falls in: less than 45
                        minutes after the life's last sample, the time up to it counts; and after it a sample of no
                        known life begins another life, of no known start.  Each part of a span in which a machine may
                        have run with no measurement is named in gaps.tsv: before its first sample (no life known), a
                        gap of 45 minutes or more, after a life's last sample (up to its deletion, if one is recorded),
                        between two deletions with no sample between them (a life no sample shows), after a deletion
                        and before the next sample of a life of no known start, an interval whose machine type names no
                        vCPU count, a machine with no sample.  A span in which no record shows a machine running (it was
                        deleted, or not yet made) is named too, and a figure with no measured interval is `not
                        measured`, never 0
    check_seconds       the elapsed wall clock time of each check's time log
    proof_lines_added, proof_lines_removed
                        git diff --numstat BASE HEAD over the unit's proofs folder, in either layout
    identical, moved, changed, added, removed
                        oft prove's count of each function class between BASE and HEAD
    contracts_changed   the contracts oft prove finds changed or removed between BASE and HEAD (their own file)
    contracts_needing_work
                        the contracts prove.json predicts need work
    edits_address, edits_layout, edits_content
                        each rewritten line pair of git diff -U0 over the proofs folder (a hunk's removed and added
                        lines, paired in order): address when the two are equal with every hex literal masked, layout
                        when equal with every number masked, else content (the classes of bs-measure/s5_hexonly.py)

A figure that no record holds is `not measured`; one whose records were read only in part is `<sum> + not measured`,
and gaps.tsv names what is missing: a machine with no sample in the span, a transcript cut short by a crash, a step
with no check log, a usage with no cost.  0 is written only where a record says so: a step that no-work.tsv records
as needing no work.  `-` is a figure that does not apply to its row: the git figures are the change's, on the total
row only, and with no unit there are none; the wall time of a row whose every step needed no work.  A tagged
transcript or a check log that cannot be read, a malformed line inside a transcript, a prove.json of another unit or
base, and a tag that breaks tag's rules (the sum checks them again: a transcript whose own session is another, a
session tagged in two steps or changes with no windows or with windows that overlap, a step that needed no work and
has a session or a check log) are errors: the sum stops and writes nothing.

This module is not the checker (keys.NOT_THE_CHECKER): no check reads a ledger."""
import collections
import csv
import datetime
import json
import os
import re
import subprocess

from . import keys, layout, prove, render

COLUMNS = ("step", "sessions", "wall_start", "wall_end", "agent_hours", "waiting_hours", "tool_hours",
           "waiting_clock_hours", "input_tokens", "output_tokens", "cache_read", "cache_write", "cost_usd",
           "vcpu_hours", "check_seconds", "proof_lines_added", "proof_lines_removed", "identical", "moved", "changed",
           "added", "removed", "contracts_changed", "contracts_needing_work", "edits_address", "edits_layout",
           "edits_content")
SESSION_COLUMNS = ("step", "session", "host", "vms", "transcript", "from", "until")
CHECK_COLUMNS = ("step", "log")
NO_WORK_COLUMNS = ("step", "why")
TOTALS_COLUMNS = ("step", "session", "host", "vms", "transcript", "from", "until", "requested", "served",
                  "wall_start", "wall_end", "agent_hours", "waiting_hours", "tool_hours", "input_tokens",
                  "output_tokens", "cache_read", "cache_write", "cost_usd")
GAP_COLUMNS = ("step", "session", "column", "what")
INPUT_COLUMNS = ("input", "value")
CONTRACT_COLUMNS = ("contract", "predicted", "final", "edited")
JOURNAL_SECTIONS = ("What we did", "Where verification helped", "Where it struggled", "What we learned",
                    "What we would do differently", "How to go faster or better",
                    "What this means for a verified-software ecosystem", "What falls short and must be fixed")

NOT_MEASURED = "not measured"
NOT_APPLICABLE = "-"
TOTAL = "total"
# an assistant turn longer than this counts as waiting_hours, not agent_hours: the agent was waiting, not working
TURN_GAP = 600
# two samples of a machine further apart than this mean it was stopped between them (bin/ossv-stream-numbers)
SAMPLE_GAP = 2700
# (ledger column, message.usage key)
USAGE = (("input_tokens", "input"), ("output_tokens", "output"), ("cache_read", "cacheRead"),
         ("cache_write", "cacheWrite"))
# the columns a usage feeds
TOKENS = tuple(c for c, _k in USAGE) + ("cost_usd",)
# the two columns an assistant turn's time goes to: every turn counts in one of them
TURN_TIME = ("agent_hours", "waiting_hours")
# the columns that are hours, written with 2 decimals
HOURS = TURN_TIME + ("tool_hours",)
AGENT = TOKENS + HOURS
GIT = ("proof_lines_added", "proof_lines_removed", "identical", "moved", "changed", "added", "removed",
       "contracts_changed", "contracts_needing_work", "edits_address", "edits_layout", "edits_content")

CHANGE = re.compile(r"[a-z0-9][a-z0-9._-]*\Z")
WORD = re.compile(r"[A-Za-z0-9][A-Za-z0-9._-]*\Z")
ELAPSED = re.compile(r"Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([0-9]+(?::[0-9]+){0,2}(?:\.[0-9]+)?)")
HEX = re.compile(r"0x[0-9a-fA-F]+")
DEC = re.compile(r"\b\d+\b")


class LedgerError(Exception):
    """A record the ledger needs that cannot be read or that contradicts another: the sum writes nothing."""


Transcript = collections.namedtuple("Transcript", "path session entries cut")


# -------------------------------------------------------------------------------------------- records


def _folder(root, change):
    if not CHANGE.match(change or ""):
        raise LedgerError("a change is named with lower-case letters, digits, '.', '_' and '-', not %r" % change)
    return os.path.join(root, "changes", change)


def _word(what, value):
    if not WORD.match(value or "") or value == TOTAL:
        raise LedgerError("a %s is named with letters, digits, '.', '_' and '-' (and is not %r), not %r"
                          % (what, TOTAL, value))


def _stored(path):
    """path, absolute, with the home folder written ~, so that a record names no user's home and holds the same path
    for each user of a machine whose files are under their own home."""
    path = os.path.abspath(path)
    if "\t" in path or "\n" in path:
        raise LedgerError("%r: a recorded path holds no tab or line break" % path)
    home = os.path.expanduser("~")
    return "~" + path[len(home):] if home != "~" and (path == home or path.startswith(home + os.sep)) else path


def _read_tsv(path, columns):
    """[{column: value}] of the TSV file at path, [] when it does not exist; its header must be columns."""
    if not os.path.exists(path):
        return []
    with open(path, encoding="utf-8") as f:
        lines = f.read().split("\n")
    if lines[0].split("\t") != list(columns):
        raise LedgerError("%s: the header is not %s" % (path, "\t".join(columns)))
    out = []
    for no, line in enumerate(lines[1:], 2):
        if line:
            cells = line.split("\t")
            if len(cells) != len(columns):
                raise LedgerError("%s:%d: %d cells, not %d" % (path, no, len(cells), len(columns)))
            out.append(dict(zip(columns, cells)))
    return out


def _write_tsv(path, columns, rows):
    with open(path, "w", encoding="utf-8") as f:
        f.write("\t".join(columns) + "\n")
        f.writelines("\t".join(str(r[c]) for c in columns) + "\n" for r in rows)


def _append(path, columns, row):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    new = not os.path.exists(path)
    with open(path, "a", encoding="utf-8") as f:
        if new:
            f.write("\t".join(columns) + "\n")
        f.write("\t".join(row[c] for c in columns) + "\n")


def _time(value, where):
    try:
        t = datetime.datetime.fromisoformat(value)
    except (TypeError, ValueError):
        raise LedgerError("%s: %r is not a timestamp" % (where, value)) from None
    if t.tzinfo is None:
        raise LedgerError("%s: %r has no time zone" % (where, value))
    return t


def _stamp(t):
    return t.astimezone(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def read_transcript(path):
    """The Transcript of the omp session file at path: its session id (its `session` entry's), its entries in order,
    and cut, why its end is lost or None.  A machine that crashes while omp writes leaves a run of zero bytes or half a
    line at the end: the lines before it count, and cut says so.  A malformed line anywhere else is an error."""
    try:
        with open(path, "rb") as f:
            data = f.read()
    except OSError as e:
        raise LedgerError("cannot read the transcript %s: %s" % (path, e.strerror)) from None
    cut = None
    kept = data.rstrip(b"\0")
    if len(kept) < len(data):
        cut = "its last %d bytes are zero, as a crash leaves a file: what it held after them is lost" % (
            len(data) - len(kept))
    lines = kept.split(b"\n")
    entries = []
    for no, raw in enumerate(lines, 1):
        if not raw.strip():
            continue
        try:
            entry = json.loads(raw)
        except (ValueError, UnicodeDecodeError):
            entry = None
        if not isinstance(entry, dict):
            if no == len(lines):
                cut = "; ".join(filter(None, (cut, "its last line is cut short: what it held is lost")))
                continue
            raise LedgerError("%s:%d: not a JSON object" % (path, no))
        entries.append(entry)
    session = next((e.get("id") for e in entries if e.get("type") == "session"), None)
    if not isinstance(session, str) or not session:
        raise LedgerError("the transcript %s has no session entry" % path)
    return Transcript(path, session, entries, cut)


def _tagged(root):
    """(change, row) of every row of every changes/*/sessions.tsv under root."""
    top = os.path.join(root, "changes")
    for change in sorted(os.listdir(top)) if os.path.isdir(top) else ():
        for row in _read_tsv(os.path.join(top, change, "sessions.tsv"), SESSION_COLUMNS):
            yield change, row


def _logical(transcript):
    """The session a transcript is a fragment of: omp writes a resumed agent's transcript as X-2.jsonl (X-3.jsonl, ...)
    beside X.jsonl, so each names X.jsonl."""
    return re.sub(r"-\d+(\.jsonl)\Z", r"\1", transcript)


def _window(row):
    """(from, until) of the tagged row's window as aware datetimes, None for an end with no bound."""
    return tuple(None if row[end] == NOT_APPLICABLE else _time(row[end], "the window of session %s" % row["session"])
                 for end in ("from", "until"))


def _inside(window, t):
    """Whether the window (from, until) holds the moment t: from is in it, until is not."""
    return (window[0] is None or window[0] <= t) and (window[1] is None or t < window[1])


def _apart(a, b):
    """Whether the windows of the tagged rows a and b share no moment."""
    (a0, a1), (b0, b1) = _window(a), _window(b)
    return any(end is not None and start is not None and end <= start for end, start in ((a1, b0), (b1, a0)))


def _where(change, row):
    window = "" if (row["from"], row["until"]) == (NOT_APPLICABLE,) * 2 else ", from %s until %s" % (row["from"],
                                                                                                   row["until"])
    return "changes/%s/sessions.tsv (step %s%s)" % (change, row["step"], window)


# what a refused tag says, when a session worked on several steps or changes
SHARED = ("; to count one session in several steps or changes, give each tag its own window (--from, --until), no "
          "two of one session overlapping")


def _tag_problem(others, change, row):
    """Why row (of changes/<change>/sessions.tsv) may not stand beside others, [(change, row)] of every other tagged
    row, or None: a session counts in one step of one change, its fragments (X.jsonl, X-2.jsonl) too, and a transcript
    is tagged once, unless the two tags have windows that share no moment: each entry then counts in the one tag whose
    window holds it, so no cost is summed twice.  Two fragments of one session may share its session id."""
    for other_change, other in others:
        fragment = _logical(other["transcript"]) == _logical(row["transcript"])
        if (other["session"] != row["session"] and not fragment) or _apart(other, row):
            continue
        if other["session"] == row["session"] and not (fragment and other["transcript"] != row["transcript"]):
            return ("session %s is already tagged in %s: a session counts in one step of one change%s"
                    % (row["session"], _where(other_change, other), SHARED))
        if fragment and (other_change, other["step"]) != (change, row["step"]):
            return ("%s is a fragment of the session of %s, tagged in %s: a session's fragments count in one step of "
                    "one change%s" % (row["transcript"], other["transcript"], _where(other_change, other), SHARED))
        if other["transcript"] == row["transcript"]:
            return "%s is already tagged in %s%s" % (row["transcript"], _where(other_change, other), SHARED)
    return None


def _idle(folder):
    """{step: why} of folder's no-work.tsv: each step recorded as needing no work."""
    path = os.path.join(folder, "no-work.tsv")
    out = {}
    for row in _read_tsv(path, NO_WORK_COLUMNS):
        if row["step"] in out:
            raise LedgerError("%s: step %s is recorded twice" % (path, row["step"]))
        out[row["step"]] = row["why"]
    return out


def _idle_problem(change, idle, sessions, checks):
    """Why the records of change may not stand together, or None: a step recorded as needing no work (idle, {step:
    why}) has no tagged session (sessions, sessions.tsv rows) and no check log (checks, checks.tsv rows)."""
    worked = ([(r["step"], "session %s is tagged" % r["session"]) for r in sessions]
              + [(r["step"], "the check log %s is recorded" % r["log"]) for r in checks])
    for step, what in worked:
        if step in idle:
            return ("step %s of %s is recorded as needing no work (no-work.tsv: %s), and %s for it: a step that needed "
                    "no work has no session and no check log" % (step, change, idle[step], what))
    return None


def _own(path, session, change):
    """The Transcript at path, whose own session id must be session, as changes/<change>/sessions.tsv tags it."""
    t = read_transcript(path)
    if t.session != session:
        raise LedgerError("%s is the transcript of session %s, not of %s as changes/%s/sessions.tsv tags it"
                          % (path, t.session, session, change))
    return t


def _moment(text, what):
    """The timestamp text (with its time zone) as sessions.tsv records an end of a window: UTC."""
    t = _time(text, what).astimezone(datetime.timezone.utc)
    return t.strftime("%Y-%m-%dT%H:%M:%S" + (".%f" if t.microsecond else "") + "Z")


def tag(root, change, step, session, host, transcript, vms=(), since=None, until=None):
    """`oft change-ledger tag`: record that the agent session `session`, which ran on host and drove vms, worked on
    step of change, with its transcript (whose own session id must be session).  A session counts in one step of one
    change, so its cost is never summed twice: one already tagged anywhere is refused, unless both tags have a window
    and the windows share no moment.  The window, since (from) and until, timestamps with a time zone, either of which
    may be left out, holds the entries that count here.  A window that holds no entry of the transcript is refused,
    and so is a step recorded as needing no work."""
    folder = _folder(root, change)
    _word("step", step)
    for machine in (host,) + tuple(vms):
        _word("host or VM", machine)
    if not session or any(c in session for c in "\t\n"):
        raise LedgerError("%r is not a session id" % session)
    path = os.path.abspath(transcript)
    t = _own(path, session, change)
    row = {"step": step, "session": session, "host": host, "vms": ",".join(vms) or NOT_APPLICABLE,
           "transcript": _stored(path),
           "from": NOT_APPLICABLE if since is None else _moment(since, "--from"),
           "until": NOT_APPLICABLE if until is None else _moment(until, "--until")}
    window = _window(row)
    if None not in window and window[1] <= window[0]:
        raise LedgerError("the window from %s until %s holds no moment" % (row["from"], row["until"]))
    if window != (None, None) and not any(e.get("timestamp") is not None and _inside(window, _time(
            e["timestamp"], "%s, entry %d" % (path, no))) for no, e in enumerate(t.entries, 1)):
        raise LedgerError("the window from %s until %s holds no entry of %s" % (row["from"], row["until"], path))
    problem = _idle_problem(change, _idle(folder), [row], []) or _tag_problem(_tagged(root), change, row)
    if problem:
        raise LedgerError(problem)
    _append(os.path.join(folder, "sessions.tsv"), SESSION_COLUMNS, row)


def no_work(root, change, step, why):
    """`oft change-ledger no-work`: record that step of change needed no work, and why (what shows it, such as oft
    prove's report that the upstream commits change no binary): its row then reads 0 where a step with no record
    reads `not measured`.  A step with a tagged session or a check log did work, and is refused; so is a step
    recorded already."""
    folder = _folder(root, change)
    _word("step", step)
    if not (why or "").strip() or any(c in why for c in "\t\n"):
        raise LedgerError("say on one line why step %s of %s needed no work (--why), not %r" % (step, change, why))
    idle = _idle(folder)
    if step in idle:
        raise LedgerError("step %s of %s is already recorded as needing no work (no-work.tsv: %s)"
                          % (step, change, idle[step]))
    problem = _idle_problem(change, {step: why}, [r for c, r in _tagged(root) if c == change],
                            _read_tsv(os.path.join(folder, "checks.tsv"), CHECK_COLUMNS))
    if problem:
        raise LedgerError(problem)
    _append(os.path.join(folder, "no-work.tsv"), NO_WORK_COLUMNS, {"step": step, "why": why})


def elapsed(path):
    """The seconds of every `Elapsed (wall clock) time` line of the GNU `time -v` log at path, summed."""
    try:
        with open(path, encoding="utf-8", errors="replace") as f:
            found = ELAPSED.findall(f.read())
    except OSError as e:
        raise LedgerError("cannot read the check log %s: %s" % (path, e.strerror)) from None
    if not found:
        raise LedgerError("the check log %s holds no `Elapsed (wall clock) time` line of GNU time -v" % path)
    total = 0.0
    for value in found:
        parts = value.split(":")
        total += float(parts[-1]) + sum(int(p) * 60 ** n for n, p in enumerate(reversed(parts[:-1]), 1))
    return total


def check(root, change, step, log):
    """`oft change-ledger check`: record the GNU `time -v` log of a check run for step of change."""
    folder = _folder(root, change)
    _word("step", step)
    path = os.path.abspath(log)
    elapsed(path)
    stored = _stored(path)
    for row in _read_tsv(os.path.join(folder, "checks.tsv"), CHECK_COLUMNS):
        if row["log"] == stored:
            raise LedgerError("%s is already recorded for step %s of %s" % (path, row["step"], change))
    problem = _idle_problem(change, _idle(folder), [], [{"step": step, "log": stored}])
    if problem:
        raise LedgerError(problem)
    _append(os.path.join(folder, "checks.tsv"), CHECK_COLUMNS, {"step": step, "log": stored})


# -------------------------------------------------------------------------------------------- sessions


def _number(value):
    return isinstance(value, (int, float)) and not isinstance(value, bool)


def _join(spans):
    """The intervals of spans [(start, stop)], joined: sorted, with every overlap merged into one."""
    out = []
    for start, stop in sorted(spans):
        if out and start <= out[-1][1]:
            out[-1] = (out[-1][0], max(out[-1][1], stop))
        else:
            out.append((start, stop))
    return out


def _without(spans, taken):
    """The joined intervals of spans with the joined intervals of taken removed."""
    out = []
    for start, stop in spans:
        for a, b in taken:
            if b <= start or a >= stop:
                continue
            if a > start:
                out.append((start, a))
            start = max(start, b)
            if start >= stop:
                break
        if start < stop:
            out.append((start, stop))
    return out


class Session:
    """The sums of one tagged transcript, of the entries its window holds.  seen holds the entry ids that the session's
    other fragments (and other tags of it in the change) already counted (a resume may copy the history before it): an
    entry whose id is in it counts again in nothing."""

    def __init__(self, row, transcript, seen):
        self.row, self.step, self.id = row, row["step"], row["session"]
        self.logical, self.seen, self.window = _logical(row["transcript"]), seen, _window(row)
        self.machines = [row["host"]] + [v for v in row["vms"].split(",") if v and v != NOT_APPLICABLE]
        self.sums = dict.fromkeys(AGENT, 0)
        self.tool_spans = []   # (start, end) of each turn's tool calls, before they are joined
        self.turn_spans = []   # (start, end) of each counted turn, to take out of the tool time
        self.waits = []        # (start, end) of the time waiting on a tool with no turn running
        self.turn_end = None   # the end of the latest turn counted, which no later turn starts before
        self.partial = collections.defaultdict(list)   # column: [why]
        self.served = collections.Counter()
        self.requested = None
        self.first = self.last = None
        self.read(transcript)

    def lost(self, column, why):
        if why not in self.partial[column]:
            self.partial[column].append(why)

    def lost_each(self, columns, why):
        for column in columns:
            self.lost(column, why)

    def tool_time(self, asked, done, untimed, named):
        """Record the tool calls of the turn at asked, whose last result is at done.  They are joined at the end of
        the read, never added up: omp writes a background call's result when it arrives, so its timestamp can be
        older than entries written before it, and two of these intervals can hold the same second.  With no start
        the time is not measured, never 0, and untimed says which of the two reasons it was: the turn that asked
        had no timestamp, or no turn of this tag asked at all."""
        if done is None:
            return
        if asked is None and untimed:
            self.lost("tool_hours", "a turn in %s has no timestamp: the time of its tool calls has no start" % named)
        elif asked is None:
            self.lost("tool_hours", "a tool result in %s answers a turn this tag does not count: it is outside the "
                                    "window, or copied from an earlier fragment" % named)
        elif done >= asked:
            self.tool_spans.append((asked, done))

    def join_spans(self):
        """tool_hours: the time with a tool call outstanding and no turn running.  The recorded intervals are joined,
        so no second counts twice, and the seconds a turn already counted are taken out.  A turn starts no earlier
        than the end of the turn counted before it, so no two turns hold one second either, and agent_hours +
        waiting_hours + tool_hours is never more than the session's own life."""
        self.waits = _without(_join(self.tool_spans), _join(self.turn_spans))
        self.sums["tool_hours"] = sum((stop - start).total_seconds() for start, stop in self.waits) / 3600

    def add_usage(self, use, where):
        if not isinstance(use, dict):
            for column in TOKENS:
                self.lost(column, "%s has no usage" % where)
            return
        for column, key in USAGE:
            if _number(use.get(key)):
                self.sums[column] += use[key]
            else:
                self.lost(column, "a usage in %s has no %s" % (where, key))
        cost = use.get("cost")
        if isinstance(cost, dict) and _number(cost.get("total")):
            self.sums["cost_usd"] += cost["total"]
        else:
            self.lost("cost_usd", "a usage in %s has no cost.total" % where)

    def read(self, t):
        """Sum t's entries; what gaps.tsv says names the transcript as sessions.tsv records it (~ for the home).  A
        turn's time runs from the entry just before it: when that entry, or the turn, has no timestamp, the turn is
        not measured.  A tool call's time runs from the assistant turn that asked for it to the last tool result
        before the next turn, so the turns and the tool calls of a session never hold the same second twice.  An
        entry another fragment counted (its id in seen) counts in no sum, nor does one outside the tag's window (a
        turn whose own timestamp the window holds counts whole), and the fragment's span (first, last: its wall time
        and the span of its machines) is that of its own entries only.  With a window, a usage with no timestamp is
        not measured: no window can be said to hold it."""
        named, before = self.row["transcript"], None   # before: the timestamp of the entry just before, or None
        asked = done = None   # the turn that asked for tool calls, and the last result of those calls
        untimed = False       # whether that turn is one this tag counts but cannot time
        windowed = self.window != (None, None)
        for no, e in enumerate(t.entries, 1):
            kind = e.get("type")
            ts = None if e.get("timestamp") is None else _time(e["timestamp"], "%s, entry %d" % (t.path, no))
            outside = windowed and (ts is None or not _inside(self.window, ts))
            copied = not outside and e.get("id") is not None and e["id"] in self.seen
            if e.get("id") is not None and not outside:
                self.seen.add(e["id"])
            skip = copied or outside
            if kind == "session_init" and self.requested is None and isinstance(e.get("resolvedModel"), str):
                self.requested = e["resolvedModel"]
            msg = e.get("message") if kind == "message" else None
            turn = isinstance(msg, dict) and msg.get("role") == "assistant"
            result = isinstance(msg, dict) and msg.get("role") == "toolResult"
            if windowed and ts is None and (turn or kind == "model_usage"):
                for column in AGENT:
                    self.lost(column, "a usage in %s has no timestamp: no window can be said to hold it" % named)
            if windowed and ts is None and result:
                self.lost("tool_hours", "a tool result in %s has no timestamp: no window can be said to hold it"
                          % named)
            if turn and not skip:
                self.tool_time(asked, done, untimed, named)
                asked, done, untimed = ts, None, ts is None
                self.add_usage(msg.get("usage"), named)
                self.served["%s/%s" % (msg.get("provider"), msg.get("model"))] += 1
                if ts is None:
                    self.lost_each(TURN_TIME, "an assistant turn in %s has no timestamp" % named)
                elif before is None:
                    self.lost_each(TURN_TIME, "the entry before an assistant turn in %s has no timestamp" % named)
                elif ts < before:
                    self.lost_each(TURN_TIME, "an assistant turn in %s is timed before the entry before it" % named)
                elif self.turn_end is not None and ts < self.turn_end:
                    # its own span is counted in no turn column, so it must not be read as tool time either
                    self.lost_each(HOURS, "an assistant turn in %s is timed before the turn counted before it"
                                   % named)
                else:
                    # a turn starts no earlier than the end of the last turn counted, so two turns never hold the
                    # same second: omp writes a background call's result when it arrives, and the entry before a
                    # turn can then be older than a turn already counted
                    start = before if self.turn_end is None else max(before, self.turn_end)
                    seconds = max(0.0, (ts - start).total_seconds())
                    self.sums["agent_hours" if seconds <= TURN_GAP else "waiting_hours"] += seconds / 3600
                    self.turn_spans.append((start, ts))
                    self.turn_end = ts if self.turn_end is None else max(self.turn_end, ts)
            elif kind == "model_usage" and not skip:
                self.add_usage(e.get("usage"), named)
            if result and not skip:
                if ts is None:
                    self.lost("tool_hours", "a tool result in %s has no timestamp" % named)
                elif asked is not None and ts < asked:
                    self.lost("tool_hours", "a tool result in %s is timed before the turn that asked for it" % named)
                else:
                    done = ts
            if ts is not None and not skip:
                self.first = ts if self.first is None else min(self.first, ts)
                self.last = ts if self.last is None else max(self.last, ts)
            before = ts
        self.tool_time(asked, done, untimed, named)
        self.join_spans()
        if t.cut:
            for column in AGENT:
                self.lost(column, "the transcript %s: %s" % (named, t.cut))


def _began(t):
    """When the Transcript t began: its session entry's timestamp, for the order of a session's fragments."""
    stamp = next((e.get("timestamp") for e in t.entries if e.get("type") == "session"), None)
    return _time(stamp, t.path) if stamp is not None else datetime.datetime.max.replace(tzinfo=datetime.timezone.utc)


def _cell(value, form, partial, measured=True):
    """value in form, `not measured` when nothing was, or `<value> + not measured` when part was not."""
    if not measured:
        return NOT_MEASURED
    return form % value + (" + " + NOT_MEASURED if partial else "")


# -------------------------------------------------------------------------------------------- machines


def _instant(text):
    """text as an aware datetime, or None: a row with no full timestamp is no sample (an allocation note)."""
    try:
        t = datetime.datetime.fromisoformat(text)
    except ValueError:
        return None
    return t if t.tzinfo is not None else None


# the machine types whose vCPUs are known: <series>-<class>-<vcpus>, and a custom type <series>-custom-<vcpus>-<memory
# MB>[-ext] or, for N1, custom-<vcpus>-<memory MB>
MACHINE_TYPE = re.compile(r"(?:[a-z][a-z0-9]*-(?:standard|highmem|highcpu|megamem|ultramem|hypermem)-(?P<vcpus>\d+)"
                          r"|(?:[a-z][a-z0-9]*-)?custom-(?P<custom>\d+)-\d+(?:-ext)?)\Z")


def vcpus_of(kind):
    """The vCPUs a machine type names, or None for a form not known (a shared core, a GPU count, a suffix): its time
    is then not measured, never read as its last number."""
    m = MACHINE_TYPE.match(kind)
    return None if m is None else int(m.group("vcpus") or m.group("custom"))


# one sample of a machine: its type, the vCPUs it names (None when not known) and its life, (created, last_start) as
# idle-stop.tsv gives them, or None
Sample = collections.namedtuple("Sample", "kind vcpus life")


def read_samples(paths):
    """{machine: {time: Sample}} from TSV files with a header naming the columns vm, time (or run_ts) and type (or
    machine_type), as notes/compute-ledger.tsv and notes/idle-stop.tsv have.  A file that also names created and
    last_start (idle-stop.tsv, from GCE) gives each sample its VM's life, (created, last_start), and each life a sample
    at its last start, so a life counts from the moment the VM started.  A row with no full timestamp is not a sample
    (an allocation note written into the ledger)."""
    out = collections.defaultdict(dict)
    for path in paths:
        try:
            with open(path, encoding="utf-8", errors="replace") as f:
                lines = f.read().split("\n")
        except OSError as e:
            raise LedgerError("cannot read the VM samples %s: %s" % (path, e.strerror)) from None
        header = lines[0].split("\t")
        cols = [next((header.index(n) for n in names if n in header), None)
                for names in (("vm",), ("time", "run_ts"), ("type", "machine_type"))]
        if None in cols:
            raise LedgerError("%s: the header names no vm, time (or run_ts) and type (or machine_type) column" % path)
        vm, when, kind = cols
        lives = [header.index(n) for n in ("created", "last_start") if n in header]
        for line in lines[1:]:
            cells = line.split("\t")
            t = _instant(cells[when]) if len(cells) > max(cols + lives) else None
            if t is None:
                continue
            life = tuple(cells[i] for i in lives) if len(lives) == 2 else None
            sample = Sample(cells[kind], vcpus_of(cells[kind]), life)
            if life is not None or out[cells[vm]].get(t, sample).life is None:
                out[cells[vm]][t] = sample
            started = _instant(life[1]) if life else None
            if started is not None and started <= t:
                out[cells[vm]].setdefault(started, sample)
    return out


GONE = re.compile(r"(?:^|,)gone=(\d\d)-(\d\d)T(\d\d):(\d\d)Z(?=,|$)")


def read_deletions(paths):
    """{machine: [(month, day, hour, minute)]} of each deletion the compute inventories at paths record (--vm-deletions,
    with no default: the one bin/ossv-vm keeps through bin/ossv-ledger, whose place each change's inputs.tsv records;
    project, name, zone, machine, status, created, labels, where each deletion appends gone=MM-DDTHH:MMZ to the
    labels)."""
    out = collections.defaultdict(list)
    for path in paths:
        try:
            with open(path, encoding="utf-8", errors="replace", newline="") as f:
                for row in csv.reader(f):
                    if len(row) >= 7:
                        out[row[1]] += [tuple(int(x) for x in m.groups()) for m in GONE.finditer(row[6])]
        except OSError as e:
            raise LedgerError("cannot read the VM deletions %s: %s" % (path, e.strerror)) from None
    return out


def _resolve(mark, near):
    """The deletion mark (read_deletions: month, day, hour, minute; no year) as a UTC time, in the year that puts it
    nearest near."""
    found = []
    for year in (near.year - 1, near.year, near.year + 1):
        try:
            found.append(datetime.datetime(year, *mark, tzinfo=datetime.timezone.utc))
        except ValueError:
            continue
    return min(found, key=lambda g: abs(g - near))


def _merge(spans):
    out = []
    for s, e in sorted(spans):
        if out and s <= out[-1][1]:
            out[-1] = (out[-1][0], max(out[-1][1], e))
        else:
            out.append((s, e))
    return out


def _lives(points):
    """{life: (its start, its last sample)} of each known life of points, [(time, Sample)]."""
    lives = {}
    for t, s in points:
        if s.life and _instant(s.life[1]):
            start, last = lives.get(s.life, (_instant(s.life[1]), t))
            lives[s.life] = (start, max(last, t))
    return lives


def _boundaries(points, gones):
    """The deletions of gones (times) that end a life, in order: one that a later sample of a known life begun before
    it contradicts is no deletion of that VM's, and one less than a minute before a sample of a life begun before it
    (the marks are cut to the minute) is moved to that sample."""
    minute = datetime.timedelta(seconds=60)
    lives = _lives(points)
    out = set()
    for g in gones:
        if not any(start <= g and last - g > minute for start, last in lives.values()):
            out.add(max((t for t, s in points if g <= t < g + minute
                         and not (s.life in lives and lives[s.life][0] > g)), default=g))
    return sorted(out)


def _reconcile(points):
    """points, [(time, Sample)] in time order, with each sample of no known life (compute-ledger.tsv names none) given
    the life of the latest life start at or before it: the VM ran in that life then, as no later one had begun.  A
    deletion between the two is a boundary _segments reads, so such a sample never joins the deleted life."""
    lives = _lives(points)
    out = []
    for t, s in points:
        if s.life is None:
            s = s._replace(life=max(((start, life) for life, (start, _last) in lives.items() if start <= t),
                                    default=(None, None))[1])
        out.append((t, s))
    return out


def _segments(points, gones):
    """[(start, end, vCPUs, why)] of a machine from its samples points, [(time, Sample)] in time order (_reconcile), and
    its deletions gones (_boundaries): each interval it ran and was measured (why None), and each in which it may have
    run with no measurement, with why; None for a start or an end with no bound.  Samples and deletions are read in
    time order, and each stretch between two of them is one of: an interval of one life, the end of a life at its
    deletion, a life no sample shows (between two deletions), or the time after a deletion before a life of no known
    start is sampled; nothing ran between a deletion and a known life's start, or after the last deletion."""
    if not points:
        return [(None, None, None, "no sample")]

    def ran(a, b, sample):
        if sample.vcpus is None:
            return a, b, None, "its machine type %s names no vCPU count" % sample.kind
        return a, b, sample.vcpus, None

    def started(t, sample):
        return sample.life is not None and _instant(sample.life[1]) == t

    events = sorted([(t, 0, s) for t, s in points] + [(g, 1, None) for g in gones], key=lambda e: e[:2])
    t0, gone0, s0 = events[0]
    out = [] if not gone0 and started(t0, s0) else [
        (None, t0, None, "before its first record" if gone0 else "before its first sample")]
    for (a, gone_a, sa), (b, gone_b, sb) in zip(events, events[1:]):
        if gone_a and gone_b:
            out.append((a, b, None, "between two recorded deletions, a life no sample shows"))
        elif gone_a:
            if not started(b, sb):
                out.append((a, b, None, "after its recorded deletion, before its next sample"))
        elif gone_b:
            out.append(ran(a, b, sa) if (b - a).total_seconds() < SAMPLE_GAP
                       else (a, b, None, "after its last sample, until its recorded deletion"))
        elif sa.life != sb.life:
            out.append((a, b, None, "after its last sample, and no deletion record after it"))
        elif (b - a).total_seconds() >= SAMPLE_GAP:
            out.append((a, b, None, "no sample for %d minutes" % ((b - a).total_seconds() // 60)))
        else:
            out.append(ran(a, b, sa))
    last, gone_last, _s = events[-1]
    return out if gone_last else out + [(last, None, None, "after its last sample, and no deletion record after it")]


def vcpu_hours(samples, deletions, machines):
    """(vCPU hours, whether any interval was measured, [(machine, start, end, why)] of each part of a span with no
    measurement) of machines, {name: [(start, end)]}: each interval a machine ran (_segments), cut to the union of its
    spans, times the vCPUs of the interval's first sample.  A span of a machine that holds no interval it ran and no
    part with no measurement is named too: no record shows the machine running then, which is never a measured 0."""
    total, measured, gaps = 0.0, False, []
    for name, spans in sorted(machines.items()):
        spans = _merge(spans)
        points = sorted(samples.get(name, {}).items())
        near = points[0][0] if points else spans[0][0]
        gones = _boundaries(points, sorted(_resolve(m, near) for m in deletions.get(name, [])))
        segments = _segments(_reconcile(points), gones)
        for s, e in spans:
            seen = False
            for a, b, vcpus, why in segments:
                lo, hi = (s if a is None else max(a, s)), (e if b is None else min(b, e))
                if hi <= lo:
                    continue
                seen = True
                if why is None:
                    total += (hi - lo).total_seconds() / 3600 * vcpus
                    measured = True
                else:
                    gaps.append((name, lo, hi, why))
            if not seen:
                gaps.append((name, s, e, "no record shows it running then"))
    return total, measured, gaps


# -------------------------------------------------------------------------------------------- git


def _git(root, *args):
    done = subprocess.run(["git", "-C", root, "-c", "core.quotepath=off", *args], capture_output=True)
    if done.returncode != 0:
        raise LedgerError("git %s: %s" % (" ".join(args), done.stderr.decode("utf-8", "replace").strip()))
    return done.stdout.decode("utf-8", "surrogateescape")


def edit_classes(diff):
    """{"address", "layout", "content": number} of the rewritten line pairs of diff, a `git diff -U0`: in each hunk,
    its removed lines paired in order with its added lines; the lines left over are no pair."""
    counts = dict.fromkeys(("address", "layout", "content"), 0)
    removed, added, in_hunk = [], [], False

    def pairs():
        for a, b in zip(removed, added):
            ha, hb = HEX.sub("@H@", a), HEX.sub("@H@", b)
            counts["address" if ha == hb else "layout" if DEC.sub("@D@", ha) == DEC.sub("@D@", hb) else "content"] += 1

    for line in diff.split("\n"):
        if line.startswith("diff --git ") or line.startswith("@@"):
            pairs()
            removed, added, in_hunk = [], [], line.startswith("@@")
        elif in_hunk and line.startswith("-"):
            removed.append(line[1:])
        elif in_hunk and line.startswith("+"):
            added.append(line[1:])
    pairs()
    return counts


def _git_figures(root, folder, unit, base, head):
    """({git column: value}, contracts.tsv rows or None, a line saying how the prediction did or None, (the base and
    head commits, as full object ids))."""
    try:
        final = prove.report(root, unit, base, head)
    except (ValueError, keys.NoKey) as e:
        raise LedgerError("oft prove %s: %s" % (unit, e)) from None
    p, h = unit.split("/")
    common = ["--no-renames", "--no-ext-diff", "--no-color", final.base, final.head, "--",
              layout.proofs_dir(p, h, layout.OLD), layout.proofs_dir(p, h, layout.NEW)]
    plus = minus = 0
    for line in _git(root, "diff", "--numstat", *common).split("\n"):
        cells = line.split("\t")
        if len(cells) >= 3 and cells[0] != "-":
            plus, minus = plus + int(cells[0]), minus + int(cells[1])
    edits = edit_classes(_git(root, "diff", "-U0", *common))
    states = {c["file"]: c["state"] for c in final.contracts}
    out = dict(final.counts, proof_lines_added=plus, proof_lines_removed=minus,
               contracts_changed=sum(1 for s in states.values() if s in prove.EDITED),
               contracts_needing_work=NOT_MEASURED,
               **{"edits_" + k: v for k, v in edits.items()})
    saved = os.path.join(folder, "prove.json")
    if not os.path.exists(saved):
        return out, None, None, (final.base, final.head)
    try:
        with open(saved, encoding="utf-8") as f:
            prediction = json.load(f)
        predicted = {c["file"]: c["state"] for c in prediction["contracts"]}
        made = (prediction["unit"], prediction["base"])
    except (OSError, ValueError, KeyError, TypeError) as e:
        raise LedgerError("%s is not oft prove --json's report: %s" % (saved, e)) from None
    if made != (unit, final.base):
        raise LedgerError("%s is the prediction for %s from %s, not for %s from %s (--base): it must be oft prove's "
                          "report of the change as it was made" % (saved, made[0], made[1], unit, final.base))
    rows = [{"contract": f, "predicted": predicted.get(f, NOT_APPLICABLE), "final": states.get(f, NOT_APPLICABLE),
             "edited": "yes" if states.get(f) in prove.EDITED else "no"} for f in sorted(set(predicted) | set(states))]
    work = [r for r in rows if r["predicted"] == "needs work"]
    out["contracts_needing_work"] = len(work)
    hit = sum(1 for r in work if r["edited"] == "yes")
    unforeseen = sum(1 for r in rows if r["edited"] == "yes" and r["predicted"] != "needs work")
    return out, rows, ("%d contracts predicted to need work, %d of them edited; %d edited with no such prediction"
                       % (len(work), hit, unforeseen)), (final.base, final.head)


# -------------------------------------------------------------------------------------------- the sum


def summarize(root, change, unit=None, base=None, head="HEAD", samples=(), deletions=(), out=None):
    """`oft change-ledger sum`: read change's records and write ledger.tsv, session-totals.tsv, gaps.tsv, inputs.tsv,
    contracts.tsv (with a saved prediction) and, when it is missing, journal.md.  With unit, the git figures are
    unit's between the commits base and head; samples are the VM sample files, and deletions the compute inventories
    that record VM deletions (read_deletions).  Every record is read before the first file is written."""
    folder = _folder(root, change)
    if (unit is None) != (base is None):
        raise LedgerError("--unit and --base go together: the git figures are a unit's between two commits")
    # the rules tag applies, again: a transcript may be replaced, or a sessions.tsv edited, after tag
    everything = list(_tagged(root))
    tagged = [row for c, row in everything if c == change]
    for i, (c, row) in enumerate(everything):
        problem = c == change and _tag_problem([x for j, x in enumerate(everything) if j != i], change, row)
        if problem:
            raise LedgerError(problem)
    logs = _read_tsv(os.path.join(folder, "checks.tsv"), CHECK_COLUMNS)
    idle = _idle(folder)
    problem = _idle_problem(change, idle, tagged, logs)
    if problem:
        raise LedgerError(problem)
    # the fragments of one session (and the tags of one transcript, each with its window), each read after those it
    # began before, share the ids of the entries counted; the sessions are then kept in the order they were tagged
    read = [(n, r, _own(os.path.expanduser(r["transcript"]), r["session"], change)) for n, r in enumerate(tagged)]
    seen, built = collections.defaultdict(set), {}
    for n, r, t in sorted(read, key=lambda nrt: (_logical(nrt[1]["transcript"]), _began(nrt[2]), nrt[0])):
        built[n] = Session(r, t, seen[_logical(r["transcript"])])
    sessions = [built[n] for n in sorted(built)]
    checks = [(r["step"], elapsed(os.path.expanduser(r["log"]))) for r in logs]
    vms = (read_samples(samples), read_deletions(deletions)) if samples else None
    git, contracts, foresight, commits = (_git_figures(root, folder, unit, base, head) if unit is not None
                                          else ({c: NOT_APPLICABLE for c in GIT}, None, None,
                                                (NOT_APPLICABLE, NOT_APPLICABLE)))
    inputs = ([("unit", unit or NOT_APPLICABLE), ("base", commits[0]), ("head", commits[1])]
              + [("vm_samples", _stored(p)) for p in samples] + [("vm_deletions", _stored(p)) for p in deletions]
              + [("summed_at", _stamp(datetime.datetime.now(datetime.timezone.utc)))])
    steps = list(dict.fromkeys([r["step"] for r in tagged] + [step for step, _s in checks] + list(idle)))
    gaps = []
    logged = {step for step, _x in checks}
    ledger = [_row(step, [s for s in sessions if s.step == step], [x for st, x in checks if st == step], False,
                   step in idle, vms, gaps, {c: NOT_APPLICABLE for c in GIT}) for step in steps]
    ledger.append(_row(TOTAL, sessions, [x for _st, x in checks], bool(set(steps) - logged - set(idle)),
                       bool(steps) and set(steps) <= set(idle), vms, gaps, git))
    totals = []
    for s in sessions:
        totals.append(dict(s.row, requested=s.requested or NOT_APPLICABLE,
                           served=", ".join("%s x%d" % kv for kv in sorted(s.served.items())) or NOT_APPLICABLE,
                           wall_start=_stamp(s.first) if s.first else NOT_MEASURED,
                           wall_end=_stamp(s.last) if s.last else NOT_MEASURED,
                           **_agent_cells([s])))
        gaps += [{"step": s.step, "session": s.id, "column": column, "what": why}
                 for column in AGENT for why in s.partial.get(column, ())]
    os.makedirs(folder, exist_ok=True)
    _write_tsv(os.path.join(folder, "ledger.tsv"), COLUMNS, ledger)
    _write_tsv(os.path.join(folder, "session-totals.tsv"), TOTALS_COLUMNS, totals)
    _write_tsv(os.path.join(folder, "gaps.tsv"), GAP_COLUMNS, gaps)
    _write_tsv(os.path.join(folder, "inputs.tsv"), INPUT_COLUMNS, [dict(zip(INPUT_COLUMNS, i)) for i in inputs])
    written = ["ledger.tsv", "session-totals.tsv", "gaps.tsv", "inputs.tsv"]
    if contracts is not None:
        _write_tsv(os.path.join(folder, "contracts.tsv"), CONTRACT_COLUMNS, contracts)
        written.append("contracts.tsv")
    journal = os.path.join(folder, "journal.md")
    if not os.path.exists(journal):
        with open(journal, "w", encoding="utf-8") as f:
            f.write(render.fill("journal.md.tmpl", "file", change=change) + "\n")
        written.append("journal.md")
    if out is not None:
        print("oft change-ledger: wrote %s in changes/%s/ (%d sessions, %d check logs, %d gaps)"
              % (", ".join(written), change, len(sessions), len(checks), len(gaps)), file=out)
        if foresight:
            print("oft change-ledger: %s" % foresight, file=out)
    return ledger


def _agent_cells(sessions, idle=False):
    """The agent columns of sessions, summed; with none, 0 when idle, else not measured.  waiting_clock_hours is not
    a sum: it is the time with at least one of these sessions waiting on a tool, so a wait that two sessions share
    counts once.  It is the row's own clock, where tool_hours is what the sessions spent."""
    out = {}
    for column in AGENT:
        total = sum(s.sums[column] for s in sessions)
        form = "%.2f" if column in HOURS else "%.4f" if column == "cost_usd" else "%d"
        out[column] = _cell(total, form, any(s.partial.get(column) for s in sessions),
                            measured=bool(sessions) or idle)
    clock = sum((stop - start).total_seconds()
                for start, stop in _join([w for s in sessions for w in s.waits])) / 3600
    out["waiting_clock_hours"] = _cell(clock, "%.2f", any(s.partial.get("tool_hours") for s in sessions),
                                       measured=bool(sessions) or idle)
    return out


def _row(step, sessions, seconds, unlogged, idle, vms, gaps, git):
    """One row of ledger.tsv; each figure not read in full adds its gap to gaps.  seconds are the elapsed times of the
    row's check logs; unlogged, whether a step in the row has none and needed work (the total row's steps); idle,
    whether each step of the row is recorded as needing no work (no-work.tsv), when the row has no session and no
    check log and its agent, VM and check figures are 0; vms, (samples, deletions) or None when no sample file was
    given."""
    row = dict(git, step=step, sessions=len({s.logical for s in sessions}))
    if idle:
        row.update(wall_start=NOT_APPLICABLE, wall_end=NOT_APPLICABLE, vcpu_hours="%.2f" % 0,
                   check_seconds="%.2f" % 0, **_agent_cells([], idle=True))
        return row
    starts = [s.first for s in sessions if s.first]
    ends = [s.last for s in sessions if s.last]
    row["wall_start"] = _stamp(min(starts)) if starts else NOT_MEASURED
    row["wall_end"] = _stamp(max(ends)) if ends else NOT_MEASURED
    row.update(_agent_cells(sessions))
    if not sessions:
        gaps.append({"step": step, "session": NOT_APPLICABLE, "column": ",".join(AGENT),
                     "what": "no session is tagged"})
    machines = collections.defaultdict(list)
    for s in sessions:
        for m in s.machines if s.first else ():
            machines[m].append((s.first, s.last))
    if vms is None or not machines:
        row["vcpu_hours"] = NOT_MEASURED
        gaps.append({"step": step, "session": NOT_APPLICABLE, "column": "vcpu_hours",
                     "what": "no VM sample file was given (--vm-samples)" if machines
                     else "no tagged session has a timestamp" if sessions else "no session is tagged"})
    else:
        total, measured, missing = vcpu_hours(*vms, machines)
        row["vcpu_hours"] = _cell(total, "%.2f", missing, measured=measured)
        gaps += [{"step": step, "session": NOT_APPLICABLE, "column": "vcpu_hours",
                  "what": "%s: not measured from %s to %s: %s" % (name, _stamp(lo), _stamp(hi), why)}
                 for name, lo, hi, why in missing]
    row["check_seconds"] = _cell(sum(seconds), "%.2f", unlogged, measured=bool(seconds))
    if not seconds:
        gaps.append({"step": step, "session": NOT_APPLICABLE, "column": "check_seconds",
                     "what": "no check log is recorded (oft change-ledger check)"})
    return row


# -------------------------------------------------------------------------------------------- the command


def cli(root, a, out):
    """`oft change-ledger tag|check|no-work|sum`; 0, or 1 with the reason on out."""
    try:
        if a.ledger_cmd == "tag":
            tag(root, a.change, a.step, a.session, a.host, a.transcript, vms=a.vm, since=a.since, until=a.until)
            window = "" if (a.since, a.until) == (None, None) else " (from %s until %s)" % (a.since or NOT_APPLICABLE,
                                                                                            a.until or NOT_APPLICABLE)
            print("oft change-ledger: tagged session %s%s as step %s of %s" % (a.session, window, a.step, a.change),
                  file=out)
        elif a.ledger_cmd == "check":
            check(root, a.change, a.step, a.time_log)
            print("oft change-ledger: recorded %s for step %s of %s" % (a.time_log, a.step, a.change), file=out)
        elif a.ledger_cmd == "no-work":
            no_work(root, a.change, a.step, a.why)
            print("oft change-ledger: recorded step %s of %s as needing no work" % (a.step, a.change), file=out)
        else:
            summarize(root, a.change, unit=a.unit, base=a.base, head=a.head, samples=a.vm_samples,
                      deletions=a.vm_deletions, out=out)
    except LedgerError as e:
        print("FAIL oft change-ledger: %s" % e, file=out)
        return 1
    return 0
