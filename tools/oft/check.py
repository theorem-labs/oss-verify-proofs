"""oft check.

`check PROJECT/HARNESS` does what CI does for one harness:

  statements       verify every published ELF's SHA-256; `dune build`, with
                   a dune cache of its own, the statement side (theories/ and the
                   harness directory's own aliases: the images, built by
                   elf-snapshot, Images.v, Statements.v, Characterise.v),
                   counting the rules it ran; then compile a file that
                   names each statement harness.yaml lists (but a withheld or
                   withdrawn one, which Statements.v does not carry) and
                   prints its assumptions: a unit with no such statement, a
                   Statements.v that lacks one, one that is an axiom (Axiom,
                   Parameter, Admitted), or an assumption outside
                   toolchain/allowed-axioms.txt fails
  proofs           build the harness's proof library, lib/ in its proofs
                   folder (proofs/<p>/<h>/, or projects/<p>/<h>/proofs/ in
                   the per-project layout; layout.py), if it has one, with dune
                   (once; dune's cache may supply it), then each proof
                   directory <s>/ there with dune, once, with a cache of its own
                   (build_proof_dirs: every rocq compile dune ran must carry
                   only the flags of oft generate's dune file), then a
                   wrapper this tool writes and compiles with its own flags,
                   which ascribes the built proof's theorem to the statement
                   and prints its assumptions; every assumption must be in
                   toolchain/allowed-axioms.txt.  The kernel checks every term
                   as it compiles.  Each statement's instance (harness.yaml
                   statements.<s>.instance), proved or not, is checked
                   too: a wrapper this tool writes defines the input from
                   the instance file's bytes and ascribes the lemma
                   lib/Instances/<s>.v proves to the type the shape gives
                   it (check_instance); a missing lemma fails the unit
                   only in a project of shapes.REQUIRED.  A unit with no
                   proof has its instances checked in the statements part.
  counterexamples  run the binary on input.bin and on control.bin under
                   qemu-user and compare with expect.yaml
  findings         run each finding's input.bin and control.bin on every
                   build its statements name, on the unpatched binaries
                   (which the project's unpatched.yaml pins), under qemu-user,
                   and compare each run's exit, signal, stdout and stderr with
                   finding.yaml; --record prints the runs of a finding that
                   has none yet, to commit, only when no run timed out or
                   died of a signal a finding does not record, its input
                   shows each statement false and its control none

--rocqchk adds rocqchk, an independent re-check of the compiled libraries:
over the statements, and once per harness over the wrappers of all its proofs.
Off by default: without its bytecode machine (see _rocqchk) it re-checks every
vm_compute certificate by reduction, which takes hours for one proof.

Each part refuses a unit when it examined nothing it was asked to examine: a unit
with no statement Statements.v defines refuses statements, and a unit with no
proof is refused when --parts names proofs. A run requesting statements or proofs
that covers no compiling work, and whose guard refuses no proof directory, is
VOID (7), not a proof verdict. Without --parts,
a unit is checked on each of statements, proofs and counterexamples that it has.

Every check first loads the facts of the whole tree and checks its rules.
--facts-to DIR and --facts-from DIR split that from the rest, so that each unit
can be checked in a view that holds only its own files:

  --facts-to DIR    load the facts and check the rules of the whole tree, then
                    write the facts each unit's check reads, and nothing of
                    another unit or of the whole tree but the release's names
                    (its namespace and opam stem, which a view's missing
                    release.yaml would give), to
                    DIR/<project>/<harness>.yaml (facts.unit_facts), with the
                    SHA-256 of each unit file they came from and the list of
                    the unit's proof, counterexample and finding directories.
                    Builds and runs nothing.
  --facts-from DIR  check each unit with its facts from DIR (facts.load_unit),
                    as a plain check would, without loading the tree or
                    checking its rules, so --root may be a view of the unit.  A
                    run is VOID and stops when a unit's file is missing, malformed,
                    of another format version or of another unit, when the file's
                    namespace does not give harness.yaml's rocq, or when, for
                    a part the run checks, a unit file its facts came from is
                    missing under --root or differs, or the unit's directories
                    differ.

That compares nothing else.  The rules read more, in the unit (source/,
Distribution.v, the build record under provenance/) and in the rest of the tree
(theories/Shapes.v, which every fingerprint hashes), so it cannot show that the
facts and the view come from one tree.  So write the facts from the checkout the
views are made from, and mount DIR read-only, so that no check can change the
facts that it or another unit is checked with.  Give a unit's check only its own
file: another unit's file holds that unit's facts, which a view leaves out.  The
file's format is part of the checker, whose files are in every unit's key
(keys.py), so a change to it re-keys every unit.

CI runs `python3 -m oft.check`, which loads the checker and none of the other
commands' modules (keys.py says which files the checker is).
"""
import argparse
import collections
import contextlib
import hashlib
import os
import re
import resource
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time

import yaml

from . import facts, fetch, layout, names, render, rules, schema, shapes, yamlio

# VOID is not a verdict. Elsewhere 0, 1, 2, 124, 134, 137, 139, 141, 143 and 255 are in use;
# 3 and 4 are the n6 pod's own "nothing was checked" codes, which it writes today.  The n6 pod and
# the farm runner, under dev/stream/bin/, do not read 7 yet; #2108 teaches them to.
VOID = 7


def void(out, reason):
    """The one VOID line: the word leads it, so a reader who sees nothing else sees it, and it carries the
    reason and the exit code.  The stream's kit job script prints a line of the same shape and exits 7
    for a round it voids itself, so a lane greps `^VOID: ` and reads exit 7 whichever of the two spoke."""
    print("VOID: %s; NOT A VERDICT (exit %d): any FAIL, ERROR or step count above describes the harness this "
          "run was given, not its proofs." % (" ".join(str(reason).split()), VOID), file=out)
    return VOID


# Print Assumptions writes into a file of its own (Redirect "assumptions" makes assumptions.out in the compile's
# working directory, and truncates it), and the audit reads that file and nothing else, so what a proof makes Rocq
# print while the wrapper or Defined.v compiles -- a deprecation or warn note, a message -- never reaches the audit.
# Before, the audit read the compile's merged output, and a note that printed "Closed under the global context" there
# hid every axiom (the Verified Linux team's report, 2026-10-29).  Both compile with every warning off (-w -all), which
# only keeps their logs quiet: a proof's `Global Set Warnings "default".` turns the warnings back on when the wrapper
# loads it, and the audit does not depend on them being off.
ASSUMPTIONS_OUT = "assumptions.out"
# A bound statement takes its b as `(n # d)`, QArith's notation, which parses only where QArith is imported; the
# import adds no assumption, and a b that is not the proof's still fails to unify.
WRAPPER = """(* written by oft check; never supplied by a pull request *)
From Stdlib Require Import QArith.
Require {stmt_mod}.
Require {proof_mod}.
Definition certified : {neg}{stmt_mod}.{stmt}{args} := {proof_mod}.{theorem}.
Set Printing Fully Qualified.
Redirect "assumptions" Print Assumptions certified.
"""

# The wrapper of a statement's instance (check_instance): the input rendered from the instance file's bytes
# (shapes.instance_input), and the instance lemma ascribed the type the statement's shape gives it
# (shapes.instance_type).  A lemma about other bytes, another input or another type does not type-check.  The imports
# are those of theories/Premises.v, and Shapes and the harness's Images as Statements.v imports them, with the
# library that defines core_input and file_core.  The input and the type are Definitions made BEFORE the wrapper
# requires the lemma's library, so every name in them (Images.<build>, Budgets.*, Env.*, and the list notation) is
# resolved against the checker's own libraries.  The library is the proof's pull request's own: once it is loaded, a
# library file of it with the same suffix (an Images.v that defines plain) would take the partly qualified name, and
# the type would be of another image (tests/instances/shadowed_images, a control).  After the Require the wrapper
# names only its own oft_instance_type, a short name that a Require does not make visible from another library, and
# the lemma by its full name.
INSTANCE_WRAPPER = """(* written by oft check; never supplied by a pull request *)
From Stdlib Require Import ZArith List.
From stdpp.bitvector Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs MemImageType StackLayout State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import FinInput MeasureLib.
From {core} Require Import Shapes.
From {rocq} Require Images.
Import ListNotations.
Definition {input} : {input_type} := {input_term}.
Definition oft_instance_type : Prop := {type}.
Require {lemma_mod}.
Definition certified : oft_instance_type := {lemma_mod}.{lemma}.
Set Printing Fully Qualified.
Redirect "assumptions" Print Assumptions certified.
"""

DEFINED = """(* written by oft check: each statement harness.yaml lists, typed, and what it assumes *)
Require {stmt_mod}.
Definition oft_listed := ({terms}).
Set Printing Fully Qualified.
Redirect "assumptions" Print Assumptions oft_listed.
"""

# What Print Assumptions prints (Rocq 9.2.0, printing/printer.ml, pr_assumptionset): "Closed under the global
# context", or sections with no blank line between them, each a heading and then one entry per line at column 0 (a long
# entry continues on indented lines).  Under "Axioms:" an axiom is "<name> : <type>"; a construct the kernel took on
# trust is a sentence instead: "<inductive> is assumed to be positive.", "<name> is assumed to be guarded.", "<name>
# relies on an unsafe hierarchy.", "<inductive> relies on definitional UIP.".  "Theory:" lists changes to the logic
# itself (type in type, impredicative Set, rewrite rules).
SECTIONS = ("Transparent constants:", "Section Variables:", "Axioms:", "Opaque constants:", "Theory:")
CLOSED = "Closed under the global context"


def wrapper_assumptions(text):
    """The axioms in Print Assumptions' output, TEXT, which is all of what it printed and nothing else (Set Printing
    Fully Qualified).  Nothing is assumed only when TEXT is exactly the one line "Closed under the global context": an
    axiom's printed type can hold that line too (a string literal with line breaks).  Otherwise TEXT is a list of
    assumptions from its first line on, with no empty line inside, and CheckError is raised on every entry that is not
    an axiom and its type (a construct taken on trust, a change to the logic, an axiom whose type did not print, a line
    a type printed): nothing parsed is not nothing assumed.  Lines end only at "\\n", and only a space or a tab makes a
    line blank or a continuation, as tests/check.sh reads them: a line a type printed that starts with another blank
    (U+00A0, a form feed) is an entry, and refused."""
    lines = text.split("\n")
    while lines and not lines[-1].strip(" \t"):
        lines.pop()
    if lines == [CLOSED]:
        return set()
    if not lines or lines[0] not in SECTIONS:
        raise CheckError("Print Assumptions printed neither exactly '%s' nor a list of assumptions" % CLOSED)
    axioms, other, section = set(), [], None
    for l in lines:
        if not l.strip(" \t"):
            raise CheckError("Print Assumptions' list of assumptions holds an empty line, which no list it prints has")
        if l[0] in " \t":
            continue
        if l in SECTIONS:
            section = l
            continue
        m = re.match(r"([^ \t]+) :( |$)", l)
        if section == "Axioms:" and m:
            axioms.add(m.group(1))
        else:
            other.append(l if section == "Axioms:" else "%s %s" % (section, l))
    if other:
        raise CheckError("the proof relies on what the kernel did not check: %s" % "; ".join(other))
    if not axioms:
        raise CheckError("Print Assumptions printed an empty list of assumptions")
    return axioms


def read_assumptions(d, log):
    """The axioms Print Assumptions wrote into D/assumptions.out (see ASSUMPTIONS_OUT); LOG is the compile's log."""
    path = os.path.join(d, ASSUMPTIONS_OUT)
    if not os.path.isfile(path):
        raise CheckError("Print Assumptions wrote no %s (see %s)" % (ASSUMPTIONS_OUT, log))
    return wrapper_assumptions(facts.read_raw(path))   # a carriage return stays, as tests/check.sh reads it


class CheckError(RuntimeError):
    pass


class Compilation:
    """Compiling work covered by one check: dune targets (cache hits included) and rocq compile invocations, in
    `files`; and in `refused`, the proof directories build_proof_dirs' guard refused before any compile of them.

    `run` keeps one of these and reads it for the void rules.  Every function below that compiles takes it as
    a KEYWORD argument defaulting to None, so each keeps the signature it had before this
    counter existed: the two gate-job scripts, under tools/publish/ and dev/stream/bin/, call
    check_statements,
    compile_lib and check_proof positionally and from outside this module, and a positional parameter here
    ended them in TypeError (the CI/CD lead, 2026-11-06 17:25Z).  A caller that passes none compiles exactly
    as before and its work is counted into a throwaway (`counter`): the void rules are `oft check`'s own, and
    a caller that drives these functions itself reaches none of them."""

    def __init__(self):
        self.files = 0
        self.refused = 0
        self.jobs = None

    def run(self, cmd, cwd, log, count=1, env=None, watch=None):
        self.files += count
        try:
            return _run(cmd, cwd, log, env=env, watch=watch)
        except OSError:
            self.files -= count  # the compiler did not start
            raise

    def dune(self, root, targets, log, env=None, watch=None):
        # The job count is _jobs(), which main gave both build paths in #2121: OFT_JOBS, else the cgroup's
        # CPU quota, at most the CPUs this process may run on.  Not the affinity alone, which this branch
        # used before the rebase: in a pod with a CPU limit and no cpuset the affinity is the node's 32-64
        # CPUs, and -j that many ran the pod out of memory.  What this class adds is that the count is
        # RECORDED, so a round that compiled under no job count can be told from one that compiled under
        # this job's own width.
        # Never -j 0.  _jobs floors at 1 only on its cgroup-quota branch: with no quota it answers the size
        # of the affinity set, which is 0 on a runner that reports none, and dune then got `-j 0` (CI run
        # 42285943632, the sixth non-author review of #2109).  The floor belongs here, where the count is
        # used, rather than in _jobs, which is main's.  So this tool always passes an explicit positive -j
        # and has no "no job count" case to void; that case is real one layer out, in the n6 pod, which can
        # run a job for which no width was ever determined and then sets dune no job count at all (#2108).
        # What this class adds is that the count is RECORDED, so a reader can tell a round that compiled
        # under this job's own width from one that did not.  env and watch go to _run as they are: the
        # statement side's and the proof directories' own dune cache (own_dune_cache), and build_proof_dirs'
        # watch of the job's deadline (DirTimeLimit).
        if self.jobs is None:
            self.jobs = max(1, _jobs())
        return self.run(["dune", "build", "--root", root, "--display", "short", "-j", str(self.jobs)] + targets,
                        root, log, len(targets), env=env, watch=watch)


def counter(compilation):
    """COMPILATION, or a throwaway for a caller outside `run` that passed none (Compilation)."""
    return compilation if compilation is not None else Compilation()


def _run(cmd, cwd, log, timeout=None, env=None, watch=None):
    """Run cmd, appending its output to log; its return code.  Without watch, timeout bounds the run as
    subprocess.run's does; with watch, call watch(process) about once a second while it runs.  timeout and watch
    together raise ValueError: a watched run has no timeout, so a caller would lose its bound."""
    if timeout is not None and watch is not None:
        raise ValueError("_run takes a timeout or a watch, not both")
    with open(log, "a", encoding="utf-8") as f:
        f.write("$ %s\n" % " ".join(cmd))
        f.flush()
        if watch is None:
            return subprocess.run(cmd, cwd=cwd, stdout=f, stderr=subprocess.STDOUT, timeout=timeout,
                                  env=env).returncode
        with subprocess.Popen(cmd, cwd=cwd, stdout=f, stderr=subprocess.STDOUT, env=env) as p:
            while True:
                try:
                    return p.wait(timeout=1)
                except subprocess.TimeoutExpired:
                    watch(p)


def _processes():
    """{pid: (parent pid, argv)} of every process /proc shows; one that ends while it is read is left out."""
    out = {}
    for e in os.listdir("/proc"):
        if not e.isdigit():
            continue
        try:
            with open("/proc/%s/stat" % e, "rb") as f:
                ppid = int(f.read().rsplit(b")", 1)[1].split()[1])
            with open("/proc/%s/cmdline" % e, "rb") as f:
                argv = f.read().decode("utf-8", "replace").split("\0")
        except (OSError, ValueError, IndexError):
            continue
        out[int(e)] = (ppid, argv)
    return out


class DirTimeLimit:
    """The watch of build_proof_dirs' dune: no proof directory compiles past `deadline`, an absolute time.monotonic()
    bound (the job's own end).  From then on, each compile of a proof directory's .v file seen among dune's
    descendants (dune 3.23.0 runs each as `rocqworker --kind=compile ... <dir>/<file>.v`, the path relative to
    _build/default) is killed, and its directory is stopped; dune then fails only those rules and builds the other
    targets.  `stopped` holds each directory it stopped."""

    def __init__(self, dirs, deadline):
        self.dirs, self.deadline = sorted(dirs), deadline
        self.stopped = set()

    def _dir(self, argv):
        if not any(a == "compile" or a.startswith("--kind=compile") for a in argv):
            return None
        for a in argv:
            if a.endswith(".v"):
                d = next((d for d in self.dirs if a.startswith(d + "/")), None)
                if d:
                    return d
        return None

    def __call__(self, proc):
        if time.monotonic() < self.deadline:
            return
        procs = _processes()
        mine, grew = {proc.pid}, True
        while grew:
            grew = False
            for pid, (ppid, _) in procs.items():
                if ppid in mine and pid not in mine:
                    mine.add(pid)
                    grew = True
        for pid in sorted(mine - {proc.pid}):
            d = self._dir(procs[pid][1])
            if d is None:
                continue
            self.stopped.add(d)
            try:
                os.kill(pid, signal.SIGKILL)
            except ProcessLookupError:
                pass


def _log_end(log):
    """Where the next _run's output into log starts: _run appends, and a work directory may hold earlier runs."""
    try:
        return os.path.getsize(log)
    except FileNotFoundError:
        return 0


# A build that fails says why in its log, which can run to hundreds of thousands of lines, and the log is in the check's
# work directory, which a build service's pod deletes when it ends.  So the CheckError of a failed build quotes the
# log's errors (log_errors).  An Error: block is dune's or Rocq's `File "...", line N...` header and the lines up to the
# next such header or the end of the log, when one of them starts with `Error:`.  An `Error:` line with no header open
# before it (dune's `Error: Don't know how to build ...`), or one that would not be quoted whole in the open block,
# opens a block of its own, with as many of the ERROR_CONTEXT lines before it as fit, as the gate's pod script reads a log
# with `grep -C 5`.  At most ERROR_BLOCKS blocks are quoted, the first ones, in at most ERROR_BYTES bytes and ERROR_LINES
# lines, every byte of a quoted line counted, its prefix too; a later block only when what is left holds it whole up to
# its Error: line.  One note per quoted block that says how many of its lines were left out comes on top.  So an
# Error: line is cut only when it alone is longer than the bound.  Each quoted line starts with QUOTE, as proofs_apart
# echoes a process's output, also where a log line holds a character that str.splitlines ends a line at (a carriage
# return, U+2028): no line of the log can stand as a line of the check's own output, a summary or a proof's claim.
ERROR_BLOCKS = 5
ERROR_BYTES = 8000
ERROR_LINES = 200
ERROR_CONTEXT = 5
# what a log with no Error: line shows instead: its last lines
ERROR_TAIL_LINES = 40
FILE_HEADER = re.compile(r'File "[^"]*", lines? \d+')
QUOTE = "  | "
CUT = " [cut]"


def _log_lines(f):
    """(line, whether it was cut) for each line of the binary file f, without its line end, decoded: a line longer than
    ERROR_BYTES bytes is cut to them and the rest of it read in pieces of that size and dropped, so no line is held
    whole, also in a log with no line end at all."""
    while True:
        raw = f.readline(ERROR_BYTES + 1)
        if not raw:
            return
        cut = len(raw) > ERROR_BYTES and not raw.endswith(b"\n")
        if cut:
            rest = raw
            while rest and not rest.endswith(b"\n"):
                rest = f.readline(ERROR_BYTES + 1)
            raw = raw[:ERROR_BYTES]
        yield raw.rstrip(b"\r\n").decode("utf-8", "replace"), cut


def _quoted(line, cut):
    """The quoted lines of one log line: QUOTE and each piece str.splitlines gives, the last marked CUT when the log line
    was cut."""
    pieces = line.splitlines() or [""]
    if cut:
        pieces[-1] += CUT
    return [QUOTE + p for p in pieces]


class _Quote:
    """Quoted lines, kept to ERROR_BYTES bytes (each line's own, its line end included) and ERROR_LINES lines, and the
    notes among them, which are not counted."""

    def __init__(self):
        self.lines, self.size, self.count = [], 0, 0

    def full(self):
        return self.size >= ERROR_BYTES or self.count >= ERROR_LINES

    def add(self, text, front=False):
        """Add text, cut (never inside a character, and marked CUT) to the room that is left; whether it was added
        whole.  Nothing is added when there is no room for more than the prefix."""
        if self.full():
            return False
        b, room = (text + "\n").encode("utf-8"), ERROR_BYTES - self.size
        got = text
        if len(b) > room:
            keep = room - len((CUT + "\n").encode("utf-8"))
            if keep <= len(QUOTE):
                self.size = ERROR_BYTES
                return False
            got = b[:keep].decode("utf-8", "ignore") + CUT
        if front:
            self.lines.insert(0, got)
        else:
            self.lines.append(got)
        self.size += len((got + "\n").encode("utf-8"))
        self.count += 1
        return got == text

    def note(self, text):
        self.lines.append(text)


def _size(line, cut):
    """(bytes, lines) that _Quote takes for the quoted lines of one log line, their line ends included."""
    pieces = _quoted(line, cut)
    return sum(len((p + "\n").encode("utf-8")) for p in pieces), len(pieces)


class _Block:
    """A block of the log as log_errors reads it: its lines from its start for as long as each fits whole in
    ERROR_BYTES and ERROR_LINES, counted as _Quote counts them; how many lines it has in all; and whether one of them
    starts with Error:."""

    def __init__(self):
        self.lines, self.size, self.count, self.all, self.error, self.closed = [], 0, 0, 0, False, False

    def fits(self, line, cut):
        if self.closed:
            return False
        n, k = _size(line, cut)
        return self.size + n <= ERROR_BYTES and self.count + k <= ERROR_LINES

    def add(self, line, cut, force=False):
        """Keep the line if it fits whole, else close the block: no later line is kept.  With force (the block's
        first Error: line) keep it anyway, for _Quote to cut, since only a line longer than the whole bound fails to
        fit a block that it opened (log_errors)."""
        self.all += 1
        if self.fits(line, cut) or force:
            n, k = _size(line, cut)
            self.lines.append((line, cut))
            self.size, self.count = self.size + n, self.count + k
        else:
            self.closed = True


def log_errors(log):
    """The text a CheckError for a build that failed adds after its first line: the first Error: blocks of log, as many
    as ERROR_BLOCKS, ERROR_BYTES and ERROR_LINES allow, how many it leaves out and where the whole log is; for a log
    with no Error: line at all, its last lines, at most ERROR_TAIL_LINES of them in the same bounds.  It reads the log
    in pieces of at most ERROR_BYTES + 1 bytes and keeps only what it can quote, so a log of any size, or with lines of
    any length, takes little memory."""
    found, kept, block = 0, [], None
    before = collections.deque(maxlen=ERROR_CONTEXT)
    tail = collections.deque(maxlen=ERROR_TAIL_LINES)

    def close():
        nonlocal found
        if block is not None and block.error:
            found += 1
            if len(kept) < ERROR_BLOCKS:
                kept.append(block)

    try:
        with open(log, "rb") as f:
            for line, cut in _log_lines(f):
                header, error = FILE_HEADER.match(line), line.startswith("Error:")
                # an Error: line that would not be quoted whole in the open block opens a block of its own
                if header or error and (block is None or not block.fits(line, cut)):
                    close()
                    block = _Block()
                    if not header:
                        # the lines before it, as many as fit with it
                        size, count = _size(line, cut)
                        context = []
                        for c in reversed(before):
                            n, k = _size(*c)
                            if size + n > ERROR_BYTES or count + k > ERROR_LINES:
                                break
                            context.insert(0, c)
                            size, count = size + n, count + k
                        for c in context:
                            block.add(*c)
                before.append((line, cut))
                tail.append((line, cut))
                if block is None:
                    continue
                block.add(line, cut, force=error and not block.error)
                block.error = block.error or error
            close()
    except OSError as e:
        return "\nthe log %s cannot be read: %s" % (log, e)
    if found:
        q, quoted = _Quote(), 0
        for b in kept:
            lines, count = b.lines, b.all
            # a later block is quoted only when what is left holds it whole up to its Error: line
            first = next((i for i, (l, _) in enumerate(lines) if l.startswith("Error:")), len(lines) - 1)
            need_bytes = need_lines = 0
            for c in lines[:first + 1]:
                n, k = _size(*c)
                need_bytes, need_lines = need_bytes + n, need_lines + k
            if q.full() or quoted and (q.size + need_bytes > ERROR_BYTES or q.count + need_lines > ERROR_LINES):
                break
            shown = 0   # lines quoted, the last one maybe cut
            for line, cut in lines:
                n = q.count
                whole = all(q.add(p) for p in _quoted(line, cut))
                shown += q.count > n
                if not whole:
                    break
            quoted += shown > 0
            if shown and count > shown:
                q.note("%s[%d more line(s) of this block left out]" % (QUOTE, count - shown))
        return "\nthe log holds %d Error: block(s): %d quoted here%s; the whole log is %s\n%s" % (
            found, quoted, ", %d left out" % (found - quoted) if found > quoted else "", log, "\n".join(q.lines))
    if not tail:
        return "\nthe log holds no Error: line and is empty: %s" % log
    q, shown = _Quote(), 0
    for line, cut in reversed(tail):
        pieces = _quoted(line, cut)
        need = sum(len((p + "\n").encode("utf-8")) for p in pieces)
        if q.size + need > ERROR_BYTES or q.count + len(pieces) > ERROR_LINES:
            if not shown:   # the last line alone is too long: its end, cut
                q.add(pieces[-1], front=True)
                shown = 1
            break
        for p in reversed(pieces):
            q.add(p, front=True)
        shown += 1
    return "\nthe log holds no Error: line; its last %d line(s) are quoted here; the whole log is %s\n%s" % (
        shown, log, "\n".join(q.lines))


def _again(e):
    """What each proof after the first prints for one failure that fails them all (a proof library that does not
    compile): its first line, and where the log it quotes is, so that the quoted log is printed once."""
    head, _, rest = str(e).partition("\n")
    return head + (" (its log is quoted above, at the first proof that failed on it)" if rest else "")


def allowed_axioms(root, path):
    p = os.path.join(root, path)
    if not os.path.isfile(p):
        raise CheckError("%s is missing" % path)
    out = {l.strip() for l in facts.read(p).splitlines() if l.strip() and not l.startswith("#")}
    if not out:
        raise CheckError("%s is empty" % path)
    return out


UNSAFE = ("relying on type-in-type", "relying on unsafe (co)fixpoints", "whose positivity is assumed")


def rocqchk_axioms(text):
    """(finished, axioms) from rocqchk -o's CONTEXT SUMMARY.  `finished` is
    False unless every module checked and nothing relies on type-in-type,
    unsafe fixpoints or assumed positivity."""
    ok = "Modules were successfully checked" in text and "CONTEXT SUMMARY" in text
    axioms, inside = set(), False
    for line in text.split("CONTEXT SUMMARY", 1)[-1].splitlines():
        s = line.strip()
        if s.startswith("*"):
            inside = s.startswith("* Axioms:")
            if any(u in s for u in UNSAFE) and not s.endswith("<none>"):
                ok = False
            continue
        if inside and s and s != "<none>":
            axioms.add(s)
    return ok, axioms


def _loadpath(build, h):
    """-Q mappings for the core and one harness, from a _build/default tree."""
    return ["-Q", os.path.join(build, "theories"), names.rocq_core(h.tree.namespace),
            "-Q", os.path.join(build, h.dir), h.data["rocq"]]


def _rocqchk(root, qargs, modules, allowed, log):
    open(log, "w").close()
    # without its bytecode machine: stock rocqchk 9.2.0 refuses every library that
    # holds a primitive string with it on (tests/check.sh says more)
    rc = _run(["rocqchk", "-o", "-bytecode-compiler", "no"] + qargs + modules, root, log)
    ok, axioms = rocqchk_axioms(facts.read(log))
    if rc != 0 or not ok:
        raise CheckError("rocqchk failed (see %s)" % log)
    if not axioms:
        raise CheckError("rocqchk reported no axioms at all: its summary was not read (see %s)" % log)
    outside = sorted(axioms - allowed)
    if outside:
        raise CheckError("axioms outside the allowlist: %s" % ", ".join(outside))
    return len(axioms)


def check_statements(root, h, allowed, work, out, rocqchk=False, compilation=None):
    compilation = counter(compilation)
    if not h.builds():
        raise CheckError("every build is withheld: nothing to check")
    listed = sorted(st.name for st in h.statements.values() if st.rendered())
    if not listed:
        raise CheckError("every statement harness.yaml lists is withheld or withdrawn, so Statements.v defines none: "
                         "nothing to check")
    if not os.path.isfile(os.path.join(root, h.dir, "Statements.v")):
        raise CheckError("%s/Statements.v is missing (run ./oft generate)" % h.dir)
    # Also here, and not only in run(), which checks every build of the unit before any part of it runs: the two
    # gate-job scripts, under tools/publish/ and dev/stream/bin/, call check_statements themselves,
    # from outside this module, and a check of theirs must refuse the wrong binary too.
    if fetch.verify_builds(root, h, out)[1]:
        raise CheckError("the binaries are missing or do not match (run ./oft fetch %s)" % h.project.name)
    mods = [h.data["rocq"] + "." + f[:-2] for f in ("Images.v", "Statements.v", "Characterise.v")
            if os.path.isfile(os.path.join(root, h.dir, f))]
    log = _unit_log(work, h, "statements")
    start = _log_end(log)
    # The statement side never reads or writes the caller's dune cache (OSSV-299 R7; own_dune_cache): every rule of it
    # runs here, and the line below counts them.  --display short: the log names each rule dune ran.
    rc = _build_statement_side(root, h, work, log, compilation)
    if rc != 0:
        raise CheckError("dune build failed (see %s)%s" % (log, log_errors(log)))
    rules_run = _log_rules(log, start)
    counted = "; %d rules run, %d under theories/" % (
        len(rules_run), sum(1 for r in rules_run if any(t.startswith("theories/") for t in r)))
    build = os.path.join(root, "_build", "default")
    check_defined(root, h, listed, build, work, allowed, compilation=compilation)
    if not rocqchk:
        print("%s: statements compiled, each of the %d listed defined%s" % (h.dir, len(listed), counted), file=out)
        return
    n = _rocqchk(root, _loadpath(build, h), mods, allowed,
                 os.path.join(work, names.ident(h.project.name) + "." + names.ident(h.name) + ".rocqchk.log"))
    print("%s: statements compiled, each of the %d listed defined; rocqchk: %d axioms, all allowed%s"
          % (h.dir, len(listed), n, counted), file=out)


# The folders of a harness directory that hold no part of its statements: each is a theory of its own or no theory.
NOT_STATEMENTS = ("proofs", "counterexamples", "findings")


def statement_targets(root, h):
    """What dune builds of the statement side: theories/'s default alias, the .vo of each .v at the top of h.dir, and
    the default alias of each directory below h.dir (but NOT_STATEMENTS) that holds a .v or a dune file (images/, whose
    rule writes the .v files Images.v loads).  Never h.dir's own default alias: in the per-project layout dune 3.23.0
    builds the proofs folder under it with it (coturn/FuzzStunClient, 2026-11-02: 1,091 library rules and each proof
    directory's), which would compile the proofs here, outside build_proof_dirs and its check of their flags."""
    out = ["@@theories/default"]
    top = os.path.join(root, h.dir)
    for dp, dn, fn in os.walk(top):
        if dp == top:
            dn[:] = [d for d in dn if d not in NOT_STATEMENTS]
            out += sorted(os.path.join(h.dir, f[:-2] + ".vo") for f in fn if f.endswith(".v"))
        dn.sort()
        if dp != top and any(f.endswith(".v") or f == "dune" for f in fn):
            out.append("@@%s/default" % os.path.relpath(dp, root))
    return out


_RULE = re.compile(r" +([A-Za-z][\w.+-]*) (\S+)( \(.*\))?$")


def _expand(spec):
    """The paths of one target list of dune's short display: `a/B.{glob,vo},a/NB.{cmi,cmxs}`."""
    out, parts, depth, cur = [], [], 0, ""
    for c in spec:
        if c == "," and depth == 0:
            parts.append(cur)
            cur = ""
            continue
        depth += (c == "{") - (c == "}")
        cur += c
    parts.append(cur)
    for p in parts:
        m = re.fullmatch(r"(.*)\{([^{}]*)\}(.*)", p)
        out.extend([m.group(1) + x + m.group(3) for x in m.group(2).split(",")] if m else [p])
    return out


def _rule_targets(line):
    """The targets of the rule one line of a `dune build --display short` log names as run, or None: a line of an
    indented program name and its targets (dune 3.23.0)."""
    m = _RULE.fullmatch(line)
    return _expand(m.group(2)) if m else None


def _log_rules(log, start=0):
    """[the targets of each rule] that the `dune build --display short` log at log names as run from byte start on.
    The log is read a line at a time, each line within ERROR_BYTES (_log_lines), so a log of any size takes memory
    for the rules it names, not for its text."""
    out = []
    with open(log, "rb") as f:
        f.seek(start)
        for line, _cut in _log_lines(f):
            targets = _rule_targets(line)
            if targets is not None:
                out.append(targets)
    return out


def _unit_log(work, h, kind):
    """The log in work of one kind of h's dune builds: statements (check_statements' and compile_lib's statement
    side), lib (the library's build alone) or proofs (build_proof_dirs')."""
    return os.path.join(work, "%s.%s.%s.dune.log" % (names.ident(h.project.name), names.ident(h.name), kind))


def _build_statement_side(root, h, work, log, compilation):
    """The exit status of dune's build of h's statement side (statement_targets) into log, with a dune cache of its
    own (own_dune_cache): check_statements' and compile_lib's."""
    with own_dune_cache(work) as env:
        return compilation.dune(root, statement_targets(root, h), log, env=env)


@contextlib.contextmanager
def own_dune_cache(work):
    """The environment of a dune build that neither reads nor writes the caller's dune cache: the statement side's
    (OSSV-299 R7) and the proof directories' (each proof is compiled here, never taken from a cache).  It keeps the
    caller's DUNE_CACHE and sets DUNE_CACHE_ROOT to a new empty directory under work, removed after the build.
    DUNE_CACHE must stay the caller's: dune 3.23.0 digests each rule together with whether the rule may go in the
    cache, which DUNE_CACHE decides (bin/common.ml, can_go_in_shared_cache_default; src/dune_engine/build_system.ml,
    compute_rule_digest), so a build under another DUNE_CACHE than compile_lib's, in the same _build, runs again every
    rule the build before it ran.  Under a caller's dune cache (DUNE_CACHE=enabled), as the farm's lanes run, the proof
    build so compiled the whole library a second time, after the store had supplied it, and left .vo files that the
    store's entries do not name: the push skipped those entries, and the next build missed them (zlib/checksum_fuzzer,
    2026-11-02)."""
    root = tempfile.mkdtemp(prefix="dune-cache-", dir=work)
    try:
        yield {**os.environ, "DUNE_CACHE_ROOT": root}
    finally:
        shutil.rmtree(root, ignore_errors=True)


def check_defined(root, h, listed, build, work, allowed, compilation=None):
    """Have the kernel type every statement in listed, from h's compiled Statements (a _build/default tree), and print
    what they assume.  A Statements.v that compiles but lacks one, or defines none at all, is not a check of that
    statement, and neither is one that states it as an axiom (Axiom, Parameter, or a Definition closed by Admitted)
    or defines it from an assumption outside the allowlist."""
    compilation = counter(compilation)
    d = tempfile.mkdtemp(prefix="defined-", dir=work)
    stmt_mod = h.data["rocq"] + ".Statements"
    with open(os.path.join(d, "Defined.v"), "w", encoding="utf-8") as f:
        f.write(DEFINED.format(stmt_mod=stmt_mod, terms=", ".join("@%s.%s" % (stmt_mod, s) for s in listed)))
    log = os.path.join(d, "defined.log")
    if compilation.run(["rocq", "compile", "-w", "-all"] + _loadpath(build, h)
                       + ["-Q", d, "OftDefined", os.path.join(d, "Defined.v")], d, log) != 0:
        raise CheckError("%s/Statements.v does not define every statement harness.yaml lists (%s; see %s)%s"
                         % (h.dir, ", ".join(listed), log, log_errors(log)))
    axioms = read_assumptions(d, log)
    stated = sorted(s for s in listed if "%s.%s" % (stmt_mod, s) in axioms)
    if stated:
        raise CheckError("%s/Statements.v states %s as an axiom (Axiom, Parameter or Admitted), not a definition (see "
                         "%s)" % (h.dir, ", ".join(stated), log))
    outside = sorted(axioms - allowed)
    if outside:
        raise CheckError("%s/Statements.v: the statements assume axioms outside the allowlist: %s (see %s)"
                         % (h.dir, ", ".join(outside), log))


# Where _jobs reads the CPU quota; a test points it at a fake tree.
CGROUP_ROOT = "/sys/fs/cgroup"


def _cpu_quota(root):
    """The CPUs the quota of this process's cgroup allows, rounded up: cgroup v2's cpu.max (`<quota> <period>`,
    quota `max` when there is none), else cgroup v1's cpu.cfs_quota_us and cpu.cfs_period_us (quota -1 when there is
    none).  None with no quota, or when neither is readable and well formed."""
    def ceil_div(quota, period):
        return -(-quota // period) if quota > 0 and period > 0 else None
    try:
        with open(os.path.join(root, "cpu.max")) as f:
            quota, period = f.read().split()
        return None if quota == "max" else ceil_div(int(quota), int(period))
    except (OSError, ValueError):
        pass
    for v1 in (os.path.join(root, "cpu"), os.path.join(root, "cpu,cpuacct")):
        try:
            with open(os.path.join(v1, "cpu.cfs_quota_us")) as f:
                quota = int(f.read())
            with open(os.path.join(v1, "cpu.cfs_period_us")) as f:
                period = int(f.read())
        except (OSError, ValueError):
            continue
        return None if quota == -1 else ceil_div(quota, period)
    return None


def _jobs():
    """How many jobs dune runs at once: OFT_JOBS when it is a positive integer, else the cgroup's CPU quota, at most
    the CPUs this process may run on.  In a pod with a CPU limit and no cpuset (the build service), the affinity is
    the node's 32-64 CPUs, and -j that many compiles 20 files at once and runs the pod out of memory."""
    cpus = len(os.sched_getaffinity(0))
    env = os.environ.get("OFT_JOBS", "").strip()
    if env.isdigit() and int(env) > 0:
        return min(int(env), cpus)
    quota = _cpu_quota(CGROUP_ROOT)
    return cpus if quota is None else max(1, min(quota, cpus))


def compile_lib(root, h, work, libs, out, compilation=None):
    """The -Q mapping of h's proof library, lib/ in its proofs folder (Tree.proof_libs), as
    <namespace>.Proofs.<p>.<h>.lib (every .v at any depth), or [] when h has none.  Built once per check run by
    dune, from the rocq.theory stanza of oft generate's lib/dune, against the statements in root's _build; `libs` holds
    the mapping, or the error, per harness.  dune takes a file from its cache (DUNE_CACHE) only when the file's sources,
    its dependencies and the Rocq binary all hash the same as when the cached copy was compiled.  The statement side the
    library reads is built first, with a cache of its own (own_dune_cache) and into the statements' log
    (_build_statement_side), so the library build never takes a file of it from the caller's cache (OSSV-299 R7): after
    check_statements nothing runs, and in a `--parts proofs` run that first build compiles it.  The library's log holds
    the library's build alone.  A library that failed once fails again with _again's one line, so that its log is
    quoted once."""
    compilation = counter(compilation)
    if h.dir in libs:
        if isinstance(libs[h.dir], CheckError):
            raise CheckError(_again(libs[h.dir]))
        return libs[h.dir]
    rel = h.tree.proof_libs.get("%s/%s" % (h.project.name, h.name))
    if rel is None:
        libs[h.dir] = []
        return []
    try:
        targets = _lib_targets(root, h, rel, out)
        slog = _unit_log(work, h, "statements")
        rc = _build_statement_side(root, h, work, slog, compilation)
        if rc != 0:
            raise CheckError("%s: the statement side it reads does not compile (see %s)%s"
                             % (rel, slog, log_errors(slog)))
        log = _unit_log(work, h, "lib")
        start = _log_end(log)
        rc = compilation.dune(root, targets, log)
        if rc != 0:
            raise _failed_run(rel, log, rc, work)
    except CheckError as e:
        libs[h.dir] = e
        raise
    libs[h.dir] = ["-Q", os.path.join(root, "_build", "default", rel),
                   names.rocq_proof(h.tree.namespace, h.project.name, h.name, "lib")]
    named = {t for r in _log_rules(log, start) for t in r}
    print("%s: %d of %d library targets compiled (log %s)" % (rel, len(set(targets) & named), len(targets), log),
          file=out)
    return libs[h.dir]


# dune reads build rules under the names of layout.DUNE_FILES.  dune builds a proof library from the rules of lib/ and
# of every directory above it ((subdir ...) adds stanzas below; (env ...) sets flags or the compiler for everything
# below).  So oft check writes lib/dune itself and refuses any other build file in lib/ or above it (the root's
# dune-project, which oft generate writes, aside): every .vo of a library is `rocq compile` of its own .v files.  In
# the per-project layout two directories above the library hold a dune file of oft generate's, each refused unless it
# is exactly that file.
def _lib_targets(root, h, rel, out):
    """The .vo of every .v file in h's proof library, rel (relative to root).  Refuses a symbolic link in the library
    (dune follows one, a walk does not) and any dune build file in it or in a directory above it, but the two the
    per-project layout puts above it, which must be exactly what oft generate renders: the barrier dune of the proofs
    folder, which shuts that folder out of the statement theory, and the statement folder's dune, which is that theory.
    Writes lib/dune as this oft generate renders it, so the rule dune runs is this tool's, whichever tools rendered the
    tree."""
    from . import generate
    _guard_above(root, h, rel, "a proof library")
    src = os.path.join(root, rel)
    targets = []
    for dp, dn, fn in os.walk(src):
        for f in dn + fn:
            if os.path.islink(os.path.join(dp, f)):
                raise CheckError("%s: a proof library holds no symbolic link" % os.path.relpath(os.path.join(dp, f), root))
        for f in fn:
            path = os.path.relpath(os.path.join(dp, f), root)
            if f in layout.DUNE_FILES and path != os.path.join(rel, "dune"):
                raise CheckError("%s: a proof library holds no build file but lib/dune" % path)
            if f.endswith(".v"):
                targets.append(path[:-2] + ".vo")
    if not targets:
        raise CheckError("%s: holds no .v file" % rel)
    dune = os.path.join(src, "dune")
    want = generate.proof_lib_dune(h.tree.namespace, h.tree.opam_stem, h.project.name, h.name)
    if not os.path.isfile(dune) or facts.read(dune) != want:
        with open(dune, "w", encoding="utf-8") as f:
            f.write(want)
        print("%s: written as this oft generate renders it" % os.path.join(rel, "dune"), file=out)
    return sorted(targets)


def _guard_above(root, h, rel, what):
    """Refuse a symbolic link on the way to rel (relative to root), and any dune build file in a directory above it
    (the root's dune-workspace too: oft generate writes none), but the two the per-project layout puts above a proofs
    folder's contents, which must be exactly what oft generate renders: the barrier dune of the proofs folder, which
    shuts that folder out of the statement theory, and the statement folder's dune, which is that theory.  `what`
    names rel in the refusal."""
    from . import generate
    p, hn = h.project.name, h.name
    # neither directory is above an old-layout proofs folder, proofs/<p>/<h>/
    rendered = {os.path.join(layout.proofs_dir(p, hn, layout.NEW), "dune"): generate.barrier_dune(),
                os.path.join(layout.statement_dir(p, hn), "dune"): generate.harness_dune(h)}
    d = rel
    while True:
        for f in layout.DUNE_FILES if d != rel else ():
            path = os.path.join(d, f)
            if path == "dune-project" or not os.path.lexists(os.path.join(root, path)):
                continue
            if path not in rendered:
                raise CheckError("%s: no directory above %s holds a build file" % (path, what))
            if not _holds_exactly(os.path.join(root, path), rendered[path]):
                raise CheckError("%s: differs from its rendering (run ./oft generate)" % path)
        if d and os.path.islink(os.path.join(root, d)):
            raise CheckError("%s: %s holds no symbolic link" % (d, what))
        if not d:
            break
        d = os.path.dirname(d)


# The flags dune 3.23.0 gives `rocq compile` for a rocq.theory whose dune file sets none, as oft generate's proof
# dune files are (templates/proof-dune.tmpl), with the number of arguments each takes: dune's default warnings,
# native output, load paths and -boot, which dune passes with its own -R of Corelib (_build/trace.csexp of a dune
# 3.23.0 build, read 2026-11-02).  A flag outside this set, or one that changes the logic, refuses the unit.
PROOF_FLAGS = {"-q": 0, "-boot": 0, "-w": 1, "-native-output-dir": 1, "-native-compiler": 1, "-nI": 1, "-R": 2,
               "-Q": 2, "-o": 1}
UNSOUND_FLAGS = ("-type-in-type", "-impredicative-set", "-allow-rewrite-rules", "-indices-matter", "-noinit")


def _csexp(b, i=0):
    """(value, next index) of the canonical S-expression at b[i:]: a list or a str atom."""
    if b[i:i + 1] == b"(":
        i, out = i + 1, []
        while b[i:i + 1] != b")":
            if i >= len(b):
                raise ValueError("unterminated list")
            x, i = _csexp(b, i)
            out.append(x)
        return out, i + 1
    j = b.index(b":", i)
    n = int(b[i:j])
    if j + 1 + n > len(b):
        raise ValueError("atom past the end")
    return b[j + 1:j + 1 + n].decode("utf-8", "replace"), j + 1 + n


def traced_compiles(path):
    """[argv after `compile`] of every `rocq compile` dune started, from its _build/trace.csexp (dune 3.23.0 writes
    each run's process starts there, and no _build/log).  Only process_args is read: the trace also holds dune's
    environment, which is never printed."""
    with open(path, "rb") as f:
        b = f.read()
    i, out = 0, []
    while i < len(b):
        e, i = _csexp(b, i)
        if isinstance(e, list) and e[:2] == ["process", "start"]:
            f = {k[0]: k[1:] for k in e[3:] if isinstance(k, list) and k and isinstance(k[0], str)}
            args = f.get("process_args", [[]])[0]
            prog = f.get("prog", [""])[0]
            if isinstance(args, list) and args[:1] == ["compile"] and os.path.basename(str(prog)) in ("rocq", "coqc"):
                out.append(args[1:])
    return out


def bad_proof_flags(argv):
    """The flags of one `rocq compile` argv (after `compile`) that are not dune's defaults for a proof directory."""
    bad, i = [], 0
    while i < len(argv):
        a = argv[i]
        if a in UNSOUND_FLAGS or (a.startswith("-") and a not in PROOF_FLAGS):
            bad.append(a)
            i += 1
        elif a in PROOF_FLAGS:
            i += 1 + PROOF_FLAGS[a]
        else:
            i += 1      # the .v file
    return bad


def _proof_dir_targets(root, h, rel, sid):
    """The _build/default .vo of each .v of the proof directory rel of statement sid.  Refuses what _lib_targets
    refuses of a library: a symbolic link in it or on the way to it, a build file above it (_guard_above), any build
    file in it but its own dune, which must be exactly oft generate's; and a .v below its top, for which the generated
    dune file (no include_subdirs) gives dune no rule."""
    from . import generate
    _guard_above(root, h, rel, "a proof directory")
    src = os.path.join(root, rel)
    if os.path.islink(src) or not os.path.isdir(src):
        raise CheckError("%s: not a directory" % rel)
    if not _holds_exactly(os.path.join(src, "dune"), generate.proof_dune(h.tree, sid)):
        raise CheckError("%s: differs from its rendering (run ./oft generate)" % os.path.join(rel, "dune"))
    targets = []
    for dp, dn, fn in os.walk(src):
        dn.sort()
        for f in sorted(dn + fn):
            if os.path.islink(os.path.join(dp, f)):
                raise CheckError("%s: a proof directory holds no symbolic link"
                                 % os.path.relpath(os.path.join(dp, f), root))
        for f in sorted(fn):
            path = os.path.relpath(os.path.join(dp, f), root)
            if f in layout.DUNE_FILES and path != os.path.join(rel, "dune"):
                raise CheckError("%s: a proof directory holds no build file but its own dune" % path)
            if f.endswith(".v"):
                if dp != src:
                    raise CheckError("%s: a proof directory's .v files are at its top: its dune file gives dune no "
                                     "rule for one below" % path)
                targets.append(os.path.join("_build", "default", path[:-2] + ".vo"))
    if not targets:
        raise CheckError("%s: holds no .v file" % rel)
    return targets


def _failure_texts(log, start, dirs):
    """{d: (text, whether it ran out of stack)} for each proof directory d of dirs, from the `--display short` log at
    log, from byte start on: the blocks of the log that name d (a rule line or a `File` line and what follows it up to
    the next such line; never a `$ ` line's), each line quoted as log_errors quotes one (QUOTE), and whether one of
    those blocks holds one of STACK_WORDS.  The log is read a line at a time within ERROR_BYTES (_log_lines), each
    block kept as far as it fits whole in ERROR_BYTES and ERROR_LINES (_Block), and each directory's text held to them
    (_Quote), with one note for what it leaves out: so a log of any size takes little memory."""
    quotes = {d: _Quote() for d in dirs}
    left = dict.fromkeys(dirs, 0)
    stack = dict.fromkeys(dirs, False)
    block, mine, words, ours = None, set(), False, False

    def close():
        if block is None or not ours:
            return
        lines = list(block.lines)
        while lines and not lines[-1][0].strip():
            lines.pop()
        for d in mine:
            stack[d] = stack[d] or words
            q, shown = quotes[d], 0
            for line, cut in lines:
                n = q.count
                whole = all(q.add(p) for p in _quoted(line, cut))
                shown += q.count > n
                if not whole:
                    break
            left[d] += block.all - len(block.lines) + len(lines) - shown

    with open(log, "rb") as f:
        f.seek(start)
        for line, cut in _log_lines(f):
            if line.startswith("File ") or _RULE.fullmatch(line) or line.startswith("$ "):
                close()
                block, mine, words, ours = _Block(), set(), False, not line.startswith("$ ")
            if block is None:
                continue
            block.add(line, cut)
            mine.update(d for d in dirs if d + "/" in line)
            words = words or any(w in line for w in STACK_WORDS)
        close()
    return {d: ("\n".join(quotes[d].lines) + (
        "\n%s[%d more line(s) of the log about %s left out]" % (QUOTE, left[d], d) if left[d] else ""), stack[d])
        for d in dirs}


def _proofs_key(h):
    return ("proof-dirs", h.dir)


def build_proof_dirs(root, h, work, out, dirs, libs=None, *, deadline_s=None, compilation=None):
    """Build the proof directories `dirs` of h (relative to root) once, with dune, after h's library (compile_lib),
    with a dune cache of its own (own_dune_cache), so each proof is compiled here and never taken from a cache; record
    and return, per directory, None when every .vo it should have exists afterwards, else why not (its guard refusal,
    or dune's text for it, quoted (_failure_texts)).  A library that does not compile fails every directory: the first
    with its quoted log, each after it with _again's one line.  Each .v is an explicit target (@@<dir>/default is
    non-recursive and builds no proof directory).  dune runs every `rocq compile` with the flags of oft generate's
    dune file; one with another flag, in the trace dune writes, refuses every directory.  deadline_s: an absolute
    time.monotonic() bound for every directory, the job's own end (DirTimeLimit).  A directory past it fails alone,
    and dune builds the others.  The results go into libs, where check_proof reads them.  compilation counts the
    library's and the directories' dune targets, and the directories the guard (_proof_dir_targets) refused
    (Compilation)."""
    compilation = counter(compilation)
    libs = {} if libs is None else libs
    got = libs.setdefault(_proofs_key(h), {})
    sid = {st.proof.path: st.id for st in h.statements.values() if st.proof}
    targets = {}
    try:
        compile_lib(root, h, work, libs, out, compilation=compilation)
    except (CheckError, subprocess.TimeoutExpired, OSError) as e:
        for i, d in enumerate(dirs):
            got[d] = str(e) if i == 0 else _again(e)
        return {d: got[d] for d in dirs}
    for d in dirs:
        if d not in sid:
            got[d] = "%s: no statement of %s has this proof directory" % (d, h.dir)
            continue
        try:
            targets[d] = _proof_dir_targets(root, h, d, sid[d])
        except CheckError as e:
            got[d] = str(e)
            compilation.refused += 1
    log = _unit_log(work, h, "proofs")
    start = _log_end(log)
    if targets:
        limit = DirTimeLimit(targets, deadline_s) if deadline_s is not None else None
        try:
            with own_dune_cache(work) as env:
                rc = compilation.dune(root, [t for d in sorted(targets) for t in targets[d]], log, env=env,
                                      watch=limit)
            rules = _log_rules(log, start)
            refusal = _trace_refusal(root, targets, rules)
        except (CheckError, subprocess.TimeoutExpired, OSError) as e:
            rc, rules, refusal = None, [], str(e)
        stopped = limit.stopped if limit else set()
        missing = {d: [t for t in ts if not os.path.isfile(os.path.join(root, t))] for d, ts in targets.items()}
        failed = {} if refusal else _failure_texts(log, start, sorted(d for d in targets if missing[d]))
        for d in targets:
            text, exhausted = failed.get(d, ("", False))
            if refusal:
                got[d] = refusal
            elif d in stopped and missing[d]:
                got[d] = "%s: stopped by the job's deadline (see %s)" % (d, log)
            elif missing[d] and exhausted:
                # a rocq of this directory ran out of stack (dune: `(got signal SEGV)`, or Rocq's own Stack_overflow):
                # a class apart from a proof that does not compile (_failed_run)
                got[d] = "%s: %s (see %s)\n%s" % (d, stack_exhausted_words(work), log, text)
            elif missing[d]:
                got[d] = "%s: dune built no %s (dune exited %s; see %s)%s" % (
                    d, ", ".join(t[len("_build/default/"):] for t in missing[d]), rc, log,
                    ("\n" + text) if text else "")
            else:
                got[d] = None
        print("%s: %d proof director%s built by dune, %d rules run%s (log %s)" % (
            h.dir, len(targets), "y" if len(targets) == 1 else "ies", len(rules),
            ", %d stopped by the job's deadline" % len(stopped) if stopped else "", log), file=out)
    return {d: got[d] for d in dirs}


def _trace_refusal(root, targets, rules):
    """Why the proof directories' build is refused, from dune's _build/trace.csexp, or None: a `rocq compile` of a
    proof directory with a flag outside PROOF_FLAGS, or a proof directory the build's rules (_log_rules) name as
    compiled that the trace holds no `rocq compile` of (nothing to judge its flags by)."""
    dirs = sorted(targets)
    trace = os.path.join(root, "_build", "trace.csexp")
    seen = set()
    if os.path.isfile(trace):
        try:
            compiles = traced_compiles(trace)
        except (ValueError, IndexError) as e:
            return "dune's _build/trace.csexp does not parse (%s): the proof directories' flags cannot be read" % e
        for argv in compiles:
            files = [a for a in argv if a.endswith(".v")]
            d = next((d for d in dirs if any(f.startswith(d + "/") for f in files)), None)
            if d is None:
                continue
            seen.add(d)
            bad = bad_proof_flags(argv)
            if bad:
                return "%s: dune compiled it with %s, which oft generate's dune file never gives" % (d, " ".join(bad))
    for r in rules:
        for d in dirs:
            if any(t.startswith(d + "/") and t.endswith(".vo") for t in r) and d not in seen:
                return "%s: dune compiled it, and _build/trace.csexp records no rocq compile of it" % d
    return None



def _holds_exactly(path, text):
    """Whether path is a regular file, not a symbolic link, whose bytes are text's."""
    if os.path.islink(path) or not os.path.isfile(path):
        return False
    with open(path, "rb") as f:
        return f.read() == text.encode("utf-8")


def check_proof(root, st, pd, allowed, work, out, libs, rocqchk=False, compilation=None):
    """Audit one proof directory as build_proof_dirs left it, built by dune in root's _build: compile only a wrapper of
    this tool's own, with its own flags and load path, against the statements, the harness's proof library and the
    built .vo, and audit the wrapper's assumptions.  Compiles no file of the proof.  A directory build_proof_dirs could
    not build fails with what it recorded, before the library is asked for, so that a library that does not compile is
    quoted at the first proof and named in one line (_again) at each after it.  With rocqchk, return what
    rocqchk_proofs needs."""
    compilation = counter(compilation)
    h = st.harness
    p, hn, s = st.id.split("/")
    proof_mod = names.rocq_proof(h.tree.namespace, p, hn, s)
    main = "Refutation" if pd.refutes else "Proof"
    built = libs.get(_proofs_key(h), {})
    if pd.path not in built:
        raise CheckError("%s: not built (build_proof_dirs builds a unit's proof directories before their audits)"
                         % pd.path)
    if built[pd.path] is not None:
        raise CheckError(built[pd.path])
    libq = compile_lib(root, h, work, libs, out, compilation=compilation)
    base = os.path.join(root, "_build", "default")
    pbuild = os.path.join(base, pd.path)
    for dp, _dn, fn in os.walk(os.path.join(root, pd.path)):
        for f in fn:
            if f.endswith(".v"):
                vo = os.path.relpath(os.path.join(dp, f), root)[:-2] + ".vo"
                if not os.path.isfile(os.path.join(base, vo)):
                    raise CheckError("%s: dune built no %s" % (pd.path, vo))
    d = tempfile.mkdtemp(prefix="proof-", dir=work)
    q = _loadpath(base, h) + libq + ["-Q", pbuild, proof_mod]
    args = wrapper_args(st, pd)
    theorem = "%s_%s" % (s, "refuted" if pd.refutes else "holds")
    wdir = os.path.join(d, "wrap")
    os.makedirs(wdir)
    with open(os.path.join(wdir, "Wrapper.v"), "w", encoding="utf-8") as f:
        f.write(WRAPPER.format(stmt_mod=h.data["rocq"] + ".Statements", proof_mod=proof_mod + "." + main,
                               neg="~ " if pd.refutes else "", stmt=s, args=args, theorem=theorem))
    wrap = "Wrap." + names.ident(s)
    wq = q + ["-Q", wdir, wrap]
    wlog = os.path.join(d, "wrapper.log")
    if compilation.run(["rocq", "compile", "-w", "-all"] + wq + [os.path.join(wdir, "Wrapper.v")], d, wlog) != 0:
        raise CheckError("%s: the wrapper does not type-check: the proof is not of this statement (see %s)%s"
                         % (pd.path, wlog, log_errors(wlog)))
    axioms = read_assumptions(d, wlog)
    outside = sorted(axioms - allowed)
    if outside:
        raise CheckError("%s: axioms outside the allowlist: %s" % (pd.path, ", ".join(outside)))
    print("%s: %s %s; assumptions: %d axioms, all allowed" % (pd.path, "refutes" if pd.refutes else "proves",
                                                               st.id + args, len(axioms)), file=out)
    if not rocqchk:
        return None
    # rocqchk runs once per harness, over the wrappers of all its proofs (rocqchk_proofs): their closures share the
    # harness's library, which one run checks once.
    return {"base": _loadpath(base, h) + libq, "own": ["-Q", pbuild, proof_mod, "-Q", wdir, wrap],
            "module": wrap + ".Wrapper"}


def wrapper_args(st, pd):
    """The arguments the wrapper applies statement st to for proof pd: the b a proof of a statement that takes a bound
    names (proof.yaml bound, n/d or n; shapes.takes_bound), as `(n # d)`; none for any other proof, or for a
    refutation."""
    if st.takes_bound() and not pd.refutes:
        n_, _, d_ = pd.data["bound"].partition("/")
        return " (%s # %s)" % (n_, d_ or "1")
    return ""


def rocqchk_proofs(root, h, checked, allowed, work, out):
    """rocqchk over the wrappers of the proofs `checked` (what check_proof returned) of harness h, in one run, and
    every assumption of their closures against the allowlist."""
    q = list(checked[0]["base"])
    for c in checked:
        q += c["own"]
    log = os.path.join(work, names.ident(h.project.name) + "." + names.ident(h.name) + ".proofs.rocqchk.log")
    n = _rocqchk(root, q, [c["module"] for c in checked], allowed, log)
    folder = layout.proofs_dir(h.project.name, h.name, h.tree.unit_layout("%s/%s" % (h.project.name, h.name)))
    print("%s: rocqchk over the wrappers of %d proof(s): %d axioms, all allowed" % (folder, len(checked), n), file=out)


class InstanceError(CheckError):
    """A statement's instance refused, at `step`: missing (no lemma, in a project of shapes.REQUIRED), input (the
    instance file is not the one its record names), shape (the statement's fields choose no shape), compile (the lemma
    or a library file of an instance control does not compile), wrapper (the lemma is not of this input and this
    type) or axioms (it assumes what the allowlist does not hold)."""

    def __init__(self, step, msg):
        super().__init__(msg)
        self.step = step


def check_instance(root, st, allowed, work, out, libs, compilation=None):
    """Check the instance of statement st (harness.yaml statements.<s>.instance) with its lemma <s>_instance, in
    Instances/<s>.v of the fuzz target's proof library, which compile_lib builds, against the statements in root's
    _build (audit_instance, with shapes.REQUIRED)."""
    h = st.harness
    p, hn, s = st.id.split("/")
    lemma = st.instance_lemma()
    base = os.path.join(root, "_build", "default")
    audit_instance(st, h.dir, os.path.join(root, layout.instance_path(p, hn, h.tree.unit_layout("%s/%s" % (p, hn)),
                                                                      st.data["instance"]["file"])),
                   os.path.join(root, lemma), lemma,
                   lambda: _loadpath(base, h) + compile_lib(root, h, work, libs, out, compilation=compilation),
                   names.rocq_proof(h.tree.namespace, p, hn, "lib") + ".Instances." + s,
                   names.rocq_core(h.tree.namespace), shapes.REQUIRED, allowed, work, out, compilation=compilation)


def instance_wrapper(st, data, lemma_mod, core):
    """The text of the wrapper (INSTANCE_WRAPPER) of statement st's instance, whose file holds data, for its lemma
    <s>_instance of module lemma_mod; core is the core's theory.  Raises shapes.ShapeError for fields that choose no
    shape."""
    h = st.harness
    return INSTANCE_WRAPPER.format(
        core=core, rocq=h.data["rocq"], lemma_mod=lemma_mod, lemma=st.name + "_instance", input=shapes.INSTANCE_INPUT,
        input_type="FinProcInput" if shapes.instance_finite(st.data) else "ProcInput",
        input_term=shapes.instance_input(h.data, st.data, data), type=shapes.instance_type(st.data, h.project.data))


def audit_instance(st, label, data_path, lemma_path, lemma_rel, loadpath, lemma_mod, core, required, allowed, work,
                   out, compilation=None):
    """Check the instance of statement st, whose file is data_path, with its lemma <s>_instance of module lemma_mod,
    in the file lemma_path (named lemma_rel in messages); loadpath() gives the -Q mappings of the core, of the
    harness's statements and images, and of the built library that holds the lemma; core is the core's theory.

    With no lemma file, the instance fails when st's project is in `required`, and otherwise passes with a line that
    says it has no lemma and is not required.  Else the file must have the record's size and SHA-256, the wrapper
    (INSTANCE_WRAPPER) must type-check, and every axiom it assumes must be in `allowed`; then it prints
    `<label>: instance of <id> at <file> (<path>): holds; assumptions: N axioms, all allowed`.  Raises InstanceError."""
    compilation = counter(compilation)
    h, inst, s = st.harness, st.data["instance"], st.name
    head = "%s: instance of %s at %s (%s)" % (label, st.id, inst["file"], inst["path"])
    if not os.path.isfile(lemma_path):
        if h.project.name in required:
            raise InstanceError("missing", "no lemma %s_instance: %s is missing, and project %s requires one for every "
                                           "statement" % (s, lemma_rel, h.project.name))
        print("%s: has no lemma (%s), and project %s does not require one" % (head, lemma_rel, h.project.name),
              file=out)
        return
    try:
        f = facts.read_instance(data_path)
    except (OSError, facts.BoundedFileError) as e:
        raise InstanceError("input", "the instance file %s cannot be read: %s" % (inst["file"], e))
    if (f.bytes, f.sha256) != (inst["bytes"], inst["sha256"]):
        raise InstanceError("input", "the instance file %s has %d bytes and sha256 %s, not the record's %d bytes and "
                                     "sha256 %s" % (inst["file"], f.bytes, f.sha256, inst["bytes"], inst["sha256"]))
    try:
        text = instance_wrapper(st, f.data, lemma_mod, core)
    except shapes.ShapeError as e:
        raise InstanceError("shape", str(e))
    q = loadpath()
    d = tempfile.mkdtemp(prefix="instance-", dir=work)
    wdir = os.path.join(d, "wrap")
    os.makedirs(wdir)
    with open(os.path.join(wdir, "Wrapper.v"), "w", encoding="utf-8") as f:
        f.write(text)
    log = os.path.join(d, "wrapper.log")
    if compilation.run(["rocq", "compile", "-w", "-all"] + q + ["-Q", wdir, "Wrap." + names.ident(s),
                                                               os.path.join(wdir, "Wrapper.v")], d, log) != 0:
        raise InstanceError("wrapper", "the wrapper does not type-check: %s_instance is not of this input and this "
                                       "type (see %s)%s" % (s, log, log_errors(log)))
    try:
        axioms = read_assumptions(d, log)
    except CheckError as e:
        raise InstanceError("axioms", str(e))
    outside = sorted(axioms - allowed)
    if outside:
        raise InstanceError("axioms", "axioms outside the allowlist: %s" % ", ".join(outside))
    print("%s: holds; assumptions: %d axioms, all allowed" % (head, len(axioms)), file=out)


def instance_control(root, d, allowed, out):
    """`python3 -m oft.check --instance-control DIR`: one of tests/check.sh's instance controls (tests/README.md),
    checked by audit_instance as check_instance checks a statement's instance.  DIR holds instance.yaml (`statement`,
    an id of tests/toy/<harness>/Statements.v; `fields`, its fields as harness.yaml writes them; `distribution`, argv0
    and input_file; `instance`, the record; `project`, and `required`, the projects that stand in for
    shapes.REQUIRED), the instance file and the lemma, Instances/<statement>.v, or none, and any other .v file of the
    proof library the lemma loads (an Images.v, at the top of DIR, is the module Control.<dir>.Images).  Every .v file
    of DIR is compiled, in the order `rocq dep -sort` gives, against the core and the tests' library as root's _build
    holds them (`dune build` of theories and tests).  0 for a pass, the missing lemma that is not required among them;
    1, after `FAIL <dir>: refused at <step>: <why>`, for a refusal (InstanceError's steps)."""
    d = os.path.abspath(d)
    label = os.path.relpath(d, root)
    try:
        allow = allowed_axioms(root, allowed)
        y = yamlio.load_file(os.path.join(d, "instance.yaml"))
        p, hn, s = y["statement"].split("/")
        proj = facts.Project(facts.Tree(root), y["project"], {})
        h = facts.Harness(proj, hn, {"rocq": "OSSVerify.Tests.%s.%s" % (p, hn), "distribution": y["distribution"]})
        st = facts.Statement(h, s, dict(y["fields"], instance=y["instance"]))
    except (CheckError, OSError, yamlio.YamlError, KeyError, TypeError, ValueError) as e:
        print("FAIL %s: the control does not read: %s" % (label, e), file=out)
        return 1
    base = os.path.join(root, "_build", "default")
    base_q = ["-Q", os.path.join(base, "theories"), "OSSVerify.Core",
              "-Q", os.path.join(base, "tests"), "OSSVerify.Tests"]
    work = tempfile.mkdtemp(prefix="oft-check-instance-")
    lib_mod = "Control." + names.ident(os.path.basename(d))
    lemma = os.path.join("Instances", s + ".v")

    def loadpath():
        lib = os.path.join(work, "lib")
        files = _sources(d)
        for rel, text in files.items():
            os.makedirs(os.path.dirname(os.path.join(lib, rel)), exist_ok=True)
            with open(os.path.join(lib, rel), "wb") as f:
                f.write(text)
        q = base_q + ["-Q", lib, lib_mod]
        deps = subprocess.run(["rocq", "dep", "-sort"] + q + sorted(os.path.join(lib, rel) for rel in files),
                              capture_output=True, text=True)
        if deps.returncode != 0:
            raise InstanceError("compile", "rocq dep failed: %s" % deps.stderr.strip())
        log = os.path.join(work, "lemma.log")
        for f in deps.stdout.split():
            if os.path.abspath(f).startswith(lib + os.sep) and _run(["rocq", "compile"] + q + [f], work, log) != 0:
                raise InstanceError("compile", "%s does not compile (see %s)%s"
                                    % (os.path.relpath(f, lib), log, log_errors(log)))
        return q

    try:
        audit_instance(st, label, os.path.join(d, y["instance"]["file"]), os.path.join(d, lemma),
                       os.path.join(label, lemma), loadpath, lib_mod + ".Instances." + s, "OSSVerify.Core",
                       y.get("required") or [], allow, work, out)
    except InstanceError as e:
        print("FAIL %s: refused at %s: %s" % (label, e.step, e), file=out)
        return 1
    except (CheckError, subprocess.TimeoutExpired, OSError) as e:
        print("FAIL %s: %s" % (label, e), file=out)
        return 1
    return 0


def _sources(d):
    """{path relative to d: bytes} of every .v file under d."""
    out = {}
    for dp, _dn, fn in os.walk(d):
        for f in fn:
            if f.endswith(".v"):
                with open(os.path.join(dp, f), "rb") as g:
                    out[os.path.relpath(os.path.join(dp, f), d)] = g.read()
    return out


def given_lib(root, h, lib):
    """The -Q mapping of h's proof library as compile_lib built it in the directory lib (--lib, which proofs_apart gives
    its processes: root's _build copy of the library, which this check built), or the CheckError each proof of h then
    fails with: h must have a library (Tree.proof_libs, in either layout), lib must be that copy,
    root/_build/default/<the library's folder>, the only place compile_lib builds it, and it must hold exactly the
    library's .v files, byte for byte.  The compiled files are used as they are: this compares sources only, so it
    refuses a build of another version of the library, not one whose compiled files were changed after the build."""
    unit = "%s/%s" % (h.project.name, h.name)
    rel = h.tree.proof_libs.get(unit)
    if rel is None:
        return CheckError("--lib names %s, but %s has no proof library (%s)" % (
            lib, h.dir, layout.proof_lib_dir(h.project.name, h.name, h.tree.unit_layout(unit))))
    built = os.path.join(root, "_build", "default", rel)
    if os.path.realpath(lib) != os.path.realpath(built):
        return CheckError("--lib names %s, which is not this checkout's build of its proof library (%s)" % (lib, built))
    if not os.path.isdir(lib):
        return CheckError("--lib names %s, which is not a directory" % lib)
    if _sources(lib) != _sources(os.path.join(root, rel)):
        return CheckError("--lib names %s, whose .v files are not those of %s" % (lib, rel))
    return ["-Q", os.path.abspath(lib), names.rocq_proof(h.tree.namespace, h.project.name, h.name, "lib")]


def proof_claim(st, text):
    """The line check_proof prints when st's proof passes (`<proof dir>: proves|refutes <unit>/<statement>...;
    assumptions: N axioms, all allowed`), if text holds it as a whole line (lines end only at "\\n"), else None."""
    claim = re.compile(r"%s: %s %s( \([^)]*\))?; assumptions: \d+ axioms, all allowed" % (
        re.escape(st.proof.path), "refutes" if st.proof.refutes else "proves", re.escape(st.id)))
    return next((l for l in text.split("\n") if claim.fullmatch(l)), None)


def proofs_apart(root, unit, h, sts, allowed, jobs, work, out, libs, compilation=None, facts_from=None):
    """Check the proofs of the statements sts of harness h, each in a process of its own (`python3 -m oft.check --root
    ROOT UNIT --parts proofs --statements S --lib DIR --proofs-built`), at most jobs at once, against the statements in
    root's _build, h's library and the proof directories, built here once (compile_lib, then build_proof_dirs) and
    handed to each process with --lib and --proofs-built, so no process runs dune; a statement whose directory did not
    build fails here and gets no process, and a library that does not compile fails every statement here, quoted at the
    first and named in one line (_again) at each after it.  With facts_from, each process reads the unit's facts from
    there too (--facts-from), as this one did: root may be a view of the unit, which no process loads whole.  Each
    process takes this one's measured stack (--stack-from-parent, prepare_stack), and checks no instance
    (--no-instances): this one checks the unit's instances (instances_to_check).  A statement passes only when its
    process exits 0 and its output holds check_proof's own line for it (proof_claim); a process that a signal ends,
    that exits non-zero, that ends without that line, or that does not start fails it, and one that ran out of stack
    (stack_exhausted, on its output and its exit) fails it as `stack exhausted ...`.  compilation counts the targets of
    the builds here and each process's own compiles (its COMPILED line).  Returns (passed, failed)."""
    compilation = counter(compilation)
    root = os.path.abspath(root)
    try:
        libq = compile_lib(root, h, work, libs, out, compilation=compilation)
        built = build_proof_dirs(root, h, work, out, [st.proof.path for st in sts], libs, compilation=compilation)
    except (CheckError, subprocess.TimeoutExpired, OSError) as e:
        for i, st in enumerate(sts):
            print("FAIL %s: %s" % (st.proof.path, e if i == 0 else _again(e)), file=out)
        return 0, len(sts)
    here = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    env = dict(os.environ, PYTHONPATH=os.pathsep.join(
        [here] + [p for p in os.environ.get("PYTHONPATH", "").split(os.pathsep) if p]))
    logs = tempfile.mkdtemp(prefix="statements-", dir=work)
    pending, running, passed, failed = [], {}, 0, 0
    for st in sts:
        if built[st.proof.path] is None:
            pending.append(st)
        else:
            print("FAIL %s: %s" % (st.proof.path, built[st.proof.path]), file=out, flush=True)
            failed += 1
    if pending:
        print("%s: %d statement(s) with a proof, each in a process of its own, %d at a time"
              % (unit, len(pending), min(jobs, len(pending))), file=out, flush=True)
    while pending or running:
        while pending and len(running) < jobs:
            st = pending.pop(0)
            log = os.path.join(logs, st.name + ".log")
            cmd = [sys.executable, "-m", "oft.check", "--root", root, unit, "--parts", "proofs", "--statements",
                   st.name, "--allowed", allowed, "--stack-from-parent", "--proofs-built", "--no-instances"] + (
                       ["--lib", libq[1]] if libq else []) + (
                       ["--facts-from", os.path.abspath(facts_from)] if facts_from is not None else [])
            try:
                with open(log, "w") as f, open(log + ".stderr", "w") as e:
                    running[subprocess.Popen(cmd, stdout=f, stderr=e, env=env)] = (st, log)
            except OSError as e:
                print("FAIL %s: its process did not start: %s" % (st.proof.path, e), file=out, flush=True)
                failed += 1
        done = [p for p in running if p.poll() is not None]
        if not done:
            if running:
                time.sleep(1)
            continue
        for p in done:
            st, log = running.pop(p)
            with open(log, encoding="utf-8", errors="replace") as f:
                text = f.read()
            with open(log + ".stderr", encoding="utf-8", errors="replace") as f:
                err = f.read()
            # Children run the same checker; their summary counts the compiles they actually started, including a
            # failed compile. Merely starting a proof process is not compiling anything.
            # The child prints its counts on a line of its own, just BEFORE its `oft check: ` line (run's
            # end).  A child runs no dune -- it is given --lib and --proofs-built, and compiles only its wrapper, since
            # --no-instances leaves the unit's instances to this process -- so its dune job count is always `-`; the
            # proof directories' targets are counted here, once.
            summaries = re.findall(r"(?m)^COMPILED (\d+) file\(s\) with dune -j -$", text)
            if summaries:
                compilation.files += int(summaries[-1])
            for line in text.splitlines():
                print("  | " + line, file=out)
            for line in err.splitlines():
                print("  | " + line, file=sys.stderr)
            claim = proof_claim(st, text)
            if p.returncode == 0 and claim:
                print(claim, file=out, flush=True)
                passed += 1
                continue
            why = (stack_exhausted_words(work) if stack_exhausted(text + err, p.returncode) else
                   "its process was ended by signal %d" % -p.returncode if p.returncode < 0 else
                   "its process exited %d" % p.returncode if p.returncode else
                   "its process exited 0 without check_proof's line for %s" % st.id)
            print("FAIL %s: %s (see %s)" % (st.proof.path, why, log), file=out, flush=True)
            failed += 1
    return passed, failed


def _outcome(rc):
    """(exit status as a shell reports it, signal name or None) of a run."""
    if rc < 0:
        return 128 - rc, signal.Signals(-rc).name
    return rc, None


def _no_core_file():
    """Run in the child before qemu starts.  A program that dies of a signal
    still dies of it, but no core file is written: the kernel's core of qemu
    covers the whole guest address space qemu reserved, 17 TB for an
    AddressSanitizer build, and writing it took about 150 s per run."""
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))


def _run_input(qemu_path, elf, input_path, work, timeout):
    """(exit, signal, stdout SHA-256, stderr SHA-256) of one run of elf under qemu on a copy of input_path, named
    input.bin, in a fresh directory, with an empty environment and no core file."""
    d = tempfile.mkdtemp(prefix=os.path.basename(input_path)[:-len(".bin")] + "-", dir=work)
    shutil.copy(input_path, os.path.join(d, "input.bin"))
    # an empty environment: the binaries read none, and the model gives them none
    r = subprocess.run([qemu_path, elf, "input.bin"], cwd=d, capture_output=True, timeout=timeout, env={},
                       preexec_fn=_no_core_file)
    return _outcome(r.returncode) + (hashlib.sha256(r.stdout).hexdigest(), hashlib.sha256(r.stderr).hexdigest())


def check_counterexample(root, st, cx, qemu, timeout, work, out):
    h = st.harness
    exp = cx.data
    build = exp["observed"]["build"]
    rel = h.elf_path(build)
    elf = os.path.join(root, rel)
    if not os.path.isfile(elf):
        raise CheckError("%s: %s is not fetched" % (cx.path, rel))
    # The run is evidence only about the program this tree pins, so the bytes are compared before qemu sees them,
    # as check_finding compares the unpatched binary it runs (OSSV-462).  Only the build this
    # counterexample names, not every published build of the unit: a counterexamples run needs the builds its
    # counterexamples name, and a tree may hold those alone.
    rec = h.data["builds"][build]
    if os.path.getsize(elf) != rec["bytes"] or facts.sha256_file(elf) != rec["sha256"]:
        print("%s: does not match its SHA-256 in harness.yaml" % rel, file=out)
        raise CheckError("the binaries are missing or do not match (run ./oft fetch %s)" % h.project.name)
    qemu_path = shutil.which(qemu)
    if qemu_path is None:
        raise CheckError("%s: %s is not installed (the runner image has it)" % (cx.path, qemu))
    results = {which: _run_input(qemu_path, elf, os.path.join(root, cx.path, which + ".bin"), work, timeout)[:2]
               for which in ("input", "control")}
    want = exp["observed"]
    got_exit, got_sig = results["input"]
    if got_exit != want["exit"] or got_sig != want.get("signal"):
        raise CheckError("%s: the input no longer reproduces: exit %s signal %s, expected exit %s signal %s"
                         % (cx.path, got_exit, got_sig, want["exit"], want.get("signal")))
    if results["control"][0] != exp["control"]["exit"]:
        raise CheckError("%s: the control input exited %s, expected %s"
                         % (cx.path, results["control"][0], exp["control"]["exit"]))
    print("%s: reproduces (exit %d%s); control exits %d" % (
        cx.path, got_exit, " " + got_sig if got_sig else "", exp["control"]["exit"]), file=out)


def check_finding(root, h, f, qemu, timeout, work, out, record=False):
    """Run the finding's input.bin, then its control.bin, on each build its statements name, on the unpatched
    binaries, as check_counterexample runs a counterexample, and compare every run's exit, signal, stdout and stderr
    with finding.yaml.  A pruned finding is checked the same way, and fails first if its input still shows a statement
    false.  With record, a finding that has no runs yet prints the input and control to commit instead, and only when
    they are evidence: every run ended within the timeout (a timeout is not a fixed outcome: a slower or faster machine
    gives another) and has the shape a finding records (rules.run_ok, which `oft ledger` anchors a record by), the
    input shows each statement false (none, when it is pruned) and the control shows none false.  Runs that are not
    evidence are never printed, so a record never gets runs the rules refuse."""
    sts = [h.statements[s] for s in f.data["statements"]]
    builds = sorted({b for st in sts for b in st.data["builds"]}, key=schema.BUILDS.index)
    pins = h.tree.unpatched_paths[f.project]
    elves = {}
    for b in builds:
        rel = h.unpatched_elf_path(b)
        rec = h.tree.unpatched[f.project]["harnesses"][h.name][b]
        p = os.path.join(root, rel)
        if not os.path.isfile(p):
            raise CheckError("%s is not fetched (run ./oft fetch --findings %s)" % (rel, f.project))
        if os.path.getsize(p) != rec["bytes"] or facts.sha256_file(p) != rec["sha256"]:
            raise CheckError("%s does not match its SHA-256 in %s (run ./oft fetch --findings %s)"
                             % (rel, pins, f.project))
        elves[b] = p
    qemu_path = shutil.which(qemu)
    if qemu_path is None:
        raise CheckError("%s is not installed (the runner image has it)" % qemu)
    recording = record and "input" not in f.data
    got = {}
    for which in ("input", "control"):
        got[which] = {}
        for b in builds:
            try:
                ex, sig, so, se = _run_input(qemu_path, elves[b], os.path.join(root, f.path, which + ".bin"), work,
                                             timeout)
            except subprocess.TimeoutExpired:
                raise CheckError("%s.bin on %s ran past the %s s limit: a timeout is not a fixed outcome, so %s"
                                 % (which, b, timeout, "there are no runs to record" if recording
                                    else "the record is not reproduced")) from None
            got[which][b] = dict([("exit", ex)] + ([("signal", sig)] if sig else []) +
                                 [("stdout_sha256", so), ("stderr_sha256", se)])
    false = [st.name for st in sts if facts.shows_false(st, got["input"])]
    if f.data["state"] == "pruned" and false:
        raise CheckError("pruned, but still reproduces: on the unpatched binaries the input shows %s false"
                         % render.join_words(false))
    if recording:
        # the shape a run must have to anchor a record (rules.run_ok, which `oft ledger` uses too): the runs qemu gives
        # always have an exit from 0 to 255 and two SHA-256s, so only a signal no finding records can break it
        for which in ("input", "control"):
            for b in builds:
                if not rules.run_ok(got[which][b]):
                    raise CheckError("%s.bin on %s ended by %s, which a finding's run does not record (only %s), so "
                                     "there are no runs to record" % (which, b, got[which][b].get("signal"),
                                                                      ", ".join(rules.RUN_SIGNALS)))
        unshown = [st.name for st in sts if st.name not in false] if f.data["state"] != "pruned" else []
        if unshown:
            raise CheckError("on the unpatched binaries the input does not show %s false, so there are no runs to "
                             "record" % render.join_words(unshown))
        control = [st.name for st in sts if facts.shows_false(st, got["control"])]
        if control:
            raise CheckError("the control does not behave normally: on the unpatched binaries it shows %s false, so "
                             "there are no runs to record" % render.join_words(control))
        print("# %s: add these runs\n%s" % (os.path.join(f.path, "finding.yaml"), yamlio.dump(got)), end="", file=out)
        return
    for which in ("input", "control"):
        for b in builds:
            want = f.data[which][b]
            for k in facts.RUN_FIELDS:
                if got[which][b].get(k) != want.get(k):
                    raise CheckError("%s.bin on %s: %s is %s, recorded %s"
                                     % (which, b, k, got[which][b].get(k), want.get(k)))
    print("%s: %d runs match the record; %s" % (
        f.path, 2 * len(builds), "pruned: the input shows no statement false" if f.data["state"] == "pruned"
        else "the input shows %s false" % render.join_words(false)), file=out)


# The stack every rocq, rocqchk and dune this process starts gets.  Rocq recurses on the system stack, and large proof
# terms overflow the usual 8 MiB.  It is a soft limit to set, not a threshold to refuse at: a runtime that caps the
# stack (gVisor gives 8 MiB under an unlimited limit, about 128 MiB under 1 GiB or more) cannot be asked for more, and
# units pass there; the stack it gave is measured and printed (prepare_stack), and a check that runs out says so.
# 2 GiB, not 1 GiB: plugin-hostd/fuzz_command's lib RtSStrcspnMW.v overflows at 1 GiB and compiles at 2 GiB (build
# service probe farm/20261102t212408z-41b752: 508 s, peak 30.2 GiB), and at 4 GiB and unlimited.  It stays finite for
# glibc's thread stacks (raise_stack_limit).
STACK_NEEDED = 2 << 30
# How deep the probe goes before it says "at least": past gVisor's 8 MiB and 128 MiB, and small enough to touch at once.
STACK_PROBE_CEILING = 256 << 20
STACK_PROBE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "stackprobe.c")


def raise_stack_limit():
    """Set the stack limit every rocq, rocqchk and dune this process starts inherits, and return (soft, hard) before
    and after it.  The soft limit becomes min(hard, STACK_NEEDED), an unlimited hard limit counted as infinite, so it
    is always finite (the CI/CD lead, 2026-11-01 06:57Z and 08:36Z; the stream lead, 07:16Z): glibc sizes each new
    thread's stack from a finite soft limit, so one far above the memory fails to start dune's or zstd's threads, and
    an unlimited one is what gVisor turns into 8 MiB.  A hard limit below STACK_NEEDED gives soft = hard and runs: it
    is never a reason to refuse, and the measured stack and a "stack exhausted" failure tell what it cost.  This changes
    where the kernel runs, not what it checks."""
    soft0, hard = resource.getrlimit(resource.RLIMIT_STACK)
    soft = STACK_NEEDED if hard == resource.RLIM_INFINITY else min(hard, STACK_NEEDED)
    resource.setrlimit(resource.RLIMIT_STACK, (soft, hard))
    return soft0, hard, soft, hard


def measure_stack(work):
    """(usable bytes, text) of the stack a process this one starts gets: tools/oft/stackprobe.c, compiled into work
    with cc and run with STACK_PROBE_CEILING.  The text is "<N> MiB" (where it faulted), "at least <ceiling> MiB" (it
    did not fault), or "not measured (<why>)" with None: no cc on PATH (the checker image has one), or a probe that
    did not build or run."""
    cc = shutil.which("cc")
    if cc is None:
        return None, "not measured (no cc on PATH)"
    exe = os.path.join(work, "stackprobe")
    try:
        built = subprocess.run([cc, "-O0", "-o", exe, STACK_PROBE], capture_output=True, text=True, timeout=300)
        if built.returncode != 0:
            return None, "not measured (cc exited %d: %s)" % (built.returncode, " ".join(built.stderr.split())[-200:])
        r = subprocess.run([exe, str(STACK_PROBE_CEILING)], capture_output=True, text=True, timeout=300)
    except (OSError, subprocess.TimeoutExpired) as e:
        return None, "not measured (%s)" % e
    m = re.fullmatch(r"stackprobe: fault at (\d+)\n", r.stdout)
    if m:
        return int(m.group(1)), "%d MiB" % (int(m.group(1)) >> 20)
    if r.stdout == "stackprobe: no fault below %d\n" % STACK_PROBE_CEILING:
        return STACK_PROBE_CEILING, "at least %d MiB" % (STACK_PROBE_CEILING >> 20)
    return None, "not measured (the probe exited %d: %s)" % (r.returncode, " ".join((r.stdout + r.stderr).split())[-200:])


_MEASURED = []   # this process's own measure, once it took one (usable_stack_text)


def _limit(n):
    return "unlimited" if n == resource.RLIM_INFINITY else str(n)


def runtime():
    """The runtime the stack line names, by the gate's own test (bin/ossv-gate-job: `case "$(uname -r)" in
    *gvisor*)`): a name, so it only labels the line; what the stack is, is what measure_stack measured."""
    return "gvisor" if "gvisor" in os.uname().release else "linux"


def prepare_stack(work, out, child=False):
    """Set the stack limit (raise_stack_limit), read both limits back, take the usable stack, and print it in one line
    that never starts `oft check: ` (a check log holds exactly one such line):

        stack: <N> MiB usable (soft <S>, hard <H>; started with soft <s0>, hard <h0>; runtime <gvisor|linux>)

    in bytes, `unlimited` for no limit.  A per-statement process (child, --stack-from-parent) takes its parent's
    measure from OFT_STACK_USABLE; any other measures its own, even when it inherited one, so that no check prints
    another process's stack.  Sets OFT_STACK_USABLE to the text, for the processes this one starts, and returns it."""
    soft0, hard0, _soft, _hard = raise_stack_limit()
    soft, hard = resource.getrlimit(resource.RLIMIT_STACK)
    text = os.environ.get("OFT_STACK_USABLE") if child else None
    if not text:
        text = measure_stack(work)[1]
        _MEASURED[:] = [text]
    print("stack: %s%s (soft %s, hard %s; started with soft %s, hard %s; runtime %s)"
          % (text, "" if text.startswith("not measured") else " usable", _limit(soft), _limit(hard), _limit(soft0),
             _limit(hard0), runtime()), file=out, flush=True)
    os.environ["OFT_STACK_USABLE"] = text
    return text


def usable_stack_text(work):
    """The usable stack a failure line names: OFT_STACK_USABLE when set (prepare_stack's), else measure_stack's text,
    measured once in this process and kept."""
    if os.environ.get("OFT_STACK_USABLE"):
        return os.environ["OFT_STACK_USABLE"]
    if not _MEASURED:
        _MEASURED.append(measure_stack(work)[1])
    return _MEASURED[0]


def stack_exhausted_words(work):
    """What a failure that ran out of stack says, a class apart from a proof that does not compile: `stack exhausted at
    <N> MiB`, `stack exhausted with at least <N> MiB usable`, or `stack exhausted (the stack was not measured: <why>)`."""
    text = usable_stack_text(work)
    if text.startswith("not measured (") and text.endswith(")"):
        return "stack exhausted (the stack was not measured: %s)" % text[len("not measured ("):-1]
    if text.startswith("at least "):
        return "stack exhausted with %s usable" % text
    return "stack exhausted at %s" % text


# What a step that ran out of stack leaves in its output, for stack_exhausted and stack_exhausted_in: Rocq reports
# OCaml's Stack_overflow, a child oft's own line says so (for --proof-jobs, in the child's output, which its process
# log in statements-*/ holds), and dune reports that a process it ran died of SIGSEGV (dune itself then exits 1, as
# compile_lib's library build does).
STACK_WORDS = ("Error: Stack overflow.", ": stack exhausted ", "(got signal SEGV)")
# how much of a log stack_exhausted_in holds at once; a log of a failed build has no bound of its own (a library
# build that fails after hours of output), and reading it whole took about 2 bytes of memory per byte of log
STACK_CHUNK = 1 << 20


def stack_exhausted(text, returncode):
    """Whether a step ran out of stack: its output holds one of STACK_WORDS, or the process died of SIGSEGV (or
    exited 139, as a shell reports it)."""
    return (any(w in text for w in STACK_WORDS)
            or returncode in (-signal.SIGSEGV, 128 + signal.SIGSEGV))


def stack_exhausted_in(log, returncode):
    """stack_exhausted of the file at log, which is read in pieces of STACK_CHUNK bytes with the overlap a word needs,
    so a log of any size takes little memory.  A log that cannot be read counts as holding none of the words: the
    returncode still decides, and the message says `does not compile` rather than failing here."""
    if returncode in (-signal.SIGSEGV, 128 + signal.SIGSEGV):
        return True
    words = [w.encode() for w in STACK_WORDS]
    keep = max(len(w) for w in words) - 1
    carry = b""
    try:
        with open(log, "rb") as f:
            while True:
                piece = f.read(STACK_CHUNK)
                if not piece:
                    return False
                text = carry + piece
                if any(w in text for w in words):
                    return True
                carry = text[-keep:]
    except OSError:
        return False


def _failed_run(path, log, rc, work):
    """The CheckError of a compile of path that exited rc, its output in log: `<path>: stack exhausted ...` when
    stack_exhausted_in holds (stack_exhausted_words), else `<path>: does not compile`, and after the first line the
    log's first Error: blocks (log_errors), so that a reader of the message sees what failed without the log.  Both
    read the log in bounded pieces, so a log of any size takes little memory."""
    why = stack_exhausted_words(work) if stack_exhausted_in(log, rc) else "does not compile"
    return CheckError("%s: %s (see %s)%s" % (path, why, log, log_errors(log)))


# The parts `oft check` runs when --parts is not given: each of them that the unit has.
DEFAULT_PARTS = "statements,proofs,counterexamples"


# The parts whose check COMPILES the unit's published binaries, projects/<p>/bin/<h>/, the ones harness.yaml pins:
# statements and proofs both build the images dune makes of them (images/dune's `elf-snapshot %{elf}`), which
# Statements.v and every proof over it are about.  Each run of these parts needs every published build of the unit,
# so the whole unit's pins are checked for them (verify_builds, in run()).
#
# The other two parts are not here, because each needs only the one binary it runs and checks that one itself:
# findings runs the UNPATCHED binaries and compares each with its pin in the project's unpatched.yaml
# (check_finding), holding no projects/<p>/bin at all in its view (unitpaths.binaries), and counterexamples
# compares the build its counterexample names with that build's pin before qemu runs it (check_counterexample).
# Asking either for the whole unit's pins would refuse a run that holds the builds it needs and no others.
PARTS_THAT_COMPILE_THE_BINARIES = {"statements", "proofs"}


# The default --timeout: the seconds one counterexample or finding run of a binary under qemu gets.  It must hold the
# slowest run measured, on the slowest runner it ran on, or a correct counterexample fails on a slow runner and
# passes on a fast one.  ffmpeg/ffmpeg_AV_CODEC_ID_SIPR_fuzzer's .asan and .asan-ubsan runs measure about 535 s each
# on an ubuntu-24.04-16core runner (public run 42228615142: its seven counterexamples took 1072.7 s, of which the
# other five took 2.5 s), and the same two ran past 600 s on another runner of the same class (internal run
# 42281582157).  3 x 535 s = 1605 s, rounded up to 1620 s (27 min).
RUN_TIMEOUT_SECONDS = 1620


def run_steps(steps, out):
    """Run each (label, step, whether its success alone passes it) of steps, with a FAIL line for each that raises:
    (how many passed, how many failed)."""
    passed = failed = 0
    for label, step, passes in steps:
        try:
            step()
            passed += 1 if passes else 0
        except (CheckError, subprocess.TimeoutExpired, OSError) as e:
            print("FAIL %s: %s" % (label, e), file=out)
            failed += 1
    return passed, failed


def instances_to_check(h, want, statements, checks_instances):
    """The statements of harness h whose instances a run checks (check_instance), after the proofs it checks (in their
    processes of proofs_apart, and under rocqchk too): a run of the parts `want`, with --statements `statements` (None
    for every proved statement), and checks_instances false for a statement's process of proofs_apart.

    Each statement Statements.v carries that has an instance, proof or not, has its instance checked once per unit,
    and never in a statement's process of proofs_apart, whose parent checks them.  The proofs part checks them; so does
    the statements part of a unit with no proof, which is checked on its statements alone
    (tools/oft/ci/check-units.sh).  A run of --statements that is not such a process (a unit the farm checks one proof
    per job) checks the instances of the statements it names, and the run whose statements hold the unit's first
    proved statement by name checks those of the statements with no proof too, so the jobs of a split unit check each
    instance once."""
    unproved = not any(st.proof for st in h.statements.values())
    if not checks_instances or not ("proofs" in want or "statements" in want and unproved):
        return []
    first = min((st.name for st in h.statements.values() if st.proof), default=None)
    return [st for st in h.statements.values() if "instance" in st.data and st.rendered() and (
        statements is None or st.name in statements or not st.proof and first in statements)]



def run(root, units, parts=None, allowed="toolchain/allowed-axioms.txt",
        qemu="qemu-riscv64", timeout=RUN_TIMEOUT_SECONDS, rocqchk=False, record=False, facts_to=None, facts_from=None,
        statements=None, lib=None, proof_jobs=1, stack_from_parent=False, proofs_built=False, checks_instances=True,
        out=sys.stdout):
    """parts: the comma-separated parts to check, where naming proofs refuses a unit with no proof; None (no --parts)
    checks each part of DEFAULT_PARTS that the unit has, so an unproved unit is checked on its statements.

    facts_to    a directory; load the facts of the whole tree, check its rules, write each unit's facts there
                (write_facts) and check nothing
    facts_from  a directory facts_to wrote; check each unit with its facts from there (read_facts), without loading
                the tree or checking its rules, so root may hold that unit's files alone; each statement's process
                (proof_jobs) reads them too
    statements  the statements whose proofs are checked (default: every one with a proof); each must have one
    lib         the unit's proof library as compile_lib built it, to use instead of building it here
    proofs_built  the unit's proof directories are in root's _build as an earlier oft check built them
                (build_proof_dirs, which proofs_apart runs before it starts each statement's process): audit them
                without building them again
    proof_jobs  with more than 1, each statement's proof is checked in a process of its own (proofs_apart), as many
                at once, after one build of the library and the proof directories; rocqchk keeps one process
    stack_from_parent  this is such a process: it prints its parent's measured stack, not its own (prepare_stack)
    checks_instances  false for such a process too: its parent checks the unit's instances (instances_to_check)

    Before it checks statements or proofs it sets the stack limit, measures the stack and prints it (prepare_stack).
    Before a unit compiles anything that reads its binaries (PARTS_THAT_COMPILE_THE_BINARIES), every published build
    of that unit must be the binary harness.yaml pins, in bytes and SHA-256 (fetch.verify_builds); a unit whose
    binaries differ fails there, with nothing of it compiled."""
    named = parts is not None
    parts = parts if named else DEFAULT_PARTS
    want = set(parts.split(","))
    if record and (facts_to or facts_from):
        print("FAIL --record goes with neither --facts-to nor --facts-from: it checks a tree whose findings may have "
              "no runs yet", file=out)
        return 1
    if record and "findings" not in want:
        print("FAIL --record records findings: add findings to --parts", file=out)
        return 1
    if (statements is not None or lib is not None or proofs_built) and (len(units) != 1 or want != {"proofs"}):
        print("FAIL --statements, --lib and --proofs-built check the proofs of one unit: give one unit and --parts "
              "proofs", file=out)
        return 1
    if statements is not None and not statements:
        print("FAIL --statements names no statement", file=out)
        return 1
    if proof_jobs < 1:
        print("FAIL --proof-jobs must be at least 1", file=out)
        return 1
    # A check reads each unit's files from the working tree: its proof library builds, and its statements and
    # proofs are checked against what that build gives.  A sparse workspace that does not hold a unit's library
    # would give an empty library, and the check would answer on a tree it did not read.  So the run refuses
    # before it starts and names the commands that add each library (INFRA-1385 R12).  A view that --facts-from
    # reads is no git repository, so it is never refused: it holds one unit's files by design.
    missing = layout.unwritten_libraries(root, units)
    if missing:
        print(layout.unwritten_libraries_message("oft check", missing, root), file=out)
        return 1
    if facts_from is None:
        tree = facts.load(root, record=record)
        rules.check(tree)
        if tree.errors:
            for e in tree.errors:
                print("error: " + e, file=out)
            return 1
        if facts_to is not None:
            return write_facts(tree, units, facts_to, out)
    work = tempfile.mkdtemp(prefix="oft-check-")
    bad = examined = 0
    # harness dir -> its proof library's -Q mapping, or the error compiling it; _proofs_key(h) -> {proof directory:
    # None when dune built it, else why not} (build_proof_dirs records it, check_proof reads it)
    libs = {}
    compilation = Compilation()
    try:
        allow = allowed_axioms(root, allowed) if want & {"statements", "proofs"} else set()
    except CheckError as e:
        print("FAIL %s" % e, file=out)
        return 1
    if want & {"statements", "proofs"}:
        prepare_stack(work, out, child=stack_from_parent)
    memory = None
    for unit in units:
        if memory:
            memory.finish()
        memory = UnitMemory(unit)
        if facts_from is None:
            h = _harness(tree, unit)
            if not h:
                print("%s: no such harness" % unit, file=out)
                bad += 1
                continue
        else:
            try:
                h = read_facts(root, facts_from, unit, want)
            except (OSError, yamlio.YamlError, facts.UnitFactsError) as e:
                memory.finish()
                reason = str(e) if isinstance(e, facts.UnitFactsError) else "facts that do not read at %s: %s" % (
                    facts_file(facts_from, unit), e)
                return void(out, reason)
        steps = []    # (label, step, whether its success alone passes it)
        checked = []  # (label, what check_proof returned) of the proofs whose compile and audit passed
        if lib is not None:
            libs[h.dir] = given_lib(root, h, lib)
        proved = [st for st in h.statements.values()
                  if st.proof and "proofs" in want and (statements is None or st.name in statements)]
        unknown = sorted(set(statements or ()) - {st.name for st in proved})
        if unknown:
            # a statement the caller asked for and this run would not check is a failure, never a silent pass
            print("FAIL %s: --statements names %s, which %s no proof here" % (
                unit, ", ".join(unknown), "has" if len(unknown) == 1 else "have"), file=out)
            bad += 1
            continue
        # each statement's proof in a process of its own, after one build of the library: rocqchk keeps the
        # in-process path, since it checks every wrapper of a harness in one run (rocqchk_proofs)
        apart = proved if proof_jobs > 1 and len(proved) > 1 and not rocqchk else []
        if "statements" in want:
            steps.append(("statements",
                          lambda h=h: check_statements(root, h, allow, work, out, rocqchk,
                                                       compilation=compilation), True))
        if proved and not apart:
            if proofs_built:
                libs[_proofs_key(h)] = {st.proof.path: None for st in proved}
            else:
                # every proof directory once, by dune, after the statements and the library; then each audit
                steps.append(("proof directories", lambda h=h: build_proof_dirs(
                    root, h, work, out, [st.proof.path for st in proved], libs, compilation=compilation), False))
        for st in h.statements.values():
            if st in proved and not apart:
                steps.append((st.proof.path, lambda st=st: checked.append((st.proof.path, check_proof(
                    root, st, st.proof, allow, work, out, libs, rocqchk,
                    compilation=compilation))), not rocqchk))
            if st.counterexample and "counterexamples" in want:
                steps.append((st.counterexample.path, lambda st=st: check_counterexample(
                    root, st, st.counterexample, qemu, timeout, work, out), True))
        unproved = not any(st.proof for st in h.statements.values())
        instances = [("%s instance" % st.id, lambda st=st: check_instance(
            root, st, allow, work, out, libs, compilation=compilation), True)
            for st in instances_to_check(h, want, statements, checks_instances)]
        for f in sorted(h.tree.findings.values(), key=lambda f: f.path) if "findings" in want else []:
            if f.unit == unit:
                steps.append((f.path, lambda f=f: check_finding(root, h, f, qemu, timeout, work, out, record), True))
        if not steps and not instances and not apart:
            print("%s: nothing to check for parts %s" % (unit, parts), file=out)
            bad += 1
            continue
        if named and "proofs" in want and unproved:
            # asked for proofs by name, a unit with none would pass on its statements alone: check-units.sh asks for
            # them only of a unit the plan lists in proof_units
            print("FAIL %s: nothing to check for part proofs: the unit has no proof (check it with --parts statements)"
                  % unit, file=out)
            bad += 1
            continue
        # This unit has something to compile, so every published build of it must be the binary harness.yaml pins
        # BEFORE the first step runs.  A job's binaries come as a staged archive the farm's job submitter made at one
        # commit, so a job handed another run's archive gets an ELF this tree does not pin; images/dune runs
        # `elf-snapshot %{elf}` and reads no hash, so the images, and every vm_compute fact about them, would be of
        # another program and the run could go green.  Until 2026-11-09 only check_statements compared them, so a
        # run whose --parts did not name statements -- the farm's split per-proof jobs, `--parts proofs
        # --statements S` -- compiled against whatever ELF was in projects/<p>/bin, and a `statements,proofs` run
        # still compiled its proofs after the statements step had failed on them (OSSV-462).
        if want & PARTS_THAT_COMPILE_THE_BINARIES and fetch.verify_builds(root, h, out)[1]:
            print("FAIL %s: the binaries are missing or do not match (run ./oft fetch %s)"
                  % (unit, h.project.name), file=out)
            bad += 1
            continue
        passed, failed = run_steps(steps, out)
        examined += passed
        bad += failed
        if apart:
            passed, failed = proofs_apart(root, unit, h, apart, allowed, proof_jobs, work, out, libs, compilation,
                                          facts_from)
            examined += passed
            bad += failed
        if rocqchk and checked:
            # With rocqchk, a proof passes only when the one rocqchk over every compiled wrapper of this harness passes.
            try:
                rocqchk_proofs(root, h, [c for _, c in checked], allow, work, out)
                examined += len(checked)
            except (CheckError, subprocess.TimeoutExpired, OSError) as e:
                for label, _ in checked:
                    print("FAIL %s: %s" % (label, e), file=out)
                bad += len(checked)
        passed, failed = run_steps(instances, out)
        examined += passed
        bad += failed
    if memory:
        memory.finish()
    # Two lines, not one, and COMPILED comes FIRST.
    #
    # The `oft check: ` line stays byte for byte as it was: dev/stream's lane/tools/ship-farm.sh,
    # lane/tools/merge-pr.sh and lane/tools/combine_rewrite.py match it WHOLE, and a farm pod runs the
    # checked commit's own tools/, so a clause added inside it would have made ship-farm.sh exit 1 on a
    # PASSING check.  And it stays LAST: the check-of-record tool's build-service rule takes the last
    # non-blank line of job.log and requires it to be that line -- the pod prints nothing after a pass --
    # so a COMPILED line printed after it would have left every passing check of record `unresolved`
    # (the two non-author reviews of #2109, 2026-11-06).  The farm runner's RUN_SCRIPT and
    # docs/check-of-record.md both say the log ends with it.
    #
    # What a reader needs for the void rules goes on the line BEFORE it, which starts with neither
    # `oft check: ` nor `FAIL `, so nothing that scans for either picks it up.  It is printed only for a
    # run that wanted statements or proofs, the one case the void rule reads: `--record` prints the runs it
    # would commit as YAML up to the `oft check: ` line, and a COMPILED line in front of them made
    # yamlio.load raise (CI run 42264478851, job tests; the third non-author review of #2109).  A
    # counterexamples or findings run compiles nothing by design and has nothing to say here.
    counted = bool(want & {"statements", "proofs"})
    if counted:
        print("COMPILED %d file(s) with dune -j %s"
              % (compilation.files, compilation.jobs if compilation.jobs is not None else "-"), file=out)
    print("oft check: %d step(s) passed, %d failed; work files in %s" % (examined, bad, work), file=out)
    # A proof directory the guard refused (build_proof_dirs, Compilation.refused) is a FAILED proof, judged on its own
    # files, though nothing compiled: in a `--parts proofs --statements S` job of a unit with no proof library, the
    # farm's split, the guard is the first thing that reads a .v file, and the farm reruns a void unit for ever (the
    # sixth non-author review of #2109; main counted the `rocq dep` of each proof for the same case).  COMPILED stays
    # the compiles started, 0 here, and the refusal alone keeps the run from void.  A library the guard refuses still
    # voids it: that refusal is of the harness the run was given, before any proof directory is read.
    if counted and compilation.files == 0 and not compilation.refused:
        return void(out, "COMPILED 0 file(s): no statements or proofs were compiled")
    return 1 if bad or not examined else 0


def _harness(tree, unit):
    """The Harness of unit (<project>/<harness>) in tree, or None."""
    p, _, hn = unit.partition("/")
    return tree.projects[p].harnesses.get(hn) if p in tree.projects else None


def facts_file(d, unit):
    """Where --facts-to writes the facts of unit, and --facts-from reads them: d/<project>/<harness>.yaml."""
    p, _, hn = unit.partition("/")
    return os.path.join(d, p, hn + ".yaml")


def write_facts(tree, units, d, out):
    """--facts-to: the facts of each unit of tree (facts.unit_facts), a tree whose rules passed, into its file under d.
    1 when a unit has no harness."""
    bad = 0
    for unit in units:
        h = _harness(tree, unit)
        if not h:
            print("%s: no such harness" % unit, file=out)
            bad += 1
            continue
        path = facts_file(d, unit)
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "w", encoding="utf-8") as f:
            f.write(yamlio.dump(facts.unit_facts(tree, h)))
        print("%s: facts written to %s" % (unit, path), file=out)
    return 1 if bad else 0


def read_facts(root, d, unit, parts):
    """--facts-from: the Harness of unit from its file under d, in a tree at root, for a check of parts
    (facts.load_unit).  Raises UnitFactsError, naming the file, for facts it cannot use, malformed ones among them."""
    path = facts_file(d, unit)
    if not os.path.isfile(path):
        raise facts.UnitFactsError("no facts file at %s (write it with --facts-to)" % path)
    try:
        return facts.load_unit(root, yamlio.load_file(path), unit, parts)
    except yamlio.YamlError:
        raise
    except facts.UnitFactsError as e:
        raise facts.UnitFactsError("facts that do not read at %s: %s" % (path, e)) from None
    except (KeyError, TypeError, AttributeError, ValueError) as e:
        raise facts.UnitFactsError("facts that do not read at %s: not a facts file of version %d: %s %s"
                                   % (path, facts.UNIT_FACTS_VERSION, type(e).__name__, e)) from None


class UnitMemory:
    """While one unit is checked, sample the memory.stat of this process's own cgroup v2 (in CI, the checker
    container's, where the check runs alone) every 2 s; finish() prints to stderr, never into the check's own output
    (which `--record` makes YAML), the largest anonymous memory seen and the CPUs the check had: the unit's peak on
    the runner that ran it.  Prints nothing where the file is not readable."""

    def __init__(self, unit):
        self.unit, self.peak, self.stop = unit, None, threading.Event()
        self.stat = None
        try:
            with open("/proc/self/cgroup") as f:
                for line in f:
                    if line.startswith("0::"):
                        self.stat = os.path.join("/sys/fs/cgroup", line[3:].strip().lstrip("/"), "memory.stat")
        except OSError:
            pass
        self.thread = threading.Thread(target=self._run, daemon=True)
        self.thread.start()

    def _anon(self):
        if not self.stat:
            return None
        try:
            with open(self.stat) as f:
                for line in f:
                    if line.startswith("anon "):
                        return int(line.split()[1])
        except (OSError, ValueError):
            return None
        return None

    def _run(self):
        while True:
            a = self._anon()
            if a is not None:
                self.peak = max(self.peak or 0, a)
            if self.stop.wait(2):
                return

    def finish(self):
        self.stop.set()
        self.thread.join()
        if self.peak is not None:
            print("%s: peak memory %.1f GiB (anon in this process's cgroup, sampled every 2 s) on %d CPUs"
                  % (self.unit, self.peak / (1 << 30), _jobs()), file=sys.stderr)


# ------------------------------------------------------------------ segments

def snapshot_segments(elf, tool="elf-snapshot"):
    """The `segments` field of a build: how many .hex chunks elf-snapshot
    writes for each LOAD segment of `elf`.  Measured by running the tool,
    so images/dune lists exactly the files the rule will produce."""
    with tempfile.TemporaryDirectory() as d:
        r = subprocess.run([tool, elf, os.path.join(d, "Plain.v"), "--prefix", "Plain", "--module-name", "M",
                            "--namespace", "X"], capture_output=True, text=True)
        if r.returncode != 0:
            raise CheckError("%s failed on %s: %s" % (tool, elf, r.stderr.strip()))
        counts = {}
        for f in os.listdir(d):
            m = re.fullmatch(r"Plain_seg_(\d{3})(?:_chunk_(\d{3}))?\.hex", f)
            if m:
                counts[int(m.group(1))] = counts.get(int(m.group(1)), 0) + 1
    if not counts or sorted(counts) != list(range(len(counts))):
        raise CheckError("%s wrote no segments, or not segments 0..n-1, for %s" % (tool, elf))
    return [counts[i] for i in range(len(counts))]


# ----------------------------------------------------------------------- cli

def add_arguments(c):
    """oft check's arguments, for `oft check` and for `python3 -m oft.check`."""
    c.add_argument("units", nargs="+", metavar="PROJECT/HARNESS")
    c.add_argument("--parts", help="comma-separated, of statements, proofs, counterexamples and findings; naming "
                                   "proofs refuses a unit with no proof (default: each of statements, proofs and "
                                   "counterexamples that the unit has)")
    c.add_argument("--allowed", default="toolchain/allowed-axioms.txt")
    c.add_argument("--qemu", default="qemu-riscv64")
    c.add_argument("--timeout", type=int, default=RUN_TIMEOUT_SECONDS,
                   help="seconds per counterexample or finding run (default: %(default)s)")
    c.add_argument("--rocqchk", action="store_true",
                   help="also re-check the compiled libraries with rocqchk (slow: hours for a large proof)")
    c.add_argument("--record", action="store_true",
                   help="with --parts findings: run each finding that has no runs yet and print them, to commit")
    phase = c.add_mutually_exclusive_group()
    phase.add_argument("--facts-to", metavar="DIR",
                       help="load the facts and check the rules of the whole tree, write each unit's facts to "
                            "DIR/<project>/<harness>.yaml, and check nothing")
    phase.add_argument("--facts-from", metavar="DIR",
                       help="check each unit with its facts from DIR, as --facts-to wrote them, without loading the "
                            "tree: --root may hold that unit's files alone (DIR must be read-only to the check)")
    c.add_argument("--statements", type=lambda s: [x for x in s.split(",") if x],
                   help="with one unit and --parts proofs: check only these statements' proofs (comma-separated); "
                        "each must have one")
    c.add_argument("--lib", help="with one unit and --parts proofs: its proof library, built in this directory by an "
                                 "earlier oft check (root's _build copy of it), instead of building it again")
    c.add_argument("--proof-jobs", type=int, default=1,
                   help="check each statement's proof in a process of its own, this many at once, after one build of "
                        "the unit's proof library and its proof directories (default 1: one after another in this "
                        "process)")
    c.add_argument("--proofs-built", action="store_true",
                   help="with one unit and --parts proofs: its proof directories are in --root's _build as an earlier "
                        "oft check built them; audit them without building them again")
    # proofs_apart's per-statement process: it prints its parent's measured stack (prepare_stack), and leaves the
    # unit's instances to its parent (instances_to_check); not for people
    c.add_argument("--stack-from-parent", action="store_true", help=argparse.SUPPRESS)
    c.add_argument("--no-instances", dest="checks_instances", action="store_false", help=argparse.SUPPRESS)


def cli(root, a):
    return run(root, a.units, parts=a.parts, allowed=a.allowed, qemu=a.qemu, timeout=a.timeout,
               rocqchk=a.rocqchk, record=a.record, facts_to=a.facts_to, facts_from=a.facts_from,
               statements=a.statements, lib=a.lib and os.path.abspath(a.lib), proof_jobs=a.proof_jobs,
               stack_from_parent=a.stack_from_parent, proofs_built=a.proofs_built,
               checks_instances=a.checks_instances)


if __name__ == "__main__":
    # `python3 -m oft.check`, as tools/oft/ci/check-units.sh runs it: the check without the modules of the other
    # commands, which are not part of the checker (keys.NOT_THE_CHECKER)
    if "--instance-control" in sys.argv[1:]:
        # tests/check.sh's instance controls (instance_control), which have no harness.yaml to load
        p = argparse.ArgumentParser(prog="python3 -m oft.check --instance-control",
                                    description="check one instance control of tests/instances/")
        p.add_argument("--root", default=".", help="the repository root (default: .)")
        p.add_argument("--instance-control", metavar="DIR", required=True)
        p.add_argument("--allowed", default="toolchain/allowed-axioms.txt")
        a = p.parse_args()
        sys.exit(instance_control(os.path.abspath(a.root), a.instance_control, a.allowed, sys.stdout))
    p = argparse.ArgumentParser(prog="python3 -m oft.check", description="oft check")
    p.add_argument("--root", default=".", help="the repository root (default: .)")
    add_arguments(p)
    a = p.parse_args()
    sys.exit(cli(os.path.abspath(a.root), a))
