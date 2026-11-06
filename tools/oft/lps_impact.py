"""oft lps-impact: the consumer impact list of an LPS commit, as one command.

What it does: for each unit of the tree, `oft check` it in the checker image
built from the LPS commit under test, as the unit check of
tools/oft/ci/check-units.sh runs it (`python3 -m oft.check --root /work
<unit> --parts <parts>` in the image, no network, the same user, and dune's
cache off).  A unit with a proof is checked with `--parts statements,proofs`;
a unit with no proof with `--parts statements`.  A unit that fails is checked
again in the control image (the checker the release pins) to tell a break the
new model caused from a failure that was there before.

One difference from CI, which measures nothing by itself and is worth knowing:
CI writes each unit's facts once (`--facts-to`) and checks the unit in a view
that holds only that unit's paths (`--facts-from`, check-units.sh make_view),
while this command checks in the whole tree and loads the whole tree's facts
for each unit.  So a unit is checked here with more of the tree readable than
CI gives it, and the run costs one facts load per unit.

    ./oft lps-impact --commit SHA --checker-image REF [--control-image REF]
                     [--units proved|all] [--shard K/N] [--first FILE]
                     [--jobs N] [--work DIR] --out DIR

Both arms are read per proof, never per unit.  `oft check` runs every step of
a unit and keeps going, and it names each step it fails (`FAIL <proof path>:
...`) and each proof that passed (`<proof path>: proves <id>; assumptions:
...`).  A unit's verdict is therefore not a statement's verdict: a unit with
two proofs can break one and keep the other, and most proved units have more
than one proof.  So each statement is given its own proof's outcome, in the
checker image and in the control image alike, and the unit's first error only
when the step that failed is the statements step every statement shares.

It writes, under DIR:

  units.tsv       first line `# commit <SHA> image <REF> line <tree sha> units <scope>`,
                  then one row per unit: unit parts result stage exit
                  first_error proofs_pass proofs_fail wall_s control
                  control_stage control_exit
  impact.tsv      one row per statement of the units checked: id kind reading
                  status revision_change proof recheck class stage first_error
  logs/<unit>.log the checker's output, and the control image's in
                  <unit>.control.log
  logs/<unit>.d/  every log `oft check` wrote under its TMPDIR in the
                  container, copied out before the container was removed
                  (<unit>.control.d/ for the control image)
  work/<unit>/    the container's TMPDIR while the unit is checked, removed
                  once its logs are copied to logs/<unit>.d/

`result` and `recheck` are `pass`, `fail`, `infra` (the check could not run:
docker or the image) or `not-run`.  `control` is the same for the re-check in
the control image, and `not-run` when the unit passed or no control image was
given.

`stage` and `exit` say why a unit that did not pass ended where it did, so
that a row which could not run is never read as a model finding.  `exit` is
the container's exit status; `stage` is one of

  none            the check passed
  statements      the statements step failed
  proofs          a proof step failed
  counterexamples a recorded counterexample's step failed
  findings        a finding's step failed
  checker         the checker refused the run before any step: it could not
                  raise the stack limit, read the unit's facts, or find the
                  part --parts names (nothing of the model was examined)
  no-diagnostic   the check exited non-zero and named no failure: the output
                  holds no `FAIL` line, so nothing of the unit is known
  timeout         the check ran past --timeout (the container is removed)
  oom-killed      the kernel killed the container (exit 137)
  terminated      the container was ended by SIGTERM (exit 143)
  docker-start    docker could not start the container (exit 125)
  not-executable  the command could not be run in the image (exit 126)
  not-found       the command is not in the image (exit 127)
  worker-tree     the worker's copy of the tree could not be made
  host-error      the host or the docker client failed while the unit was
                  being checked (no space, no permission)
  harness-defect  this command raised where it handles none: a defect here,
                  not of the host and not of the model

`class` says what the failure is:

  unchanged        the check passed
  infra            the check could not run (`stage` says what stopped it), so
                   the failure is of the host or the image, not of the model
  timeout          the check ran past the limit: nothing is attributed
  pre-existing     this statement's own proof fails in the control image too
  control-infra    the control image's check of this statement could not run,
                   so the failure is attributed to nothing
  not-attributed   the unit failed in another statement's part, not in this
                   statement's own
  arity            a constructor or function takes a new argument
  guard            a premise or side condition the proof must now show
  initial-ledger   the start state's ledger or reserved list is not what the
                   proof reduced it to
  witness          an existential witness the proof gives is no longer one
  counterexample   a recorded counterexample no longer reproduces
  other            a failure none of the above describes

`--jobs 1`, the default, checks in the tree itself; from 2 each worker checks
in a copy of the tree of its own, since one `_build` and one dune workspace
lock serve one build at a time, and `oft check` renders each proof library's
`lib/dune` into the tree it checks.
"""
import argparse
import concurrent.futures
import hashlib
import os
import re
import shutil
import stat
import subprocess
import sys
import threading
import time
import uuid

HEADER_UNITS = ("unit", "parts", "result", "stage", "exit", "first_error", "proofs_pass", "proofs_fail",
                "wall_s", "control", "control_stage", "control_exit")
HEADER_IMPACT = ("id", "kind", "reading", "status", "revision_change", "proof", "recheck", "class", "stage",
                 "first_error")
# oft check prints a step's failure as `FAIL <label>: ...`; the statements step's label is `statements`, and a
# proof's is its path (check.py:791,794,819).  So a first error under this prefix is the step every statement of
# the unit shares, and any other is one step's.
STATEMENTS_FAIL = "FAIL statements:"
FAIL_LABEL = re.compile(r"^FAIL ([^:]+):")
# check_proof's line for a proof that passed (check.py:435), which proofs_apart prints again for a proof it ran in
# a process of its own (check.py:551, proof_claim at :490).  Anchored at the start of a line: proofs_apart echoes
# a worker's own output with a `  | ` prefix, and the parent prints its verdict for each proof itself.
PROOF_PASS = re.compile(r"^(\S+): (?:proves|refutes) [^;]*; assumptions: \d+ axioms")
# Exit codes docker gives for a container the kernel killed (137 = SIGKILL, the out-of-memory killer) or that could
# not start (125, 126, 127): the check never ran, so its unit is `infra`, not a failure of the model.
INFRA_EXITS = (125, 126, 127, 137, 143)
TIMEOUT_EXIT = 124
STAGE_OF_EXIT = {124: "timeout", 125: "docker-start", 126: "not-executable", 127: "not-found",
                 137: "oom-killed", 143: "terminated"}
# The container's TMPDIR, mounted from the host: see docker_check.
WORK_IN_CONTAINER = "/oftwork"
# `oft check` names the compiler's log of a failure in its error line, as `(see <path>)`.
SEE_LOG = re.compile(r"\(see ([^)\s]+)\)")
# What is worth copying out of the container's TMPDIR, and how much of a log is kept.
LOG_SUFFIXES = (".log", ".out", ".stderr", ".err")
LOG_TAIL_BYTES = 1 << 20


class ImpactError(RuntimeError):
    pass


def _tsv(path):
    with open(path, encoding="utf-8") as f:
        rows = [l.rstrip("\n").split("\t") for l in f if l.strip()]
    return rows[0], rows[1:]


def units_of(root, scope):
    """Every unit of the tree (`all`), or every unit with a proof (`proved`), sorted."""
    _, rows = _tsv(os.path.join(root, "index", "harnesses.tsv"))
    every = sorted("%s/%s" % (r[0], r[1]) for r in rows)
    proved = proof_units(root)
    if scope == "proved":
        return [u for u in every if u in proved]
    return every


def proof_units(root):
    """The units index/proofs.tsv gives a proof."""
    _, rows = _tsv(os.path.join(root, "index", "proofs.tsv"))
    return {"%s/%s" % (r[0], r[1]) for r in rows}


def positive(what):
    """An argparse type for a whole number of `what`, 1 or more.  A --timeout of 0 would time every check out
    before it started, and each unit would read `fail`: a malformed run must not write a measurement."""
    def parse(s):
        try:
            n = int(s)
        except ValueError:
            n = 0
        if n < 1:
            raise argparse.ArgumentTypeError("%r is not a %s (1 or more)" % (s, what))
        return n
    return parse


def shard_arg(s):
    """An argparse type for --shard K/N: the K-th of N parts, K from 1.  A mistyped shard is refused by the
    parser, before the run has made its output directory and its caches."""
    k, sep, n = s.partition("/")
    if not sep:
        raise argparse.ArgumentTypeError("%r is not a shard: give it as K/N" % s)
    try:
        k, n = int(k), int(n)
    except ValueError:
        raise argparse.ArgumentTypeError("%r is not a shard: K and N are whole numbers" % s)
    if n < 1 or not 1 <= k <= n:
        raise argparse.ArgumentTypeError("--shard %s: K must be 1..N and N at least 1" % s)
    return k, n


def shard(units, k, n):
    """The k-th of n disjoint parts of units (k from 1), in the order given."""
    if not 1 <= k <= n:
        raise ImpactError("--shard %d/%d: K must be 1..N" % (k, n))
    return units[k - 1::n]


def order_first(units, first):
    """units, with those `first` names in front, each group in the order given.  A name `first` repeats is taken
    once: a unit checked twice would write two rows and one log, and the impact list would keep whichever row came
    last."""
    want, seen = [], set()
    for u in first:
        if u in units and u not in seen:
            seen.add(u)
            want.append(u)
    rest = [u for u in units if u not in seen]
    return want + rest


ERROR_LINE = re.compile(r"^(?:FAIL |error: |Error)")


def first_error(text):
    """The first line of `oft check` output that names a failure; "" when none does."""
    for line in text.splitlines():
        line = line.strip()
        if ERROR_LINE.match(line):
            return re.sub(r"\s+", " ", line)[:400]
    for line in text.splitlines():
        if "Error" in line or "error" in line:
            return re.sub(r"\s+", " ", line.strip())[:400]
    return ""


def is_proof_label(label):
    """Whether a `FAIL <label>:` names a proof directory.  A step's label is its path, and a unit's steps are its
    statements, its proofs, its counterexamples and its findings (check.py:791-802)."""
    return label.startswith("proofs/") or "/proofs/" in label


def proof_outcomes(text):
    """({proof path: the line that says it failed}, {proof paths that passed}) of one `oft check` run.

    This is what makes a unit's verdict a statement's verdict.  `oft check` runs every step and keeps going, so a
    log holds a `FAIL <proof path>:` for each proof that failed and check_proof's own line for each that passed,
    and a proof named by neither never ran: the unit ended before it."""
    failed, passed = {}, set()
    for raw in text.splitlines():
        m = FAIL_LABEL.match(raw)
        if m:
            label = m.group(1).strip()
            if is_proof_label(label):
                failed.setdefault(label, re.sub(r"\s+", " ", raw.strip())[:400])
            continue
        m = PROOF_PASS.match(raw)
        if m and is_proof_label(m.group(1)):
            passed.add(m.group(1))
    return failed, passed


def stage_of(code, err):
    """Which stage of the check the unit ended in: what a row needs to say so that a unit which could not run is
    never read as a finding of the model.  `err` is the unit's first error, before any log of the container is
    read into it."""
    if code == 0:
        return "none"
    if code in STAGE_OF_EXIT:
        return STAGE_OF_EXIT[code]
    m = FAIL_LABEL.match(err or "")
    if not m:
        return "no-diagnostic"
    label = m.group(1).strip()
    if label == "statements":
        return "statements"
    if is_proof_label(label):
        return "proofs"
    if label.startswith("counterexamples/") or "/counterexamples/" in label:
        return "counterexamples"
    if label.startswith("findings/") or "/findings/" in label:
        return "findings"
    return "checker"


# In order: the first pattern a first error matches names the failure.  counterexample and guard come before
# witness, whose text is the least specific of the three.
CLASS_PATTERNS = (
    ("arity", re.compile(r"not enough arguments|too many arguments|expects \d+ argument|"
                         r"The term .* has type .* while it is expected to have type .*->|"
                         r"Illegal application|Non strictly positive", re.I)),
    ("initial-ledger", re.compile(r"vm_reserved|init_reserved|init_model|initial ledger|vdso_reserved", re.I)),
    ("counterexample", re.compile(r"\.bin on |runs match the record|counterexample", re.I)),
    ("guard", re.compile(r"Unable to satisfy|no applicable tactic|Attempt to save an incomplete proof|"
                         r"premise|side condition|guard", re.I)),
    # `exists` alone is not a witness: `File exists` is an error of the file system, and a goal may name an
    # existential without the proof's witness being what broke.
    ("witness", re.compile(r"Unable to unify|cannot be applied to|witness|"
                           r"(?:provide|give|supply|instantiate).{0,40}\bexists\b|"
                           r"\bexists\b.{0,40}(?:does not|no longer|cannot)", re.I)),
)

# A stage in which the check never reached the model: the class is `infra`, whatever the output says.  `checker`
# is one of them: `oft check` refuses a run before its first step when it cannot raise the stack limit, when a
# unit's facts cannot be read, or when --parts names a part the unit has not (check.py:754,771,783,810), and it
# reports each as a `FAIL` line of its own.  Nothing of the model was examined, so none of it is the move's.
INFRA_STAGES = ("docker-start", "not-executable", "not-found", "oom-killed", "terminated", "worker-tree",
                "host-error", "harness-defect", "no-diagnostic", "checker")


def classify(result, err, control="not-run", stage=None):
    """What a statement's failure is.  A check that could not run has no verdict on the model: it is `infra`,
    before any pattern of an error message is read, because `other` means a break the move caused that the
    patterns could not name.  A control image that could not run attributes the failure to nothing: a reader must
    not take it for a break the new model caused.  `control` is this statement's own outcome in the control
    image, never the unit's (see control_verdict)."""
    if result == "pass":
        return "unchanged"
    if result != "fail" or stage in INFRA_STAGES:
        return "infra"
    if stage == "timeout":
        return "timeout"
    if control == "fail":
        return "pre-existing"
    if control == "infra":
        return "control-infra"
    for name, pattern in CLASS_PATTERNS:
        if pattern.search(err):
            return name
    return "other"


def control_verdict(row, proof):
    """What the control image did with this statement's own part: `fail` (the break was there before the model
    moved), `pass`, `infra` (the control check of this part could not run, so it attributes nothing), or
    `not-run`.

    Per proof, never per unit.  A unit with one proof already broken before the move would otherwise report every
    break the move caused in its other proofs as `pre-existing`, which is the attribution this command exists to
    make, inverted."""
    ctl = row.get("control", "not-run")
    if ctl in ("not-run", "pass", "infra"):
        return ctl
    if row.get("control_stage") in INFRA_STAGES or row.get("control_stage") == "timeout":
        return "infra"
    if proof:
        if proof in row.get("control_fail", ()):
            return "fail"
        if proof in row.get("control_pass", ()):
            return "pass"
        return "infra"      # the control run ended before this proof: it says nothing about it
    # the statements step, which every statement of the unit shares: it is pre-existing only when the control
    # image fails it too, and the statements step is the first a unit runs, so it is the control's first error
    return "fail" if row.get("control_error", "").startswith(STATEMENTS_FAIL) else "pass"


def docker_check(image, work, tools, pydeps, cache, unit, parts, timeout, proof_jobs=1, tmp=None):
    """Run `oft check` of one unit in `image`, as the unit check of check-units.sh runs it, but over the whole tree
    and not over that unit's view (the module's docstring says what that changes).  The stack limit is lifted here
    because a container that inherits this host's hard limit fails the check before it starts.

    `tmp` is a directory of the host for the container's TMPDIR.  `oft check` makes its scratch directory there
    (check.py:746) and reports a Rocq failure as one line naming the compiler's log inside it (`... (see
    <path>)`), and a `--rm` container takes its own /tmp with it: without this mount every diagnostic the checker
    writes is gone before the error is read, and each failure is one line naming a file that does not exist.
    ci/port-check.sh mounts the checker's TMPDIR the same way.
    -> (exit, output, wall seconds)"""
    docker = os.environ.get("OFT_DOCKER", "docker").split()
    # A name, so that a timeout can remove the container: subprocess.run's timeout kills the docker client, and
    # the daemon goes on running the container.
    name = "lps-impact-" + uuid.uuid4().hex[:12]
    cmd = docker + [
        "run", "--rm", "--name", name, "--network", "none", "-u", "%d:%d" % (os.getuid(), os.getgid()),
        "--ulimit", "stack=-1:-1",
        # The dune cache is off by default.  Its key covers the workspace, not the Rocq libraries the image
        # installs, so a cache that two images reach hands back a .vo built against the other model, and the
        # build then fails with "dune build failed" or with statements that Statements.v "does not define".
        # With OFT_DUNE_CACHE_ON, name the image by digest and not by a tag: two builds behind one mutable tag
        # share cache_of's directory, which is the failure this comment describes.
        "-e", "HOME=/tmp", "-e", "XDG_CACHE_HOME=/cache",
        "-e", "DUNE_CACHE=%s" % ("enabled" if os.environ.get("OFT_DUNE_CACHE_ON") else "disabled"),
        "-e", "DUNE_CACHE_STORAGE_MODE=copy", "-e", "PYTHONDONTWRITEBYTECODE=1", "-e", "PYTHONSAFEPATH=1",
        "-e", "PYTHONPATH=/tools:/pydeps",
        "-v", "%s:/work" % work, "-v", "%s:/tools:ro" % tools, "-v", "%s:/pydeps:ro" % pydeps,
        "-v", "%s:/cache" % cache,
    ]
    if tmp:
        cmd += ["-e", "TMPDIR=" + WORK_IN_CONTAINER, "-v", "%s:%s" % (tmp, WORK_IN_CONTAINER)]
    cmd += ["-w", "/work", image, "python3", "-m", "oft.check", "--root", "/work", unit, "--parts", parts]
    if proof_jobs > 1:
        cmd += ["--proof-jobs", str(proof_jobs)]
    start = time.time()
    try:
        done = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
        code, text = done.returncode, done.stdout + done.stderr
    except subprocess.TimeoutExpired as e:
        code = TIMEOUT_EXIT
        text = (e.stdout or b"").decode("utf-8", "replace") if isinstance(e.stdout, bytes) else (e.stdout or "")
        text += "\nFAIL %s: the check ran past the %d s limit" % (unit, timeout)
        # The client is dead, the container is not: it would go on building in the same /work the next unit is
        # checked in, with a second dune build in one workspace, and the units after it would fail for a reason
        # that is not the model.
        gone = subprocess.run(docker + ["rm", "-f", name], capture_output=True, text=True)
        if gone.returncode == 0:
            text += "\nthe container %s was removed" % name
        else:
            text += "\nFAIL %s: the container %s could not be removed: %s" % (unit, name,
                                                                              (gone.stderr or "").strip())
    return code, text, round(time.time() - start, 1)


def _copy_log(src, dst):
    """Copy a log the checker wrote, keeping its last LOG_TAIL_BYTES when it is longer: the diagnostic a Rocq
    failure leaves is at the end, and a build log can be very long."""
    os.makedirs(os.path.dirname(dst), exist_ok=True)
    size = os.path.getsize(src)
    with open(src, "rb") as f:
        if size > LOG_TAIL_BYTES:
            f.seek(size - LOG_TAIL_BYTES)
        data = f.read()
    with open(dst, "wb") as f:
        if size > LOG_TAIL_BYTES:
            f.write(b"... the first %d bytes of this log are not kept ...\n" % (size - LOG_TAIL_BYTES))
        f.write(data)


def harvest_logs(tmp, dest):
    """Copy every log `oft check` left under the container's TMPDIR into `dest`, keeping its path, and return how
    many were copied.  The container is gone by the time this runs and the directory also holds the build, so the
    logs are kept and the rest is not (run removes the directory after this).

    Only a regular file is copied, and by `lstat`, never by following a link: the container is the thing being
    measured, and it chose these paths.  A link it leaves behind would copy a file of this host into the
    published evidence of a unit.  os.walk does not descend a directory link either (followlinks is off)."""
    n = 0
    for base, _dirs, files in os.walk(tmp):
        for f in sorted(files):
            if not f.endswith(LOG_SUFFIXES):
                continue
            src = os.path.join(base, f)
            try:
                if not stat.S_ISREG(os.lstat(src).st_mode):
                    continue
                _copy_log(src, os.path.join(dest, os.path.relpath(src, tmp)))
                n += 1
            except OSError:
                continue
    return n


def log_detail(err, dest):
    """The first error of the log that `err` names, read from the copy harvested into `dest`; "" when the error
    names no log, or the log holds no error.  This is the Rocq diagnostic: without it `err` is one line saying a
    proof did not type-check, naming a file inside a container that no longer exists, and every real break reads
    `other`.

    The path comes from the container's own output, so it is read only when it resolves inside this unit's
    harvested directory: `(see /oftwork/../outside.log)` would otherwise quote a file of this host as a unit's
    build error, in a column that is published as evidence about the proof trees."""
    m = SEE_LOG.search(err or "")
    if not m or not m.group(1).startswith(WORK_IN_CONTAINER + "/"):
        return ""
    path = os.path.realpath(os.path.join(dest, os.path.relpath(m.group(1), WORK_IN_CONTAINER)))
    root = os.path.realpath(dest)
    if path != root and not path.startswith(root + os.sep):
        return ""
    try:
        if not stat.S_ISREG(os.lstat(path).st_mode):
            return ""
        with open(path, encoding="utf-8", errors="replace") as f:
            text = f.read()
    except OSError:
        return ""
    return first_error(text)


def with_detail(err, dest):
    """`err` with the diagnostic of the log it names, so that one line carries both what failed and why."""
    detail = log_detail(err, dest)
    return "%s | %s" % (err[:300], detail[:300]) if detail else err


def _worktree(root, work_root, name, jobs):
    """The tree each worker checks in.  One worker checks in the tree itself; two or more each get a copy of
    their own: one `_build` and one dune workspace lock serve one build at a time, and `oft check` renders each
    proof library's lib/dune into the tree it checks (check.py:370-376), so two workers in one tree would each
    build over the other's files."""
    if jobs < 2:
        return root
    dst = os.path.join(work_root, name)
    if os.path.isdir(dst):
        shutil.rmtree(dst)
    os.makedirs(work_root, exist_ok=True)
    done = subprocess.run(["cp", "-a", root, dst], capture_output=True, text=True)
    if done.returncode != 0:
        raise ImpactError("cp %s %s: %s" % (root, dst, done.stderr.strip()))
    shutil.rmtree(os.path.join(dst, "_build"), ignore_errors=True)   # never another image's artifacts
    return dst


def cache_of(work_root, image):
    """A dune cache of its own for each image.  Dune keys a rule by what the workspace holds, and the model is
    installed in the image, not in the workspace: one cache shared by two images serves a .vo built against the
    other model, and the build fails."""
    return os.path.join(work_root, "cache-" + hashlib.sha256(image.encode()).hexdigest()[:12])


def _write(path, text):
    with open(path, "w", encoding="utf-8") as f:
        f.write(text)


def _fresh(path):
    if os.path.isdir(path):
        shutil.rmtree(path, ignore_errors=True)
    os.makedirs(path, exist_ok=True)
    return path


def _result(code, stage, timeout_is_infra=False):
    """`pass`, `infra` or `fail` for one arm.  It reads the stage, not the exit status alone: two causes that
    examined nothing of the model arrive with exit 1 — a run the checker refused before its first step
    (`checker`) and a non-zero exit that named no failure (`no-diagnostic`) — and a unit the check could not run
    is `infra`, never `fail`.  `result`, `recheck` and `class` all decide it on INFRA_STAGES, so a row cannot
    say `class=infra` and `result=fail` at once.  (They are not one field: `result` is the unit's and `class` is
    each statement's, so one cannot be derived from the other; they share the rule instead.)  A control image
    that ran past the limit measured nothing either, so its timeout is `infra`; the checker arm's timeout is the
    unit's own outcome, which `stage` names and `classify` reads."""
    if code == 0:
        return "pass"
    if code in INFRA_EXITS or stage in INFRA_STAGES or (timeout_is_infra and code == TIMEOUT_EXIT):
        return "infra"
    return "fail"


def _arm(image, work, tools, pydeps, work_root, unit, parts, timeout, proof_jobs, logs, name, tmp_root):
    """One image's check of one unit: run it, keep its output and every log it wrote inside the container, and
    read its per-proof outcome.  Both arms run through here, so neither can drift from the other.

    `raw_error` is the first error as the checker printed it, which `stage_of` and the statements-step test read;
    `error` is that line with the diagnostic of the log it names, which is what a reader of a row gets.
    -> dict(exit, stage, raw_error, error, passed, failed, wall_s)"""
    tmp = _fresh(os.path.join(tmp_root, name)) if tmp_root else None
    dest = os.path.join(logs, name + ".d")
    code, text, wall = docker_check(image, work, tools, pydeps, cache_of(work_root, image), unit, parts,
                                    timeout, proof_jobs, tmp=tmp)
    _write(os.path.join(logs, name + ".log"), text)
    if tmp:
        harvest_logs(tmp, dest)
        shutil.rmtree(tmp, ignore_errors=True)
    failed, passed = proof_outcomes(text)
    raw = first_error(text)
    return dict(exit=code, stage=stage_of(code, raw), raw_error=raw, wall_s=wall, passed=sorted(passed),
                failed={p: with_detail(line, dest) for p, line in failed.items()},
                error="" if code == 0 else with_detail(raw or "exit %d" % code, dest))


def check_one(work, tools, pydeps, work_root, unit, parts, image, control, timeout, logs, proof_jobs,
              control_tree=None, tmp_root=None):
    """One unit in the checker image, and, when it fails and a control image is given, in that too.

    The control check runs in a tree of its own: dune's _build in a tree holds the .vo the last image's model
    built, and the installed model is no input of a dune rule, so a second image in the same tree reuses them
    and every later build fails.

    The row carries each arm's per-proof outcome, its exit status and the stage it ended in: a reader of one row
    can tell a proof the model broke from a proof the run never reached."""
    name = unit.replace("/", "__")
    a = _arm(image, work, tools, pydeps, work_root, unit, parts, timeout, proof_jobs, logs, name, tmp_root)
    row = dict(unit=unit, parts=parts, result=_result(a["exit"], a["stage"]), stage=a["stage"], exit=a["exit"],
               first_error=a["error"], proofs_pass=a["passed"], proofs_fail=a["failed"],
               wall_s=a["wall_s"], control="not-run", control_stage="-", control_exit="-", control_pass=(),
               control_fail={}, control_error="")
    # a unit the check could not run has no failure to attribute, so the control image is not spent on it
    if row["result"] != "fail" or not control:
        return row
    # a control tree that cannot be made loses the control arm for this unit, never the verdict already
    # measured in the checker image
    try:
        cwork = control_tree() if control_tree else work
        c = _arm(control, cwork, tools, pydeps, work_root, unit, parts, timeout, proof_jobs, logs,
                 name + ".control", tmp_root)
    except (ImpactError, OSError, subprocess.SubprocessError) as e:
        text = "FAIL %s: the control tree could not be made: %s" % (unit, e)
        _write(os.path.join(logs, name + ".control.log"), text)
        c = dict(exit=125, stage="worker-tree", raw_error=text, error=text, passed=(), failed={}, wall_s=0)
    row.update(control=_result(c["exit"], c["stage"], timeout_is_infra=True), control_stage=c["stage"],
               control_exit=c["exit"], control_pass=c["passed"], control_fail=c["failed"],
               control_error=c["error"])
    return row


def run(root, out, commit, image, control=None, scope="all", shard_spec=None, first=None, jobs=1,
        work_root=None, timeout=14400, line=None, proof_jobs=1, printer=print):
    tools = os.path.join(root, "tools")
    pydeps = os.environ.get("OFT_PYDEPS", os.path.join(root, ".pydeps"))
    work_root = work_root or "/var/tmp/lps-impact"
    logs = os.path.join(out, "logs")
    tmp_root = os.path.join(out, "work")
    for d in (logs, tmp_root, work_root, cache_of(work_root, image)) + (
            (cache_of(work_root, control),) if control else ()):
        os.makedirs(d, exist_ok=True)
    if jobs < 2:
        # the one worker checks in the tree itself, and a _build left there by a run in another image holds .vo
        # files built against the other model; every worker copy is cleared the same way (_worktree)
        shutil.rmtree(os.path.join(root, "_build"), ignore_errors=True)

    units = units_of(root, scope)
    if shard_spec:
        k, n = shard_spec
        units = shard(units, k, n)
    if first:
        with open(first, encoding="utf-8") as f:
            units = order_first(units, [l.strip() for l in f if l.strip()])
    proved = proof_units(root)
    rows = []
    queue = list(units)
    lock = threading.Lock()
    state = {"next": 0, "done": 0}

    def worker(w):
        # a tree this worker cannot make (no space, no permission) leaves its units `infra` below, so the run
        # still writes a row for every unit and an impact list; it never ends with neither
        try:
            work, failed_tree = _worktree(root, work_root, "w%d" % w, jobs), None
        except (ImpactError, OSError, subprocess.SubprocessError) as e:
            work, failed_tree = None, "the worker's tree could not be made: %s" % e
        made = {}

        def control_tree():                      # one copy per worker, made when a failure first needs it
            if "t" not in made:
                made["t"] = _worktree(root, work_root, "control-w%d" % w, 2)
            return made["t"]

        while True:
            with lock:
                i = state["next"]
                if i >= len(queue):
                    return
                state["next"] = i + 1
            u = queue[i]
            parts = "statements,proofs" if u in proved else "statements"
            try:
                if failed_tree:
                    # the tree, not this unit: `worker-tree` is the stage of that failure alone
                    row = _infra_row(u, parts, "worker-tree", ImpactError(failed_tree))
                else:
                    row = check_one(work, tools, pydeps, work_root, u, parts, image, control, timeout, logs,
                                    proof_jobs, control_tree=control_tree, tmp_root=tmp_root)
            except (ImpactError, OSError, subprocess.SubprocessError) as e:
                # the host or the docker client failed while this unit was checked: a row for the unit, never a
                # hole, and a stage that names what stopped it rather than one that names the tree copy
                row = _infra_row(u, parts, "host-error", e)
            except Exception as e:                  # a defect here reads as a defect, never as a flaky host
                row = _infra_row(u, parts, "harness-defect", e)
            with lock:
                rows.append(row)
                state["done"] += 1
                printer("%4d/%d %s %s %s %s" % (state["done"], len(queue), row["result"], row["stage"], u,
                                                row["first_error"][:120]))
                write_units(out, rows, commit, image, line, scope)

    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as pool:
        for fut in [pool.submit(worker, w) for w in range(jobs)]:
            fut.result()
    rows.sort(key=lambda r: r["unit"])
    write_units(out, rows, commit, image, line, scope)
    write_impact(root, out, rows)
    return 0 if all(r["result"] == "pass" for r in rows) else 1


def _infra_row(unit, parts, stage, e):
    return dict(unit=unit, parts=parts, result="infra", stage=stage, exit="-",
                first_error=("%s: %s" % (type(e).__name__, e))[:400], proofs_pass=(), proofs_fail={}, wall_s=0,
                control="not-run", control_stage="-", control_exit="-", control_pass=(), control_fail={},
                control_error="")


def _joined(paths):
    return ",".join(sorted(paths)) if paths else "-"


def write_units(out, rows, commit, image, line, scope):
    path = os.path.join(out, "units.tsv")
    with open(path, "w", encoding="utf-8") as f:
        f.write("# commit %s image %s line %s units %s\n" % (commit, image, line or "-", scope))
        f.write("\t".join(HEADER_UNITS) + "\n")
        for r in sorted(rows, key=lambda r: r["unit"]):
            f.write("\t".join(str(x) for x in (
                r["unit"], r["parts"], r["result"], r.get("stage", "-"), r.get("exit", "-"), r["first_error"],
                _joined(r.get("proofs_pass", ())), _joined(r.get("proofs_fail", ())), r["wall_s"],
                r.get("control", "not-run"), r.get("control_stage", "-"), r.get("control_exit", "-"))) + "\n")
    return path


def _columns(header, path, want):
    """{name: index} of the columns `want` in `header`, or an error naming the file: this index is read by name,
    so that a column inserted in it does not silently shift a statement's reading, status or proof."""
    at = {name: i for i, name in enumerate(header)}
    missing = [w for w in want if w not in at]
    if missing:
        raise ImpactError("%s: no column %s" % (path, ", ".join(missing)))
    return at


STATEMENT_COLUMNS = ("id", "kind", "reading", "status", "proof")


def write_impact(root, out, rows):
    """One row per statement of each unit checked, with that statement's own outcome.

    A unit is checked whole, but `oft check` names every step it failed and every proof that passed, so a
    statement's verdict is its own proof's: `fail` when its proof is one the run failed, `pass` when its proof
    printed its pass line in the same run, and `not-run` when the run named neither, which is what a unit that
    ended early leaves.  A statement whose proof says nothing gets the unit's first error only when the step that
    failed is the statements step, which every statement of the unit shares, or when the unit had nothing but its
    statements to check.  The control image is read the same way, proof by proof: a unit with a proof that was
    broken before the model moved must not report the proofs this move broke as `pre-existing`."""
    by_unit = {r["unit"]: r for r in rows}
    spath = os.path.join(root, "index", "statements.tsv")
    header, stmts = _tsv(spath)
    at = _columns(header, spath, STATEMENT_COLUMNS)
    path = os.path.join(out, "impact.tsv")
    with open(path, "w", encoding="utf-8") as f:
        f.write("\t".join(HEADER_IMPACT) + "\n")
        for s in stmts:
            sid, kind = s[at["id"]], s[at["kind"]]
            reading, status = s[at["reading"]], s[at["status"]]
            proof = s[at["proof"]] if len(s) > at["proof"] else "-"
            proof = "" if proof in ("-", "") else proof
            unit = "/".join(sid.split("/")[:2])
            row = by_unit.get(unit)
            if row is None:
                continue
            recheck, klass, err = _verdict(row, proof)
            f.write("\t".join((sid, kind, reading, status, "yes", proof or "-", recheck, klass,
                               row.get("stage", "-"), err)) + "\n")
    return path


def _verdict(row, proof):
    """(recheck, class, first error) of one statement in the unit `row` records."""
    unit_err = row["first_error"]
    stage = row.get("stage", "-")
    if row["result"] == "pass":
        return ("pass" if proof else "not-run"), "unchanged", ""
    if row["result"] != "fail":
        # the check never ran: every statement of the unit shares that, and none of it is the model's
        return "infra", classify(row["result"], unit_err, stage=stage), unit_err
    if proof and proof in row.get("proofs_fail", {}):
        err = row["proofs_fail"][proof]
        return "fail", classify("fail", err, control_verdict(row, proof), stage="proofs"), err
    if proof and proof in row.get("proofs_pass", ()):
        # its proof passed in this very run: the unit failed elsewhere
        return "pass", "unchanged", ""
    shared = unit_err.startswith(STATEMENTS_FAIL) or "proofs" not in row["parts"]
    if shared:
        return "fail", classify("fail", unit_err, control_verdict(row, ""), stage=stage), unit_err
    if proof:
        # the run named this proof neither failed nor passed: it ended before it.  `stage` and `exit` in
        # units.tsv say what stopped it; nothing here is attributed to the model.
        klass = "timeout" if stage == "timeout" else ("infra" if stage in INFRA_STAGES else "not-attributed")
        return "not-run", klass, unit_err
    return "not-run", "not-attributed", unit_err


def add_arguments(p):
    p.add_argument("--commit", required=True, help="the LPS commit the checker image was built from")
    p.add_argument("--checker-image", required=True, help="the image to check in, by digest or tag")
    p.add_argument("--control-image", help="check a failing unit again in this image, to find a failure that was "
                                           "there before the model moved")
    p.add_argument("--units", choices=("proved", "all"), default="all",
                   help="all: every unit, the statements part alone for a unit with no proof")
    p.add_argument("--shard", type=shard_arg, metavar="K/N", help="the K-th of N disjoint parts of the units")
    p.add_argument("--first", metavar="FILE", help="a file of units to check before the others")
    p.add_argument("--jobs", type=positive("number of units at once"), default=1,
                   help="units to check at once, each in a tree of its own")
    p.add_argument("--proof-jobs", type=positive("number of proofs at once"), default=1,
                   help="oft check --proof-jobs")
    p.add_argument("--work", help="where the per-worker trees and the dune cache go")
    p.add_argument("--timeout", type=positive("number of seconds"), default=14400,
                   help="seconds for one unit, 1 or more")
    p.add_argument("--line", help="the commit of the proofs tree checked, for the header")
    p.add_argument("--out", required=True,
                   help="a directory for units.tsv, impact.tsv, the logs and each unit's TMPDIR")


def cli(root, a):
    os.makedirs(a.out, exist_ok=True)
    return run(root, a.out, a.commit, a.checker_image, control=a.control_image, scope=a.units,
               shard_spec=a.shard, first=a.first, jobs=a.jobs, work_root=a.work, timeout=a.timeout,
               line=a.line, proof_jobs=a.proof_jobs)


if __name__ == "__main__":
    # `python3 -m oft.lps_impact`, the same command `./oft lps-impact` runs, with one definition of its flags
    # (add_arguments), as oft.check and oft.fetch do
    p = argparse.ArgumentParser(prog="python3 -m oft.lps_impact", description=__doc__.splitlines()[0])
    p.add_argument("--root", default=".", help="the repository root (default: .)")
    add_arguments(p)
    a = p.parse_args()
    sys.exit(cli(os.path.abspath(a.root), a))
