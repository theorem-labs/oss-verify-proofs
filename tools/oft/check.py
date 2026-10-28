"""oft check.

`check PROJECT/HARNESS` does what CI does for one harness:

  statements       verify every published ELF's SHA-256; `dune build` the
                   images (elf-snapshot, at build time), Images.v,
                   Statements.v, Characterise.v; then compile a file that
                   names each statement harness.yaml lists (but a withheld or
                   withdrawn one, which Statements.v does not carry) and
                   prints its assumptions: a unit with no such statement, a
                   Statements.v that lacks one, one that is an axiom (Axiom,
                   Parameter, Admitted), or an assumption outside
                   toolchain/allowed-axioms.txt fails
  proofs           build the harness's proof library proofs/<p>/<h>/lib/, if
                   it has one, with dune (once; dune's cache may supply it),
                   then compile each proofs/<p>/<h>/<s>/ afresh with `rocq
                   compile` against the statements and the library, then a
                   wrapper this tool writes, which ascribes the proof's theorem
                   to the statement and prints its assumptions; every
                   assumption must be in toolchain/allowed-axioms.txt.  The
                   kernel checks every term as it compiles.
  counterexamples  run the binary on input.bin and on control.bin under
                   qemu-user and compare with expect.yaml
  findings         run each finding's input.bin and control.bin on every
                   build its statements name, on the unpatched binaries
                   (findings/<p>/unpatched.yaml), under qemu-user, and compare
                   each run's exit, signal, stdout and stderr with
                   finding.yaml; --record prints the runs of a finding that
                   has none yet, to commit, only when no run timed out or
                   died of a signal a finding does not record, its input
                   shows each statement false and its control none

--rocqchk adds rocqchk, an independent re-check of the compiled libraries:
over the statements, and once per harness over the wrappers of all its proofs.
Off by default: without its bytecode machine (see _rocqchk) it re-checks every
vm_compute certificate by reduction, which takes hours for one proof.

Each part fails when it examined nothing it was asked to examine: a unit
with no statement Statements.v defines fails statements, and a unit with no
proof fails when --parts names proofs.  Without --parts, a unit is checked
on each of statements, proofs and counterexamples that it has.

CI runs `python3 -m oft.check`, which loads the checker and none of the other
commands' modules (keys.py says which files the checker is).
"""
import hashlib
import os
import re
import resource
import shutil
import signal
import subprocess
import sys
import tempfile

import yaml

from . import facts, fetch, names, render, rules, schema, yamlio

# A bound statement takes its b as `(n # d)`, QArith's notation, which parses only where QArith is imported; the
# import adds no assumption, and a b that is not the proof's still fails to unify.
WRAPPER = """(* written by oft check; never supplied by a pull request *)
From Stdlib Require Import QArith.
Require {stmt_mod}.
Require {proof_mod}.
Definition certified : {neg}{stmt_mod}.{stmt}{args} := {proof_mod}.{theorem}.
Set Printing Fully Qualified.
Print Assumptions certified.
"""

DEFINED = """(* written by oft check: each statement harness.yaml lists, typed, and what it assumes *)
Require {stmt_mod}.
Definition oft_listed := ({terms}).
Set Printing Fully Qualified.
Print Assumptions oft_listed.
"""

# What Print Assumptions prints (Rocq 9.2.0, printing/printer.ml, pr_assumptionset): "Closed under the global
# context", or sections with no blank line between them, each a heading and then one entry per line at column 0 (a long
# entry continues on indented lines).  Under "Axioms:" an axiom is "<name> : <type>"; a construct the kernel took on
# trust is a sentence instead: "<inductive> is assumed to be positive.", "<name> is assumed to be guarded.", "<name>
# relies on an unsafe hierarchy.", "<inductive> relies on definitional UIP.".  "Theory:" lists changes to the logic
# itself (type in type, impredicative Set, rewrite rules).
SECTIONS = ("Transparent constants:", "Section Variables:", "Axioms:", "Opaque constants:", "Theory:")


def wrapper_assumptions(text):
    """The axioms the wrapper's Print Assumptions lists (Set Printing Fully Qualified).  Raises CheckError on every
    entry that is not an axiom and its type (a construct taken on trust, a change to the logic, an axiom whose type did
    not print), and when the output holds neither "Closed under the global context" nor a list of assumptions: nothing
    parsed is not nothing assumed."""
    lines = text.splitlines()
    if "Closed under the global context" in lines:
        return set()
    first = next((i for i, l in enumerate(lines) if l in SECTIONS), None)
    if first is None:
        raise CheckError("Print Assumptions printed neither 'Closed under the global context' nor a list of assumptions")
    axioms, other, section = set(), [], None
    for l in lines[first:]:
        if not l.strip():
            break
        if l[0].isspace():
            continue
        if l in SECTIONS:
            section = l
            continue
        m = re.match(r"(\S+) :( |$)", l)
        if section == "Axioms:" and m:
            axioms.add(m.group(1))
        else:
            other.append(l if section == "Axioms:" else "%s %s" % (section, l))
    if other:
        raise CheckError("the proof relies on what the kernel did not check: %s" % "; ".join(other))
    if not axioms:
        raise CheckError("Print Assumptions printed an empty list of assumptions")
    return axioms


class CheckError(RuntimeError):
    pass


def _run(cmd, cwd, log, timeout=None, env=None):
    """Run cmd, appending its output to log; its return code."""
    with open(log, "a", encoding="utf-8") as f:
        f.write("$ %s\n" % " ".join(cmd))
        f.flush()
        r = subprocess.run(cmd, cwd=cwd, stdout=f, stderr=subprocess.STDOUT, timeout=timeout, env=env)
    return r.returncode


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
    return ["-Q", os.path.join(build, "theories"), "OssFuzzTheorems.Core",
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


def check_statements(root, h, allowed, work, out, rocqchk=False):
    if not h.builds():
        raise CheckError("every build is withheld: nothing to check")
    listed = sorted(st.name for st in h.statements.values() if st.rendered())
    if not listed:
        raise CheckError("every statement harness.yaml lists is withheld or withdrawn, so Statements.v defines none: "
                         "nothing to check")
    if not os.path.isfile(os.path.join(root, h.dir, "Statements.v")):
        raise CheckError("%s/Statements.v is missing (run ./oft generate)" % h.dir)
    if fetch.verify_sha(root, [h.project.name], harness=h.name, out=out) != 0:
        raise CheckError("the binaries are missing or do not match (run ./oft fetch %s)" % h.project.name)
    targets = [os.path.join(h.dir, f[:-2] + ".vo") for f in ("Images.v", "Statements.v", "Characterise.v")
               if os.path.isfile(os.path.join(root, h.dir, f))]
    log = os.path.join(work, "dune.log")
    # --display short: the log names each rule dune ran; one it took from its cache is not named.
    if _run(["dune", "build", "--root", root, "--display", "short"] + targets, root, log) != 0:
        raise CheckError("dune build failed (see %s)" % log)
    build = os.path.join(root, "_build", "default")
    check_defined(root, h, listed, build, work, allowed)
    if not rocqchk:
        print("%s: statements compiled, each of the %d listed defined" % (h.dir, len(listed)), file=out)
        return
    mods = [h.data["rocq"] + "." + os.path.basename(t)[:-3] for t in targets]
    n = _rocqchk(root, _loadpath(build, h), mods, allowed,
                 os.path.join(work, names.ident(h.project.name) + "." + names.ident(h.name) + ".rocqchk.log"))
    print("%s: statements compiled, each of the %d listed defined; rocqchk: %d axioms, all allowed"
          % (h.dir, len(listed), n), file=out)


def check_defined(root, h, listed, build, work, allowed):
    """Have the kernel type every statement in listed, from h's compiled Statements (a _build/default tree), and print
    what they assume.  A Statements.v that compiles but lacks one, or defines none at all, is not a check of that
    statement, and neither is one that states it as an axiom (Axiom, Parameter, or a Definition closed by Admitted)
    or defines it from an assumption outside the allowlist."""
    d = tempfile.mkdtemp(prefix="defined-", dir=work)
    stmt_mod = h.data["rocq"] + ".Statements"
    with open(os.path.join(d, "Defined.v"), "w", encoding="utf-8") as f:
        f.write(DEFINED.format(stmt_mod=stmt_mod, terms=", ".join("@%s.%s" % (stmt_mod, s) for s in listed)))
    log = os.path.join(d, "defined.log")
    if _run(["rocq", "compile"] + _loadpath(build, h) + ["-Q", d, "OftDefined", os.path.join(d, "Defined.v")],
            d, log) != 0:
        raise CheckError("%s/Statements.v does not define every statement harness.yaml lists (%s; see %s)"
                         % (h.dir, ", ".join(listed), log))
    axioms = wrapper_assumptions(facts.read(log))
    stated = sorted(s for s in listed if "%s.%s" % (stmt_mod, s) in axioms)
    if stated:
        raise CheckError("%s/Statements.v states %s as an axiom (Axiom, Parameter or Admitted), not a definition (see "
                         "%s)" % (h.dir, ", ".join(stated), log))
    outside = sorted(axioms - allowed)
    if outside:
        raise CheckError("%s/Statements.v: the statements assume axioms outside the allowlist: %s (see %s)"
                         % (h.dir, ", ".join(outside), log))


# The names under which dune reads build rules in a directory.  dune builds a proof library from the rules of lib/ and
# of every directory above it ((subdir ...) adds stanzas below; (env ...) sets flags or the compiler for everything
# below).  So oft check writes lib/dune itself and refuses any other build file in lib/ or above it (the root's
# dune-project, which oft generate writes, aside): every .vo of a library is `rocq compile` of its own .v files.
DUNE_FILES = ("dune", "dune-file", "dune-project", "dune-workspace")


def compile_lib(root, h, work, libs, out):
    """The -Q mapping of h's proof library, proofs/<p>/<h>/lib/ (OssFuzzTheorems.Proofs.<p>.<h>.lib, every .v at any
    depth), or [] when h has none.  Built once per check run by dune, from the rocq.theory stanza of oft generate's
    lib/dune, against the statements in root's _build; `libs` holds the mapping, or the error, per harness.  dune takes a
    file from its cache (DUNE_CACHE) only when the file's sources, its dependencies and the Rocq binary all hash the
    same as when the cached copy was compiled."""
    if h.dir in libs:
        if isinstance(libs[h.dir], CheckError):
            raise libs[h.dir]
        return libs[h.dir]
    rel = os.path.join("proofs", h.project.name, h.name, "lib")
    src = os.path.join(root, rel)
    if not os.path.isdir(src):
        libs[h.dir] = []
        return []
    try:
        targets = _lib_targets(root, h, rel, out)
        log = os.path.join(work, "%s.%s.lib.dune.log" % (names.ident(h.project.name), names.ident(h.name)))
        if _run(["dune", "build", "--root", root, "--display", "short", "-j", str(len(os.sched_getaffinity(0)))]
                + targets, root, log) != 0:
            raise CheckError("%s: does not compile (see %s)" % (rel, log))
    except CheckError as e:
        libs[h.dir] = e
        raise
    libs[h.dir] = ["-Q", os.path.join(root, "_build", "default", rel), names.rocq_proof(h.project.name, h.name, "lib")]
    print("%s: %d files compiled or taken from dune's cache (log %s)" % (rel, len(targets), log), file=out)
    return libs[h.dir]


def _lib_targets(root, h, rel, out):
    """The .vo of every .v file in proofs/<p>/<h>/lib/ (relative to root).  Refuses a symbolic link in the library (dune
    follows one, a walk does not) and any dune build file in it or in a directory above it; writes lib/dune as this
    oft generate renders it, so the rule dune runs is this tool's, whichever tools rendered the tree."""
    from . import generate
    src = os.path.join(root, rel)
    d = rel
    while True:
        for f in DUNE_FILES:
            p = os.path.join(d, f)
            if p != "dune-project" and d != rel and os.path.lexists(os.path.join(root, p)):
                raise CheckError("%s: no directory above a proof library holds a build file" % p)
        if d and os.path.islink(os.path.join(root, d)):
            raise CheckError("%s: a proof library holds no symbolic link" % d)
        if not d:
            break
        d = os.path.dirname(d)
    targets = []
    for dp, dn, fn in os.walk(src):
        for f in dn + fn:
            if os.path.islink(os.path.join(dp, f)):
                raise CheckError("%s: a proof library holds no symbolic link" % os.path.relpath(os.path.join(dp, f), root))
        for f in fn:
            path = os.path.relpath(os.path.join(dp, f), root)
            if f in DUNE_FILES and path != os.path.join(rel, "dune"):
                raise CheckError("%s: a proof library holds no build file but lib/dune" % path)
            if f.endswith(".v"):
                targets.append(path[:-2] + ".vo")
    if not targets:
        raise CheckError("%s: holds no .v file" % rel)
    dune, want = os.path.join(src, "dune"), generate.proof_lib_dune(h.project.name, h.name)
    if not os.path.isfile(dune) or facts.read(dune) != want:
        with open(dune, "w", encoding="utf-8") as f:
            f.write(want)
        print("%s: written as this oft generate renders it" % os.path.join(rel, "dune"), file=out)
    return sorted(targets)


def check_proof(root, st, pd, allowed, work, out, libs, rocqchk=False):
    """Compile one proof directory afresh, against the statements in root's _build and its harness's proof library, then
    the wrapper, and audit the wrapper's assumptions.  With rocqchk, return what rocqchk_proofs needs."""
    h = st.harness
    p, hn, s = st.id.split("/")
    proof_mod = names.rocq_proof(p, hn, s)
    main = "Refutation" if pd.refutes else "Proof"
    libq = compile_lib(root, h, work, libs, out)
    d = tempfile.mkdtemp(prefix="proof-", dir=work)
    src = os.path.join(root, pd.path)
    for f in os.listdir(src):
        if f.endswith(".v"):
            shutil.copy(os.path.join(src, f), os.path.join(d, f))
    base = os.path.join(root, "_build", "default")
    q = _loadpath(base, h) + libq + ["-Q", d, proof_mod]
    log = os.path.join(d, "compile.log")
    deps = subprocess.run(["rocq", "dep", "-sort"] + libq + ["-Q", d, proof_mod] + sorted(
        os.path.join(d, f) for f in os.listdir(d) if f.endswith(".v")), capture_output=True, text=True)
    if deps.returncode != 0:
        raise CheckError("%s: rocq dep failed: %s" % (pd.path, deps.stderr.strip()))
    # rocq dep -sort lists the whole closure in order, the library's files included: those are compiled already.
    own = [f for f in deps.stdout.split() if os.path.dirname(os.path.abspath(f)) == d]
    if not own:
        raise CheckError("%s: rocq dep listed none of its .v files" % pd.path)
    for f in own:
        if _run(["rocq", "compile"] + q + [f], d, log) != 0:
            raise CheckError("%s: does not compile (see %s)" % (pd.path, log))
    args = ""
    if st.kind == "bound" and not pd.refutes:
        n_, _, d_ = pd.data["bound"].partition("/")
        args = " (%s # %s)" % (n_, d_ or "1")
    theorem = "%s_%s" % (s, "refuted" if pd.refutes else "holds")
    wdir = os.path.join(d, "wrap")
    os.makedirs(wdir)
    with open(os.path.join(wdir, "Wrapper.v"), "w", encoding="utf-8") as f:
        f.write(WRAPPER.format(stmt_mod=h.data["rocq"] + ".Statements", proof_mod=proof_mod + "." + main,
                               neg="~ " if pd.refutes else "", stmt=s, args=args, theorem=theorem))
    wrap = "Wrap." + names.ident(s)
    wq = q + ["-Q", wdir, wrap]
    wlog = os.path.join(d, "wrapper.log")
    if _run(["rocq", "compile"] + wq + [os.path.join(wdir, "Wrapper.v")], d, wlog) != 0:
        raise CheckError("%s: the wrapper does not type-check: the proof is not of this statement (see %s)"
                         % (pd.path, wlog))
    axioms = wrapper_assumptions(facts.read(wlog))
    outside = sorted(axioms - allowed)
    if outside:
        raise CheckError("%s: axioms outside the allowlist: %s" % (pd.path, ", ".join(outside)))
    print("%s: %s %s; assumptions: %d axioms, all allowed" % (pd.path, "refutes" if pd.refutes else "proves",
                                                               st.id + args, len(axioms)), file=out)
    if not rocqchk:
        return None
    # rocqchk runs once per harness, over the wrappers of all its proofs (rocqchk_proofs): their closures share the
    # harness's library, which one run checks once.
    return {"base": _loadpath(base, h) + libq, "own": ["-Q", d, proof_mod, "-Q", wdir, wrap],
            "module": wrap + ".Wrapper"}


def rocqchk_proofs(root, h, checked, allowed, work, out):
    """rocqchk over the wrappers of the proofs `checked` (what check_proof returned) of harness h, in one run, and
    every assumption of their closures against the allowlist."""
    q = list(checked[0]["base"])
    for c in checked:
        q += c["own"]
    log = os.path.join(work, names.ident(h.project.name) + "." + names.ident(h.name) + ".proofs.rocqchk.log")
    n = _rocqchk(root, q, [c["module"] for c in checked], allowed, log)
    print("%s: rocqchk over the wrappers of %d proof(s): %d axioms, all allowed"
          % (os.path.join("proofs", h.project.name, h.name), len(checked), n), file=out)


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
    elf = os.path.join(root, h.elf_path(exp["observed"]["build"]))
    if not os.path.isfile(elf):
        raise CheckError("%s: %s is not fetched" % (cx.path, h.elf_path(exp["observed"]["build"])))
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
    pins = os.path.join("findings", f.project, "unpatched.yaml")
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


STACK_NEEDED = 1 << 30


def raise_stack_limit():
    """Give every rocq, rocqchk and dune this process starts the largest stack the hard limit allows.  Rocq recurses on
    the system stack, and large proof terms overflow the usual 8 MiB; tests/check.sh runs `ulimit -s unlimited` for
    the same reason.  This changes where the kernel runs, not what it checks."""
    _, hard = resource.getrlimit(resource.RLIMIT_STACK)
    if hard != resource.RLIM_INFINITY and hard < STACK_NEEDED:
        raise CheckError("the stack's hard limit is %d bytes; Rocq needs at least %d (docker run --ulimit stack=-1:-1)"
                         % (hard, STACK_NEEDED))
    resource.setrlimit(resource.RLIMIT_STACK, (hard, hard))


# The parts `oft check` runs when --parts is not given: each of them that the unit has.
DEFAULT_PARTS = "statements,proofs,counterexamples"


def run(root, units, parts=None, allowed="toolchain/allowed-axioms.txt",
        qemu="qemu-riscv64", timeout=600, rocqchk=False, record=False, out=sys.stdout):
    """parts: the comma-separated parts to check, where naming proofs refuses a unit with no proof; None (no --parts)
    checks each part of DEFAULT_PARTS that the unit has, so an unproved unit is checked on its statements."""
    named = parts is not None
    parts = parts if named else DEFAULT_PARTS
    want = set(parts.split(","))
    if record and "findings" not in want:
        print("FAIL --record records findings: add findings to --parts", file=out)
        return 1
    tree = facts.load(root, record=record)
    rules.check(tree)
    if tree.errors:
        for e in tree.errors:
            print("error: " + e, file=out)
        return 1
    work = tempfile.mkdtemp(prefix="oft-check-")
    bad = examined = 0
    libs = {}  # harness dir -> its proof library's -Q mapping, or the error compiling it
    try:
        allow = allowed_axioms(root, allowed) if want & {"statements", "proofs"} else set()
        if want & {"statements", "proofs"}:
            raise_stack_limit()
    except CheckError as e:
        print("FAIL %s" % e, file=out)
        return 1
    for unit in units:
        p, _, hn = unit.partition("/")
        h = tree.projects.get(p) and tree.projects[p].harnesses.get(hn)
        if not h:
            print("%s: no such harness" % unit, file=out)
            bad += 1
            continue
        steps = []    # (label, step, whether its success alone passes it)
        checked = []  # (label, what check_proof returned) of the proofs whose compile and audit passed
        if "statements" in want:
            steps.append(("statements", lambda h=h: check_statements(root, h, allow, work, out, rocqchk), True))
        for st in h.statements.values():
            if st.proof and "proofs" in want:
                steps.append((st.proof.path, lambda st=st: checked.append((st.proof.path, check_proof(
                    root, st, st.proof, allow, work, out, libs,
                    rocqchk))), not rocqchk))
            if st.counterexample and "counterexamples" in want:
                steps.append((st.counterexample.path, lambda st=st: check_counterexample(
                    root, st, st.counterexample, qemu, timeout, work, out), True))
        for f in sorted(tree.findings.values(), key=lambda f: f.path) if "findings" in want else []:
            if f.unit == unit:
                steps.append((f.path, lambda f=f: check_finding(root, h, f, qemu, timeout, work, out, record), True))
        if not steps:
            print("%s: nothing to check for parts %s" % (unit, parts), file=out)
            bad += 1
            continue
        if named and "proofs" in want and not any(st.proof for st in h.statements.values()):
            # asked for proofs by name, a unit with none would pass on its statements alone: check-units.sh asks for
            # them only of a unit the plan lists in proof_units
            print("FAIL %s: nothing to check for part proofs: the unit has no proof (check it with --parts statements)"
                  % unit, file=out)
            bad += 1
            continue
        for label, step, passes in steps:
            try:
                step()
                examined += 1 if passes else 0
            except (CheckError, subprocess.TimeoutExpired, OSError) as e:
                print("FAIL %s: %s" % (label, e), file=out)
                bad += 1
        if rocqchk and checked:
            # With rocqchk, a proof passes only when the one rocqchk over every compiled wrapper of this harness passes.
            try:
                rocqchk_proofs(root, h, [c for _, c in checked], allow, work, out)
                examined += len(checked)
            except (CheckError, subprocess.TimeoutExpired, OSError) as e:
                for label, _ in checked:
                    print("FAIL %s: %s" % (label, e), file=out)
                bad += len(checked)
    print("oft check: %d step(s) passed, %d failed; work files in %s" % (examined, bad, work), file=out)
    return 1 if bad or not examined else 0


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
    c.add_argument("--timeout", type=int, default=600, help="seconds per counterexample or finding run")
    c.add_argument("--rocqchk", action="store_true",
                   help="also re-check the compiled libraries with rocqchk (slow: hours for a large proof)")
    c.add_argument("--record", action="store_true",
                   help="with --parts findings: run each finding that has no runs yet and print them, to commit")


def cli(root, a):
    return run(root, a.units, parts=a.parts, allowed=a.allowed, qemu=a.qemu, timeout=a.timeout,
               rocqchk=a.rocqchk, record=a.record)


if __name__ == "__main__":
    # `python3 -m oft.check`, as tools/oft/ci/check-units.sh runs it: the check without the modules of the other
    # commands, which are not part of the checker (keys.NOT_THE_CHECKER)
    import argparse
    p = argparse.ArgumentParser(prog="python3 -m oft.check", description="oft check")
    p.add_argument("--root", default=".", help="the repository root (default: .)")
    add_arguments(p)
    a = p.parse_args()
    sys.exit(cli(os.path.abspath(a.root), a))
