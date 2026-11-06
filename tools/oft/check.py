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
  proofs           build the harness's proof library, lib/ in its proofs
                   folder (proofs/<p>/<h>/, or projects/<p>/<h>/proofs/ in
                   the per-project layout; layout.py), if it has one, with dune
                   (once; dune's cache may supply it), then compile each proof
                   directory <s>/ there afresh with `rocq compile` against the
                   statements and the library, then a
                   wrapper this tool writes, which ascribes the proof's theorem
                   to the statement and prints its assumptions; every
                   assumption must be in toolchain/allowed-axioms.txt.  The
                   kernel checks every term as it compiles.
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

Each part fails when it examined nothing it was asked to examine: a unit
with no statement Statements.v defines fails statements, and a unit with no
proof fails when --parts names proofs.  Without --parts, a unit is checked
on each of statements, proofs and counterexamples that it has.

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
                    unit fails when its file is missing, malformed, of another
                    format version or of another unit, when the file's
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

from . import facts, fetch, layout, names, render, rules, schema, yamlio

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


def check_statements(root, h, allowed, work, out, rocqchk=False):
    if not h.builds():
        raise CheckError("every build is withheld: nothing to check")
    listed = sorted(st.name for st in h.statements.values() if st.rendered())
    if not listed:
        raise CheckError("every statement harness.yaml lists is withheld or withdrawn, so Statements.v defines none: "
                         "nothing to check")
    if not os.path.isfile(os.path.join(root, h.dir, "Statements.v")):
        raise CheckError("%s/Statements.v is missing (run ./oft generate)" % h.dir)
    if fetch.verify_builds(root, h, out)[1]:
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
    if _run(["rocq", "compile", "-w", "-all"] + _loadpath(build, h)
            + ["-Q", d, "OftDefined", os.path.join(d, "Defined.v")], d, log) != 0:
        raise CheckError("%s/Statements.v does not define every statement harness.yaml lists (%s; see %s)"
                         % (h.dir, ", ".join(listed), log))
    axioms = read_assumptions(d, log)
    stated = sorted(s for s in listed if "%s.%s" % (stmt_mod, s) in axioms)
    if stated:
        raise CheckError("%s/Statements.v states %s as an axiom (Axiom, Parameter or Admitted), not a definition (see "
                         "%s)" % (h.dir, ", ".join(stated), log))
    outside = sorted(axioms - allowed)
    if outside:
        raise CheckError("%s/Statements.v: the statements assume axioms outside the allowlist: %s (see %s)"
                         % (h.dir, ", ".join(outside), log))


def compile_lib(root, h, work, libs, out):
    """The -Q mapping of h's proof library, lib/ in its proofs folder (Tree.proof_libs), as
    <namespace>.Proofs.<p>.<h>.lib (every .v at any depth), or [] when h has none.  Built once per check run by
    dune, from the rocq.theory stanza of oft generate's lib/dune, against the statements in root's _build; `libs` holds
    the mapping, or the error, per harness.  dune takes a file from its cache (DUNE_CACHE) only when the file's sources,
    its dependencies and the Rocq binary all hash the same as when the cached copy was compiled."""
    if h.dir in libs:
        if isinstance(libs[h.dir], CheckError):
            raise libs[h.dir]
        return libs[h.dir]
    rel = h.tree.proof_libs.get("%s/%s" % (h.project.name, h.name))
    if rel is None:
        libs[h.dir] = []
        return []
    try:
        targets = _lib_targets(root, h, rel, out)
        log = os.path.join(work, "%s.%s.lib.dune.log" % (names.ident(h.project.name), names.ident(h.name)))
        rc = _run(["dune", "build", "--root", root, "--display", "short", "-j", str(len(os.sched_getaffinity(0)))]
                  + targets, root, log)
        if rc != 0:
            raise _failed_run(rel, log, rc, work)
    except CheckError as e:
        libs[h.dir] = e
        raise
    libs[h.dir] = ["-Q", os.path.join(root, "_build", "default", rel),
                   names.rocq_proof(h.tree.namespace, h.project.name, h.name, "lib")]
    print("%s: %d files compiled or taken from dune's cache (log %s)" % (rel, len(targets), log), file=out)
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
    p, hn = h.project.name, h.name
    # neither directory is above an old-layout library, proofs/<p>/<h>/lib/
    rendered = {os.path.join(layout.proofs_dir(p, hn, layout.NEW), "dune"): generate.barrier_dune(),
                os.path.join(layout.statement_dir(p, hn), "dune"): generate.harness_dune(h)}
    src = os.path.join(root, rel)
    d = rel
    while True:
        for f in layout.DUNE_FILES if d != rel else ():
            path = os.path.join(d, f)
            if path == "dune-project" or not os.path.lexists(os.path.join(root, path)):
                continue
            if path not in rendered:
                raise CheckError("%s: no directory above a proof library holds a build file" % path)
            if not _holds_exactly(os.path.join(root, path), rendered[path]):
                raise CheckError("%s: differs from its rendering (run ./oft generate)" % path)
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


def _holds_exactly(path, text):
    """Whether path is a regular file, not a symbolic link, whose bytes are text's."""
    if os.path.islink(path) or not os.path.isfile(path):
        return False
    with open(path, "rb") as f:
        return f.read() == text.encode("utf-8")


def check_proof(root, st, pd, allowed, work, out, libs, rocqchk=False):
    """Compile one proof directory afresh, against the statements in root's _build and its harness's proof library, then
    the wrapper, and audit the wrapper's assumptions.  With rocqchk, return what rocqchk_proofs needs."""
    h = st.harness
    p, hn, s = st.id.split("/")
    proof_mod = names.rocq_proof(h.tree.namespace, p, hn, s)
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
        rc = _run(["rocq", "compile"] + q + [f], d, log)
        if rc != 0:
            raise _failed_run(pd.path, log, rc, work)
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
    if _run(["rocq", "compile", "-w", "-all"] + wq + [os.path.join(wdir, "Wrapper.v")], d, wlog) != 0:
        raise CheckError("%s: the wrapper does not type-check: the proof is not of this statement (see %s)"
                         % (pd.path, wlog))
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
    folder = layout.proofs_dir(h.project.name, h.name, h.tree.unit_layout("%s/%s" % (h.project.name, h.name)))
    print("%s: rocqchk over the wrappers of %d proof(s): %d axioms, all allowed" % (folder, len(checked), n), file=out)


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


def proofs_apart(root, unit, h, sts, allowed, jobs, work, out, libs, facts_from=None):
    """Check the proofs of the statements sts of harness h, each in a process of its own (`python3 -m oft.check --root
    ROOT UNIT --parts proofs --statements S --lib DIR`), at most jobs at once, against the statements in root's _build
    and h's library, built here once (compile_lib) and handed to each process with --lib, so no process runs dune.
    With facts_from, each process reads the unit's facts from there too (--facts-from), as this one did: root may be
    a view of the unit, which no process loads whole.  Each process takes this one's measured stack
    (--stack-from-parent, prepare_stack).  A statement passes only when its process exits 0 and its output holds
    check_proof's own line for it (proof_claim); a process that a signal ends, that exits non-zero, that ends without
    that line, or that does not start fails it, and one that ran out of stack (stack_exhausted, on its output and its
    exit) fails it as `stack exhausted ...`.  Returns (passed, failed)."""
    root = os.path.abspath(root)
    try:
        libq = compile_lib(root, h, work, libs, out)
    except (CheckError, subprocess.TimeoutExpired, OSError) as e:
        for st in sts:
            print("FAIL %s: %s" % (st.proof.path, e), file=out)
        return 0, len(sts)
    here = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    env = dict(os.environ, PYTHONPATH=os.pathsep.join(
        [here] + [p for p in os.environ.get("PYTHONPATH", "").split(os.pathsep) if p]))
    logs = tempfile.mkdtemp(prefix="statements-", dir=work)
    print("%s: %d statement(s) with a proof, each in a process of its own, %d at a time"
          % (unit, len(sts), min(jobs, len(sts))), file=out, flush=True)
    pending, running, passed, failed = list(sts), {}, 0, 0
    while pending or running:
        while pending and len(running) < jobs:
            st = pending.pop(0)
            log = os.path.join(logs, st.name + ".log")
            cmd = [sys.executable, "-m", "oft.check", "--root", root, unit, "--parts", "proofs", "--statements",
                   st.name, "--allowed", allowed, "--stack-from-parent"] + (["--lib", libq[1]] if libq else []) + (
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


def stack_exhausted(text, returncode):
    """Whether a step ran out of stack: Rocq reported OCaml's Stack_overflow (`Error: Stack overflow.`), a child oft's
    own line says so (`: stack exhausted `, for --proof-jobs, whose rocq writes into the child's compile.log), the
    process died of SIGSEGV (or exited 139, as a shell reports it), or dune reports that a process it ran did (`(got
    signal SEGV)`: dune itself then exits 1, as compile_lib's library build does)."""
    return ("Error: Stack overflow." in text or ": stack exhausted " in text or "(got signal SEGV)" in text
            or returncode in (-signal.SIGSEGV, 128 + signal.SIGSEGV))


def _failed_run(path, log, rc, work):
    """The CheckError of a compile of path that exited rc, its output in log: `<path>: stack exhausted ...` when
    stack_exhausted holds (stack_exhausted_words), else `<path>: does not compile`."""
    with open(log, encoding="utf-8", errors="replace") as f:
        text = f.read()
    why = stack_exhausted_words(work) if stack_exhausted(text, rc) else "does not compile"
    return CheckError("%s: %s (see %s)" % (path, why, log))


# The parts `oft check` runs when --parts is not given: each of them that the unit has.
DEFAULT_PARTS = "statements,proofs,counterexamples"


def run(root, units, parts=None, allowed="toolchain/allowed-axioms.txt",
        qemu="qemu-riscv64", timeout=600, rocqchk=False, record=False, facts_to=None, facts_from=None,
        statements=None, lib=None, proof_jobs=1, stack_from_parent=False, out=sys.stdout):
    """parts: the comma-separated parts to check, where naming proofs refuses a unit with no proof; None (no --parts)
    checks each part of DEFAULT_PARTS that the unit has, so an unproved unit is checked on its statements.

    facts_to    a directory; load the facts of the whole tree, check its rules, write each unit's facts there
                (write_facts) and check nothing
    facts_from  a directory facts_to wrote; check each unit with its facts from there (read_facts), without loading
                the tree or checking its rules, so root may hold that unit's files alone; each statement's process
                (proof_jobs) reads them too
    statements  the statements whose proofs are checked (default: every one with a proof); each must have one
    lib         the unit's proof library as compile_lib built it, to use instead of building it here
    proof_jobs  with more than 1, each statement's proof is checked in a process of its own (proofs_apart), as many
                at once, after one build of the library; rocqchk keeps one process
    stack_from_parent  this is such a process: it prints its parent's measured stack, not its own (prepare_stack)

    Before it checks statements or proofs it sets the stack limit, measures the stack and prints it (prepare_stack)."""
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
    if (statements is not None or lib is not None) and (len(units) != 1 or want != {"proofs"}):
        print("FAIL --statements and --lib check the proofs of one unit: give one unit and --parts proofs", file=out)
        return 1
    if statements is not None and not statements:
        print("FAIL --statements names no statement", file=out)
        return 1
    if proof_jobs < 1:
        print("FAIL --proof-jobs must be at least 1", file=out)
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
    libs = {}  # harness dir -> its proof library's -Q mapping, or the error compiling it
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
                print("FAIL %s: %s" % (unit, e), file=out)
                bad += 1
                continue
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
            steps.append(("statements", lambda h=h: check_statements(root, h, allow, work, out, rocqchk), True))
        for st in h.statements.values():
            if st in proved and not apart:
                steps.append((st.proof.path, lambda st=st: checked.append((st.proof.path, check_proof(
                    root, st, st.proof, allow, work, out, libs,
                    rocqchk))), not rocqchk))
            if st.counterexample and "counterexamples" in want:
                steps.append((st.counterexample.path, lambda st=st: check_counterexample(
                    root, st, st.counterexample, qemu, timeout, work, out), True))
        for f in sorted(h.tree.findings.values(), key=lambda f: f.path) if "findings" in want else []:
            if f.unit == unit:
                steps.append((f.path, lambda f=f: check_finding(root, h, f, qemu, timeout, work, out, record), True))
        if not steps and not apart:
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
        if apart:
            passed, failed = proofs_apart(root, unit, h, apart, allowed, proof_jobs, work, out, libs, facts_from)
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
    if memory:
        memory.finish()
    print("oft check: %d step(s) passed, %d failed; work files in %s" % (examined, bad, work), file=out)
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
        raise facts.UnitFactsError("no facts file %s (write it with --facts-to)" % path)
    try:
        return facts.load_unit(root, yamlio.load_file(path), unit, parts)
    except yamlio.YamlError:
        raise
    except facts.UnitFactsError as e:
        raise facts.UnitFactsError("%s: %s" % (path, e)) from None
    except (KeyError, TypeError, AttributeError, ValueError) as e:
        raise facts.UnitFactsError("%s: not a facts file of version %d: %s %s"
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
                  % (self.unit, self.peak / (1 << 30), len(os.sched_getaffinity(0))), file=sys.stderr)


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
                        "the unit's proof library (default 1: one after another in this process)")
    # proofs_apart's per-statement process: it prints its parent's measured stack (prepare_stack); not for people
    c.add_argument("--stack-from-parent", action="store_true", help=argparse.SUPPRESS)


def cli(root, a):
    return run(root, a.units, parts=a.parts, allowed=a.allowed, qemu=a.qemu, timeout=a.timeout,
               rocqchk=a.rocqchk, record=a.record, facts_to=a.facts_to, facts_from=a.facts_from,
               statements=a.statements, lib=a.lib and os.path.abspath(a.lib), proof_jobs=a.proof_jobs,
               stack_from_parent=a.stack_from_parent)


if __name__ == "__main__":
    # `python3 -m oft.check`, as tools/oft/ci/check-units.sh runs it: the check without the modules of the other
    # commands, which are not part of the checker (keys.NOT_THE_CHECKER)
    p = argparse.ArgumentParser(prog="python3 -m oft.check", description="oft check")
    p.add_argument("--root", default=".", help="the repository root (default: .)")
    add_arguments(p)
    a = p.parse_args()
    sys.exit(cli(os.path.abspath(a.root), a))
