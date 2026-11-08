"""Where a fuzz target's proofs, counterexamples and findings live.

Two layouts.  Every tool reads both while the repository moves from the first to the second:

  old  proofs/<p>/<h>/<statement>/            counterexamples/<p>/<h>/<statement>/
       proofs/<p>/<h>/lib/                    findings/<p>/<h>/<slug>/, findings/<p>/<h>/series
       proofs/<p>/<h>/provenance/             findings/<p>/unpatched.yaml
                                              patches/<p>/
  new  projects/<p>/<h>/proofs/<statement>/   projects/<p>/<h>/counterexamples/<statement>/
       projects/<p>/<h>/proofs/lib/           projects/<p>/<h>/findings/<slug>/, projects/<p>/<h>/findings/series
       projects/<p>/<h>/proofs/provenance/    projects/<p>/unpatched.yaml
                                              projects/<p>/patches/

The statement folder, projects/<p>/<h>/, is the same in both: a fuzz target's proofs, counterexamples and findings
move into it, and a project's unpatched.yaml and patches into its project folder.  `oft port-layout` moves an
old-layout tree to the new one (`moved` says where each path goes); proofs/lib/ and proofs/lib-lean/ have no place in
the new layout.

Every path of either layout is built here, so that no other module spells one out.  A tree holds a fuzz target's
proofs, counterexamples and findings in one layout at a time: the loader (facts.load) refuses a unit that is in both.
"""
import os
import subprocess

OLD = "old"
NEW = "new"
LAYOUTS = (OLD, NEW)

# the top-level folders of the old layout
OLD_TOPS = ("proofs", "counterexamples", "findings", "patches")
# the entries of projects/<p>/<h>/ that a change brings (a pull request that is not a release changes only these)
CHANGE_NAMES = ("proofs", "counterexamples", "findings")
# old-layout folders the new layout gives no place: no fuzz target's
NO_PLACE = ("proofs/lib", "proofs/lib-lean")
# The names under which dune reads build rules in a directory, whatever the layout.  keys.py holds every file with
# one of these names on a unit's build path, and refuses the hand-written ones a build could read (check_hand_dune);
# check.py refuses any build file in a proof library or above it but the two oft generate renders (_lib_targets).
# One tuple, so that a name dune gains or loses cannot reach one of them alone.
DUNE_FILES = ("dune", "dune-file", "dune-project", "dune-workspace")

# -------------------------------------------------------------------------------------------- one fuzz target


def statement_dir(project, harness):
    """The fuzz target's statement folder (harness.yaml, Statements.v, images/).  The same in both layouts."""
    return "projects/%s/%s" % (project, harness)


def symbol_fact(project, harness, build):
    """The build's symbol fact (`oft symbols`), in the statement folder: the same in both layouts."""
    return "%s/symbols/%s.tsv" % (statement_dir(project, harness), build)


def split_unit(unit):
    """(project, harness) of a fuzz target named <project>/<harness>, as a command takes one; ValueError for any other
    text: not two parts, or an empty, `.` or `..` part."""
    parts = unit.split("/")
    if len(parts) != 2 or any(p in ("", ".", "..") for p in parts):
        raise ValueError("a unit is <project>/<harness>, not %r" % unit)
    return parts[0], parts[1]


def proofs_dir(project, harness, layout):
    """The folder of the fuzz target's proofs: its statement directories, its proof library and its build record."""
    return "proofs/%s/%s" % (project, harness) if layout == OLD else "projects/%s/%s/proofs" % (project, harness)


def proof_dir(project, harness, statement, layout):
    """One statement's proof: Proof.v (or Refutation.v), proof.yaml, dune."""
    return "%s/%s" % (proofs_dir(project, harness, layout), statement)


def proof_lib_dir(project, harness, layout):
    """The fuzz target's proof library, shared by its proofs and compiled once."""
    return "%s/lib" % proofs_dir(project, harness, layout)


def provenance_dir(project, harness, layout):
    """The build record of the binaries the fuzz target's proofs are about."""
    return "%s/provenance" % proofs_dir(project, harness, layout)


def record_path(project, harness, layout):
    """The build record itself, PROVENANCE.yaml."""
    return "%s/PROVENANCE.yaml" % provenance_dir(project, harness, layout)


def counterexamples_dir(project, harness, layout):
    """The folder of the fuzz target's counterexample directories."""
    return ("counterexamples/%s/%s" % (project, harness) if layout == OLD
            else "projects/%s/%s/counterexamples" % (project, harness))


def counterexample_dir(project, harness, statement, layout):
    """One statement's counterexample: input.bin, control.bin, expect.yaml."""
    return "%s/%s" % (counterexamples_dir(project, harness, layout), statement)


def findings_dir(project, harness, layout):
    """The folder of the fuzz target's findings, the library bugs found while proving."""
    return ("findings/%s/%s" % (project, harness) if layout == OLD
            else "projects/%s/%s/findings" % (project, harness))


def finding_dir(project, harness, slug, layout):
    """One finding: finding.yaml, input.bin, control.bin and its patch."""
    return "%s/%s" % (findings_dir(project, harness, layout), slug)


def series_path(project, harness, layout):
    """The fuzz target's findings series."""
    return "%s/series" % findings_dir(project, harness, layout)


def barrier_dirs(project, harness):
    """The new layout's folders inside the statement folder that its statement theory must not take: each holds a
    generated dune file (include_subdirs no)."""
    return proofs_dir(project, harness, NEW), counterexamples_dir(project, harness, NEW)


# -------------------------------------------------------------------------------------------- one project


def unpatched_path(project, layout):
    """The pins of the unpatched binaries the project's findings run on."""
    return "findings/%s/unpatched.yaml" % project if layout == OLD else "projects/%s/unpatched.yaml" % project


def patches_dir(project, layout):
    """The project's patches."""
    return "patches/%s" % project if layout == OLD else "projects/%s/patches" % project


def unpatched_bin_dir(project):
    """Where `oft fetch --findings` unpacks the project's unpatched binaries: never tracked, the same whatever the
    layout of the findings."""
    return "projects/%s/unpatched-bin" % project


# the names under projects/<p>/ that are no fuzz target's folder
NOT_A_HARNESS = ("bin", "patches", "unpatched-bin")

# -------------------------------------------------------------------------------------------- whole paths


def moved(rel):
    """Where an old-layout path goes in the new layout, by prefix, whatever its name: everything under
    proofs/<p>/<h>/, counterexamples/<p>/<h>/, findings/<p>/<h>/ and patches/<p>/, and findings/<p>/unpatched.yaml.
    None for any other path: one that is not in the old layout, or that the new layout gives no place (proofs/lib/,
    proofs/lib-lean/, a file directly under proofs/<p>/, findings/<p>/bin/ that `oft fetch --findings` filled)."""
    parts = rel.split("/")
    top = parts[0]
    if top in ("proofs", "counterexamples", "findings") and len(parts) > 3:
        if "/".join(parts[:2]) in NO_PLACE or (top == "findings" and parts[2] == "bin"):
            return None
        return "projects/%s/%s/%s/%s" % (parts[1], parts[2], top, "/".join(parts[3:]))
    if top == "findings" and len(parts) == 3 and parts[2] == "unpatched.yaml":
        return unpatched_path(parts[1], NEW)
    if top == "patches" and len(parts) > 2:
        return "%s/%s" % (patches_dir(parts[1], NEW), "/".join(parts[2:]))
    return None


def canonical(rel):
    """rel in the new layout: where it moves, or rel itself when it does not move."""
    return moved(rel) or rel


def is_change(rel):
    """Whether rel is a file a change brings in either layout: under proofs/, counterexamples/ or findings/, under
    projects/<p>/<h>/proofs/, counterexamples/ or findings/, or a projects/<p>/unpatched.yaml.  Everything else is
    the facts (or tools, or generated)."""
    parts = rel.split("/")
    if parts[0] in CHANGE_NAMES:
        return True
    if parts[0] != "projects":
        return False
    return (len(parts) >= 4 and parts[3] in CHANGE_NAMES) or (len(parts) == 3 and parts[2] == "unpatched.yaml")


def unit_of(rel):
    """"<project>/<harness>" of a file of one fuzz target in either layout (its statement folder, proofs,
    counterexamples or findings); None for any other path."""
    rel = canonical(rel)
    parts = rel.split("/")
    if parts[0] == "projects" and len(parts) > 3 and parts[2] not in NOT_A_HARNESS:
        return "%s/%s" % (parts[1], parts[2])
    return None


def of_path(rel):
    """OLD for a path under an old-layout top folder, NEW for a path in one of the new layout's places for what the
    old layout kept outside projects/, None for any other path (a statement folder's own files among them)."""
    parts = rel.split("/")
    if parts[0] in OLD_TOPS:
        return OLD
    if parts[0] == "projects" and ((len(parts) >= 4 and (parts[3] in CHANGE_NAMES or parts[2] == "patches"))
                                   or (len(parts) == 3 and parts[2] == "unpatched.yaml")):
        return NEW
    return None


def of_tree(root):
    """OLD when any old-layout top folder under root holds a file, else NEW.  findings/<p>/bin/, which `oft fetch
    --findings` filled before the new layout and git never tracks, does not count, nor does a build's _build/."""
    for top in OLD_TOPS:
        base = os.path.join(root, top)
        for dp, dns, fns in os.walk(base):
            rel = os.path.relpath(dp, root).replace(os.sep, "/").split("/")
            dns[:] = [d for d in dns if d not in ("_build", ".git")
                      and not (top == "findings" and len(rel) == 2 and d == "bin")]
            if fns:
                return OLD
    return NEW


# -------------------------------------------------------------------------- a workspace that holds some libraries
#
# A Legion issue pod writes the proof library of the fuzz targets its issue names and no other
# (.legion/hooks/checkout, INFRA-1385 R8).  A tool that reads the working tree across units would then
# read an empty place where a library is and answer as if the library held nothing, so each such tool
# refuses instead and names the two commands that add it (INFRA-1385 R12): a check must never pass on a
# tree it did not read.


def _git(root, *args):
    """`git -C root args`, or None where git cannot answer: it failed, or there is no git here.  A check
    image carries no git at all (toolchain/runner.Dockerfile), and a missing program raises rather than
    failing, so this is what keeps a tool that asks these questions running everywhere."""
    try:
        done = subprocess.run(["git", "-C", root, *args], capture_output=True, text=True)
    except OSError:
        return None
    return done.stdout if done.returncode == 0 else None


def sparse(root):
    """Whether root's working copy holds a part of its commit: git's sparse checkout is on.

    git's own patterns are the question, not jj's: Legion requires that the two agree before it records
    a checkout (INFRA-1385 R3), and a refusal needs the commit's directories, which only git gives
    (_tracked_dirs).  False where git cannot answer, so a directory that is no git repository, which is
    what a unit's view is (`oft check --facts-from`), is never refused."""
    out = _git(root, "config", "--bool", "--get", "core.sparseCheckout")
    return out is not None and out.strip() == "true"


def _tracked_dirs(root):
    """Every directory of root's HEAD commit, from git, or None when git cannot answer."""
    out = _git(root, "ls-tree", "-r", "-d", "--name-only", "HEAD")
    return None if out is None else set(out.splitlines())


def _left_out(root, lib):
    """Whether the working copy leaves lib out because it is sparse: git's index marks at least one file under it
    skip-worktree (`git ls-files -t` writes `S`).  A library the change itself removed -- `git rm`, an `rm -rf`, a
    move to the other layout -- keeps its entries, which git tags `H`, so this is False for it and the tool reads
    the tree as the change left it.  False where git cannot answer."""
    out = _git(root, "ls-files", "-t", "--", lib + "/")
    if out is None:
        return False
    return any(line.startswith("S ") for line in out.splitlines())


def unwritten_libraries(root, units):
    """[(unit, its proof library)] for each unit of units whose proof library the commit holds, the working copy
    does not, and git's index marks skip-worktree (_left_out): the libraries a sparse workspace left unwritten.
    [] in a full working copy, [] when git cannot say what the commit holds, and [] for a library the change
    itself removed, which is the tree as its author means it."""
    if not sparse(root):
        return []
    tracked = _tracked_dirs(root)
    if tracked is None:
        return []
    missing = []
    for unit in units:
        try:
            project, harness = split_unit(unit)
        except ValueError:
            continue
        for lay in LAYOUTS:
            lib = proof_lib_dir(project, harness, lay)
            if lib in tracked and not os.path.isdir(os.path.join(root, lib)) and _left_out(root, lib):
                missing.append((unit, lib))
    return missing


def cone(root):
    """Whether root's sparse checkout is git's cone mode, which takes a directory path and refuses a pattern
    (`/<dir>/` exits 128 there).  A pod's is not: the hook writes patterns (INFRA-1385 R8)."""
    out = _git(root, "config", "--bool", "--get", "core.sparseCheckoutCone")
    return out is not None and out.strip() == "true"


def unwritten_libraries_message(what, missing, root=None):
    """What a tool prints when it refuses: what it would have read, and the two commands that add each
    library (jj's and git's own, as Legion adds none of its own).  git's command is the one this workspace
    takes: a directory in cone mode, a pattern otherwise (cone)."""
    lines = ["FAIL %s reads the working tree of %d fuzz target(s) whose proof library this sparse workspace "
             "does not hold, so it would answer on files it did not read:" % (what, len(missing))]
    for unit, lib in missing:
        lines.append("  %s: %s" % (unit, lib))
    lines.append("Add each library, then run this again:")
    in_cone = root is not None and cone(root)
    for _unit, lib in missing:
        lines.append("  jj sparse set --add %s" % lib)
        lines.append("  git sparse-checkout add %s" % (lib if in_cone else "/%s/" % lib))
    return "\n".join(lines)


# -------------------------------------------------------------------------------------------- regular expressions
#
# For the rules that match a path by a regular expression.  Each lists the old layout's shape first, then the new one.

# one fuzz target's proofs folder; proofs/lib/ and proofs/lib-lean/ are no fuzz target's
PROOF_HARNESS_RE = r"(?:proofs/(?!lib/|lib-lean/)[^/]+/[^/]+|projects/[^/]+/[^/]+/proofs)"
# the same with its project captured: group 1 in the old layout, group 2 in the new, so that `(?:\1|\2)` later in the
# pattern names the same project (a back-reference to a group that did not match never matches)
PROOF_HARNESS_PROJECT_RE = r"(?:proofs/((?!lib/|lib-lean/)[^/]+)/[^/]+|projects/([^/]+)/[^/]+/proofs)"
# a file of one finding's directory
FINDING_FILE_RE = r"(?:findings/[^/]+/[^/]+|projects/[^/]+/[^/]+/findings)/[^/]+/"
# a project's unpatched.yaml, its project captured: group 1 in the old layout, group 2 in the new
UNPATCHED_FILE_RE = r"(?:findings/([^/]+)|projects/([^/]+))/unpatched\.yaml$"
