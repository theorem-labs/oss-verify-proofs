"""The paths of each part of a unit's check that the part's content key holds (keys.py digests their entries), and
the view of them that CI checks the part in (tools/oft/ci/check-units.sh).  A view holds those paths and nothing else
of the tree, so a check reads no file of another unit, and no change that the key misses can change its result.

    every part      the statement folder projects/<p>/<h>/, but its README.md and the proofs, counterexamples and
                    findings the per-project layout puts in it (drop); projects/<p>/project.yaml and every
                    projects/<p>/*/harness.yaml
    build           the unit's proofs folder, theories/, toolchain/allowed-axioms.txt; of dune-project, the forms
                    that a build of p's harnesses reads (dune_project_forms)
    counterexamples the unit's counterexamples folder
    findings        the unit's findings folder, its project's unpatched.yaml

Each in either layout (layout.py): the proofs folder is proofs/<p>/<h>/ in the old one and projects/<p>/<h>/proofs/ in
the per-project one, and so on (own gives each path in a layout; a unit has them in one layout at a time).  The
per-project layout's proofs and counterexamples folders each hold the dune file oft generate writes there, the barrier
that keeps the statement theory out of them: the folder's own component leaves it out (paths.is_gen: lint holds it to
its rendering), the unit's build key holds it as a file of its build path (keys._dune_path), and the view holds it,
since a build reads it.

A view holds two more groups of files.  The first is the binaries that `oft fetch` put in place: projects/<p>/bin/<h>/
for build and counterexamples, and projects/<p>/unpatched-bin/<h>/ for findings (layout.unpatched_bin_dir).  No key
holds them by path, since harness.yaml and unpatched.yaml (in the key) pin each one's SHA-256 and the check verifies
them.  The second is a dune-project that holds only the forms dune_project_forms keeps, so a check can read of it only
what the key holds.  The checker (tools/), whose id is in every key, is mounted beside the view.  The facts come from
`oft check --facts-to` on the whole tree, in a file of the unit's own.

    python3 -m oft.unitpaths --root ROOT --part PART [--dune-project-to FILE] PROJECT/HARNESS

prints each path of the view of that part that exists under ROOT, one per line, with dune-project left out.  For
build, --dune-project-to writes the view's dune-project to FILE, its package stanzas named by the opam stem ROOT's
release.yaml names (facts.read_release_names).  This module imports nothing of oft but names and layout, and facts for
that stem, so check-units.sh can run it as it runs the checker (keys.NOT_THE_CHECKER)."""
import argparse
import os
import re
import sys

from . import layout, names

PARTS = ("build", "counterexamples", "findings")
# What the statement folder's component leaves out: its README.md (generated, and no check reads it) and the folders
# of each part that the per-project layout puts in it, each another component.
HARNESS_DROP = ("README.md",) + layout.CHANGE_NAMES


def own(unit, part, unit_layout=layout.NEW):
    """{component: path} of the paths of unit's part that its key holds, by component name, with the unit's proofs,
    counterexamples and findings in unit_layout (layout.OLD or layout.NEW)."""
    p, h = unit.split("/", 1)
    out = {"harness": layout.statement_dir(p, h)}
    if part == "build":
        out.update({"proofs": layout.proofs_dir(p, h, unit_layout), "theories": "theories",
                    "allowed-axioms": "toolchain/allowed-axioms.txt"})
    elif part == "counterexamples":
        out["counterexamples"] = layout.counterexamples_dir(p, h, unit_layout)
    elif part == "findings":
        out.update({"findings": layout.findings_dir(p, h, unit_layout),
                    "unpatched": layout.unpatched_path(p, unit_layout)})
    else:
        raise ValueError("no part %r" % part)
    return out


def drop(name, unit_layout):
    """The names that component name of own(..., unit_layout) leaves out of what the key holds of it: the statement
    folder's HARNESS_DROP, and the barrier dune file of a per-project proofs or counterexamples folder."""
    if name == "harness":
        return HARNESS_DROP
    if name in ("proofs", "counterexamples") and unit_layout == layout.NEW:
        return ("dune",)
    return ()


def project_files(p, subdirs):
    """The files of project p that every part's key holds: projects/<p>/project.yaml and the harness.yaml of each of
    subdirs, the directories in projects/<p>/, but those that are no fuzz target's (layout.NOT_A_HARNESS: bin/,
    patches/, unpatched-bin/).  The other files directly in projects/<p>/, its README.md and its .opam file, are
    generated, and no check reads them."""
    return ["projects/%s/project.yaml" % p] + ["projects/%s/%s/harness.yaml" % (p, d) for d in subdirs
                                               if d not in layout.NOT_A_HARNESS]


def binaries(unit, part):
    """The directory that `oft fetch` puts the binaries of unit's part in (with --findings for findings)."""
    p, h = unit.split("/", 1)
    if part == "findings":
        return "%s/%s" % (layout.unpatched_bin_dir(p), h)
    return "projects/%s/bin/%s" % (p, h)


def forms(text, name="dune-project"):
    """The top-level forms of the dune file name, each as its text, read as dune's lexer reads them
    (otherlibs/stdune/src/dune_sexp/lexer.mll): a comment runs from ';' to the end of its line, '#' and '|' are atom
    characters, a string that opens with "\\| or "\\> is a block string that runs to the end of its line, and any other
    string runs to its closing quote, past backslash escapes.  Raises ValueError for a file it cannot read."""
    out, depth, start, i, n = [], 0, None, 0, len(text)
    while i < n:
        c = text[i]
        if c == ";" or text.startswith(('"\\|', '"\\>'), i):
            j = text.find("\n", i)
            i = n if j < 0 else j
            continue
        if c == '"':
            i += 1
            while i < n and text[i] != '"':
                i += 2 if text[i] == "\\" else 1
            if i >= n:
                raise ValueError("%s: a string with no closing quote" % name)
        elif c == "(":
            if depth == 0:
                start = i
            depth += 1
        elif c == ")":
            depth -= 1
            if depth == 0:
                out.append(text[start:i + 1])
            elif depth < 0:
                raise ValueError("%s: a ')' with no '('" % name)
        i += 1
    if depth:
        raise ValueError("%s: a '(' with no ')'" % name)
    return out


PACKAGE = re.compile(r"\(package\s+\(name\s+([^\s()]+)\)")


def dune_packages(p, opam_stem):
    """The packages of dune-project whose stanzas a build of project p's harnesses reads, named by the release's opam
    stem (facts.Tree.opam_stem): the core's, the meta package's (whose name is the prefix of every project's), and p's
    own two, its statements' and its proofs'."""
    return [names.opam_package(opam_stem, "core"), names.opam_package(opam_stem, "")[:-1],
            names.opam_package(opam_stem, p), names.opam_package(opam_stem, p) + "-proofs"]


def dune_project_forms(parsed, p, opam_stem):
    """(the forms of parsed, dune-project's forms as forms() reads them, that are not package stanzas, {package: its
    stanza} of dune_packages(p, opam_stem) that it has, those two together in dune-project's order).  oft generate
    writes a stanza per project, so a project added to the tree changes none of this for another project."""
    shared, package, ordered = [], {}, []
    wanted = set(dune_packages(p, opam_stem))
    for form in parsed:
        m = PACKAGE.match(form)
        if m is None:
            shared.append(form)
        elif m.group(1) in wanted:
            package[m.group(1)] = form
        else:
            continue
        ordered.append(form)
    return shared, package, ordered


def view(root, unit, part):
    """The paths, relative to root, of the view of unit's part that exist under root, sorted, dune-project left out:
    own(unit, part) in the layout the unit has under root (each path a change brings in the layout root has it in, as
    keys.py takes it at the change; ValueError for one in both layouts), the statement folder as its entries but
    HARNESS_DROP, as the key holds it; project_files; and binaries(unit, part); less any path under another of them."""
    p, _h = unit.split("/", 1)
    project = os.path.join(root, "projects", p)
    subdirs = sorted(d for d in os.listdir(project) if os.path.isdir(os.path.join(project, d))) \
        if os.path.isdir(project) else []
    new, old = own(unit, part, layout.NEW), own(unit, part, layout.OLD)
    wanted = []
    for name, rel in new.items():
        if rel != old[name]:
            here = [r for r in (rel, old[name]) if os.path.lexists(os.path.join(root, r))]
            if len(here) == 2:
                raise ValueError("in both layouts: %s and %s" % tuple(here))
            rel = here[0] if here else rel
        if name == "harness":
            d = os.path.join(root, rel)
            wanted += ["%s/%s" % (rel, e) for e in (sorted(os.listdir(d)) if os.path.isdir(d) else [])
                       if e not in HARNESS_DROP]
        else:
            wanted.append(rel)
    rels = {rel for rel in wanted + project_files(p, subdirs) + [binaries(unit, part)]
            if os.path.lexists(os.path.join(root, rel))}
    real = os.path.realpath(root)
    for rel in rels:
        if os.path.realpath(os.path.join(root, rel)) != os.path.join(real, rel):
            # a mount follows a symbolic link to wherever it points
            raise ValueError("%s is or is under a symbolic link" % rel)
    return sorted(rel for rel in rels if not any(rel.startswith(o + "/") for o in rels))


def main(argv=None):
    a = argparse.ArgumentParser(prog="python3 -m oft.unitpaths", description=__doc__.split("\n\n")[0])
    a.add_argument("--root", required=True)
    a.add_argument("--part", required=True, choices=PARTS)
    a.add_argument("--dune-project-to", metavar="FILE",
                   help="build only: write the view's dune-project, the forms dune_project_forms keeps, to FILE")
    a.add_argument("unit", metavar="PROJECT/HARNESS")
    args = a.parse_args(argv)
    if not re.fullmatch(r"[^./\s:,][^/\s:,]*/[^./\s:,][^/\s:,]*", args.unit):
        a.error("%r is not PROJECT/HARNESS" % args.unit)
    if (args.dune_project_to is not None) != (args.part == "build"):
        a.error("--dune-project-to goes with --part build, and build needs it")
    try:
        rels = view(args.root, args.unit, args.part)
        if args.dune_project_to is not None:
            from . import facts   # the tree's opam stem, by facts.Tree's rule; only here, so the rest needs no YAML
            with open(os.path.join(args.root, "dune-project"), encoding="utf-8") as f:
                ordered = dune_project_forms(forms(f.read()), args.unit.split("/", 1)[0],
                                             facts.read_release_names(args.root)[1])[2]
            with open(args.dune_project_to, "w", encoding="utf-8") as f:
                f.write("\n\n".join(ordered) + "\n")
    except ValueError as e:
        sys.exit("%s: %s" % (args.unit, e))
    for rel in rels:
        if re.search(r"[\s:,]", rel):
            sys.exit("%s: a path a mount cannot name" % rel)
    print("".join(rel + "\n" for rel in rels), end="")
    return 0


if __name__ == "__main__":
    sys.exit(main())
