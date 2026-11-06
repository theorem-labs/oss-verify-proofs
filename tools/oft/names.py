"""Public names: Rocq identifiers, statement names, file names.

Every name is computed from typed fields; nothing parses an old name to
recover a fact (statement_builds looks a name up among the names
statement_name computes).  `ident` must be injective over each population it
is used on (projects; the harnesses of one project), which `oft lint` checks;
and the identifiers Symbols.v defines for a build (rocq_idents) must be
distinct, which `oft generate` checks (rules.symbol_facts).
"""
import collections
import re

# The Rocq namespace of the theories and the stem of the opam packages of a release that names neither in its
# release.yaml (`namespace`, `opam_stem`: facts.Tree.namespace, facts.Tree.opam_stem).  Every name below takes the
# namespace or the stem from its caller, which reads it from the tree: nothing here knows which release it names.
NAMESPACE_DEFAULT = "OssFuzzTheorems"
OPAM_STEM_DEFAULT = "oss-fuzz-theorems"
# plus api-driver for OSS-Fuzz targets; patches and unpatched-bin are a project's own folders (tools/oft/layout.py)
RESERVED_HARNESS_NAMES = {"images", "source", "bin", "proofs", "patches", "unpatched-bin"}
API_DRIVER = "api-driver"

BUILD_IDENT = {"plain": "plain", "ubsan": "ubsan", "asan": "asan", "asan-ubsan": "asan_ubsan"}
BUILD_MODULE = {"plain": "Plain", "ubsan": "Ubsan", "asan": "Asan", "asan-ubsan": "AsanUbsan"}
BUILD_WORDS = {"plain": "plain", "ubsan": "UBSan", "asan": "ASan", "asan-ubsan": "ASan+UBSan"}


def ident(name):
    """A Rocq identifier for an OSS-Fuzz project or harness name."""
    s = re.sub(r"[^A-Za-z0-9_]", "_", name)
    if s[:1].isdigit():
        s = "h_" + s
    return s


def rocq_ident(name):
    """The Rocq identifier Symbols.v gives a function or data object of a build's symbol fact: s_ and its name, with
    each character outside [A-Za-z0-9_] written _ (rocq_idents refuses two names that give one identifier)."""
    return "s_" + re.sub(r"[^A-Za-z0-9_]", "_", name)


def section_ident(name):
    """The Rocq identifier Symbols.v gives an allocated section of a build in the build's module Sec: rocq_ident of its
    name less one leading . (.got gives s_got)."""
    return rocq_ident(name[1:] if name.startswith(".") else name)


def rocq_idents(fact_names, ident_of=rocq_ident):
    """{name: ident_of(name)}, in their order, of the names of one namespace of a build's symbol fact (one per row)
    that the build's module of Symbols.v defines, the address under the identifier and the size under the same
    identifier in the module's Size: every name one row alone has.  A name two or more rows share is left out, since
    one identifier cannot name them all (musl's static dummy, which several of its files define).  ValueError, naming
    them, for two names that give one identifier."""
    count = collections.Counter(fact_names)
    out, given = {}, collections.defaultdict(list)
    for name in count:
        if count[name] == 1:
            out[name] = ident_of(name)
            given[out[name]].append(name)
    clashes = [(ns, ident_) for ident_, ns in sorted(given.items()) if len(ns) > 1]
    if clashes:
        raise ValueError("two names give one identifier of Symbols.v, which names each s_<name> with each character "
                         "outside [A-Za-z0-9_] written _ (a section's name less its leading .): " + "; ".join(
                             "%s and %r %s give %s" % (", ".join(map(repr, ns[:-1])), ns[-1],
                                                      "both" if len(ns) == 2 else "all", ident_)
                             for ns, ident_ in clashes))
    return out


def symbol_idents(rows):
    """(idents, sections) of one build's symbol fact (rows with a name and a kind, symbols.Sym): rocq_idents of its
    functions' and data objects' names, which Symbols.v defines in the build's module, and rocq_idents under
    section_ident of its sections' names, which it defines in the module's Sec, a namespace of their own.  ValueError
    as rocq_idents."""
    return (rocq_idents([r.name for r in rows if r.kind != "section"]),
            rocq_idents([r.name for r in rows if r.kind == "section"], section_ident))


def release_names(release):
    """(namespace, opam stem) that release.yaml's data `release` names (`namespace`, `opam_stem`), each the default when
    it names none: the one rule of facts.Tree, facts.read_release_names and keys.release_names."""
    release = release if isinstance(release, dict) else {}
    ns, stem = release.get("namespace"), release.get("opam_stem")
    return (ns if isinstance(ns, str) and ns else NAMESPACE_DEFAULT,
            stem if isinstance(stem, str) and stem else OPAM_STEM_DEFAULT)


def rocq_core(namespace):
    """The theory of theories/: the shapes and image definitions every harness requires."""
    return "%s.Core" % namespace


def rocq_tests(namespace):
    """The theory of tests/: the one a hand-written dune file may declare (keys.check_hand_dune)."""
    return "%s.Tests" % namespace


def rocq_harness(namespace, project, harness):
    return "%s.%s.%s" % (namespace, ident(project), ident(harness))


def rocq_proof(namespace, project, harness, statement):
    return "%s.Proofs.%s.%s.%s" % (namespace, ident(project), ident(harness), statement)


def opam_package(opam_stem, project):
    return "rocq-%s-%s" % (opam_stem, project)


def build_file(harness, build):
    return "%s.%s" % (harness, build)


def statement_name(kind, builds, reading):
    """The one name a statement with these fields may have."""
    san = BUILD_IDENT[builds[-1]]
    if kind == "halts":
        return san + ("_halts_may_fail" if reading == "may-fail" else "_halts")
    if kind == "agreement":
        return san + "_agrees"
    if kind == "bound":
        return san + "_disagrees_at_most"
    if kind == "decidability":
        return san + "_agreement_decidable"
    raise ValueError(kind)


_STATEMENT_BUILDS = dict(
    [(statement_name("agreement", ("plain", b), None), ("plain", b)) for b in BUILD_IDENT if b != "plain"] +
    [(statement_name("halts", (b,), r), (b,)) for b in BUILD_IDENT for r in ("budget", "may-fail")])


def statement_builds(name):
    """The builds of the agreement or halts statement that statement_name gives this name, or None for any other
    name.  `oft ledger` and lint's base comparison read a finding's own files only, so they take its statements'
    builds from their names."""
    return _STATEMENT_BUILDS.get(name)


def statement_id(project, harness, statement):
    return "%s/%s/%s" % (project, harness, statement)
