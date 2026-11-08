"""The work key of each contract file of a fuzz target (`oft plan --contracts`, contract_keys): which contracts need an
agent after a change, and never a basis for verdict reuse.  A proof imports its harness's whole image module
(Images.<Build>), which no contract key holds, and Rocq checks every proof in every run (OSSV-218).  No CI job reads
these keys, and `--contracts` refuses `--store`.  `oft prove` (prove.py) reads them to predict each contract's state.

This module is not the checker (keys.NOT_THE_CHECKER): no check reads a contract key or a symbol fact."""
import collections
import hashlib
import json
import re
import subprocess
import sys

from . import keys, layout, lint, names, rocq, symbols

# A Require command in a Rocq file with its comments and strings blanked (rocq.strip): the prefix From names, if it has
# one, and what follows Require up to the full stop that ends the sentence, a `.` before a blank or the end.
_REQUIRE = re.compile(r"(?<![\w'.])(?:From\s+([^\W\d][\w'.]*?)\s+)?Require(?![\w'])(.*?)\.(?=\s|\Z)", re.S)
# a qualified name in a Require command, and an import category in parentheses, which names no library
_QUALID = re.compile(r"(?<![\w'.])[^\W\d][\w']*(?:\.[^\W\d][\w']*)*")
_CATEGORY = re.compile(r"\([^()]*\)")


def blobs(repo, oids):
    """{object id: bytes} of each blob of oids in the repository at repo, read by one git cat-file --batch; keys.NoKey
    for an object git cannot give or that is no blob.  contract_keys and prove.py read files at a commit with it."""
    oids = list(dict.fromkeys(oids))
    if not oids:
        return {}
    done = subprocess.run(["git", "-C", repo, "cat-file", "--batch"], input="".join(o + "\n" for o in oids).encode(),
                          capture_output=True)
    if done.returncode != 0:
        raise keys.NoKey("git cat-file --batch: %s" % done.stderr.decode(errors="replace").strip())
    out, data, i = {}, done.stdout, 0
    for oid in oids:
        end = data.index(b"\n", i)
        head = data[i:end].split()
        if len(head) != 3 or head[1] != b"blob":
            raise keys.NoKey("git cat-file: %s is no blob" % oid)
        size = int(head[2])
        out[oid] = data[end + 1:end + 1 + size]
        i = end + 2 + size
    return out


def _read_rocq(data):
    """What a contract key reads of a Rocq file, data its bytes, its comments and strings blanked: ([(From prefix or
    None, library)] of the libraries its Require commands load; {(module, path): (line, name as written)} of the first
    reference to each definition of Symbols.v (symbols.reference, as lint's contract-literals reads one); [(line, name)]
    of each name that uses a module of Symbols.v as a whole outside a Require command: a build's module or one of its
    submodules (Symbols.Plain, Symbols.Plain.Sec, Plain.Size), or the root module itself (Symbols, or a path that ends
    in .Symbols: Import Symbols, Module S := Symbols); [(line, name)] of each bare build module name (Plain) outside a
    Require command; whether a Require Import or Export loads a library named Symbols, after which a bare Plain may be
    Symbols.Plain; and the SHA-256 of its code (rocq.code, every byte kept: its comments and layout left out), which
    identifies it as a file a contract requires."""
    code = rocq.code(data.decode("utf-8", "surrogateescape"))
    text = data.decode("utf-8", "replace")
    stripped = rocq.strip(text)
    requires, spans, imports_symbols = [], [], False
    for m in _REQUIRE.finditer(stripped):
        spans.append(m.span())
        words = _QUALID.findall(_CATEGORY.sub(" ", m.group(2)))
        libraries = [q for q in words if q not in ("Import", "Export")]
        requires += [(m.group(1), q) for q in libraries]
        imports_symbols |= words[:1] in (["Import"], ["Export"]) and any(q.rsplit(".", 1)[-1] == "Symbols"
                                                                        for q in libraries)
    refs, whole, bare = {}, [], []
    for n in symbols.ROCQ_NAME.finditer(stripped):
        token = n.group()
        ref = symbols.reference(token)
        if ref is not None and ref[1] not in symbols.MODULES:
            if ref in refs:
                continue
            into = None
        elif ref is not None:
            into = whole
        elif token in symbols.BUILD_OF or token.rsplit(".", 1)[-1].strip() == "Symbols":
            if any(a <= n.start() < b for a, b in spans):
                continue
            into = bare if token in symbols.BUILD_OF else whole
        else:
            continue
        at = (stripped.count("\n", 0, n.start()) + 1, " ".join(token.split()))
        if into is None:
            refs[ref] = at
        else:
            into.append(at)
    return (requires, refs, whole, bare, imports_symbols,
            hashlib.sha256(code.encode("utf-8", "surrogateescape")).hexdigest())


def _libraries(modules, prefix, library):
    """The paths of modules ({last name: [(module path, file)]}) that `From prefix Require library` may load, as Rocq
    9.2 finds a library (vernac/loadpath.ml, expand_path and locate_qualified_library): the module whose path is the
    whole name (prefix.library, or library with no prefix) when there is one, else each module whose path ends in
    library, a partly qualified name, under prefix when there is one.  Rocq refuses a name with several such modules,
    and takes a partly qualified name with no prefix only in a -R path: each extra file only makes a key read more."""
    whole = library if prefix is None else prefix + "." + library
    out = []
    for module, path in modules.get(library.rsplit(".", 1)[-1], ()):
        if module == whole:
            return [path]
        if not module.endswith("." + library):
            continue
        if prefix is not None and not (module.startswith(prefix + ".")
                                       and len(module) >= len(prefix) + 1 + len(library)):
            continue
        out.append(path)
    return out


def fact_ids(repo, units, commits):
    """{(unit, commit): {build: (path, object id)}} of each symbol fact (layout.symbol_fact) of each of units at each of
    commits, read by one git: where each fact is, for load_facts."""
    specs = {(u, c, b): "%s:%s" % (c, layout.symbol_fact(*u.split("/"), b))
             for u in units for c in commits for b in names.BUILD_MODULE}
    oids = keys.object_ids(repo, list(specs.values()))
    out = {(u, c): {} for u in units for c in commits}
    for (u, c, b), spec in specs.items():
        if oids[spec] != "-":
            out[u, c][b] = (spec.split(":", 1)[1], oids[spec])
    return out


def load_facts(repo, commit, facts_at):
    """{build: (path, object id, [symbols.Sym])} of each symbol fact facts_at lists ({build: (path, object id)}) at
    commit, read by one git.  keys.NoKey for a fact over symbols.CAP and one that does not parse."""
    data = blobs(repo, [oid for _path, oid in facts_at.values()])
    out = {}
    for build, (path, oid) in facts_at.items():
        try:
            if len(data[oid]) > symbols.CAP:
                raise ValueError("%d bytes, over the %d-byte cap" % (len(data[oid]), symbols.CAP))
            out[build] = (path, oid, symbols.parse(data[oid].decode("utf-8"))[1])
        except (ValueError, UnicodeDecodeError) as e:
            raise keys.NoKey("%s at %s: %s" % (path, commit, e))
    return out


def symbol_tables(loaded, commit):
    """{build: symbols.Table} of each symbol fact loaded (load_facts) at commit: what symbols.resolve resolves a
    reference against.  keys.NoKey for one whose names give one identifier twice."""
    tables = {}
    for build, (path, _oid, rows) in loaded.items():
        try:
            tables[build] = symbols.table(rows)
        except ValueError as e:
            raise keys.NoKey("%s at %s: %s" % (path, commit, e))
    return tables


def _symbol_id(row, sized):
    """The id of what a contract names from Symbols.v (row, a symbols.Sym; None, `-`, for one the fact lacks): its
    kind; the masked bytes of a function with a size and its targets (symbols.mask and symbols.target_id: the same
    function at another address has the same, and a function that calls or reads another symbol has other targets,
    though its masked bytes are the same), or the bytes of a data object or section with file contents; and its
    size, when it has no bytes or when a reference names its size.  Never its address: a contract names it from
    Symbols.v, which follows a move.

    A function whose targets are `?` has no id that says what it points at, so no key names it: the contract that
    does is unknown instead (_contract_components), and this id is never asked for one."""
    if row is None:
        return "-"
    parts = [row.kind]
    if row.kind == "func" and row.size:
        parts.append("masked " + row.masked)
        parts.append("targets " + row.targets)
    elif row.kind != "func" and row.exact != "-":
        parts.append("exact " + row.exact)
    else:
        sized = True
    if sized:
        parts.append("size %d" % row.size)
    return " ".join(parts)


# What the harness component leaves out of the statement folder, besides what the build key leaves out (README.md and
# the proofs, counterexamples and findings): harness.yaml, whose pins name the image (its statement fields reach
# Statements.v), images/ (the rules that build the image from the pinned binary), symbols/ and Symbols.v (the
# addresses: each symbol a contract names enters by itself, _symbol_id), and source/ (the fuzz target's source, which
# no Rocq file reads).  A work key leaves the image out on purpose.  Each Rocq file directly in the statement folder
# but Symbols.v (Statements.v, Images.v, Characterise.v, Distribution.v) is left out too: it enters the key of each
# contract that requires it by itself (harness/<file>), as a file of the proof library does.
HARNESS_DROP = ("README.md",) + layout.CHANGE_NAMES + ("harness.yaml", "images", "symbols", "Symbols.v", "source")

# One contract file at one commit: its key (None when unknown), {component: id}, its references (contract_keys),
# {"<build>:<name>": (build, symbols.Sym)} of each symbol component, and why its key is unknown, or None.
_Contract = collections.namedtuple("_Contract", "key comp references named unknown")


def _contract_components(repo, unit, commit, read):
    """{contract file: _Contract} of each contract file of unit at commit, in either layout (contract_keys says what
    its key holds).  read caches _read_rocq by object id across commits."""
    p, h = unit.split("/", 1)
    new, old = layout.proof_lib_dir(p, h, layout.NEW), layout.proof_lib_dir(p, h, layout.OLD)
    statements = layout.statement_dir(p, h)
    attrs = keys.Attributes(repo, commit, (statements, old, "theories", "toolchain/allowed-axioms.txt",
                                           "dune-project"))
    lib, _drop = attrs.either(unit, new, old)
    blob = {path: e.split()[2] for path, e in attrs.entry.items() if e.split()[1] == "blob"}
    contracts = sorted(path for path in blob if path.startswith(lib + "/") and lint.CONTRACT_FILE.match(path))
    if not contracts:
        return {}
    namespace, opam_stem = keys.release_names(repo, commit)
    # the modules a Require may load: each file of the proof library, and each Rocq file directly in the statement
    # folder but Symbols.v (the statement library: dune's include_subdirs gives a file in a subfolder another path)
    named = {}   # file: its component name
    for path in blob:
        folder, _, name = path.rpartition("/")
        if path.startswith(lib + "/") and path.endswith(".v"):
            named[path] = "lib/" + path[len(lib) + 1:]
        elif folder == statements and name.endswith(".v") and name not in HARNESS_DROP:
            named[path] = "harness/" + name
    prefix = {"lib": names.rocq_proof(namespace, p, h, "lib"), "harness": names.rocq_harness(namespace, p, h)}
    modules = {}
    for path, name in named.items():
        top, rel = name.split("/", 1)
        module = prefix[top] + "." + rel[:-len(".v")].replace("/", ".")
        modules.setdefault(module.rsplit(".", 1)[-1], []).append((module, path))
    # the files each file requires, read level by level, one git per level
    edges, todo, seen = {}, contracts, set(contracts)
    while todo:
        data = blobs(repo, [blob[f] for f in todo if blob[f] not in read])
        read.update((oid, _read_rocq(text)) for oid, text in data.items())
        later = []
        for f in todo:
            edges[f] = {d for frm, library in read[blob[f]][0] for d in _libraries(modules, frm, library) if d != f}
            later += [d for d in sorted(edges[f]) if d not in seen]
            seen.update(edges[f])
        todo = later
    facts_at = {b: (rel, blob[rel]) for b, rel in ((b, layout.symbol_fact(p, h, b)) for b in names.BUILD_MODULE)
                if rel in blob}
    tables = symbol_tables(load_facts(repo, commit, facts_at), commit)
    # the proof environment, as the build key holds it (keys.keys), less what HARNESS_DROP and the statement library
    # leave out of the statement folder: every proof is checked against it
    harness_drop = HARNESS_DROP + tuple(name[len("harness/"):] for name in named.values()
                                        if name.startswith("harness/"))
    environment = {"harness": attrs.id(statements, harness_drop), "theories": attrs.id("theories"),
                   "allowed-axioms": attrs.id("toolchain/allowed-axioms.txt"),
                   "dune-project": keys.dune_project(repo, commit, [p], attrs, opam_stem)[p],
                   "checker": keys.checker(repo, commit), "image": keys.images(repo, commit)[0]}
    out = {}
    for contract in contracts:
        required, stack = set(), [contract]
        while stack:
            for d in edges[stack.pop()] - required - {contract}:
                required.add(d)
                stack.append(d)
        files = [contract] + sorted(required)
        comp = dict(environment, contract=attrs.id(contract))
        # a file it requires by its mode, its code and its checkout attributes: a change to its comments or layout
        # alone, which Rocq does not read, changes no key
        comp.update((named[d], "%s %s %s" % (attrs.entry[d].split()[0], read[blob[d]][5], attrs.of(d)))
                    for d in required)
        # what keeps a contract from a key that looks complete, in file order (the contract, then the files it
        # requires) and line order: a module of Symbols.v used as a whole brings names into scope that no reference
        # shows (Import Symbols.Plain, then s_x; Module S := Symbols, then S.Plain.s_x), a reference to a build
        # with no symbol fact, or to a name its fact gives Symbols.v no identifier for, reads no bytes, and a
        # function whose targets are `?` has an immediate the fact cannot say what points at, so no key of it can
        # say that a call or a read of it changed (symbols.target_id)
        imports_symbols = any(read[blob[f]][4] for f in files)
        references, found, problems = {}, {}, []
        for i, f in enumerate(files):
            where = named[f]
            _requires, refs, whole, bare, _imports, _code = read[blob[f]]
            problems += [(i, line, "%s:%d: %s is used as a module, so the names it brings into scope cannot be read"
                          % (where, line, name)) for line, name in whole + (bare if imports_symbols else [])]
            for (module, path), (line, written) in refs.items():
                build = symbols.BUILD_OF[module]
                row, sized = symbols.resolve(tables.get(build), path)
                references.setdefault((build, path), {
                    "build": build, "written": path, "name": None if row is None else row.name,
                    "status": "unresolved" if row is None else "resolved", "kind": None if row is None else row.kind})
                if row is None:
                    problems.append((i, line, "%s:%d: %s cannot be resolved: %s" % (
                        where, line, written, "%s has no symbol fact" % build if build not in tables else
                        "the symbol fact of %s has no row that Symbols.v names %s" % (build, path))))
                else:
                    found[build, row.name] = (row, sized or found.get((build, row.name), (row, False))[1])
                    if row.kind == "func" and row.size and row.targets == "?":
                        problems.append((i, line, "%s:%d: %s is a function with an address immediate that the "
                                         "symbol fact of %s cannot resolve, so no key says what it points at"
                                         % (where, line, written, build)))
        comp.update(("%s:%s" % (b, n), _symbol_id(row, sized)) for (b, n), (row, sized) in found.items())
        why = min(problems)[2] if problems else None
        key = None if why else keys.digest("%s=%s" % kv for kv in comp.items())
        out[contract] = _Contract(key, comp, [references[r] for r in sorted(references)],
                                  {"%s:%s" % (b, n): (b, row) for (b, n), (row, _sized) in found.items()}, why)
    return out


def _size(named, component):
    """{"kind", "size"} of the symbol component of named (_Contract.named), or None where it names none."""
    _build, row = named.get(component, (None, None))
    return None if row is None else {"kind": row.kind, "size": row.size}


def _difference(component, now, old):
    """One component of a contract's key whose id differs between old (at the base) and now (_Contract), as data."""
    if component in now.named or component in old.named:
        build, row = now.named.get(component) or old.named[component]
        return {"component": component, "type": "symbol", "build": build, "name": row.name,
                "before": _size(old.named, component), "after": _size(now.named, component)}
    kind = ("contract" if component == "contract" else "library" if component.startswith(("lib/", "harness/"))
            else "environment")
    return {"component": component, "type": kind, "build": None, "name": None, "before": None, "after": None}


def contract_keys(repo, unit, ref, base=None):
    """{contract file: row} of each contract file of unit (lint.CONTRACT_FILE: a <fn>_c.v under Prog/ of its proof
    library, in either layout) at commit ref, judged against commit base when given.

    The key is a work key: it says which contracts need an agent after a change, and is never a basis for verdict
    reuse.  A proof imports its harness's whole image module (Images.<Build>), which no key here holds.  The key is
    the SHA-256 of

        contract        the id of the contract file (keys.Attributes.id: its mode, blob id and checkout attributes)
        lib/<path>      the code id of each .v file of the unit's proof library that the contract requires,
                        transitively (a Require command whose library is a module of the proof library)
        harness/<file>  the code id of each Rocq file directly in the statement folder but Symbols.v (Statements.v,
                        Images.v, Characterise.v, Distribution.v) that the contract requires, transitively, as a file
                        of the proof library: a module of the statement library (names.rocq_harness)
        harness, theories, allowed-axioms, dune-project
                        the proof environment, as the build key holds it (keys.keys), but for what HARNESS_DROP leaves
                        out of the statement folder: harness.yaml, images/, symbols/, Symbols.v and source/, and the
                        Rocq files of the statement library, which a contract's key holds only when it requires them
        <build>:<name>  for each function, data object or section the contract or those files name from Symbols.v
                        (Symbols.<Build>.s_<name>, .Size.s_<name>, .Sec.s_<name>, as lint's contract-literals reads a
                        reference), from the symbol fact at ref: _symbol_id, its masked bytes or bytes, and its size
                        when it has no bytes or a reference names its size
        checker, image  the checker of the tools at ref (keys.checker) and the checker image release.yaml at ref pins

    A file's code id is its mode, the SHA-256 of its code (rocq.code, as a statement's fingerprint reads Statements.v:
    its comments and layout left out, which Rocq does not read) and its checkout attributes: a comment in a file many
    contracts require changes no key.  No address is in the key: a function that moves with the same masked bytes
    keeps it, and oft classify reports the move.

    Each row is

        state           "keyed", or "unknown" when the contract or a file it requires uses a module of Symbols.v as a
                        whole (an Import or a module alias of a build's module, of one of its submodules or of the root
                        module Symbols), so that a name it makes visible cannot be read, or names one that cannot be
                        resolved (its build has no symbol fact, or the fact gives Symbols.v no identifier for it)
        key             the key, or None when unknown
        unknown         why the key is unknown, where (the first such place, in file and line order), or None
        references      {"build", "written", "name", "status", "kind"} of each reference of the contract and of the
                        files it requires to Symbols.v, by build and then written: written is its path in the build's
                        module as the reference writes it (s_<name>, Size.s_<name>, Sec.s_<name>, Sec.Size.s_<name>);
                        status "resolved", with the name and kind of the symbol fact's row it names, or "unresolved",
                        with None for both.  An identifier is never read as a symbol's name: it names the row the
                        fact's identifiers give it (names.symbol_idents), or none
        base            "no base", "not at the base", "unknown at the base", or "keyed at the base"
        base_unknown    why the key at the base is unknown, or None
        changed         when both keys are known, {"component", "type", "build", "name", "before", "after"} of each
                        component whose id differs at the base, by component: type "contract", "library" (lib/<path>
                        or harness/<file>), "environment" or "symbol", which has its build, its name and {"kind",
                        "size"} at the base (before) and at ref (after), None where it names nothing (the others have
                        None for all four); else None
        why             text from them: unknown; else the base when no key there is compared; else "changed: " and
                        the components, or "unchanged from the base" when none differs."""
    read = {}
    now = _contract_components(repo, unit, ref, read)
    before = _contract_components(repo, unit, base, read) if base is not None and now else None
    out = {}
    for contract, c in now.items():
        old = None if before is None else before.get(contract)
        at_base = ("no base" if before is None else "not at the base" if old is None
                   else "unknown at the base" if old.unknown else "keyed at the base")
        changed = None
        if c.unknown is None and at_base == "keyed at the base":
            changed = [_difference(n, c, old) for n in sorted(c.comp.keys() | old.comp.keys())
                       if c.comp.get(n) != old.comp.get(n)]
        if c.unknown:
            why = c.unknown
        elif changed is None:
            why = at_base
        else:
            why = "changed: " + ", ".join(d["component"] for d in changed) if changed else "unchanged from the base"
        out[contract] = {"state": "unknown" if c.unknown else "keyed", "key": c.key, "unknown": c.unknown,
                         "references": c.references, "base": at_base,
                         "base_unknown": None if old is None else old.unknown, "changed": changed, "why": why}
    return out


def contract_files(repo, unit, commit):
    """The contract files of unit at commit (lint.CONTRACT_FILE), sorted, in the layout its proof library has there,
    read by one git ls-tree: the files contract_keys keys at that commit.  keys.NoKey when the library is in both
    layouts, as contract_keys refuses it."""
    p, h = unit.split("/", 1)
    new, old = layout.proof_lib_dir(p, h, layout.NEW), layout.proof_lib_dir(p, h, layout.OLD)
    paths = [path for _mode, kind, _oid, path in keys.ls_tree(repo, "-r", commit, "--", new, old) if kind == "blob"]
    if any(x.startswith(new + "/") for x in paths) and any(x.startswith(old + "/") for x in paths):
        raise keys.NoKey("%s: in both layouts" % unit)
    return sorted(x for x in paths if lint.CONTRACT_FILE.match(x))


def run(root, unit, change="HEAD", base=None, out=sys.stdout):
    """`oft plan --contracts`: contract_keys of unit at change, judged against base, as JSON; 1 when unit has no
    contract file at change."""
    got = contract_keys(root, unit, change, base)
    if not got:
        print("%s: no contract file at %s" % (unit, change), file=out)
        return 1
    json.dump(got, out, sort_keys=True)
    out.write("\n")
    return 0


