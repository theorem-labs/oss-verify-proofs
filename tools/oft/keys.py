"""The content key of each part of a unit's check, and the passes recorded under those keys.

A unit is a harness <p>/<h>.  A check job checks up to three parts of it: build (its statements and proofs, in the
checker image), counterexamples and findings (both in the runner image).  The key of a part is the SHA-256 of the
git object ids of what that part's check reads, so a part whose key has a recorded pass is not checked again:

    every part      projects/<p>/<h>/; projects/<p>/project.yaml and every projects/<p>/*/harness.yaml (`oft fetch`
                    unpacks a project's archive only when every harness's builds are in it); the
                    checker (NOT_THE_CHECKER says what is not)
    build           proofs/<p>/<h>/, proofs/lib/; theories/; toolchain/allowed-axioms.txt (the rest of toolchain/
                    builds the images, whose digests are keyed); of dune-project, what the project's build reads
                    (_dune_project); the checker image; whether rocqchk runs
    counterexamples counterexamples/<p>/<h>/; the runner image
    findings        findings/<p>/<h>/, findings/<p>/unpatched.yaml; the runner image

A part's components come from two commits: `facts`, the commit whose statements are checked, and `change`, the
commit whose proofs/, counterexamples/ and findings/ are checked.  They are one commit for a release; for any other
change, pr.yml checks the base's statements with the change's proofs, counterexamples and findings.

Each path's id is its git object id and a digest of the checkout attributes of its files (CHECKOUT_ATTRIBUTES), since
a .gitattributes change alters the bytes a check reads without changing a blob.

Tree-wide state is in no key: the facts' rules, and the dune files of the whole tree, which dune reads for any build.
The facts' rules can only turn a pass into a failure; every `oft check` checks them first, and so does pr.yml's lint
job.  A dune file could also turn a failure into a pass, by declaring a theory a build finds before the installed one
(dune looks in the workspace first).  The dune files oft generate writes cannot (paths.is_gen): each names only its
own unit's theories, and lint holds them to their rendering.  Every other dune file is hand-written (tests/,
theories/, or one lint admits in a fuzz target's source/ or a proof's provenance/), and a plan refuses one that
could (check_hand_dune), in the tree it checks and in the change, so what is left can only fail a build.

A plan reads the passes recorded on the branch check-results (oft plan --store), one file per pass:
units/<p>/<h>/<part>/<key>.json.  No workflow of this repository writes or reads that branch."""
import bisect
import hashlib
import re
import subprocess

import yaml

from . import names, paths

PARTS = ("build", "counterexamples", "findings")
# Raised when what a key reads changes, so that no key computed the old way can equal one computed the new way.
VERSION = "1"
# The files of tools/oft/ that a check never opens.  Every other file of tools/ is the checker, whose ids are in every
# key: `python3 -m oft.check` and `python3 -m oft.fetch`, as check-units.sh runs them, open no file this matches
# (test_keys.Checker says so).  generate.py, paths.py and templates/proof-dune.tmpl are the checker: oft check
# renders each proof library's lib/dune itself, with them.
NOT_THE_CHECKER = re.compile(
    r"(?:__main__\.py|lint\.py|lint-exceptions\.yaml|urls\.py|ledger\.py|approvals\.py"
    r"|release_tree\.py|revisions\.py|plan\.py|README\.md|templates/(?!proof-dune\.tmpl$).*|tests/.*"
    r"|ci/facts-review-.*)")
STORE_BRANCH = "check-results"


class NoKey(Exception):
    """A key that cannot be computed: a commit or a file git cannot read, or a dune file no key can hold."""


def _git(repo, *args, stdin=None):
    done = subprocess.run(["git", "-C", repo, *args], input=stdin, capture_output=True, text=True)
    if done.returncode != 0:
        raise NoKey("git %s: %s" % (" ".join(args), done.stderr.strip()))
    return done.stdout


def _digest(lines):
    return hashlib.sha256("".join(l + "\n" for l in sorted(lines)).encode()).hexdigest()


def object_ids(repo, specs):
    """{spec: object id, or "-" for a path that does not exist} for each "<commit>:<path>" in specs, in one git."""
    specs = list(dict.fromkeys(specs))
    if not specs:
        return {}
    lines = _git(repo, "cat-file", "--batch-check=%(objectname)", stdin="".join(s + "\n" for s in specs)).splitlines()
    if len(lines) != len(specs):
        raise NoKey("git cat-file answered %d of %d paths" % (len(lines), len(specs)))
    return {s: ("-" if l.endswith(" missing") else l) for s, l in zip(specs, lines)}


def _ls_tree(repo, *args):
    """[(type, object id, path)] of `git ls-tree -z args`."""
    rows = []
    for rec in _git(repo, "ls-tree", "-z", *args).split("\0"):
        if rec:
            meta, path = rec.split("\t", 1)
            _mode, kind, oid = meta.split()
            rows.append((kind, oid, path))
    return rows


def checker(repo, commit):
    """The id of the checker in the tools at commit: a digest of the path, blob id and checkout attributes of each
    file of tools/ (a check job copies all of it and puts it on PYTHONPATH) but the files of tools/oft/ that
    NOT_THE_CHECKER names."""
    rows = [(oid, path) for _kind, oid, path in _ls_tree(repo, "-r", commit, "--", "tools/")
            if not (path.startswith("tools/oft/") and NOT_THE_CHECKER.fullmatch(path[len("tools/oft/"):]))]
    if not any(path.startswith("tools/oft/") for _oid, path in rows):
        raise NoKey("%s has no tools/oft/" % commit)
    attrs = _Attributes(repo, commit, ("tools",))
    return _digest("%s=%s %s" % (path, oid, attrs.of(path)) for oid, path in rows)


def images(repo, commit):
    """(checker image, runner image) as release.yaml at commit pins them."""
    try:
        data = yaml.safe_load(_git(repo, "show", "%s:release.yaml" % commit))
        return data["images"]["checker"], data["images"]["runner"]
    except (NoKey, yaml.YAMLError, TypeError, KeyError) as e:
        raise NoKey("release.yaml at %s names no images.checker and images.runner (%s)" % (commit, e))


# The attributes that change the bytes git checks a file out as (gitattributes(5)).
CHECKOUT_ATTRIBUTES = ("text", "eol", "crlf", "filter", "ident", "working-tree-encoding")


class _Attributes:
    """The checkout attributes of every file under some paths at one commit, as git check-attr --source gives them:
    a .gitattributes change alters the bytes a check reads without changing a blob, so a component's id carries a
    digest of its files' attributes too."""

    def __init__(self, repo, commit, paths):
        files = [p for _kind, _oid, p in _ls_tree(repo, "-r", commit, "--", *paths)]
        out = _git(repo, "check-attr", "-z", "--stdin", "--source=%s" % commit, *CHECKOUT_ATTRIBUTES,
                   stdin="".join(p + "\0" for p in files)).split("\0")
        lines = {}
        for i in range(0, len(out) - 2, 3):
            path, attr, value = out[i:i + 3]
            if value != "unspecified":
                lines.setdefault(path, []).append("%s:%s=%s" % (path, attr, value))
        self.files = sorted(lines)
        self.lines = lines

    def of(self, path):
        """A digest of the attributes of path and of every file under it."""
        lo = bisect.bisect_left(self.files, path)
        hi = bisect.bisect_left(self.files, path + "/\uffff")
        return _digest(l for p in self.files[lo:hi] if p == path or p.startswith(path + "/") for l in self.lines[p])


def _project(repo, commit, p, attrs):
    """A digest of projects/<p>/project.yaml and of each projects/<p>/*/harness.yaml, at commit, with their
    attributes.  The other files directly in projects/<p>/, its README.md and its .opam file, are generated and no
    check reads them; a proof re-renders the README."""
    rows = _ls_tree(repo, commit, "--", "projects/%s/" % p)
    paths = {path: oid for kind, oid, path in rows if kind == "blob" and path.rsplit("/", 1)[-1] == "project.yaml"}
    ids = object_ids(repo, ["%s:%s/harness.yaml" % (commit, path) for kind, _oid, path in rows if kind == "tree"])
    paths.update({spec.split(":", 1)[1]: oid for spec, oid in ids.items()})
    return _digest("%s=%s %s" % (path, oid, attrs.of(path)) for path, oid in paths.items())


def _forms(text, name="dune-project"):
    """The top-level forms of the dune file name, each as its text, read as dune's lexer reads them
    (otherlibs/stdune/src/dune_sexp/lexer.mll): a comment runs from ';' to the end of its line, '#' and '|' are atom
    characters, a string that opens with "\\| or "\\> is a block string that runs to the end of its line, and any other
    string runs to its closing quote, past backslash escapes."""
    forms, depth, start, i, n = [], 0, None, 0, len(text)
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
                raise NoKey("%s: a string with no closing quote" % name)
        elif c == "(":
            if depth == 0:
                start = i
            depth += 1
        elif c == ")":
            depth -= 1
            if depth == 0:
                forms.append(text[start:i + 1])
            elif depth < 0:
                raise NoKey("%s: a ')' with no '('" % name)
        i += 1
    if depth:
        raise NoKey("%s: a '(' with no ')'" % name)
    return forms


PACKAGE = re.compile(r"\(package\s+\(name\s+([^\s()]+)\)")


def _dune_project(repo, commit, projects, attrs):
    """{project: id} of what a build of a project's harnesses reads from dune-project at commit: every form but the
    package stanzas, and the stanzas of the core's package, the meta package and the project's own two, its statements'
    and its proofs'.  oft generate writes a stanza per project, so adding a project changes no other project's id.  A
    stanza another project's dune files name and dune-project lacks fails dune for every build; the controls, which
    run whenever a dune file changes, build with every one."""
    ids = object_ids(repo, ["%s:dune-project" % commit])
    if ids["%s:dune-project" % commit] == "-":
        return {p: "-" for p in projects}
    shared, package = [], {}
    for form in _forms(_git(repo, "show", "%s:dune-project" % commit)):
        m = PACKAGE.match(form)
        if m:
            package[m.group(1)] = form
        else:
            shared.append(form)
    # the meta package's name is the prefix of every project's
    common = shared + [package.get(n, "-") for n in (names.opam_package("core"), names.opam_package("")[:-1])]
    return {p: _digest(common + [package.get(names.opam_package(p), "-"),
                                 package.get(names.opam_package(p) + "-proofs", "-"), attrs.of("dune-project")])
            for p in projects}


DUNE_FILES = ("dune", "dune-project", "dune-workspace", "dune-file")
FACTS_PATHS = ("projects", "theories", "toolchain/allowed-axioms.txt", "dune-project")
CHANGE_PATHS = ("proofs", "counterexamples", "findings")


# The dune files oft generate writes, which lint holds to their rendering, each naming only its own unit's theories,
# are the ones tools/oft/paths.py calls generated (is_gen): its placeholders refuse a segment that is not a name, so
# projects/<p>/bin/dune, which lint never reads (paths.IGNORED_PATTERNS), is hand-written.  proofs/lib/ is keyed whole
# (proofs-lib); every other dune file is hand-written.
# What a hand-written dune file may hold: none of it can change what a statements or proof build of any harness
# compiles.  A rule's targets are in its own directory, and the only theory it may declare is the tests' own.
# theories/dune declares the core, whose directory is in every build's key, and holds nothing else.
HAND_DUNE_STANZAS = {"rule", "alias", "rocq.theory", "coq.theory", "include_subdirs", "data_only_dirs", "dirs"}
HAND_THEORY = re.compile(r"OssFuzzTheorems\.Tests(?:\.[^\s()]+)?")
THEORIES_DUNE_STANZAS = {"rocq.theory", "coq.theory"}


def check_hand_dune(repo, facts, change=None):
    """Refuse (NoKey) a hand-written dune file a check's dune reads that could turn a failing build into a passing
    one, which no key would hold: one that declares a theory a build could find before the installed one (dune looks
    in the workspace first), or holds a stanza HAND_DUNE_STANZAS does not name (include, subdir, a library: what it
    brings in cannot be seen here).  Every file with a dune file's name that paths.is_gen does not call generated, but
    dune-project (_dune_project): from change under proofs/, counterexamples/ and findings/, and from facts
    elsewhere."""
    for commit, in_change in ((facts, False), (change or facts, True)):
        for _kind, _oid, path in _ls_tree(repo, "-r", commit):
            if (path.rsplit("/", 1)[-1] not in DUNE_FILES or path == "dune-project" or paths.is_gen(path)
                    or path.startswith(tuple(p + "/" for p in CHANGE_PATHS)) != in_change):
                continue
            allowed = THEORIES_DUNE_STANZAS if path == "theories/dune" else HAND_DUNE_STANZAS
            for form in _forms(_git(repo, "show", "%s:%s" % (commit, path)), path):
                head = re.match(r"\(\s*([^\s()]+)", form)
                if not head or head.group(1) not in allowed:
                    raise NoKey("%s: a hand-written dune file with a %s stanza, which could change what a build "
                                "compiles" % (path, head.group(1) if head else "nameless"))
                if head.group(1) in ("rocq.theory", "coq.theory") and path != "theories/dune":
                    # the stanza's fields as dune reads them, so a comment or a string cannot hold a second name
                    fields = _forms(form[form.index(head.group(1)) + len(head.group(1)):-1], path)
                    names = [m.group(1) for m in (re.fullmatch(r"\(\s*name\s+([^\s()\"]+)\s*\)", f) for f in fields)
                             if m]
                    if len(names) != 1 or not HAND_THEORY.fullmatch(names[0]):
                        raise NoKey("%s: a hand-written dune file declares the theory %s, which a build could find "
                                    "before the installed one; only OssFuzzTheorems.Tests may be declared outside the "
                                    "generated files" % (path, " and ".join(names) or "with no plain (name ...) field"))


def keys(repo, wanted, facts, change, tools, rocqchk=False):
    """{(unit, part): (key, {component: id})} for each (unit, part) in wanted, with the statements of commit facts,
    the proofs/, counterexamples/ and findings/ of commit change, and the checker of the tools at commit tools.  A
    component's id is its object id and a digest of its files' checkout attributes; "-" is a path that does not
    exist."""
    checker_id = checker(repo, tools)
    checker_image, runner_image = images(repo, facts)
    attrs = {facts: _Attributes(repo, facts, FACTS_PATHS + (CHANGE_PATHS if change == facts else ()))}
    if change != facts:
        attrs[change] = _Attributes(repo, change, CHANGE_PATHS)
    projects = sorted({u.split("/", 1)[0] for u, _ in wanted})
    project = {p: _project(repo, facts, p, attrs[facts]) for p in projects}
    dune_project = _dune_project(repo, facts, projects, attrs[facts])
    if any(part == "build" for _u, part in wanted):
        check_hand_dune(repo, facts, change)
    specs = {}
    for unit, part in wanted:
        p, h = unit.split("/", 1)
        own = {"harness": (facts, "projects/%s/%s" % (p, h))}
        if part == "build":
            own.update({"proofs": (change, "proofs/%s/%s" % (p, h)), "proofs-lib": (change, "proofs/lib"),
                        "theories": (facts, "theories"),
                        "allowed-axioms": (facts, "toolchain/allowed-axioms.txt")})
        elif part == "counterexamples":
            own["counterexamples"] = (change, "counterexamples/%s/%s" % (p, h))
        elif part == "findings":
            own.update({"findings": (change, "findings/%s/%s" % (p, h)),
                        "unpatched": (change, "findings/%s/unpatched.yaml" % p)})
        else:
            raise NoKey("no part %r" % part)
        specs[(unit, part)] = own
    ids = object_ids(repo, ["%s:%s" % cp for own in specs.values() for cp in own.values()])
    out = {}
    for (unit, part), own in specs.items():
        comp = {"version": VERSION, "unit": unit, "part": part, "checker": checker_id,
                "project": project[unit.split("/", 1)[0]], "image": checker_image if part == "build" else runner_image}
        for name, (commit, path) in own.items():
            oid = ids["%s:%s" % (commit, path)]
            comp[name] = oid if oid == "-" else "%s %s" % (oid, attrs[commit].of(path))
        if part == "build":
            comp["dune-project"] = dune_project[unit.split("/", 1)[0]]
            comp["rocqchk"] = "yes" if rocqchk else "no"
        out[(unit, part)] = (_digest("%s=%s" % kv for kv in comp.items()), comp)
    return out


def wanted(tree):
    """[(unit, part)] of every part the tree has to check: build for a harness with published builds and a statement
    Statements.v carries (one whose every statement is withdrawn has none, and rules.check refuses one whose every
    statement is withheld), counterexamples for one with a counterexample, findings for one with a finding."""
    out = {("%s/%s" % (h.project.name, h.name), "build") for h in tree.harnesses()
           if h.builds() and any(st.rendered() for st in h.statements.values())}
    out |= {(sid.rsplit("/", 1)[0], "counterexamples") for sid in tree.counterexamples}
    out |= {(f.unit, "findings") for f in tree.findings.values()}
    return sorted(out)


def recorded(repo, ref):
    """{(unit, part): {key, ...}} of the passes recorded at ref, a commit of the branch check-results."""
    out = {}
    for _kind, _oid, path in _ls_tree(repo, "-r", ref, "--", "units/"):
        m = re.fullmatch(r"units/([^/]+/[^/]+)/([a-z]+)/([0-9a-f]{64})\.json", path)
        if m:
            out.setdefault((m.group(1), m.group(2)), set()).add(m.group(3))
    return out


def record_path(unit, part, key):
    return "units/%s/%s/%s.json" % (unit, part, key)
