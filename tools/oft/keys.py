"""The content key of each part of a unit's check, and the passes recorded under those keys.

A unit is a harness <p>/<h>.  A check job checks up to three parts of it: build (its statements and proofs, in the
checker image), counterexamples and findings (both in the runner image).  The key of a part is the SHA-256 of what
that part's check reads, so a part whose key has a recorded pass is not checked again:

    every part      the statement folder projects/<p>/<h>/, but its README.md (generated, and no check reads it) and
                    the proofs, counterexamples and findings the per-project layout puts in it;
                    projects/<p>/project.yaml and every projects/<p>/*/harness.yaml (`oft fetch` unpacks a project's
                    archive only when every harness's builds are in it); the checker (NOT_THE_CHECKER says what is not)
    build           the unit's proofs folder, but two parts of its build record that no check reads: its prose
                    (provenance/PROVENANCE.md) and its licence evidence with the tooling that makes it
                    (provenance/evidence/licence/); unitpaths.PROOFS_DROP names both, and the record itself,
                    provenance/PROVENANCE.yaml, which the rules read, stays keyed.  theories/;
                    toolchain/allowed-axioms.txt (the rest of toolchain/ builds
                    the images, whose digests are keyed); every dune file of its build path, the generated barriers
                    among them (_dune_path); of dune-project, what the project's build reads (dune_project); the
                    checker image; whether rocqchk runs
    counterexamples the unit's counterexamples folder; the runner image
    findings        the unit's findings folder and its project's unpatched.yaml; the runner image

unitpaths.py defines the paths of this table, and what each leaves out (unitpaths.own, unitpaths.drop).  CI checks
each part in a view that holds those paths and the unit's fetched binaries, and no other file of the tree
(tools/oft/ci/check-units.sh), so a check cannot read a file that its key does not hold.

The proofs, counterexamples and findings are in either layout (layout.py): the proofs folder is proofs/<p>/<h>/ or
projects/<p>/<h>/proofs/, and so on; a unit with one of them in both layouts has no key.  A part's components come
from two commits: `facts`, the commit whose statements are checked, and `change`, the commit whose proofs,
counterexamples and findings are checked (layout.is_change says which files those are).  They are one commit for a
release; for any other change, pr.yml checks the base's statements with the change's proofs, counterexamples and
findings.

Each path's id is a digest of its entries (the mode, type, git object id and name of each, as git ls-tree gives them;
a file's own entry) and a digest of the checkout attributes of its files (CHECKOUT_ATTRIBUTES), since a .gitattributes
change alters the bytes a check reads without changing a blob.  Each file is named by its path inside the path, so a
folder that moves keeps its id, as every proofs, counterexamples and findings folder does when `oft port-layout`
moves it into the per-project layout; the dune file oft generate then writes in a per-project proofs or
counterexamples folder (the barrier, paths.is_gen) is left out of its id, and the unit's build key holds it as a
file of the build path instead (_dune_path).

A build key holds every dune file of the unit's build path: each name of layout.DUNE_FILES in the repository root,
in every folder down to the statement folder, in every folder down to the proofs folder, and in each folder the
statement folder's own dune takes into the statement theory with (include_subdirs qualified) — the unit's proofs,
counterexamples and findings folders, which the harness component drops — in either layout (dune_path_files).  A
file that is not there is a component of its own, "-" under its path, so adding or removing one changes the key;
the barriers `oft generate` writes in a per-project proofs and counterexamples folder are two of them.  `dune
build` of the statements and the proofs reads those files (check.check_statements, check.compile_lib), and a dune
file can turn a failure into a pass, by declaring a theory a build finds before the installed one (dune looks in
the workspace first).  The OSS Verify lead ruled on 2026-10-30 that a pass recorded without a dune file of the
build path is not a pass of a tree that has it: before this, a pass recorded before L2, without the barrier, had
the key of the ported tree that has it.

A counterexamples key and a findings key hold no dune file.  Neither run reads one: both run binaries under qemu
in the runner image (check.check_counterexample, check.check_finding).  What their folders hold that a build does
read is a dune file of their own, and the build path keys that.

The root dune-project is the one path of a build path left out of dune_path_files, because dune_project already
keys every byte of it that a build reads, and keys its absence: the forms that are not package stanzas, the core's,
the meta package's and the project's own stanzas, read with dune's own lexer, and the file's checkout attributes.
Keying the file whole instead would re-check every build of every project for a comment or for another project's
enrolment, which rewrites dune-project, and would say nothing more about any build.

What a dune file off the build path may hold is still bounded by refusal, not by a key: a plan refuses a hand-written
dune file anywhere in the tree that could declare a shadowing theory or bring in what this reader cannot see
(check_hand_dune), in the tree it checks and in the change, so what is left of them can only fail a build.  The dune
files oft generate writes cannot shadow a theory at all (paths.is_gen): each names only its own unit's theories, and
lint holds them to their rendering.  The facts' rules are in no key either; they can only turn a pass into a failure,
and every `oft check` checks them first, as pr.yml's lint job does.

A plan reads the passes recorded on the branch check-results (oft plan --store), one file per pass:
units/<p>/<h>/<part>/<key>.json.  No workflow of this repository writes or reads that branch."""
import bisect
import hashlib
import re
import subprocess

import yaml

from . import layout, names, paths, unitpaths

# What each part's key holds by path is in unitpaths.py, which the views that CI checks each part in hold, too.
PARTS = unitpaths.PARTS
# Raised when what a key reads or how it is computed changes, so that no key computed the old way can equal one
# computed the new way.  2: a path's id is its entries and its files' attributes by their paths inside it, not its
# tree id.  3: a build key holds every dune file of the unit's build path, the generated barriers among them
# (_dune_path).  4: the proofs component leaves out the build record's prose and its licence evidence
# (unitpaths.PROOFS_DROP), and a component's drop may name a path under its root, not only an entry of it.
VERSION = "4"
# The files of tools/, by their paths inside tools/, that a check never opens.  Every other file of tools/ is the
# checker, whose ids are in every key: `python3 -m oft.check` and `python3 -m oft.fetch`, as check-units.sh runs them,
# open no file this matches (test_keys.Checker says so).  oft/generate.py, oft/paths.py,
# oft/templates/proof-dune.tmpl and oft/templates/harness-dune.tmpl are the checker: oft check renders each proof
# library's lib/dune itself, with them, and compares a statement folder's dune file with its rendering.  oft/port.py
# and oft/ci/port-check.sh move a tree to the per-project layout and check the moved tree, and oft/nsrename.py renames
# a tree's Rocq namespace (`oft rename-namespace`); no check opens any of them.  oft/disclosure.py is here because
# only oft/lint.py and oft/release_tree.py import it, and both are here too; oft/model.py and oft/model.yaml
# because only oft/lint.py's release rules `model` and `pins` read them; oft/migration-pin.yaml because
# only pr.yml's plan step and release-check.yml's read it, from the base, and the pin's own digests leave that file
# out (pr.yml's plan step); oft/ci/pr-steps.sh and oft/ci/pin-digests.sh because they are run by hand on a clone, to
# rehearse a pull request's run and to print the digests a pin names; oft/ci/regenerate-shared.sh because index.yml
# runs it after a merge to render the shared generated files.  oft/symbols.py and oft/elf.py write a build's symbol
# fact (`oft symbols`), oft/classify.py compares two (`oft classify`), oft/contracts.py keys each contract file for
# work (`oft plan --contracts`), oft/prove.py reports a change's functions and contracts from them (`oft prove`),
# oft/check_run.py posts that report as a pull request check (`oft prove --post-check`) and oft/ci/prove-pr runs both
# in prove.yml's job: no check reads one; and oft/change_ledger.py sums what a change cost from its sessions'
# transcripts and git (`oft change-ledger`).  oft/lps_impact.py is here because it is run by hand on a clone, and
# starts a container that runs `python3 -m oft.check` in an image of its own, so no check loads it.  Two directories
# are here whole: enroll/, the scripts that carry a merged theorem-labs/oss-verify enrollment into these facts
# (tools/enroll/README.md), which enroll.yml and enroll-build.yml run and which `oft release-tree` removes from a
# release, and publish/, the tools that publish a release, which the publishing workflow runs.  No module of
# tools/oft imports either.
NOT_THE_CHECKER = re.compile(
    r"(?:oft/__main__\.py|oft/lint\.py|oft/lint-exceptions\.yaml|oft/urls\.py|oft/ledger\.py|oft/approvals\.py"
    r"|oft/lps_impact\.py|oft/release_tree\.py|oft/revisions\.py|oft/plan\.py|oft/pack\.py|oft/proof-times\.tsv"
    r"|oft/port\.py|oft/nsrename\.py|oft/disclosure\.py|oft/model\.py|oft/model\.yaml|oft/migration-pin\.yaml"
    r"|oft/README\.md|oft/symbols\.py|oft/elf\.py|oft/classify\.py|oft/contracts\.py|oft/prove\.py|oft/check_run\.py"
    r"|oft/change_ledger\.py"
    r"|oft/templates/(?!(?:proof|harness)-dune\.tmpl$).*|oft/tests/.*|oft/ci/facts-review-.*|oft/ci/port-check\.sh"
    r"|oft/ci/pr-steps\.sh|oft/ci/pin-digests\.sh|oft/ci/regenerate-shared\.sh|oft/ci/prove-pr|enroll/.*|publish/.*)")
STORE_BRANCH = "check-results"


class NoKey(Exception):
    """A key that cannot be computed: a commit or a file git cannot read, or a dune file no key can hold."""


def dropped(rel, drop):
    """Whether rel, a path inside a component's root, is one of the paths drop leaves out of that component, or lies
    under one (unitpaths.drop gives them; a name with no "/" is an entry of the root itself)."""
    return any(rel == d or rel.startswith(d + "/") for d in drop)


def git(repo, *args, stdin=None):
    """The standard output, as text, of `git -C repo args` with stdin as its input; NoKey, with git's message, when it
    fails.  contracts.py and prove.py read commits with it too."""
    done = subprocess.run(["git", "-C", repo, *args], input=stdin, capture_output=True, text=True)
    if done.returncode != 0:
        raise NoKey("git %s: %s" % (" ".join(args), done.stderr.strip()))
    return done.stdout


def digest(lines):
    """The SHA-256, in hex, of lines sorted, each ended by a newline: every key and component id is one."""
    return hashlib.sha256("".join(l + "\n" for l in sorted(lines)).encode()).hexdigest()


def object_ids(repo, specs):
    """{spec: object id, or "-" for a path that does not exist} for each "<commit>:<path>" in specs, in one git."""
    specs = list(dict.fromkeys(specs))
    if not specs:
        return {}
    lines = git(repo, "cat-file", "--batch-check=%(objectname)", stdin="".join(s + "\n" for s in specs)).splitlines()
    if len(lines) != len(specs):
        raise NoKey("git cat-file answered %d of %d paths" % (len(lines), len(specs)))
    return {s: ("-" if l.endswith(" missing") else l) for s, l in zip(specs, lines)}


def ls_tree(repo, *args):
    """[(mode, type, object id, path)] of `git ls-tree -z args`."""
    rows = []
    for rec in git(repo, "ls-tree", "-z", *args).split("\0"):
        if rec:
            meta, path = rec.split("\t", 1)
            mode, kind, oid = meta.split()
            rows.append((mode, kind, oid, path))
    return rows


def not_the_checker(path):
    """Whether path, a path from the repository root, is a file of tools/ that NOT_THE_CHECKER leaves out of the
    checker id."""
    return path.startswith("tools/") and NOT_THE_CHECKER.fullmatch(path[len("tools/"):]) is not None


def checker(repo, commit):
    """The id of the checker in the tools at commit: a digest of the path, blob id and checkout attributes of each
    file of tools/ (a check job copies all of it and puts it on PYTHONPATH) but the files not_the_checker names."""
    rows = [(oid, path) for _mode, _kind, oid, path in ls_tree(repo, "-r", commit, "--", "tools/")
            if not not_the_checker(path)]
    if not any(path.startswith("tools/oft/") for _oid, path in rows):
        raise NoKey("%s has no tools/oft/" % commit)
    attrs = Attributes(repo, commit, ("tools",))
    return digest("%s=%s %s" % (path, oid, attrs.of(path)) for oid, path in rows)


def images(repo, commit):
    """(checker image, runner image) as release.yaml at commit pins them."""
    try:
        data = yaml.safe_load(git(repo, "show", "%s:release.yaml" % commit))
        return data["images"]["checker"], data["images"]["runner"]
    except (NoKey, yaml.YAMLError, TypeError, KeyError) as e:
        raise NoKey("release.yaml at %s names no images.checker and images.runner (%s)" % (commit, e))


def release_names(repo, commit):
    """(namespace, opam stem) that release.yaml at commit names, by facts.Tree's rule (names.release_names): the
    defaults when it is absent or names neither."""
    spec = "%s:release.yaml" % commit
    if object_ids(repo, [spec])[spec] == "-":
        return names.release_names(None)
    try:
        return names.release_names(yaml.safe_load(git(repo, "show", spec)))
    except yaml.YAMLError as e:
        raise NoKey("release.yaml at %s cannot be read (%s)" % (commit, e)) from None


# The attributes that change the bytes git checks a file out as (gitattributes(5)).
CHECKOUT_ATTRIBUTES = ("text", "eol", "crlf", "filter", "ident", "working-tree-encoding")


class Attributes:
    """Every entry under some paths at one commit (git ls-tree -r -t), and the checkout attributes of each file, as
    git check-attr --source gives them: a .gitattributes change alters the bytes a check reads without changing a
    blob, so a component's id carries a digest of its files' attributes too.  One listing per commit serves every
    component's entries, so a plan starts no git per fuzz target."""

    def __init__(self, repo, commit, paths):
        self.commit = commit
        self.listed = tuple(dict.fromkeys(paths))   # the prefixes this listing covers; id() refuses any other path
        rows = ls_tree(repo, "-r", "-t", commit, "--", *self.listed)
        self.entry = {}      # path: "<mode> <type> <object id>"
        self.children = {}   # folder: [(name, path)] of its entries
        for mode, kind, oid, path in rows:
            self.entry[path] = "%s %s %s" % (mode, kind, oid)
            folder, _, name = path.rpartition("/")
            self.children.setdefault(folder, []).append((name, path))
        files = [path for _mode, kind, _oid, path in rows if kind != "tree"]
        out = git(repo, "check-attr", "-z", "--stdin", "--source=%s" % commit, *CHECKOUT_ATTRIBUTES,
                  stdin="".join(p + "\0" for p in files)).split("\0")
        lines = {}
        for i in range(0, len(out) - 2, 3):
            path, attr, value = out[i:i + 3]
            if value != "unspecified":
                lines.setdefault(path, []).append("%s=%s" % (attr, value))
        self.files = sorted(lines)
        self.lines = lines

    def of(self, path, drop=()):
        """A digest of the lines "<file>:<attribute>=<value>" of path and of every file under it, each file named by
        its path relative to path (path itself, a file, by its file name), the files that drop leaves out left out:
        a folder that moves keeps its digest."""
        lo = bisect.bisect_left(self.files, path)
        hi = bisect.bisect_left(self.files, path + "/\uffff")
        out = []
        for p in self.files[lo:hi]:
            if p == path:
                rel = p.rsplit("/", 1)[-1]
            elif p.startswith(path + "/") and not dropped(p[len(path) + 1:], drop):
                rel = p[len(path) + 1:]
            else:
                continue
            out += ["%s:%s" % (rel, a) for a in self.lines[p]]
        return digest(out)

    def entries(self, root, drop=()):
        """sha256 over the sorted lines "<mode> <type> <object id>\\t<name>" of root's entries, as `git ls-tree -z
        <commit>:<root>` gives them, less what drop leaves out (root a file: its own entry, under its file name);
        "-" when root does not exist.  It plays the role root's tree id would, and writes nothing into the
        repository."""
        if root not in self.entry:
            return "-"
        if self.entry[root].split()[1] != "tree":
            return digest(["%s\t%s" % (self.entry[root], root.rsplit("/", 1)[-1])])
        return digest(self._entry_lines(root, drop))

    def _entry_lines(self, root, drop):
        """The lines of the folder root's entries that entries() digests, what drop leaves out left out; [] for a
        folder that drop empties.  A drop name with no "/" is an entry of root, left out whole.  One with a "/" is a
        path under root, and the folder it leads through is read again by this rule rather than by its object id, so
        that what is under that folder and is not dropped is still in the digest and what is dropped is in no digest
        at all; the folder's line carries that digest in place of its tree id (64 hex digits, never an object id's
        40).  A folder that drop empties is left out whole, so adding the dropped path to a unit that had none does
        not change the id either."""
        out = []
        for name, path in self.children.get(root, ()):
            if name in drop:
                continue
            mode, kind, _oid = self.entry[path].split()
            under = tuple(d[len(name) + 1:] for d in drop if d.startswith(name + "/"))
            if not under or kind != "tree":
                out.append("%s\t%s" % (self.entry[path], name))
                continue
            lines = self._entry_lines(path, under)
            if lines:
                out.append("%s %s %s\t%s" % (mode, kind, digest(lines), name))
        return out

    def id(self, root, drop=()):
        """root's id: "<entries digest> <attributes digest>", drop left out of both; "-" when root does not exist.
        A root outside the paths this listing was built over is a mistake of the caller, not an absent file, and
        raises: it would read as "-" and give a tree that has the file the key of one that has not."""
        if not any(root == p or root.startswith(p + "/") for p in self.listed):
            raise ValueError("%s: no path of the listing of %s covers it (keys.FACTS_PATHS, layout.OLD_TOPS); a "
                             "component may read only what keys() lists" % (root, self.commit))
        entries = self.entries(root, drop)
        return entries if entries == "-" else "%s %s" % (entries, self.of(root, drop))

    def either(self, unit, new, old, new_drop=(), old_drop=()):
        """(root, drop) of what a component of unit reads: its new-layout path new, with new_drop, when it exists,
        else its old-layout path old, with old_drop; NoKey when both exist."""
        if new in self.entry and old in self.entry:
            raise NoKey("%s: in both layouts" % unit)
        return (new, new_drop) if new in self.entry else (old, old_drop)


def _project(repo, commit, p, attrs):
    """A digest of unitpaths.project_files of project p at commit, projects/<p>/project.yaml and each
    projects/<p>/*/harness.yaml, with their attributes; a proof re-renders the README, which no check reads.  A
    folder of projects/<p>/ that is no fuzz target's (layout.NOT_A_HARNESS: its patches/ in the per-project layout)
    has no harness.yaml here."""
    rows = ls_tree(repo, commit, "--", "projects/%s/" % p)
    folders = [path.rsplit("/", 1)[-1] for _mode, kind, _oid, path in rows if kind == "tree"]
    files = unitpaths.project_files(p, folders)
    ids = object_ids(repo, ["%s:%s" % (commit, f) for f in files])
    paths = {f: ids["%s:%s" % (commit, f)] for f in files}
    if paths[files[0]] == "-":
        del paths[files[0]]  # a missing project.yaml is in no digest; a missing harness.yaml is, as "-"
    return digest("%s=%s %s" % (path, oid, attrs.of(path)) for path, oid in paths.items())


def _forms(text, name="dune-project"):
    """unitpaths.forms, or NoKey for a file it cannot read."""
    try:
        return unitpaths.forms(text, name)
    except ValueError as e:
        raise NoKey(str(e)) from None


def dune_project(repo, commit, projects, attrs, opam_stem):
    """{project: id} of what a build of a project's harnesses reads from dune-project at commit
    (unitpaths.dune_project_forms): every form but the package stanzas, and the stanzas of unitpaths.dune_packages,
    named by opam_stem, the stem release.yaml at commit names.  A stanza another project's dune files name and
    dune-project lacks fails dune for every build; the controls, which run whenever a dune file changes, build with
    every one."""
    ids = object_ids(repo, ["%s:dune-project" % commit])
    if ids["%s:dune-project" % commit] == "-":
        return {p: "-" for p in projects}
    parsed = _forms(git(repo, "show", "%s:dune-project" % commit))
    out = {}
    for p in projects:
        shared, package, _ordered = unitpaths.dune_project_forms(parsed, p, opam_stem)
        out[p] = digest(shared + [package.get(n, "-") for n in unitpaths.dune_packages(p, opam_stem)]
                         + [attrs.of("dune-project")])
    return out


# The paths of a commit a key reads, as git ls-tree takes them: every root dune file among them, since a build key
# holds the dune files of the unit's build path (_dune_path), and the rest of that path is under projects/ in the
# new layout and under layout.OLD_TOPS in the old one, which keys() adds for the commit that carries a change's
# proofs, counterexamples and findings.
FACTS_PATHS = ("projects", "theories", "toolchain/allowed-axioms.txt") + layout.DUNE_FILES


def dune_path_files(project, harness):
    """Every path a dune file of the build path of the unit <project>/<harness> can have: each name of
    layout.DUNE_FILES in the repository root, in every folder down to the unit's statement folder, in every folder
    down to its proofs folder, and in each folder the statement folder's own dune takes into the statement theory
    with (include_subdirs qualified) (templates/harness-dune.tmpl): the unit's proofs, counterexamples and findings
    folders, which the harness component drops (layout.CHANGE_NAMES).  Both layouts are listed whatever the tree
    holds, so that the list does not turn on the layout the tree uses or on whether the unit has such a folder at
    all: a path with no file there is a component of its own, "-", and a path of the other layout has none.  In the
    old layout the counterexamples and findings folders lie outside the statement folder, so no build reads a dune
    file of theirs; the key reads them there, as it reads a dune-workspace below the root, which is the safe
    direction.  A dune file deeper than those folders is not here, nor is another unit's: a proofs folder's own id
    holds every file under it that is not its barrier and that unitpaths.PROOFS_DROP does not drop (the build
    record's prose and its licence evidence, which hold no dune file a build reads), a counterexamples or findings
    folder's id holds the rest of
    what is under it for its own part, and what a hand-written one of them may hold is bounded by refusal, not by
    a key (check_hand_dune).  Each unit reads only its own path.  The root dune-project is not here either:
    dune_project keys every byte of it a build reads, and its absence, and keying the file whole would re-check
    every build for a comment or for another project's enrolment."""
    dirs = {""}
    for base in (layout.statement_dir(project, harness),
                 *(layout.proofs_dir(project, harness, lay) for lay in layout.LAYOUTS)):
        parts = base.split("/")
        dirs |= {"/".join(parts[:i + 1]) for i in range(len(parts))}
    for lay in layout.LAYOUTS:
        dirs |= {layout.counterexamples_dir(project, harness, lay), layout.findings_dir(project, harness, lay)}
    return sorted({"%s/%s" % (d, name) if d else name
                   for d in dirs for name in layout.DUNE_FILES} - {"dune-project"})


def _dune_path(project, harness, facts, change, attrs):
    """The id of the dune files of the unit's build path: a digest of the id of each path dune_path_files names,
    under that path, from change for a path a change brings (layout.is_change: the unit's proofs, counterexamples
    and findings folders, the barriers among them) and from facts for the rest, as check_hand_dune reads them and
    as pr.yml composes the tree a check builds.  A path with no file there has the id "-", so adding or removing a
    dune file of the build path changes the key."""
    return digest("%s=%s" % (path, attrs[change if layout.is_change(path) else facts].id(path))
                  for path in dune_path_files(project, harness))


# The dune files oft generate writes, which lint holds to their rendering, each naming only its own unit's theories,
# are the ones tools/oft/paths.py calls generated (is_gen): its placeholders refuse a segment that is not a name, so
# projects/<p>/bin/dune, which lint never reads (paths.IGNORED_PATTERNS), is hand-written.  Every other dune file is
# hand-written, proofs/lib/dune among them: no key holds proofs/lib/, which no row admits and the per-project layout
# gives no place.
# What a hand-written dune file may hold: none of it can change what a statements or proof build of any harness
# compiles.  A rule's targets are in its own directory, and the only theory it may declare is the tests' own.
# theories/dune declares the core, whose directory is in every build's key, and holds nothing else.
HAND_DUNE_STANZAS = {"rule", "alias", "rocq.theory", "coq.theory", "include_subdirs", "data_only_dirs", "dirs"}
THEORIES_DUNE_STANZAS = {"rocq.theory", "coq.theory"}


def hand_theory(namespace):
    """The theories a hand-written dune file may declare: the tests' own, <namespace>.Tests (names.rocq_tests), and
    those under it."""
    return re.compile(re.escape(names.rocq_tests(namespace)) + r"(?:\.[^\s()]+)?")


def check_hand_dune(repo, facts, change=None):
    """Refuse (NoKey) a hand-written dune file a check's dune reads that could turn a failing build into a passing
    one, which no key would hold: one that declares a theory a build could find before the installed one (dune looks
    in the workspace first), or holds a stanza HAND_DUNE_STANZAS does not name (include, subdir, a library: what it
    brings in cannot be seen here).  Every file with a dune file's name that paths.is_gen does not call generated, but
    dune-project (dune_project): from change for what a change brings (layout.is_change: the proofs, counterexamples
    and findings of either layout), and from facts elsewhere, each read with the namespace release.yaml names at the
    commit it is read from (hand_theory)."""
    for commit, in_change in ((facts, False), (change or facts, True)):
        namespace = release_names(repo, commit)[0]
        allowed_theory = hand_theory(namespace)
        for _mode, _kind, _oid, path in ls_tree(repo, "-r", commit):
            if (path.rsplit("/", 1)[-1] not in layout.DUNE_FILES or path == "dune-project" or paths.is_gen(path)
                    or layout.is_change(path) != in_change):
                continue
            allowed = THEORIES_DUNE_STANZAS if path == "theories/dune" else HAND_DUNE_STANZAS
            for form in _forms(git(repo, "show", "%s:%s" % (commit, path)), path):
                head = re.match(r"\(\s*([^\s()]+)", form)
                if not head or head.group(1) not in allowed:
                    raise NoKey("%s: a hand-written dune file with a %s stanza, which could change what a build "
                                "compiles" % (path, head.group(1) if head else "nameless"))
                if head.group(1) in ("rocq.theory", "coq.theory") and path != "theories/dune":
                    # the stanza's fields as dune reads them, so a comment or a string cannot hold a second name
                    fields = _forms(form[form.index(head.group(1)) + len(head.group(1)):-1], path)
                    declared = [m.group(1) for m in (re.fullmatch(r"\(\s*name\s+([^\s()\"]+)\s*\)", f) for f in fields)
                                if m]
                    if len(declared) != 1 or not allowed_theory.fullmatch(declared[0]):
                        raise NoKey("%s: a hand-written dune file declares the theory %s, which a build could find "
                                    "before the installed one; only %s may be declared outside the generated files"
                                    % (path, " and ".join(declared) or "with no plain (name ...) field",
                                       names.rocq_tests(namespace)))


def keys(repo, wanted, facts, change, tools, rocqchk=False):
    """{(unit, part): (key, {component: id})} for each (unit, part) in wanted, with the statements of commit facts,
    the proofs, counterexamples and findings of commit change, in either layout, and the checker of the tools at
    commit tools.  A component's id is a digest of its entries and a digest of its files' checkout attributes
    (Attributes.id); "-" is a path that does not exist.  NoKey for a unit with what a part of it reads (its proofs,
    counterexamples or findings, or its project's unpatched.yaml) in both layouts at change."""
    checker_id = checker(repo, tools)
    checker_image, runner_image = images(repo, facts)
    attrs = {facts: Attributes(repo, facts, FACTS_PATHS + (layout.OLD_TOPS if change == facts else ()))}
    if change != facts:
        attrs[change] = Attributes(repo, change, layout.OLD_TOPS + ("projects",))
    projects = sorted({u.split("/", 1)[0] for u, _ in wanted})
    project = {p: _project(repo, facts, p, attrs[facts]) for p in projects}
    dune_ids = dune_project(repo, facts, projects, attrs[facts], release_names(repo, facts)[1])
    if any(part == "build" for _u, part in wanted):
        check_hand_dune(repo, facts, change)
    at = attrs[change]
    out = {}
    for unit, part in wanted:
        p, h = unit.split("/", 1)
        # component: (commit, root, the paths left out of it).  unitpaths.own gives each path in each layout: one that
        # a change brings (layout.is_change) is read at change, in the layout it has there (Attributes.either: NoKey
        # for both), with what unitpaths.drop leaves out of it in that layout; every other path, the same in both
        # layouts, is read at facts.
        try:
            new, old = unitpaths.own(unit, part, layout.NEW), unitpaths.own(unit, part, layout.OLD)
        except ValueError as e:
            raise NoKey(str(e)) from None
        own = {}
        for name, rel in new.items():
            if layout.is_change(rel):
                own[name] = (change,) + at.either(unit, rel, old[name], unitpaths.drop(name, layout.NEW),
                                                 unitpaths.drop(name, layout.OLD))
            else:
                own[name] = (facts, rel, unitpaths.drop(name, layout.NEW))
        comp = {"version": VERSION, "unit": unit, "part": part, "checker": checker_id,
                "project": project[p], "image": checker_image if part == "build" else runner_image}
        for name, (commit, root, drop) in own.items():
            comp[name] = attrs[commit].id(root, drop)
        if part == "build":
            comp["dune-path"] = _dune_path(p, h, facts, change, attrs)
            comp["dune-project"] = dune_ids[p]
            comp["rocqchk"] = "yes" if rocqchk else "no"
        out[(unit, part)] = (key_of(comp), comp)
    return out


def key_of(comp):
    """The key of the components comp: a digest of "<name>=<id>" for each of them, in the order keys() builds them.
    It is the one place the formula lives.  A caller that must read a key an older formula wrote gives the
    components that formula held (plan.ruling_20_allows, which takes the version component back and leaves the
    dune-path one out), so the difference is named where the exception lives and this function knows of none."""
    return digest("%s=%s" % kv for kv in comp.items())


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
    for _mode, _kind, _oid, path in ls_tree(repo, "-r", ref, "--", "units/"):
        m = re.fullmatch(r"units/([^/]+/[^/]+)/([a-z]+)/([0-9a-f]{64})\.json", path)
        if m:
            out.setdefault((m.group(1), m.group(2)), set()).add(m.group(3))
    return out


def record_path(unit, part, key):
    return "units/%s/%s/%s.json" % (unit, part, key)
