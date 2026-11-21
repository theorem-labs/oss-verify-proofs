"""oft lint: the rules that keep this repository what it says it is.

    paths         every path has exactly one owner (tools/oft/paths.py), a pull
                  request changes only what its kind of pull request may change,
                  no derived file, binary, NUL byte, LFS pointer or link is
                  stored, but where binary data belongs (BINARY_OK, and a
                  classifier program its proof.yaml pins), no old-layout path
                  lies beside a per-project one (layout.py), and a symbol fact
                  is named for a build its harness.yaml publishes
    schema        closed schemas and the rules between facts (schema.py, rules.py),
                  each symbol fact reads whole and is of the binary
                  harness.yaml pins (check_symbols), a deviation record says
                  what its build record and the TLS scans of its builds say
                  (check_deviation), and each statement's instance is the
                  file its record names, of fewer than 64 MiB, on the path
                  the driver takes with it (check_instances); a project of
                  shapes.REQUIRED must carry both; each name of a
                  project's private_harnesses is one that every reader of the
                  held entries can hold and that neither the cut nor the
                  scanners find in the name, path or Rocq module of a kept
                  fuzz target or in a project's name, in any case, and the
                  field leaves its project a fuzz
                  target that publishes a build when it has one, unless the
                  project is `release: private` (check_private_harnesses);
                  and the internal tree (with tools/publish/) names no port
                  repository `none` (check_port_none)
    private-data  no host paths (but in the change ledgers, changes/, which
                  the release removes), private network addresses, private host
                  names, private theorem-labs repositories named in a path,
                  e-mail addresses, private keys or access tokens in what this
                  repository wrote (the lines of the upstream author's notice
                  in a third-party proof file whose row pins its bytes are not
                  read), and no build host in a port build record
    links         links point only where they may: never to a machine on a
                  private network or to a private theorem-labs repository
    free-text     every free-text field has a place in the rendering
    proofs        no axioms, admits, plugins or file effects in a fuzz target's
                  proofs folder, no file reads (Load, Cd, Extra Dependency) in
                  the generated Rocq files of projects/, and no wall-clock
                  limits in a Rocq file
    licence       a proof file's licence lines agree with NOTICE, or, in a
                  third-party proof file, with its row of
                  tools/oft/third-party-proofs.yaml, which pins its bytes,
                  and its licence's text is in LICENSES/; a licence text
                  lint pins is its pinned bytes; and while a harness
                  publishes a classifier or an original, NOTICE holds its
                  sentence on them (scan_licence, load_third_party,
                  scan_third_party_text, scan_pinned, check_notice)
    contract-literals
                  a contract file (lib/[UAB/]Prog/**/<fn>_c.v) of a fuzz
                  target with a symbol fact writes no numeral, hexadecimal
                  or decimal, inside an allocated section of one of its
                  builds, and
                  names only what its build's Symbols.v defines
                  (scan_contract)
    read-from     a proof file's `(* Read from: ... *)` comment names a
                  binary its own fuzz target's harness.yaml records, and
                  every SHA-256 it holds is that build's pin; the unstripped
                  twin, which harness.yaml does not pin, and a withheld
                  build, which shows none, are left alone.  A relocated
                  file's donor line, which names another fuzz target's
                  binary, is exempt only where the same file names the
                  pinned build of its own fuzz target too, and is then
                  counted and reported rather than passed in silence
                  (scan_read_from, split_donors)
    withheld      a withheld item shows no detail anywhere
    records       (--release) every proof's build record is complete and says
                  what the facts say of its binaries and what built them
    model         (--release) the checker image pins the hash of the model's
                  files at release.yaml's commit, which model.yaml requires
    pins          (--release) each commit the release pins in another
                  repository is on a branch or tag there

The per-file text rules (private-data, links, proofs) read an internal path
(is_internal: INTERNAL in paths.py, a row of the internal class or one of
INTERNAL_FILES, and LINT_ONLY_INTERNAL here), which no release carries, for a
private key or an access token alone.
private-data and links say what a release may publish, so in a directory a
release never carries whose files keep their own rows (internal_only:
dev/stream/, which `oft release-tree` cuts whole) they read only what a cut
cannot make safe: a private key, an access token, or a URL carrying user
information.

Every rule fails when it examined nothing, but `records` in a tree with no
proof and no build record.  `run` returns the findings; the command exits 1 if
there is any.

A whole-tree run also prints, on stderr, how many proof files carry no licence
line at all, in total and per fuzz target (bare_licence, bare_report).  That is
a count and no rule: requirement 7 of docs/adding-a-proof.md says a file with no
licence lines was written here under MIT, so none of these is a finding (none
outside a project that is `release: private` with a NOTICE, where no proof file
is under MIT: private_projects), but a
file whose Anthropic header was dropped is the same bytes as one written here,
and within lint only a count makes the second visible.  The strip check of
pr.yml's lint job sees the drop in the change itself: it compares each proof
file with that file at the base, and fails the change in a fuzz target whose
proofs/provenance/evidence/licence/made-from.tsv is in the tree at the base
or at the head (today curl/fuzz_bufq, curl/fuzz_fnmatch and
libreac/fuzz_scene).  In other fuzz targets it prints a notice.  The count
fails nothing.
"""
import bisect
import collections
import concurrent.futures
import concurrent.futures.process
import datetime
import functools
import hashlib
import ipaddress
import multiprocessing
import os
import re
import socket
import stat
import subprocess
import sys
import threading
import time
import urllib.parse

from . import (deviation, facts, generate, layout, model, names, nsrename, paths, rocq, rules, schema, shapes, symbols,
               urls, yamlio)

HERE = os.path.dirname(os.path.abspath(__file__))


PROOF_DIR_CAP = 5 << 20
PARALLEL_FILES = 256  # at least this many files to read run their text rules on every CPU by default (run's jobs)
DERIVED_SUFFIXES = (".vo", ".vos", ".vok", ".glob", ".aux", ".hex", ".cache", ".pyc", ".pyo")
QUOTED_NAME = re.compile(r'["\\\x00-\x1f\x7f]')  # what git quotes in a path whatever core.quotePath says
LFS_POINTER = b"version https://git-lfs.github.com/spec/v1"
# the path patterns (paths.TABLE) of a project's public patch text, in each layout: each must be named by an entry
PATCH_PATTERNS = ("patches/{project}/*.patch", "projects/{project}/patches/*.patch")


class Finding:
    def __init__(self, rule, where, msg, key=None):
        self.rule, self.where, self.msg, self.key = rule, where, msg, key

    def __str__(self):
        return "%s %s: %s%s" % (self.rule, self.where, self.msg, " (key %s)" % self.key if self.key else "")


# ---------------------------------------------------------------- the files

class IndexUnreadable(Exception):
    """git is here and would not list the checkout's files, so this lint knows nothing about the tree."""


def walk(root):
    """Every file that could be committed, as relative paths: in a git
    checkout, the tracked files and the untracked ones .gitignore does not
    exclude; elsewhere, every file outside _build/, projects/*/bin/ and
    projects/*/unpatched-bin/.

    A git that will not answer raises IndexUnreadable, and `run` turns that into a finding naming the tree.  It
    used to be `check=True`, which ended the whole lint with git's exit 128 and no message of this tool's: a
    linter that dies tells a reader nothing, and it also made the refusal in `_link_refusal` unreachable through
    `oft lint` -- a guard against an error becoming a permission that could not itself run (the review of 673)."""
    if os.path.exists(os.path.join(root, ".git")):   # a directory in a clone, a file in a worktree
        r = subprocess.run(["git", "-C", root, "ls-files", "-z", "--cached", "--others", "--exclude-standard"],
                           capture_output=True)
        if r.returncode != 0:
            raise IndexUnreadable(r.stderr.decode("utf-8", "replace").strip())
        return sorted(p for p in r.stdout.decode().split("\0")
                      if p and not paths.ignored(p) and os.path.lexists(os.path.join(root, p)))
    out = []
    for dp, dns, fns in os.walk(root):
        rel_dir = os.path.relpath(dp, root)
        keep = []
        for d in sorted(dns):
            rel = os.path.normpath(os.path.join(rel_dir, d))
            if not paths.ignored(rel):
                keep.append(d)
        dns[:] = keep
        for f in sorted(fns):
            rel = os.path.normpath(os.path.join(rel_dir, f))
            if not paths.ignored(rel):
                out.append(rel)
    return out


def left_out(root):
    """The tracked files a sparse checkout leaves off disk (git's skip-worktree bit), as relative paths.  walk lists
    none of them, so no rule reads their bytes; check_paths still judges their names.  Lint draws no conclusion from
    their absence: an exception that names one is not called unused, and a licence-pending entry whose unit has one is
    not called stale (apply_exceptions, apply_pending).  A lint of the whole tree judges those entries and those
    bytes: pr.yml's merge-queue and push lints check the tree out whole.  Empty outside a git checkout."""
    if not os.path.exists(os.path.join(root, ".git")):
        return set()
    r = subprocess.run(["git", "-C", root, "ls-files", "-z", "-t", "--cached"], capture_output=True)
    if r.returncode != 0:
        raise IndexUnreadable(r.stderr.decode("utf-8", "replace").strip())
    return {rec[2:] for rec in r.stdout.decode().split("\0")
            if rec.startswith("S ") and not os.path.lexists(os.path.join(root, rec[2:]))}


def read_text(path, cap=facts.MAX_BYTES):
    """The file's text, or None if it is binary, or is not a regular file of at most cap bytes: check_paths reports a
    link, a special file or a file over its cap, so none is followed, opened or read whole here."""
    try:
        data = facts.read_bounded(path, cap)
    except facts.BoundedFileError:
        return None
    if b"\0" in data[:8192]:
        return None
    return data.decode("utf-8", errors="replace")


# Verbatim copies of files from elsewhere, pinned by content: the licence texts and the notice that came with the proofs
# made from a bundle under Apache-2.0 OR MIT, and the licence file of coq-community/huffman, whose proof files some
# fuzz targets carry under LGPL-2.1-or-later (THIRD_PARTY).  Each is held to its bytes: a file of them that the tree
# holds with other bytes is a licence finding (scan_pinned), and is ordinary text, held to every other rule too.  A
# row's file of THIRD_PARTY needs its licence's text to be one of them, not one of Anthropic's own (ANTHROPIC_TEXTS),
# and in the tree (scan_third_party_text).
PINNED_VERBATIM = {
    "LICENSES/anthropic-proofs-LICENSE": "cfc7749b96f63bd31c3c42b5c471bf756814053e847c10f3eb003417bc523d30",
    "LICENSES/anthropic-proofs-LICENSE-MIT": "2e6105c36a95f04adbc36000b7b1ce65544385e27f8febb1b2f53b61fdb62bca",
    "LICENSES/anthropic-proofs-NOTICE": "f4cbf47ffed57359084432af1ca4b22347ecb995fcf7a2e4e346f180d2e5001d",
    "LICENSES/coq-community-huffman-LICENSE": "3f5037854d29f6b9621925b165e18ea223d8f81de4ed29ca0da5860d55f14701",
}


# a fuzz target's proofs folder in either layout (layout.PROOF_HARNESS_RE), and two parts of the build record in it:
# the copies it carries (licence texts, the slice of the recipe) and the port's files of a port-built one
PROOFS_FOLDER = re.compile(layout.PROOF_HARNESS_RE + "/")
RECORD_COPY = re.compile(layout.PROOF_HARNESS_RE + "/provenance/(?:LICENSES|recipe)/")
PORT_RECORD = re.compile(layout.PROOF_HARNESS_RE + "/provenance/port/")


def verbatim(rel, text=None):
    """Bytes that ship as they are: the jargon and link rules do not apply.  Upstream copies (a harness's source/, the
    licence texts of a build record), the slice of its recipe a build record carries, and the files of
    PINNED_VERBATIM when text is their pinned content.  The API driver's and an OSS Verify target's source are this
    repository's own text, so they are held to those rules."""
    if rel in PINNED_VERBATIM:
        return text is not None and hashlib.sha256(text.encode()).hexdigest() == PINNED_VERBATIM[rel]
    return bool(re.match(r"projects/[^/]+/(?!api-driver/)[^/]+/source/", rel) or RECORD_COPY.match(rel))


# The directories this repository keeps to itself, whose text no release carries: `oft release-tree` removes each of
# them whole (release_tree.INTERNAL), and tools/oft/tests/test_lint.py holds this list to that one, so the exemption
# below stands only while the cut does.  Only dev/stream/ is here: the other files release_tree.INTERNAL names
# (approvals.yaml, review.md, the workflows) are this repository's own facts and prose, and every rule still reads
# them.
INTERNAL_ONLY = ("dev/stream/",)


def internal_only(rel):
    """Whether rel is text that runs this stream rather than describes a proof: the OSS Verify stream's operational
    tools (dev/stream/README.md).  The private-data shapes that name a place and the link rule
    do not read it.

    Those tools name the machines they run on, the buckets they copy to and the absolute paths they live at, and
    their uv.lock pins every package by its URL.  Both rules exist so that such a name does not reach a reader of the
    release: `oft release-tree` removes this directory whole before a release is cut (release_tree.INTERNAL), so here
    there is no reader to protect, and the two rules would only refuse the tools the words they must use to work.
    What this accepts: a machine name, an address, an internal repository's name, a person's address or a link to a
    private network under dev/stream/ is nobody's finding, so the tree keeps them and only the cut stops them.
    Every other rule still reads these files: `paths` owns each of them (paths.py), and a private key, an access
    token or a URL carrying user information is still a finding here (scan_shapes), since a committed credential
    is a live credential whether or not it ships.
    """
    return rel.startswith(INTERNAL_ONLY)


def oss_verify_sources(tree):
    """The source/ directories of the fuzz targets OSS Verify builds (origin oss-verify), as
    projects/<p>/<h>/source/: what oss_verify_source reads."""
    return frozenset("projects/%s/%s/source/" % (h.project.name, h.name) for h in tree.harnesses()
                     if h.data["origin"] == "oss-verify")


def oss_verify_source(own, rel):
    """Whether rel is source text copied from the OSS Verify port: a file under one of `own`
    (oss_verify_sources)."""
    m = re.match(r"projects/[^/]+/[^/]+/source/", rel)
    return m is not None and m.group() in own


def port_record(rel):
    """Whether rel is one of the port's files in a port-built build record (provenance/port/ of a fuzz target's proofs
    folder).  They ship as they are, and are the port's own text: the private-data rules, the private-host rule and
    the rule against links to a private repository apply.  The allowlist of other links does not: the port's sources
    file pins every upstream tree by its URL."""
    return bool(PORT_RECORD.match(rel))


def proof_rocq(rel):
    """Whether rel is a Rocq file of a fuzz target's proofs folder, in either layout (a proof, or a file of its proof
    library): what the proofs rule reads as a proof."""
    return rel.endswith(".v") and PROOFS_FOLDER.match(rel) is not None


PORT_MANIFEST = re.compile(layout.PROOF_HARNESS_RE + r"/provenance/port/manifest\.yaml$")
# a build record's copy of the port's own files for its project: the record's project (group 1 in the old layout, 2 in
# the new), never proofs/lib/
PORT_PROJECT_FILE = re.compile(layout.PROOF_HARNESS_PROJECT_RE + r"/provenance/port/projects/(?:\1|\2)/")
PORT_PROJECT_YAML = re.compile(layout.PROOF_HARNESS_PROJECT_RE + r"/provenance/port/projects/(?:\1|\2)/project\.yaml$")



def scan_port_manifest(text, where):
    """private-data.  The manifest the port's tools/check writes names the machine of a --twice rebuild
    (rebuild.host); a build record's copy leaves every host out."""
    try:
        data = yamlio.load(text, where)
    except yamlio.YamlError as e:
        return [Finding("private-data", where, "not YAML: %s" % e)]
    out = []

    def visit(v, at):
        if isinstance(v, dict):
            for k, x in v.items():
                if k == "host":
                    out.append(Finding("private-data", where, "%shost names the build machine: leave it out"
                                       % (at + "." if at else ""), key=_key(str(x))))
                visit(x, (at + "." if at else "") + str(k))
        elif isinstance(v, list):
            for x in v:
                visit(x, at)

    visit(data, "")
    return out


# ------------------------------------------------------------- private-data

# /home/opam/ is the home of the user of the official OCaml/opam container
# images that toolchain/*.Dockerfile builds on; it names no host.  /mnt/disks/
# and /mnt/nvme/ are the data disks of our machines.
HOST_PATH = re.compile(r"(?<![\w.~-])/(?:data|home(?!/opam\b)|srv|Users|root|mnt/disks|mnt/nvme)/[\w.@+-]+")
# The change ledgers (oft change-ledger): each records the paths of the logs and inputs it was summed from, on the
# machine that summed it, so that it can be summed again there; `oft release-tree` removes changes/, so no host path
# there reaches a release.  The other private-data shapes still count there.
CHANGE_LEDGERS = "changes/"
# Addresses on a private network, including the shared address space Tailscale assigns to its nodes.
PRIVATE_IP = re.compile(r"(?<![\d.])(?:10\.\d{1,3}|100\.(?:6[4-9]|[7-9]\d|1[01]\d|12[0-7])|172\.(?:1[6-9]|2\d|3[01])|192\.168|169\.254)\.\d{1,3}\.\d{1,3}(?![\d.])")
# Host names that resolve only on a private network: one label (a bare machine name), localhost and its names
# (RFC 6761), or one of these suffixes (ts.net is a Tailscale network's own names; internal.cloudapp.net is Azure's).
PRIVATE_SUFFIXES = ("localhost", "internal", "local", "corp", "lan", "home.arpa", "ts.net",
                    "internal.cloudapp.net")
# static-asan is asan-static's former name; GitHub redirects it there, so it names a public repository.
# rocq is the public fork that Theorem's Rocq releases publish to.
PUBLIC_REPOS = ("oss-verify", "oss-verify-proofs", "rocq-linux-process-semantics", "rocq-read-file", "asan-static",
                "static-asan", "rocq")
INTERNAL_PORT_REPO = schema.INTERNAL_PORT_REPOSITORY.split("/", 1)[1]
# Private names, refused in any text whether or not it is a link (the link rule judges links by what they open):
# a host name under a private suffix, in any case; and a theorem-labs repository named as a path (after a /,
# backslash or the : of an ssh remote) or as owner/name, also with %2F or a character reference (a line with % or &
# is read decoded too) and, in a file GitHub renders as Markdown, split by a backslash escape or an HTML comment (a
# line of it is read as GitHub shows its text too, urls.unescape_markdown).  An image on ghcr.io, also as a regular
# expression writes it, is the GHCR rule's.  A host name starts after anything but a name character or a name and a
# dot, so a proof's qualified names (`AW_Init.internal`, `Mod_X.Sub.internal`) are not read as one.
PRIVATE_HOST_NAME = re.compile(r"(?i)(?<![\w-])(?<![\w-]\.)(?:[a-z0-9-]+\.)+(?:%s)(?![\w-]|\.[a-z0-9])"
                               % "|".join(re.escape(s) for s in PRIVATE_SUFFIXES))
REPOSITORY_PATH = re.compile(r"(?i)(?:(?<![\w.@/\\:%-])|(?<!ghcr\.io)(?<!ghcr\\\.io)[/\\:])theorem-labs[/\\]+([a-z0-9._-]+)"
                             r"|(?<![\w.-])theorem-labs" r"\.github\.io\.?[/\\]+([a-z0-9._-]+)")
EMAIL = re.compile(r"\b[A-Za-z0-9._%+-]+@[A-Za-z0-9-]+(?:\.[A-Za-z0-9-]+)*\.[A-Za-z]{2,}\b")
# The user `git` at `github.com` is GitHub's one SSH account, the fixed user half of an SSH clone URL of GitHub, which
# every tool that clones over SSH writes.  It is nobody's address and carries no secret -- the secret in that shape is
# a password or a token, which is matched in place of `git` and is still read as a URL's user information.  Any other
# user before `@github.com` (a person, `x-access-token`, a token) is left to the rules below.
EMAIL_OK = re.compile(r"@users\.noreply\.github\.com$|^noreply@github\.com$|^git@github\.com$")
# what comes just before an EMAIL match that is really a URL's user information: "//" then an optional "user:"
URL_USERINFO_BEFORE = re.compile(r"//[^\s/@]*:?$")
PRIVATE_KEY = re.compile(r"-----BEGIN (?:[A-Z]+ )*PRIVATE KEY-----")
TOKEN = re.compile(r"\b(?:gh[pousr]_[A-Za-z0-9]{36,}|github_pat_[A-Za-z0-9_]{22,}|AKIA[0-9A-Z]{16}"
                   r"|xox[abprs]-[A-Za-z0-9-]{10,}|AIza[0-9A-Za-z_-]{35}|ya29\.[0-9A-Za-z_-]{20,})")
GITHUB_ORG_PACKAGES = re.compile(r"(?i)(?<![\w.-])(?:https?://)?(?:www\.)?github\.com/orgs\Z")
ROCQ_QUALIFIED_LINE = re.compile(r"(?i)^\s*(?:Lemma\s+\w+\s*:\s+|Require\s+Import\s+)[A-Za-z_][\w.]*\.\s*$")


def _ordinary_code_name(where, line, match):
    """Whether a private-host shape is an ordinary code name, not a machine name."""
    name = match.group().lower()
    if name == "threading" + ".local" and line[match.end():].startswith("("):
        return True
    if name == "env" + ".local" and match.start() and line[match.start() - 1] == ".":
        return True
    if (name.startswith(("com.", "org.", "net.", "io.", "edu.", "gov."))
            and re.search(r"(?i)(?:^|[`\s])(?:import|package)\s+$", line[:match.start()])
            and line[match.end():].startswith(";")):
        return True
    return proof_rocq(where) and ROCQ_QUALIFIED_LINE.fullmatch(line) is not None


def _github_org_page(line, match):
    """Whether a theorem-labs path is GitHub's organisation packages page, not a repository."""
    return ((match.group(1) or match.group(2)).lower().rstrip(".").removesuffix(".git") == "packages"
            and GITHUB_ORG_PACKAGES.search(line[:match.start()]) is not None)


# a build record (provenance/PROVENANCE.yaml of a fuzz target's proofs folder), in either layout, with its project
# captured: group 1 in the old layout, group 2 in the new
_BUILD_RECORD = re.compile(layout.PROOF_HARNESS_PROJECT_RE + r"/provenance/PROVENANCE\.yaml$")
# A record's port and project.yaml's build.oss_verify: the two fields that name where the recipe was read from, one in
# project.yaml and one in each build record (tools/enroll/facts.py writes them equal)
PORT_FIELD = {("project.yaml",): ("build", "oss_verify", "repository"),
              ("proofs", "provenance", "PROVENANCE.yaml"): ("port", "repository")}
# The organisation whose repositories a private project's library may be (_library_name)
ORG = schema.OSS_VERIFY_REPOSITORY.split("/", 1)[0]
# The table facts.py writes a row of for every fuzz target it enrolls, a private project's among them: its first
# column names the row's project
HANDLER_ROWS = "analyses/failure-handlers/failure_handlers.tsv"


def _project_of(tree, where):
    """(the project a file of projects/<p>/ belongs to, in either layout, or None; the file's new-layout parts)."""
    parts = layout.canonical(where).split("/")
    if len(parts) < 3 or parts[0] != "projects":
        return None, parts
    return tree.projects.get(parts[1]), parts


def _internal_port_projects(tree):
    """rules.internal_port_projects(facts.hold(tree)), computed once for each tree a lint reads: _internal_port_lines
    asks for it for every project.yaml and every build record that names the port's internal copy, and the hold reads
    every finding of the tree."""
    projects = getattr(tree, "_lint_internal_port_projects", None)
    if projects is None:
        projects = tree._lint_internal_port_projects = frozenset(rules.internal_port_projects(facts.hold(tree)))
    return projects


def _internal_port_lines(tree, where, text):
    """The lines of the one field of where that may name the port's internal copy (PORT_FIELD):
    build.oss_verify.repository of projects/<p>/project.yaml, and port.repository of a build record of p
    (provenance/PROVENANCE.yaml of a fuzz target's proofs folder, in either layout).  Only a project that may build
    from that copy has such lines (rules.internal_port_projects: a project that a finding holds back whole, a project
    whose project.yaml says `release: private`, or a project with a held fuzz target).  No other field of these files,
    and no other file, may name it."""
    project, parts = _project_of(tree, where)
    if project is None or schema.INTERNAL_PORT_REPOSITORY not in text:
        return frozenset()
    keys = PORT_FIELD.get(tuple(parts[2:])) or (PORT_FIELD.get(tuple(parts[3:])) if len(parts) == 6 else None)
    if keys is None or project.name not in _internal_port_projects(tree):
        return frozenset()
    node = yamlio.compose(text)
    for key in keys:
        node = yamlio.mapping_value(node, key)
        if node is None:
            return frozenset()
    if getattr(node, "value", None) != schema.INTERNAL_PORT_REPOSITORY:
        return frozenset()
    return frozenset(range(node.start_mark.line + 1, node.end_mark.line + 2))


def _library_name(project):
    """{the name of the project's library repository} for a project whose project.yaml says `release: private`, which
    builds from the port's internal copy, and whose library.repository is the https URL of an ORG repository on GitHub,
    owner and name alone: a library that is not public, which builds in the internal mode alone (OSSV-618).  Empty for
    every other project.  The name is read as scan_shapes reads one (lower case, trailing dots and one .git off), and
    there is none when what is left still ends in . or .git, or is the port's internal copy, which names only its own
    fields (_internal_port_lines)."""
    port = facts.port(project) if project is not None else None
    if project is None or project.data.get("release") != "private" or not isinstance(port, dict) \
            or port.get("repository") != schema.INTERNAL_PORT_REPOSITORY:
        return frozenset()
    library = project.data.get("library")
    repo = library.get("repository") if isinstance(library, dict) else None
    if not isinstance(repo, str):
        return frozenset()
    u = urllib.parse.urlsplit(repo)
    parts = u.path.split("/")
    if (u.scheme, u.netloc, u.query, u.fragment) != ("https", "github.com", "", "") or len(parts) != 3 \
            or parts[0] or parts[1].lower() != ORG:
        return frozenset()
    name = parts[2].lower().rstrip(".").removesuffix(".git")
    if not name or name.endswith((".", ".git")) or name == INTERNAL_PORT_REPO:
        return frozenset()
    return frozenset({name})


def _no_library(no):
    """No line names a library of its own (_own_library)."""
    return frozenset()


def _own_library(tree, where, text):
    """The repository names a line of the file may name as its project's own library (_library_name), as a function
    of the line's number: every line of a file of projects/<p>/, in either layout, gets that project's, and each row
    of failure_handlers.tsv, which facts.py writes for a private project too, its project column's when its harness
    column is a fuzz target of that project.  Every other line gets none, so the name stays refused anywhere else: no
    release carries those files or rows (release_tree cuts the rows of the tree's fuzz targets it does not carry, and
    keeps a row of a fuzz target the tree no longer has, which therefore gets no name)."""
    if where == HANDLER_ROWS:
        rows = {}
        for no, line in enumerate(text.split("\n"), 1):
            project, harness = (line.split("\t") + [""])[:2]
            p = tree.projects.get(project)
            rows[no] = _library_name(p) if p is not None and harness in p.harnesses else frozenset()
        return lambda no: rows.get(no, frozenset())
    own = _library_name(_project_of(tree, where)[0])
    return lambda no: own


def _repository_value(line, match):
    """Whether match is the YAML value of a repository key, in block or flow
    form, rather than a comment or another free-text use."""
    before, after = line[:match.start()], line[match.end():]
    return ("#" not in before
            and re.search(r"(?<![\w-])repository\s*:\s*(?:['\"])?$", before) is not None
            and re.match(r"(?:['\"])?\s*(?:[,}]|#|$)", after) is not None)


# What the text rules read in an internal path (is_internal: INTERNAL of paths.py, and LINT_ONLY_INTERNAL): a private
# key or an access token, which is as bad there as in a shipped file.  The rest of private-data, and links and proofs,
# judge the published text: no release carries an internal path, and dev/stream/bin/ holds the publishing scanner's
# needles, host paths and addresses on purpose.
SECRETS = (("a private key", PRIVATE_KEY), ("an access token", TOKEN))


def scan_internal_secrets(root, rels):
    """private-data's secret scan over the internal paths rels: each regular file on disk (a sparse checkout reads
    only what it holds; check_paths reports a link and a file over its cap), read as UTF-8 with errors replaced."""
    out = []
    for rel in rels:
        full = os.path.join(root, rel)
        if os.path.islink(full) or not os.path.isfile(full):
            continue
        try:
            text = facts.read_bounded(full, facts.file_cap(rel)).decode("utf-8", "replace")
        except facts.BoundedFileError:
            continue
        for no, line in enumerate(text.split("\n"), 1):
            for what, r in SECRETS:
                for m in r.finditer(line):
                    out.append(Finding("private-data", "%s:%d" % (rel, no), what, key=_key(m.group())))
    return out


def _key(text):
    return hashlib.sha256(text.encode()).hexdigest()[:16]


def scan_shapes(text, where, source=False, internal=False, email_text=None, internal_port_lines=frozenset(),
                host_paths=True, own_library=_no_library):
    """private-data.  Upstream copies (source=True) keep their authors'
    addresses and their own example addresses, so there only paths, keys,
    tokens and private repository names count.  In a directory no release
    carries (internal=True, internal_only) only a credential counts -- a key,
    a token and a URL's user information: the shapes that name a place are
    what the rule keeps out of a release, and these files are cut before one.
    email_text, when given, is the
    text the e-mail check reads instead: a proof's .v file with its string
    literals blanked, because an encoded payload holds random runs of an
    address's shape.  Everything else is still searched inside those strings.
    host_paths=False leaves host paths out for a change ledger, which records
    where its inputs live and is removed by release-tree; every other shape
    still counts.  own_library: a function of a line's number, the repository
    names that line may name as its private project's own library's
    (_own_library)."""
    out = []
    # a key and a token are literal credential material: they count wherever they are written
    rx = [("a private key", PRIVATE_KEY), ("an access token", TOKEN)]
    names = []
    if not internal:
        rx = ([("a host path", HOST_PATH)] if host_paths else []) + rx
        names = [("a private repository's name", REPOSITORY_PATH)]
        if not source:
            rx += [("a private address", PRIVATE_IP)]
            names += [("a private host name", PRIVATE_HOST_NAME)]
    markdown = urls.MARKDOWN.search(where) is not None
    for no, line in enumerate(text.split("\n"), 1):
        for what, r in rx:
            for m in r.finditer(line):
                out.append(Finding("private-data", "%s:%d" % (where, no), what, key=_key(m.group())))
        seen, variants = set(), [line]
        if markdown:
            variants.append(urls.unescape_markdown(line))
        variants += [urllib.parse.unquote(urls.unescape(v)) for v in variants if "%" in v or "&" in v]
        for variant in dict.fromkeys(variants):
            for what, r in names:
                for m in r.finditer(variant):
                    if r is REPOSITORY_PATH:
                        if _github_org_page(variant, m):
                            continue
                        name = (m.group(1) or m.group(2)).lower().rstrip(".").removesuffix(".git")
                        bare = m.group(1) is not None and m.group()[:1].lower() == "t"
                        if name in PUBLIC_REPOS or name in own_library(no) or (
                                no in internal_port_lines and bare and name == INTERNAL_PORT_REPO
                                and _repository_value(variant, m)):
                            continue
                    if r is PRIVATE_HOST_NAME and _ordinary_code_name(where, variant, m):
                        continue
                    if m.group().lower() not in seen:
                        seen.add(m.group().lower())
                        out.append(Finding("private-data", "%s:%d" % (where, no), what, key=_key(m.group())))
    if not source:
        for no, line in enumerate((text if email_text is None else email_text).split("\n"), 1):
            for m in EMAIL.finditer(line):
                if EMAIL_OK.search(m.group()):
                    continue
                # user:password@host or user@host after a scheme's //: a URL's user information, which can be
                # a credential, and which no exception for an address clears
                if URL_USERINFO_BEFORE.search(line[:m.start()]):
                    what = "a URL's user information"
                elif internal:
                    # internal_only: a plain address names a place, and release_tree cuts the directory whole
                    # before a release, so the rule does not read one there.  A URL's user information names no
                    # place: it is a live credential wherever it is written, as a key and a token are.
                    continue
                else:
                    what = "an e-mail address"
                out.append(Finding("private-data", "%s:%d" % (where, no), what, key=_key(m.group())))
    return out


# -------------------------------------------------------------------- links

# Where a link in rendered text may go, each compared with the parsed URL (urls.parse): its scheme, host and port, and
# a prefix of its path.
FIXED_URLS = ("https://github.com/google/oss-fuzz", "https://google.github.io/oss-fuzz",
              "https://rocq-prover.org", "https://github.com/rocq-prover/", "https://reuse.software",
              "https://spdx.org/", "https://www.qemu.org", "https://opam.ocaml.org")
URL = urls.URL
GHCR = re.compile(r"\bghcr\.io/theorem-labs/([a-z0-9._-]+)")
# The hosts GitHub serves a repository's contents from, the repository named first in the path; the API names it
# under /repos/.
GITHUB_HOSTS = ("github.com", "www.github.com", "codeload.github.com", "raw.github.com", "raw.githubusercontent.com")
WEB_SCHEMES = ("http", "https", "ws", "wss", "ftp")
NETWORK_HOST = re.compile(r"(?i)[a-z0-9._-]+|\[[0-9a-f:.]+\]")
# The dated snapshots of the Debian archive the runner image installs from
# (toolchain/runner.Dockerfile).  apt reads the archive over http, as Debian's
# own images do, and checks every index against the archive's signing key.
DEBIAN_SNAPSHOT = ("http://snapshot.debian.org/archive/debian/", "https://snapshot.debian.org/")
# The two pages AddressSanitizer's runtime carries in its .rodata strings and names in a report, which the
# comparison kit copies into a build record's evidence verbatim: the container-overflow page of the sanitizers
# wiki, and issue 189.  Each stands only as the link itself is written, character for character, and not as the
# page it opens: no other page of that repository, no query, no fragment, and no other spelling of the same page
# (another case, a port, a percent-encoded path, a dot segment).  "The link itself" is what urls.links gives
# (judge's ref): a bare URL to where the text stops carrying it, so the full stop or the bracket a report puts
# after it is not part of it, and a Markdown or an HTML destination with its escapes and character references
# decoded, which is the link GitHub builds from it.
SANITIZER_URLS = ("https://github.com/google/sanitizers/wiki/AddressSanitizerContainerOverflow",
                  "https://github.com/google/sanitizers/issues/189")
# The kit writes the runtime's output as a string literal, so the end of the printed line follows the URL as text:
# `...issues/189\n\x00`, four characters for \x00 and two for \n.  One such run at the very end, and the full stop
# a report may put before it, is not part of the page the line names, and nothing else is taken off: a backslash
# is a slash to a browser (urls.parse), so `...\..\..\evil-page` opens another page and stays a finding.
SANITIZER_TAIL = re.compile(r"\.?(?:\\(?:n|r|t|0|x[0-9a-fA-F]{2}))+$")
# Where GitHub shows a file of this repository, which its relative links resolve against: its own page, and for a
# README, the page of its directory too.
PAGE_BASE = "https://github.com/theorem-labs/oss-verify-proofs/blob/main/"
DIRECTORY_BASE = "https://github.com/theorem-labs/oss-verify-proofs/tree/main/"


def fact_urls(tree):
    out = set()

    def visit(v):
        if isinstance(v, dict):
            for x in v.values():
                visit(x)
        elif isinstance(v, list):
            for x in v:
                visit(x)
        elif isinstance(v, str) and v.startswith("https://"):
            out.add(v.rstrip("/"))

    for p in tree.projects.values():
        visit(p.data)
        for h in p.harnesses.values():
            visit(h.data)
    for f in tree.findings.values():
        visit(f.data)
    return out


def private_host(host):
    """Whether a machine host is an address that is not global, a single label, or a private suffix."""
    host = host.lower().rstrip(".")
    try:
        return not ipaddress.ip_address(host.strip("[]")).is_global
    except ValueError:
        pass
    try:
        address = socket.inet_ntoa(socket.inet_aton(host))
    except OSError:
        pass
    else:
        return not ipaddress.ip_address(address).is_global
    return "." not in host or any(host == s or host.endswith("." + s) for s in PRIVATE_SUFFIXES)


def theorem_repositories(u):
    """Every theorem-labs repository a parsed URL names, on any host: each path segment after a theorem-labs one
    (github.dev and vscode.dev/github/ open a repository too), or the first segment on the organisation's Pages host,
    lower case."""
    parts = u.path.lower().split("/")
    out = [r.removesuffix(".git") for o, r in zip(parts, parts[1:]) if o == "theorem-labs" and r]
    if u.host.lower().rstrip(".") == "theorem-labs.github.io" and len(parts) > 1 and parts[1]:
        out.append(parts[1].removesuffix(".git"))
    return out


def public_repository(u):
    """Whether a parsed URL is one of the public theorem-labs repositories, where GitHub serves it."""
    path = u.path.lower()
    if u.host == "api.github.com" and path.startswith("/repos/"):
        path = path[len("/repos"):]
    elif u.host not in GITHUB_HOSTS:
        return False
    parts = path.split("/")
    return len(parts) > 2 and parts[1] == "theorem-labs" and parts[2].removesuffix(".git") in PUBLIC_REPOS


def _prefix_of(u, allowed, segment=False):
    """Whether allowed (a URL) names the same scheme, host and port as u and a prefix of its path; with segment=True,
    a prefix that ends where a path segment ends."""
    try:
        a = urls.parse(allowed)
    except urls.Unreadable:
        return False
    if a is None or (u.scheme, u.host, u.port) != (a.scheme, a.host, a.port) or not u.path.startswith(a.path):
        return False
    return not segment or len(u.path) == len(a.path) or a.path.endswith("/") or u.path[len(a.path)] == "/"


def sanitizer_url(ref):
    """Whether a link (ref, as urls.links read it) names one of the two pages ASan's runtime prints: written
    exactly as SANITIZER_URLS writes it, or with the one escaped tail the comparison kit's quoted output leaves
    after it (SANITIZER_TAIL).  Nothing else is taken off either end."""
    return bool(ref) and (ref in SANITIZER_URLS or SANITIZER_TAIL.sub("", ref, count=1) in SANITIZER_URLS)


def judge(u, known, strict=True, full=True, ref=None, own_library=frozenset()):
    """Whether a parsed link (urls.parse) may stay: it must not name a machine on a private network or a theorem-labs
    repository that is not public, but own_library's (the names the link's line may name as its private project's own
    library: _own_library).  A full link in rendered text, docs and facts (strict) must also be https and be
    one of ours, OSS-Fuzz's, one the facts record, or one of the two pages ASan's runtime prints, written as
    sanitizer_url wants it: ref, the link urls.links read, not the page it opens.  A link that opens nothing
    (None) is judged by its text alone."""
    if u is None:
        return True
    if u.host and (u.scheme in WEB_SCHEMES or NETWORK_HOST.fullmatch(u.host)) and private_host(u.host):
        return False
    if any(r not in PUBLIC_REPOS and r not in own_library for r in theorem_repositories(u)):
        return False
    if public_repository(u):
        return True
    if not (strict and full) or any(_prefix_of(u, d) for d in DEBIAN_SNAPSHOT):
        return True
    if u.scheme != "https":
        return False
    return (sanitizer_url(ref) or any(_prefix_of(u, f) for f in FIXED_URLS)
            or any(_prefix_of(u, k, segment=True) for k in known))


def link_strict(rel):
    """Rendered text, docs and facts: everything but the tools (tools/, and dev/enroll/, the enrollment scripts'
    place outside it), the tests and the workflows, whose links are code, not content."""
    return not rel.startswith(("tools/", "dev/enroll/", "tests/", ".github/"))


def _bases(where):
    bases = [PAGE_BASE + where]
    if os.path.basename(where).lower().startswith("readme"):
        bases.append((DIRECTORY_BASE + os.path.dirname(where)).rstrip("/"))
    return [urls.parse(b) for b in bases]


def scan_links(text, where, known, strict=True, own_library=_no_library):
    """links.  Every link a reader can follow (urls.links), judged by what a browser opens for it: an absolute URL
    alone, a Markdown or HTML link against each page that shows the file, and another reading of the same text
    (GitHub's extent of a bare URL, the text with character references decoded, a line of Markdown as GitHub shows
    its text) for privacy only.  A URL urls.parse cannot read for sure is refused wherever this rule reads; one that
    opens nothing, only in rendered text, docs and facts (strict), and only as an absolute URL.  One finding per line
    and target.  own_library: as scan_shapes takes it, of the link's line."""
    out, reported, judged = [], set(), set()
    bases = None
    for link in urls.links(text, bool(urls.MARKDOWN.search(where))):
        if link.kind == "link":
            bases = bases or _bases(where)
        targets = []
        for base in (bases if link.kind == "link" else [None]):
            try:
                targets.append(urls.parse(link.ref, base))
            except urls.Unreadable:
                targets.append(False)
        for target in targets:
            key = (link.line, link.ref if target is None or target is False else str(target))
            if (key, link.kind == "reading") in judged:
                continue
            judged.add((key, link.kind == "reading"))
            if target is False:
                ok = False
            elif target is None:
                ok = link.kind != "url" or not strict
            else:
                ok = judge(target, known, strict, full=link.kind != "reading", ref=link.ref,
                           own_library=own_library(link.line))
            if not ok and key not in reported:
                reported.add(key)
                out.append(Finding("links", "%s:%d" % (where, link.line),
                                   "a link that is not on the allowlist: %s" % link.text))
    for no, line in enumerate(text.split("\n"), 1):
        for m in GHCR.finditer(line):
            if not m.group(1).startswith("oss-fuzz-theorems-"):
                out.append(Finding("links", "%s:%d" % (where, no), "an image that is not one of ours: %s" % m.group()))
    return out


# ------------------------------------------------------------------- proofs

FORBIDDEN_IN_PROOFS = re.compile(
    r"\b(?:Axiom|Axioms|Parameter|Parameters|Conjecture|Admitted|admit|give_up|Declare\s+ML\s+Module"
    r"|Declare\s+(?:Instance|Module)|Admit\s+Obligations"   # each declares an axiom wherever it stands
    r"|Redirect|Add\s+(?:Rec\s+)?LoadPath|Add\s+ML\s+Path|(?:Separate\s+|Recursive\s+)?Extraction"
    r"|Unset\s+(?:\w+\s+)*Checking|bypass_check|ReadFile(?:Bytes|Int63|String)|Locate\s+File)\b"
    r"|\bPrimitive\s+\w+\s*:"                      # a primitive declaration, not Set Primitive Projections
    r"|\bRegister\s+(?:Inline\s+)?[\w.]+\s+as\b")
# An attribute that prints a note of the file's choosing wherever its constant is used: deprecated and warn.  The note
# can print the line oft check's audit takes for an empty list of assumptions (the Verified Linux team's report,
# 2026-10-29).  Strings are blanked first, so `#[warnings="-deprecated"]`, which silences warnings, is not one.  The
# command form, `Attributes deprecated(...).`, sets them for the whole file; it is refused below, as a sentence.
NOTE_ATTRIBUTE = re.compile(r"#\[[^\]]*?\b(deprecated|warn)\b")
# Variable, Hypothesis and Context are a Section's assumptions, which End turns into arguments; outside any Section
# each is a #[local] Axiom or Parameter of the file.  A sentence's first word, after its control flags, attributes and
# legacy attributes, opens or closes what it names: Section, Module (not `Module M := N.`, an alias) and End.  Under
# the control flag Fail or Succeed it opens or closes nothing: Rocq runs that sentence and then undoes it, so neither
# `Succeed Section S.` nor `Fail Section S.` (which succeeds inside a proof, where Section is an error) opens one.  The
# flag is a control word, never an attribute: `#[Fail] End S.` closes the Section (Rocq only warns of an unsupported
# attribute, and a proof can silence that warning).
# Reset goes back in the file (`Section S. Reset S.` leaves no Section open, and rocq compile accepts it), so it is
# refused, but for `Reset Ltac Profile`, which only clears a profile; and so is Attributes, the command form of the
# note attributes.
_SECTION_WORD = re.compile(r"(Section|Module|End|Variables?|Hypothes[ie]s|Context|Reset|Attributes)\b")
_UNDOING_FLAG = re.compile(r"\b(?:Fail|Succeed)\b")
_ATTRIBUTE = re.compile(r"#\[[^\]]*\]")
_LTAC_PROFILE = re.compile(r"\s+Ltac\s+Profile\b")


def _assumptions_outside_sections(stripped, where):
    out, opened = [], []
    ends = [e.end() for e in _SENTENCE_END.finditer(stripped)]
    for start, stop in zip([0] + ends, ends + [len(stripped)]):
        lead = _COMMAND_LEAD.match(stripped, start)
        m = _SECTION_WORD.match(stripped, lead.end())
        if not m or m.start() >= stop:
            continue
        word = m.group(1)
        no = stripped.count("\n", 0, m.start()) + 1
        if word == "Reset":
            if not _LTAC_PROFILE.match(stripped, m.end()):
                out.append(Finding("proofs", "%s:%d" % (where, no), "'Reset' goes back in the file, past an open Section "
                                   "too, which is not allowed in a proof"))
            continue
        if word == "Attributes":
            out.append(Finding("proofs", "%s:%d" % (where, no), "'Attributes' sets attributes of the whole file (a "
                               "deprecated or warn note prints wherever it is used), which is not allowed in a proof"))
            continue
        if word in ("Section", "Module", "End") and _UNDOING_FLAG.search(_ATTRIBUTE.sub(" ", lead.group())):
            continue
        if word == "Section":
            opened.append(word)
        elif word == "Module":
            if ":=" not in stripped[m.end():stop]:
                opened.append(word)
        elif word == "End":
            if opened:
                opened.pop()
        elif "Section" not in opened:
            out.append(Finding("proofs", "%s:%d" % (where, no),
                               "%r outside a Section declares an axiom, which is not allowed in a proof" % word))
    return out


# The commands that make a compile read a file: Load, Cd (which moves where Load and Extra Dependency look) and Extra
# Dependency.  Load and Cd are commands only where a sentence starts (the file's start, after a `.` and white space,
# or after a proof-mode bullet or brace), after any control flags (Time, Fail, Timeout 5, ...), attributes (#[...])
# and legacy attributes (Local, Program, ...); elsewhere they are ordinary names, such as the model's instruction
# constructor `Load`.  Extra Dependency is two keywords anywhere.  Every pattern runs over the whole text with comments
# and strings blanked, so a command split across lines is found.
FILE_WORDS = re.compile(r"\b(?:(Load|Cd)|(Extra\s+Dependency))\b")
# what may stand between a sentence's start and Load or Cd: proof-mode bullets and braces (sentences with no `.`), a
# goal selector before a brace (`1:{`, `[g]:{`), Rocq's control flags, attributes and legacy attributes, and a
# byte-order mark (Rocq skips one at a file's start).
# Rocq takes the flags, then the attributes, then the legacy attributes; this takes them in any order, which refuses no
# more than sentences that Rocq rejects too.
_COMMAND_LEAD = re.compile(
    r"\ufeff?(?:\s|[-+*{}]|#\[[^\]]*\]"
    r"|(?:\d\w*(?:\s*[-,]\s*\d\w*)*|\[\s*\w+\s*\]|!|all|par)\s*:\s*\{"
    r"|(?:Time|Instructions|Profile|Redirect|Timeout\s+\d\w*|Fail|Succeed"
    r"|Local|Global|Export|Polymorphic|Monomorphic|Cumulative|NonCumulative|Private|Program)\b)*")
# A sentence ends at a `.` that a blank follows, but not at the second dot of a bare `..`, which Rocq lexes as one
# token (a recursive notation's body, stdpp's `λ..`, `∀..`, `∃..`): `(cons x .. Section (cons y nil) ..)` is one
# sentence, and no Section opens in it.  A third dot (`...`) ends one, as Rocq lexes `..` then `.`.
_SENTENCE_END = re.compile(r"(?<!(?<!\.)\.)\.(?=[ \t\n\r])")
# Rocq lexes a declared token whole, so a `(` or a `"` inside one opens no comment or string there, where rocq.strip
# opens one and blanks what follows: after `Notation "<(*" := 0.` and `Definition a := <(*.`, every later sentence is
# hidden from these rules.  Only a declared token with a `"`, or with a `(` after its first character, can do that.
# The libraries that proofs import declare four such tokens, `.(`, `` `( ``, `module:(` and `red_flags:(` (Print
# Keywords after importing each module a proof imports); so a proof declares no token with a `"`, or with a `(` after
# anything but `.`, `` ` `` or `:`, and writes no comment right after `.`, `` ` `` or `:`.  Nor does a proof declare a
# token that ends in `.` (but `..`, Rocq's own): after `Notation "x '+.' 'Section' y" := 0.`, the sentence
# `Check (1 +. Section 2).` reads to these rules as a sentence that ends at `+.` and one that opens a Section.
_TOKEN_DECLARATION = re.compile(r"(?:Notation|Infix|where)\b")   # no leading \b: it stops re's literal search
_UNSAFE_TOKEN = re.compile(r'""|[^ \t\n\r.`:]\(')
_COMMENT_AFTER = re.compile(r"[.`:](?=\(\*)")


def _file_commands(stripped, where, rule, what):
    out, starts = [], None
    for m in FILE_WORDS.finditer(stripped):
        if m.group(1):
            if starts is None:   # where each sentence starts: the text's start, and after each `.` that a blank follows
                starts = [0] + [e.end() for e in _SENTENCE_END.finditer(stripped)]
            if not _COMMAND_LEAD.fullmatch(stripped, starts[bisect.bisect_right(starts, m.start()) - 1], m.start()):
                continue
        no = stripped.count("\n", 0, m.start()) + 1
        word = " ".join(m.group().split())
        out.append(Finding(rule, "%s:%d" % (where, no), "%r is not allowed in %s" % (word, what)))
    return out


def _lexer_doubts(text, stripped, where):
    """The places where Rocq could lex text otherwise than rocq.strip does (see _TOKEN_DECLARATION)."""
    out = []
    for m in _COMMENT_AFTER.finditer(text) if ".(*" in text or "`(*" in text or ":(*" in text else ():
        if stripped[m.start()] == m.group() and stripped[m.end()] == " ":   # code, then a comment's `(*`
            out.append(Finding("proofs", "%s:%d" % (where, text.count("\n", 0, m.end()) + 1),
                               "a comment right after %r, which a token can take its '(' into, is not allowed in a "
                               "proof" % m.group()))
    stop = 0
    for m in _TOKEN_DECLARATION.finditer(stripped):
        before = stripped[m.start() - 1] if m.start() else " "
        if m.start() < stop or before.isalnum() or before == "_":
            continue
        end = _SENTENCE_END.search(stripped, m.end())   # the string literals of this sentence after the keyword
        stop, at = (end.start() if end else len(stripped)), m.end()
        for kind, piece, inside in rocq.tokens(text[at:stop]):
            if kind == "string" and not inside and _UNSAFE_TOKEN.search(piece, 1, len(piece) - 1):
                out.append(Finding("proofs", "%s:%d" % (where, text.count("\n", 0, at) + 1),
                                   "a notation token with a '\"', or a '(' after anything but '.', '`' or ':', is not "
                                   "allowed in a proof", key=piece))
            if kind == "string" and not inside:
                for word in piece[1:-1].split():
                    token = word[1:-1] if len(word) > 2 and word[0] == word[-1] == "'" else word
                    if token.endswith(".") and token != "..":
                        out.append(Finding("proofs", "%s:%d" % (where, text.count("\n", 0, at) + 1),
                                           "a notation token that ends in '.' is not allowed in a proof: these rules "
                                           "would end a sentence there", key=piece))
                        break
            at += len(piece)
    return out


# A wall-clock limit makes a check depend on the machine's load: a tactic that fits its limit on an idle machine can
# run out on a loaded one. So no Rocq file of the repository (proofs/, theories/, projects/, tests/ and the templates
# that render .v files) states one: no `timeout` or `timeoutf` used as a name at all (the Ltac tactical with a number
# or a variable, Ltac2's `Control.timeout` and `Control.timeoutf` under any qualifier or import), no
# `Set Default Timeout <n>.`, no `Timeout <n>` command prefix, unless the line that has it ends with a justification
# comment, `(* timeout-ok: <why> *)`, saying why an expiry cannot fail the check: it only makes the proof take another
# alternative that is itself a proof step. A reviewer judges the reason; lint checks only that one is there.
WALL_CLOCK = (
    re.compile(r"(?<![A-Za-z0-9_'])(?:[A-Za-z_][A-Za-z0-9_']*\.)*timeoutf?(?![A-Za-z0-9_'])"),
    re.compile(r"Set\s+Default\s+Timeout\s+[0-9]+"),
)
TIMEOUT_COMMAND = re.compile(r"(?<![A-Za-z0-9_'.])Timeout\s+[0-9]+(?=\s)")
TIMEOUT_JUSTIFIED = re.compile(r"\(\*\s*timeout-ok:\s*(?:(?!\*\))\S)(?:(?!\*\))[^\n])*\*\)[ \t]*$")
# A Ltac2 `@external` binds a name to any OCaml primitive of a plugin, `"timeout"` among them, under a name that need
# not say so. So each one must bind a primitive on this list, (plugin, primitive), and no justification comment
# allows another. The declaration is read with its comments blanked and its string literals kept.
EXTERNAL_ALLOWED = frozenset({("rocq-runtime.plugins.ltac2", "string_get")})
EXTERNAL = re.compile(r"@\s*external\b")
_STRING = r'"((?:[^"]|"")*)"'
EXTERNAL_PRIMITIVE = re.compile(r"[^\"]*?:=\s*" + _STRING + r"\s*" + _STRING)


def wall_clock_scanned(rel):
    """Whether rel is a Rocq file outside the proofs folders that the wall-clock check reads (scan_proof reads those,
    proof_rocq)."""
    return (rel.endswith(".v") and rel.startswith(("theories/", "projects/", "tests/")) and not proof_rocq(rel)
            or rel.startswith("tools/oft/templates/") and rel.endswith(".v.tmpl"))


def timeout_violations(code, commented):
    """(line, text) of each wall-clock limit lint refuses: `code` is a file's text without comments or string
    literals, `commented` the same with its comments kept (rocq.strip, comments=False); both keep its offsets."""
    lines = commented.split("\n")
    out = set()
    for regex in WALL_CLOCK + (TIMEOUT_COMMAND,):
        for m in regex.finditer(code):
            if regex is TIMEOUT_COMMAND and re.search(r"Default\s*$", code[max(0, m.start() - 40):m.start()]):
                continue
            no = code.count("\n", 0, m.start()) + 1
            if not TIMEOUT_JUSTIFIED.search(lines[no - 1]):
                out.add((no, " ".join(m.group().split())))
    return sorted(out)


def external_violations(code, uncommented):
    """(line, primitive) of each Ltac2 `@external` that binds no primitive of EXTERNAL_ALLOWED: `code` is a file's text
    without comments or string literals, `uncommented` the same with its string literals kept (rocq.strip,
    strings=False); both keep its offsets. primitive is None where the declaration cannot be read."""
    out = []
    for m in EXTERNAL.finditer(code):
        p = EXTERNAL_PRIMITIVE.match(uncommented, m.end())
        prim = (p.group(1).replace('""', '"'), p.group(2).replace('""', '"')) if p else None
        if prim not in EXTERNAL_ALLOWED:
            out.append((code.count("\n", 0, m.start()) + 1, prim))
    return out


def scan_wall_clock(text, where, stripped=None):
    """The findings of the wall-clock check (timeout_violations, external_violations) on the Rocq file `text`."""
    if "imeout" not in text and "external" not in text:
        return []
    stripped = rocq.strip(text) if stripped is None else stripped
    out = [Finding("proofs", "%s:%d" % (where, no),
                   "'%s' is not allowed in Rocq source: a wall-clock limit can fail a check on a loaded machine "
                   "(keep one only on a line that ends with '(* timeout-ok: <why> *)')" % form)
           for no, form in timeout_violations(stripped, rocq.strip(text, comments=False))]
    out += [Finding("proofs", "%s:%d" % (where, no),
                    "a Ltac2 @external may bind only a primitive of lint.EXTERNAL_ALLOWED (%s); this one binds %s"
                    % (", ".join('"%s" "%s"' % a for a in sorted(EXTERNAL_ALLOWED)),
                       '"%s" "%s"' % prim if prim else "a primitive lint cannot read"))
            for no, prim in external_violations(stripped, rocq.strip(text, strings=False))]
    return out


def scan_proof(text, where):
    out = []
    stripped = rocq.strip(text)
    for m in FORBIDDEN_IN_PROOFS.finditer(stripped):
        no = stripped.count("\n", 0, m.start()) + 1
        word = " ".join(m.group().split())
        out.append(Finding("proofs", "%s:%d" % (where, no), "%r is not allowed in a proof" % word))
    for m in NOTE_ATTRIBUTE.finditer(stripped):
        no = stripped.count("\n", 0, m.start()) + 1
        out.append(Finding("proofs", "%s:%d" % (where, no), "the attribute %r is not allowed in a proof" % m.group(1)))
    out += (_assumptions_outside_sections(stripped, where) + _lexer_doubts(text, stripped, where)
            + _file_commands(stripped, where, "proofs", "a proof"))
    return out + scan_wall_clock(text, where, stripped)


# A proof file's licence lines (NOTICE; docs/adding-a-proof.md, requirement 7) open it, in its first HEADER_LINES
# lines.  A file made from Anthropic's proofs has Anthropic's two lines, its copyright and
# `SPDX-License-Identifier: Apache-2.0 OR MIT`, and its fuzz target's build record names the three texts that licence
# ships with; a file written here is under the MIT licence, with no licence line or the one line `MIT`; a file that
# restates a program's instruction words or holds data computed from one opens with the comment of its kind
# (PROGRAM_LINES) and has no other licence lines, since its code keeps the program's licences; and a third-party proof
# file, taken from another project's proofs, keeps that project's licence, one of THIRD_PARTY_LICENCES, and is a row
# of THIRD_PARTY that pins its bytes (load_third_party).  In a project whose project.yaml says `release: private` and
# whose folder holds a NOTICE file (private_projects), a file written here is under that NOTICE instead, and has the
# two lines PRIVATE_LINES with {project} its own project: no proof file there is under MIT.  PRIVATE_LINES is the one
# statement of that form: requirement 7 quotes it, and test_lint.Licence.test_the_docs_quote_the_private_lines holds
# the two together.
ANTHROPIC_TEXTS = ("LICENSES/anthropic-proofs-LICENSE", "LICENSES/anthropic-proofs-LICENSE-MIT",
                   "LICENSES/anthropic-proofs-NOTICE")
ANTHROPIC_LICENCE = "Apache-2.0 OR MIT"
PROOF_LICENCES = (ANTHROPIC_LICENCE, "MIT")
THIRD_PARTY = "tools/oft/third-party-proofs.yaml"
# the schema of a row of THIRD_PARTY (schemas/third-party-proofs.yaml), and the licences it lets a row give
THIRD_PARTY_SCHEMA = "third-party-proofs"
THIRD_PARTY_LICENCES = tuple(schema.load_schema(THIRD_PARTY_SCHEMA)["defs"]["row"]["fields"]["spdx"]["values"])
PRIVATE_LICENCE = "LicenseRef-Proprietary"
# a project's NOTICE, as a pattern of paths.py (lint alone admits it: LINT_ONLY_HAND)
PROJECT_NOTICE = "projects/{project}/NOTICE"
PRIVATE_LINES = ("(* Copyright Theorem Labs. All rights reserved: see %s. *)" % PROJECT_NOTICE,
                 "(* SPDX-License-Identifier: %s *)" % PRIVATE_LICENCE)
PROGRAM_LINES = ("(* Machine-generated data computed from the task's compiled program image",
                 "(* This file states or restates instruction words of the task's compiled program")
HEADER_LINES = 10
# NOTICE, and its sentence on the classifiers and the originals that a harness publishes (docs/licensing.md, "Harness
# copies and binaries"), which the root README says too (templates/README.md.tmpl): while a harness.yaml publishes one,
# NOTICE holds the sentence (check_notice).  NOTICE wraps its lines, so there each run of blanks and line ends reads
# as one space.
NOTICE = "NOTICE"
NOTICE_IMAGES = ("The classifiers and the originals that a harness publishes are under the licences of the code that "
                 "they are built from, as its builds are.")
# a licence tag wherever it is on its line, in any comment style: a tag the rule cannot see ships the wrong licence.  A
# carriage return before a line feed is part of the line end, here and in _ANTHROPIC_COPYRIGHT.
_SPDX = re.compile(r"SPDX-License-Identifier:[ \t]*(.*?)[ \t\r]*(?:\*\)|$)", re.M)
_ANTHROPIC_COPYRIGHT = re.compile(r"^\(\* Copyright \d{4} Anthropic PBC \*\)[ \t]*\r?$", re.M)
# each copyright of Anthropic a line names: one that is not exactly _ANTHROPIC_COPYRIGHT was changed, unless it restates
# that line's words in a file that has it (_ANTHROPIC_RESTATED)
_ANTHROPIC_NAMED = re.compile(r"Copyright\b[^\n]*?\bAnthropic\b", re.I)
# Anthropic's copyright in its own words, ending there: how a doc comment under the licence lines restates the notice
_ANTHROPIC_RESTATED = re.compile(r"Copyright \d{4} Anthropic PBC(?=[ \t]*(?:[.;,]|\*\)|\r?$))", re.M)
# the words of PRIVATE_LINES' copyright line, for any project (group 1), wherever they are on a line, in any comment: in
# the head they name the file's own project, and below it they are out of place.  _PRIVATE_ANY_CASE reads them in any
# case, as _ANTHROPIC_NAMED reads Anthropic's name: in the head a copy that is not in _PRIVATE_NAMED's case was changed.
# _PRIVATE_MARK is a plain text, lower-cased, that every match holds, for a cheap search first.
_PRIVATE_WORDS = PRIVATE_LINES[0][len("(* "):-len(". *)")]
_PRIVATE_MARK = _PRIVATE_WORDS.split("{project}")[0].lower()
_PRIVATE_NAMED = re.compile(re.escape(_PRIVATE_WORDS).replace(re.escape("{project}"), r"([^/\s]+)"))
_PRIVATE_ANY_CASE = re.compile(_PRIVATE_NAMED.pattern, re.I)
# a licence tag, a copyright of Anthropic, changed or not, or the words of PRIVATE_LINES' copyright line, in any case,
# wherever it is on its line: below HEADER_LINES it is out of place
_LICENCE_LINE = re.compile(r"SPDX-License-Identifier:|(?i:Copyright\b[^\n]*?\bAnthropic\b)|(?i:%s)"
                           % _PRIVATE_NAMED.pattern)
# the copyright line of PRIVATE_LINES, for any project (group 1), as a whole line: how scan_licence reads it in the head
_PRIVATE_COPYRIGHT = re.compile("^" + re.escape(PRIVATE_LINES[0]).replace(re.escape("{project}"), r"([^/\s]+)")
                                + r"[ \t]*\r?$", re.M)
# a licence named in words: in a head with no licence line (no tag, no copyright of Anthropic's and no copyright line of
# a project's NOTICE) a file under another licence would read as one written here, so scan_licence asks it for the tag
# of the licence it names.  Each entry starts and ends on a word boundary.  The words of a notice match in any case; a
# short name only in the spellings of the licence itself (GPL, not gpl), since in other cases it is an ordinary
# identifier (`Definition mpl := 0.`).  A phrase may wrap, so between two of its words any run of blanks, line ends and
# comment marks (_WRAP) stands for the space; each "Licen[cs]e" takes either spelling.
_WRAP = r"(?:\s|\(\*|\*\)|\*)+"
_LICENCE_WORDS = re.compile(r"\b(?:%s)\b" % "|".join(["(?i:%s)" % w.replace(" ", _WRAP) for w in (
    # the licences by the names their notices give them
    "GNU General Public Licen[cs]e", "GNU Lesser General Public Licen[cs]e", "GNU Library General Public Licen[cs]e",
    "GNU Affero General Public Licen[cs]e", "Apache Licen[cs]e", "Mozilla Public Licen[cs]e",
    "Eclipse Public Licen[cs]e", "Boost Software Licen[cs]e", "BSD Licen[cs]es?", "ISC Licen[cs]e",
    "Creative Commons",
    # the opening words of the notices that need not name their licence: MIT's grant, BSD's conditions, the GNU
    # licences' first sentence, and the grant of any licence by name
    "Permission is hereby granted", "Redistribution and use in source and binary forms",
    "This program is free software", "Licen[cs]ed under")] + [
    # the short names a notice or a comment uses for them, a version joined on or not (GPLv2, LGPL-2.1, CECILL-2.1)
    r"[LA]?GPL(?:v\d+(?:\.\d+)*)?", "MPL", "CeCILL", "CECILL"]))


@functools.lru_cache(maxsize=1)   # scan_file reads the same head twice, in scan_licence and then in bare_licence
def _licence_words(head):
    """The matches of _LICENCE_WORDS in a file's head outside its string literals, whose encoded data can spell a short
    name by chance (as the e-mail and link checks read a proof); offsets are the head's.  A tuple, since the cache
    gives each caller the same one."""
    if _LICENCE_WORDS.search(head) is None:   # most heads name none: lex only the ones that may
        return ()
    return tuple(_LICENCE_WORDS.finditer(rocq.strip(head, comments=False)))


# a Rocq file of a fuzz target's proofs folder, in either layout (layout.PROOF_HARNESS_PROJECT_RE)
_PROJECT_PROOF = re.compile(layout.PROOF_HARNESS_PROJECT_RE + r"/.+\.v$")


def anthropic_targets(root):
    """The fuzz targets, as "<project>/<harness>" (layout.unit_of), whose build record (provenance/PROVENANCE.yaml of
    the fuzz target's proofs folder, in either layout) lists every one of ANTHROPIC_TEXTS under proofs.texts.  A
    record that cannot be read counts as naming none; facts.load reports it."""
    out = set()
    for top, lay in (("proofs", layout.OLD), ("projects", layout.NEW)):
        base = os.path.join(root, top)
        for p in sorted(os.listdir(base)) if os.path.isdir(base) else []:
            pd = os.path.join(base, p)
            for h in sorted(os.listdir(pd)) if os.path.isdir(pd) else []:
                path = os.path.join(root, layout.record_path(p, h, lay))
                if (lay == layout.OLD and "proofs/" + p in layout.NO_PLACE) or not os.path.isfile(path):
                    continue
                try:
                    data = yamlio.load_file(path)
                except (OSError, yamlio.YamlError):
                    continue
                pr = data.get("proofs") if isinstance(data, dict) else None
                texts = pr.get("texts") if isinstance(pr, dict) else None
                if isinstance(texts, list) and all(t in texts for t in ANTHROPIC_TEXTS):
                    out.add("%s/%s" % (p, h))
    return frozenset(out)


# The table of third-party proof files, THIRD_PARTY: what it holds, and the one exemption its rows make.  Each row pins
# one file of a fuzz target's proofs folder that comes from another project's proofs (docs/adding-a-proof.md,
# requirement 7, case 3) by its path and the SHA-256 of its bytes, and names its licence (spdx, one of
# THIRD_PARTY_LICENCES), where it comes from (upstream: the repository, as <owner>/<name> on GitHub, the commit and,
# when given, the file's path there) and the lines of the upstream author's notice (notice: its first and last line,
# from 1).  Those bytes, and no others, are under that licence (scan_licence), and the notice's lines are the one part
# of them the private-data rule does not read (scan_file): the notice names its author's address, and every other line
# of the file is read as in any proof.  The row names the lines by number, so the table holds no address of its own;
# the pinned bytes fix what those lines hold.  A file under the row's licence ships with that licence's text: the tree
# holds it at LICENSES/<owner>-<name>-LICENSE of the upstream repository, a text of PINNED_VERBATIM but none of
# ANTHROPIC_TEXTS, so lint holds it to its bytes (scan_third_party_text, scan_pinned).  A row may come before its file:
# a row whose file the tree does not hold publishes nothing, and is no finding.  Only this module reads the table and
# the schema of its rows, schemas/third-party-proofs.yaml (keys.NOT_THE_CHECKER names both).


def _third_party_row(row, at):
    """What is wrong with row, the row of THIRD_PARTY at `at` (files[<i>]), each naming its field: what the schema of
    a row says (THIRD_PARTY_SCHEMA, schema.validate_def), and then what it cannot say, that its path is a Rocq file of
    a fuzz target's proofs folder and its notice's first line is not after its last."""
    problems = schema.validate_def(THIRD_PARTY_SCHEMA, "row", row, at)
    if problems:
        return problems
    if not proof_rocq(row["path"]):
        problems.append("%s.path: %r is not a Rocq file of a fuzz target's proofs folder" % (at, row["path"]))
    if row["notice"]["first"] > row["notice"]["last"]:
        problems.append("%s.notice: its first line, %d, is after its last, %d"
                        % (at, row["notice"]["first"], row["notice"]["last"]))
    return problems


def load_third_party(root):
    """({path in the per-project layout (layout.canonical): row of THIRD_PARTY}, the licence findings of the table
    itself).  A tree without the table has no third-party proof file.  A table that does not load, or is not
    one mapping whose one key, `files`, is the list of its rows, is a finding and gives no row; a row that is not of its
    form (_third_party_row), or whose path an earlier row names, in either layout, is a finding that names what is
    wrong, field by field, and is no row, so its file is held to the rules of any other proof file."""
    p = os.path.join(root, THIRD_PARTY)
    if not os.path.isfile(p):
        return {}, []
    try:
        with open(p, encoding="utf-8") as f:
            data = yamlio.load(f.read(), THIRD_PARTY)
    except (OSError, UnicodeDecodeError, yamlio.YamlError) as e:
        return {}, [Finding("licence", THIRD_PARTY, "the table of third-party proof files does not load: %s" % e)]
    if not isinstance(data, dict) or set(data) != {"files"} or not isinstance(data["files"], list):
        return {}, [Finding("licence", THIRD_PARTY, "the table of third-party proof files is one mapping whose one "
                                                  "key, files, is the list of its rows (files: [] when there is none)")]
    rows, out = {}, []
    for i, row in enumerate(data["files"]):
        at = "files[%d]" % i
        problems = _third_party_row(row, at)
        if not problems and layout.canonical(row["path"]) in rows:
            problems = ["%s.path: %r is a path an earlier row names, in either layout" % (at, row["path"])]
        if problems:
            out.append(Finding("licence", THIRD_PARTY, "; ".join(problems)))
            continue
        rows[layout.canonical(row["path"])] = row
    return rows, out


def file_sha256(path, cap):
    """The SHA-256, in hex, of the bytes of the regular file at path, of at most cap bytes; None when it is not one
    (facts.read_bounded)."""
    try:
        return hashlib.sha256(facts.read_bounded(path, cap)).hexdigest()
    except facts.BoundedFileError:
        return None


def scan_pinned(path, rel):
    """The licence finding of rel, the file at path, when it is a text of PINNED_VERBATIM whose bytes are not its pin,
    whatever the other rules find in it.  Any other file has none."""
    if rel not in PINNED_VERBATIM:
        return []
    digest = file_sha256(path, facts.file_cap(rel))
    if digest == PINNED_VERBATIM[rel]:
        return []
    return [Finding("licence", rel, "a licence text that lint pins is the bytes of its pin (PINNED_VERBATIM in "
                                    "tools/oft/lint.py): this file's SHA-256 is %s, the pin's %s "
                                    "(docs/adding-a-proof.md, requirement 7)"
                                    % (digest or "unread", PINNED_VERBATIM[rel]))]


def third_party_text(row):
    """The path of the licence text of a row of THIRD_PARTY: LICENSES/<owner>-<name>-LICENSE of its upstream
    repository, <owner>/<name> (docs/adding-a-proof.md, requirement 7, case 3)."""
    return "LICENSES/%s-LICENSE" % row["upstream"]["repository"].replace("/", "-")


def scan_third_party_text(root, where, row):
    """The licence finding of the file at where, a row's file of THIRD_PARTY whose bytes are the ones its row pins and
    so under the row's licence, when the text of that licence (third_party_text) is not a text of PINNED_VERBATIM, is
    one of Anthropic's own (ANTHROPIC_TEXTS: an upstream anthropic/proofs names one), or the tree does not hold it.
    scan_pinned holds the text itself to its pin."""
    text = third_party_text(row)
    if text not in PINNED_VERBATIM or text in ANTHROPIC_TEXTS:
        missing = "lint pins no third-party licence text at that path (PINNED_VERBATIM in tools/oft/lint.py)"
    elif not os.path.isfile(os.path.join(root, text)):
        missing = "the tree holds no file there"
    else:
        return []
    return [Finding("licence", where, "a third-party proof file under %s has that licence's text in the tree, at %s, "
                                      "whose bytes lint pins: %s (docs/adding-a-proof.md, requirement 7)"
                                      % (row["spdx"], text, missing))]


def check_notice(tree):
    """licence: while a harness.yaml publishes a classifier or an original (lists it and does not withhold it:
    facts.Harness.classifier_builds, original_builds), NOTICE holds NOTICE_IMAGES, its sentence on them; else one
    finding at NOTICE names the first such harness.  A NOTICE that is not read as text (none, a link, a file over its
    cap) holds no sentence, and a tree that publishes neither has no finding, whatever NOTICE says.  The rule reads
    the whole tree, so every lint runs it, one with --changed-only too: a change to NOTICE alone that drops the
    sentence is refused."""
    first = next((h for h in tree.harnesses() if h.classifier_builds() or h.original_builds()), None)
    if first is None:
        return []
    text = read_text(tree.path(NOTICE), facts.file_cap(NOTICE))
    if text is not None and NOTICE_IMAGES in " ".join(text.split()):
        return []
    return [Finding("licence", NOTICE, "%s publishes a classifier or an original, so NOTICE holds the sentence on them "
                                       "(NOTICE_IMAGES in tools/oft/lint.py; docs/licensing.md), and it does not: %s"
                                       % (os.path.join(first.dir, "harness.yaml"), NOTICE_IMAGES))]


def _blank_lines(text, first, last):
    """text with its lines first to last (from 1) blanked, each character a space: lines and offsets kept."""
    lines = text.split("\n")
    for i in range(first - 1, min(last, len(lines))):
        lines[i] = " " * len(lines[i])
    return "\n".join(lines)


# the licence _row_licence gives a row's file that its row refuses: no licence applies to its licence lines, which
# scan_licence does not read
_REFUSED = object()


def _row_licence(root, rel, path, text, blanked, row):
    """The one step that decides whether the proof file rel, at path, is under the licence of row, its row of
    THIRD_PARTY (None for none; text is the file's text, and blanked the same with its string literals blanked, or
    None): (the licence findings of its row, the text the private-data shapes read, the text the e-mail check reads,
    the licence scan_licence applies to its licence lines).  A file no row names is read whole, and its licence lines
    are judged as any proof file's (licence None).  A row's file whose bytes are the ones its row pins is under the
    row's licence (its spdx), whose text the tree must hold (scan_third_party_text), and the private-data shapes do
    not read the lines of its upstream author's notice, which name the author's address; it is refused when it has
    fewer lines than the row names as that notice.  One whose bytes are not the row's is refused, whatever its licence
    lines say, and read whole.  A refused file has no licence (_REFUSED): its refusal is the last of its licence
    findings, and scan_licence does not read it."""
    if row is None:
        return [], text, blanked, None
    digest = file_sha256(path, facts.file_cap(rel))
    if digest != row["sha256"]:
        return [Finding("licence", rel, "a third-party proof file is the bytes its row of %s pins: this file's SHA-256 "
                                        "is %s, the row's %s (docs/adding-a-proof.md, requirement 7)"
                                        % (THIRD_PARTY, digest or "unread", row["sha256"]))], text, blanked, _REFUSED
    first, last = row["notice"]["first"], row["notice"]["last"]
    shapes_text = _blank_lines(text, first, last)
    email_text = None if blanked is None else _blank_lines(blanked, first, last)
    found = scan_third_party_text(root, rel, row)
    count = text.count("\n") + (not text.endswith("\n"))
    if last > count:
        found.append(Finding("licence", rel, "its row of %s gives lines %d to %d as the upstream author's notice, and "
                                             "the file has %d lines" % (THIRD_PARTY, first, last, count)))
        return found, shapes_text, email_text, _REFUSED
    return found, shapes_text, email_text, row["spdx"]


def private_projects(tree):
    """{project: whether PROJECT_NOTICE, its NOTICE, is a file} of each project whose project.yaml says
    `release: private`.  A proof file of such a project with a NOTICE is under that NOTICE (PRIVATE_LINES) unless it is
    made from Anthropic's proofs, opens with the comment of its kind or is a row's file of THIRD_PARTY, under its row's
    licence (_row_licence), and the lines of PRIVATE_LINES are refused in any other project (scan_licence).  Read once
    for each lint run, as anthropic_targets is; a change to a NOTICE has --changed-only read every file
    (read_by_every_verdict)."""
    return {name: os.path.isfile(tree.path(PROJECT_NOTICE.format(project=name)))
            for name, p in tree.projects.items() if p.data.get("release") == "private"}


def scan_licence(text, where, targets, licence=None, private=None):
    """The findings of the licence rule on the proof file `text` at `where`.  targets: anthropic_targets, or None for a
    contributor's pull request, whose build records the maintainer writes before it merges
    (docs/adding-a-proof.md, requirement 7): then the licence lines are checked, and the record is not.  licence: the
    licence of THIRD_PARTY_LICENCES that the file's row of THIRD_PARTY puts it under (_row_licence decides it), which
    its licence line gives, or None for a file that no row puts under one: no such file is under a licence of
    THIRD_PARTY_LICENCES.  private: private_projects, or None for a tree with no project that is `release: private`."""
    lines = text.split("\n", HEADER_LINES)
    head = "\n".join(lines[:HEADER_LINES])
    rest = lines[HEADER_LINES] if len(lines) > HEADER_LINES else ""
    # a plain search first: most files have none (lower: a changed copyright line may spell the name in any case)
    low = rest.lower()
    if "SPDX-License-Identifier" in rest or "anthropic" in low or _PRIVATE_MARK in low:
        late = _LICENCE_LINE.search(text, len(head) + 1)
        if late:
            return [Finding("licence", "%s:%d" % (where, text.count("\n", 0, late.start()) + 1),
                            "a licence line opens the file, in its first %d lines (docs/adding-a-proof.md, "
                            "requirement 7)" % HEADER_LINES)]
    spdx_lines = list(_SPDX.finditer(head))
    anthropic = _ANTHROPIC_COPYRIGHT.search(head) is not None
    notices = list(_PRIVATE_COPYRIGHT.finditer(head))
    mentions = list(_PRIVATE_NAMED.finditer(head))   # notices' words, on those lines and on any other
    spdx = spdx_lines[0].group(1) if spdx_lines else None
    at = "%s:%d" % (where, head.count("\n", 0, spdx_lines[0].start()) + 1) if spdx_lines else where
    if lines[0].startswith(PROGRAM_LINES) and (spdx_lines or anthropic or mentions):
        return [Finding("licence", at, "a file that restates a program's instruction words or holds data computed "
                                       "from one has no other licence lines: its code keeps the program's licences "
                                       "(docs/adding-a-proof.md, requirement 7)")]
    other = next((m for m in spdx_lines[1:] if _expression(m) != _expression(spdx_lines[0])), None)
    if other is not None:   # a second tag that names the same licence restates it (a doc comment, say)
        return [Finding("licence", "%s:%d" % (where, head.count("\n", 0, other.start()) + 1),
                        "a proof file has one licence: this tag says %r, the first one %r" % (other.group(1), spdx))]
    if licence is not None and spdx != licence:
        return [Finding("licence", at, "its row of %s gives the licence %s, so its licence line, in its first %d "
                                       "lines, is SPDX-License-Identifier: %s (docs/adding-a-proof.md, requirement 7)"
                                       % (THIRD_PARTY, licence, HEADER_LINES, licence))]
    unit = layout.unit_of(where)
    project = unit.split("/")[0] if unit else None
    # None: the file's project is not `release: private`; False: it is, and has no NOTICE; True: it is, with a NOTICE
    held = (private or {}).get(project)
    if spdx is not None and spdx not in PROOF_LICENCES and spdx != PRIVATE_LICENCE and licence is None:
        if spdx in THIRD_PARTY_LICENCES:
            return [Finding("licence", at, "%r is the licence of a third-party proof file, which a row of %s pins by "
                                           "its path and the SHA-256 of its bytes, and no row names this file "
                                           "(docs/adding-a-proof.md, requirement 7)" % (spdx, THIRD_PARTY))]
        if held:
            return [Finding("licence", at, "%r is neither licence a proof file of %s has: %s, with Anthropic's "
                                           "copyright, for one made from Anthropic's proofs, or %s for one under %s"
                                           % (spdx, project, ANTHROPIC_LICENCE, PRIVATE_LICENCE,
                                              PROJECT_NOTICE.format(project=project)))]
        return [Finding("licence", at, "%r is neither licence a proof file has: %s, with Anthropic's copyright, for "
                                       "one made from Anthropic's proofs, or MIT for one written here (NOTICE)"
                                       % (spdx, ANTHROPIC_LICENCE))]
    for copy in _PRIVATE_ANY_CASE.finditer(head):
        if _PRIVATE_NAMED.match(head, copy.start()) is None:
            return [Finding("licence", "%s:%d" % (where, head.count("\n", 0, copy.start()) + 1),
                            "the copyright line of a project's NOTICE is `%s`, unchanged (docs/adding-a-proof.md, "
                            "requirement 7)" % PRIVATE_LINES[0].format(project="<project>"))]
    if spdx == PRIVATE_LICENCE and not held:
        return [Finding("licence", at, "%s is the licence of a proof file under its project's NOTICE, in a project "
                                       "whose project.yaml says `release: private` and whose folder holds a NOTICE "
                                       "file (docs/adding-a-proof.md, requirement 7); %s"
                                       % (PRIVATE_LICENCE, "there is no " + PROJECT_NOTICE.format(project=project)
                                          if held is False else
                                          "the project.yaml of this file's project does not say `release: private`"))]
    if anthropic and spdx != ANTHROPIC_LICENCE:
        return [Finding("licence", at, "a file with Anthropic's copyright line was made from Anthropic's proofs, so "
                                       "its licence line is SPDX-License-Identifier: %s (NOTICE)" % ANTHROPIC_LICENCE)]
    if spdx == ANTHROPIC_LICENCE and not anthropic:
        return [Finding("licence", at, "%s is the licence of a file made from Anthropic's proofs, which keeps "
                                       "Anthropic's copyright line, `(* Copyright <year> Anthropic PBC *)`, above "
                                       "it (NOTICE)" % ANTHROPIC_LICENCE)]
    for named in _ANTHROPIC_NAMED.finditer(head):
        if not (_ANTHROPIC_COPYRIGHT.match(head, head.rfind("\n", 0, named.start()) + 1)
                or (anthropic and _ANTHROPIC_RESTATED.match(head, named.start()))):
            return [Finding("licence", "%s:%d" % (where, head.count("\n", 0, named.start()) + 1),
                            "Anthropic's copyright line is `(* Copyright <year> Anthropic PBC *)`, unchanged "
                            "(docs/adding-a-proof.md, requirement 7)")]
    if spdx == PRIVATE_LICENCE and not any(m.group(1) == project and m.start() < spdx_lines[0].start()
                                           for m in notices):
        return [Finding("licence", at, "a file under %s has the line `%s` in its first %d lines, above its tag "
                                       "(docs/adding-a-proof.md, requirement 7)"
                                       % (PRIVATE_LICENCE, PRIVATE_LINES[0].format(project=project), HEADER_LINES))]
    foreign = next((m for m in mentions if m.group(1) != project), None)
    if foreign is not None:
        return [Finding("licence", "%s:%d" % (where, head.count("\n", 0, foreign.start()) + 1),
                        "this line names %s: a proof file of %s names no NOTICE but its own project's, %s "
                        "(docs/adding-a-proof.md, requirement 7)"
                        % (PROJECT_NOTICE.format(project=foreign.group(1)), project,
                           PROJECT_NOTICE.format(project=project)))]
    if mentions and spdx != PRIVATE_LICENCE:
        return [Finding("licence", "%s:%d" % (where, head.count("\n", 0, mentions[0].start()) + 1),
                        "this line goes with the tag `%s` under it and with no other licence lines: a proof file has "
                        "one licence (docs/adding-a-proof.md, requirement 7)" % PRIVATE_LINES[1])]
    if spdx is None and not lines[0].startswith(PROGRAM_LINES):
        # no licence line is left in the head (a copyright of Anthropic's, or the words of the copyright line of a
        # project's NOTICE, with no tag was refused above), so the file reads as one written here, under MIT or, in a
        # project that is `release: private` with a NOTICE, under that NOTICE: a head that names another licence in
        # words must say it with its tag.  So such a head of a private project gets this finding, not the one below.
        worded = _licence_words(head)
        if worded:
            words = ", ".join(repr(w) for w in dict.fromkeys(re.sub(_WRAP, " ", m.group()) for m in worded))
            under = (" under MIT" if not held else
                     ", which in %s is under %s" % (project, PROJECT_NOTICE.format(project=project)))
            return [Finding("licence", "%s:%d" % (where, head.count("\n", 0, worded[0].start()) + 1),
                            "its first %d lines name a licence in words (%s) and hold no licence line, so it reads as "
                            "a file written here%s: give it the SPDX-License-Identifier line of the licence they name "
                            "(docs/adding-a-proof.md, requirement 7)" % (HEADER_LINES, words, under))]
    if held and (spdx == "MIT" or (spdx is None and not lines[0].startswith(PROGRAM_LINES))):
        return [Finding("licence", at, "no proof file of %s, whose project.yaml says `release: private` and whose "
                                       "folder holds %s, is under MIT: one made from Anthropic's proofs has "
                                       "Anthropic's two lines, one of a program's instruction words or data opens with "
                                       "the comment of its kind, and any other has the lines `%s` and `%s` "
                                       "(docs/adding-a-proof.md, requirement 7)"
                                       % (project, PROJECT_NOTICE.format(project=project),
                                          PRIVATE_LINES[0].format(project=project), PRIVATE_LINES[1]))]
    if spdx != ANTHROPIC_LICENCE or targets is None:
        return []
    if unit not in targets:
        return [Finding("licence", at, "a file under %s needs a build record, %s, that lists %s under proofs.texts "
                                       "(NOTICE)" % (ANTHROPIC_LICENCE,
                                                     layout.record_path(*unit.split("/"), layout.of_path(where)),
                                                     ", ".join(ANTHROPIC_TEXTS)))]
    return []


def bare_licence(text):
    """Whether a proof file carries no licence line at all: _LICENCE_LINE, this module's own test of one (a licence
    tag, a copyright of Anthropic's, changed or not, or the words of the copyright line of a project's NOTICE, in any
    case, so a changed copy of that line is no bare file but a finding of scan_licence), matches nothing where
    scan_licence reads them (the first HEADER_LINES lines), the file does not open with the comment of its kind
    (PROGRAM_LINES), which carries none because the program's code in it keeps the program's licences
    (docs/adding-a-proof.md, requirement 7.1), and those lines name no licence in words (_licence_words).

    No rule reads this.  Requirement 7 says a file with no licence lines was written here, under the MIT licence, so
    scan_licence rightly finds nothing in one that names no other licence; but a file whose Anthropic header was
    dropped is the same bytes, and a count of findings cannot see it.  A whole-tree lint counts these files and prints
    the count (bare_report), which fails nothing: the count is what a later series writing the licence lines works
    down.  A file whose licence line is wrong -- a changed copyright of Anthropic's, a tag naming a licence no proof
    file has -- has a licence line and is no part of this count: it already fails the licence rule, and counting it
    twice would read as more debt of this kind than there is.  Nor is a file whose head names a licence in words with
    no licence line, for the same reason: the licence rule asks it for the tag of that licence.  For the same reason
    too scan_file leaves out of the count a bare file of a project that is `release: private` with a NOTICE
    (private_projects): no proof file there is under MIT, so scan_licence refuses it, and it is a finding, not debt."""
    lines = text.split("\n", HEADER_LINES)
    head = "\n".join(lines[:HEADER_LINES])
    return (_LICENCE_LINE.search(head) is None and not lines[0].startswith(PROGRAM_LINES)
            and not _licence_words(head))


def bare_report(bare):
    """The lines a whole-tree lint prints for the proof files that carry no licence line (bare_licence): the total,
    then one line per fuzz target, the most first and ties by name, since a total alone names nothing to work on.
    It is a count and not a finding, so it is printed where the sparse-checkout notice is, on stderr, and `oft lint`'s
    own summary line on stdout is untouched."""
    units = sorted(bare.items(), key=lambda kv: (-kv[1], kv[0] or ""))
    return "\n".join(["oft lint: %d proof file(s) in %d fuzz target(s) carry no licence line (no SPDX tag, no "
                      "copyright line of Anthropic's and no licence named in words in their first %d lines, and not "
                      "a file that opens with the comment of its kind): a count, which fails nothing"
                      % (sum(bare.values()), len(units), HEADER_LINES)]
                     + ["oft lint:   %s: %d" % (u or "(no fuzz target)", n) for u, n in units])


def _expression(tag):
    """The licence expression of an _SPDX match, as a sentence may end it: a closing stop or comma and runs of blanks
    do not count."""
    return " ".join(tag.group(1).rstrip(".;,").split())


_PROJECT_PREFILTER = re.compile(r"\b(?:Load|Cd|Dependency)\b")


def scan_project_rocq(text, where):
    """A generated Rocq file of projects/ reads no file while it compiles (generate --check holds it to its
    rendering; this says why, if the rendering ever does).  The ReadFile commands are left to the generator."""
    if not _PROJECT_PREFILTER.search(text):
        return []
    return _file_commands(rocq.strip(text), where, "proofs", "a file of projects/")


# -------------------------------------------------------- contract-literals

# A contract file: the contract of one function, <fn>_c.v, under the Prog/ folder of a fuzz target's proof library for
# the plain build (lib/Prog/) or for another build (lib/U/Prog/, lib/A/Prog/, lib/B/Prog/), in either layout.
CONTRACT_FILE = re.compile(layout.PROOF_HARNESS_RE + r"/lib/(?:[UAB]/)?Prog/(?:[^/]+/)*[^/]+_c\.v$")
# the paths row of a build's symbol fact, whose file name must be a build its harness.yaml publishes
SYMBOL_FACT = "projects/{project}/{harness}/symbols/*.tsv"
# A hexadecimal numeral as Rocq lexes one, not the end of an identifier (A_0x132a0): its digits (and _), then a
# fraction (a `.` and at least one digit, so a sentence's full stop is none) and a binary exponent, each optional:
# 0x1.32ap16 is 0x132a0 (rocq 9.2, in Q).  Groups: the digits, the fraction's digits, the exponent.  It is an address
# when its value is an integer and an allocated section of one of the fuzz target's builds holds it (scan_contract);
# any other (the image's base, a division's magic multiplier, a float's bits, a stack bound) is a number Symbols.v
# could not name.
_HEX = re.compile(r"(?<![\w'])0[xX]([0-9a-fA-F][0-9a-fA-F_]*)(?:\.([0-9a-fA-F][0-9a-fA-F_]*))?"
                  r"(?:[pP]([+-]?[0-9][0-9_]*))?")
# A decimal numeral as Rocq lexes one, not inside a name (A_78496, s_1) and not a field after a `.`: its digits (and
# _), then a fraction and a decimal exponent, each optional: 784.96e2 is 78496 (rocq 9.2, in Q).  Groups: the digits,
# the fraction's digits, the exponent.  It is an address under the same rule as a hexadecimal one (scan_contract): an
# integer that an allocated section holds, so a small count, size or offset is none.
_DECIMAL = re.compile(r"(?<![\w'.])([0-9][0-9_]*)(?:\.([0-9][0-9_]*))?(?:[eE]([+-]?[0-9][0-9_]*))?(?![\w'])")
# the most digits an integer below 2^64 has
_DIGITS_64 = len(str(2 ** 64))
# What a contract may use of one build's symbol fact (build_symbols)
BuildSymbols = collections.namedtuple("BuildSymbols", "table shared sections")


def build_symbols(rows):
    """What a contract may use of a build whose symbol fact is rows ([symbols.Sym]), as generate.symbols_v renders
    the build's module of Symbols.v: table, what the module defines (symbols.table); shared, {path: (name, what)} of
    each path a name that two or more rows share would have, which the module does not define (names.rocq_idents);
    and sections, (address, end, name) of each allocated section that holds a byte, by address.  ValueError as
    names.symbol_idents."""
    tab = symbols.table(rows)
    shared = {}
    for r in rows:
        section = r.kind == "section"
        ident = names.section_ident(r.name) if section else names.rocq_ident(r.name)
        if (tab.sections if section else tab.functions).get(ident) is None:
            for path in symbols.paths(ident, section):
                shared.setdefault(path, (r.name, "sections" if section else "functions or objects"))
    return BuildSymbols(tab, shared, tuple(sorted((r.address, r.address + r.size, r.name) for r in rows
                                                  if r.kind == "section" and r.size)))


def _section_of(value, builds):
    """(section, build) of the first build, in the order of builds, with an allocated section that holds the address
    value (of its sections that do, the one that starts last: a TLS section's addresses overlap the sections after
    it), or None."""
    for build, syms in builds.items():
        held = [(start, name) for start, end, name in syms.sections if start <= value < end] if syms else []
        if held:
            return max(held)[1], build
    return None


def contract_symbols(tree, rels):
    """{"<project>/<harness>": {build: build_symbols of its symbol fact}} of each fuzz target with a contract file
    among rels, for each of its symbol facts (facts.Harness.symbol_facts), in that order, as generate.symbols_v reads
    them; None for a fact that does not load, which check_symbols reports, or that oft generate refuses
    (rules.symbol_facts).  A fuzz target with no symbol fact is left out."""
    out = {}
    for unit in sorted({layout.unit_of(rel) for rel in rels if CONTRACT_FILE.match(rel)}):
        p, h = unit.split("/")
        harness = tree.projects[p].harnesses.get(h) if p in tree.projects else None
        for b, _rec, rel in harness.symbol_facts() if harness is not None else ():
            try:
                out.setdefault(unit, {})[b] = build_symbols(symbols.load(tree.path(rel))[1])
            except (ValueError, facts.BoundedFileError):
                out.setdefault(unit, {})[b] = None
    return out


def _numeral_parts(m):
    """(digits, fraction, sign, magnitude) of a _HEX or _DECIMAL match, with _ removed: the significand's digits, the
    fraction's digits, the exponent's sign, and its magnitude with leading zeros removed.  The two bases differ only
    after this parsing."""
    digits, fraction = m.group(1).replace("_", ""), (m.group(2) or "").replace("_", "")
    exponent = (m.group(3) or "0").replace("_", "")
    return digits, fraction, -1 if exponent.startswith("-") else 1, exponent.lstrip("+-").lstrip("0") or "0"


def _hex_value(m):
    """The value of a _HEX numeral when it is an integer below 2^64, which an address of a riscv64 program is; else
    None.  No power of two past that bound is computed, so no exponent makes lint build a huge number."""
    digits, fraction, sign, magnitude = _numeral_parts(m)
    mantissa = int(digits + fraction, 16)
    if not mantissa:
        return 0
    if len(magnitude) > 18:
        return None   # 2^(10^18) and more, or a fraction finer than any numeral a file holds
    shift = sign * int(magnitude) - 4 * len(fraction)
    if shift >= 0:
        return mantissa << shift if mantissa.bit_length() + shift <= 64 else None
    if -shift > mantissa.bit_length() or mantissa & ((1 << -shift) - 1):
        return None   # a fraction is left
    return mantissa >> -shift


def _decimal_value(m):
    """The value of a _DECIMAL numeral when it is an integer below 2^64; else None.  No power of ten past that bound
    is computed, and int() reads no more digits than such a number has."""
    digits, fraction, sign, magnitude = _numeral_parts(m)
    digits = (digits + fraction).lstrip("0") or "0"
    if len(magnitude) > 18:
        return 0 if digits == "0" else None
    shift = sign * int(magnitude) - len(fraction)
    if shift < 0:
        if digits == "0":
            return 0
        if -shift > len(digits) or digits[shift:].strip("0"):
            return None   # a fraction is left
        digits = digits[:shift].lstrip("0") or "0"
        shift = 0
    if digits == "0":
        return 0
    if len(digits) + shift > _DIGITS_64:
        return None
    value = int(digits) * 10 ** shift
    return value if value < 2 ** 64 else None


def scan_contract(text, where, builds):
    """contract-literals.  The findings on the contract file `text` at `where` of a fuzz target with symbol facts,
    builds ({build: build_symbols of its fact, or None for one that does not load}): each numeral, hexadecimal or
    decimal, whose value an allocated section of one of the builds holds, an address, which a rebuild moves and
    Symbols.v names; and
    each reference to Symbols.v (symbols.reference), read as the whole name Rocq reads, that the build's module does
    not define, so that a function the build lost (inlined, merged) is named before any compile (spec R3).  Comments
    and strings do not count (rocq.strip)."""
    stripped = rocq.strip(text)
    out = []
    for numeral, value_of in ((_HEX, _hex_value), (_DECIMAL, _decimal_value)):
        for m in numeral.finditer(stripped):
            value = value_of(m)
            held = None if value is None else _section_of(value, builds)
            if held is not None:
                out.append((m.start(), "%s is inside %s of %s: name it from Symbols" % ((m.group(),) + held)))
    for m in symbols.ROCQ_NAME.finditer(stripped):
        ref = symbols.reference(m.group())
        if ref is None:
            continue
        module, path = ref
        build = symbols.BUILD_OF[module]
        if not path:
            continue   # the module itself (Import Symbols.Plain.)
        if build not in builds:
            msg = "%s has no symbol fact: Symbols.v has no module %s" % (build, module)
        elif builds[build] is None or symbols.defines(builds[build].table, path):
            continue   # defined, or a fact that does not load: check_symbols or oft generate reports that
        elif path in builds[build].shared:
            msg = ("%s has no symbol %s: %s names two or more %s of %s, so Symbols.v gives it no identifier"
                   % ((build, path) + builds[build].shared[path] + (build,)))
        else:
            msg = "%s has no symbol %s" % (build, path)
        out.append((m.start(), msg))
    return [Finding("contract-literals", "%s:%d" % (where, stripped.count("\n", 0, pos) + 1), msg)
            for pos, msg in sorted(out)]


# -------------------------------------------------------------- read-from

# A generated or ported proof file names the binary its numerals were read from, in a comment of its own that the
# start-up tools write (dev/stream/.../pins.py):
#
#     (* Read from: <file> (<project>/<harness> <build>) sha256 <hex>; unstripped twin sha256 <hex> *)
#
# and, where the generator wrote the pin inside the parenthesis,
#
#     (* Read from: <file> (<project>/<harness> <build>, pin <hex>); unstripped twin sha256 <hex> *)
#
# Until this rule nothing read those comments, so one that named another fuzz target's image passed every check.
# <file> must be the `file` of a build its own fuzz target's harness.yaml records, and every digest the comment
# holds must be that build's pinned SHA-256.  Three things are left alone, each because the facts cannot judge it or
# it is not this fuzz target's claim: the unstripped twin, which is the same link without --strip-all, read for its
# symbol names, and which no harness.yaml pins (tools/oft/symbols.py), so its clause is cut out before the digests
# are read; a withheld build, which shows no digest at all (the `withheld` rule); and a build record's copy of
# someone else's proof text, which scan_file does not pass here.
#
# A fourth: the donor's line in a relocated file.  A proof ported from another fuzz target keeps the line that says
# which image the donor's numerals were read from, and gains a line of its own for this fuzz target's image; the
# donor's line is never rewritten, because that would make the file say something false to satisfy a check.  Such a
# line names another fuzz target's binary, and it passes ONLY when the same file also carries a `Read from:` that
# names a build of its OWN fuzz target whose name and SHA-256 are the pin that unit's harness.yaml gives.  Three
# things this deliberately does not do, each of which would make the rule weaker than no rule at all for the name it
# cleared: a name that is no build of any fuzz target the tree records is still a finding (read_from_donor_names);
# a donor line alone, with no line of this fuzz target's own, is still a finding; and a pin that cannot be read --
# a withheld build, or a record with no sha256 -- is not a pin that matched, so it clears nothing.  The pins are the
# ones the tree being linted holds: facts.load reads the checkout at the ref CI checked out and no other ref, and
# never a local rebuild of a binary.
# An exempt donor line does not fail, and it is not invisible either: it is counted and reported (READ_FROM_DONOR,
# split_donors), as a pending licence finding is.
# The comment's text runs to its `*)`, or to the end of the file when it has none: a `(.*?)\*\)` that can fail
# backtracks over every start, which on a 5 MiB file with an unclosed `(* Read from:` takes hours rather than the
# milliseconds this costs.
READ_FROM = re.compile(r"\(\*\s*Read from:[ \t\r\n]*([^\s()]+)(.*?)(?:\*\)|\Z)", re.S)
READ_FROM_TWIN = re.compile(r"unstripped twin[ \t\r\n]+sha256[ \t\r\n]+[0-9a-f]{64}")
READ_FROM_DIGEST = re.compile(r"(?<![0-9A-Za-z])[0-9a-f]{64}(?![0-9A-Fa-f])")

# the rule name of an exempt donor line: not a finding, and not silence either (split_donors, donors_by_unit)
READ_FROM_DONOR = "read-from-donor"


def read_from_builds(tree, rel):
    """{the file name of a build of rel's fuzz target: (build, its harness.yaml record)}, or None when the tree holds
    no harness.yaml for that fuzz target (facts.load reports that on its own)."""
    project, _, harness = (layout.unit_of(rel) or "").partition("/")
    p = tree.projects.get(project)
    h = None if p is None else p.harnesses.get(harness)
    if h is None:
        return None
    return {rec["file"]: (b, rec) for b, rec in h.builds(published_only=False)
            if isinstance(rec, dict) and isinstance(rec.get("file"), str)}


def read_from_donor_names(tree):
    """The `file` of every build of every fuzz target the tree records: the names a `Read from:` line can carry that
    are some fuzz target's binary.  A relocated file's donor line names one of these; a typo, a stale name or an
    invented one names none, and is a finding whatever else the file carries.  One pass over the facts, kept on the
    tree (each worker process of a run has its own copy of it, and reads every proof file through it)."""
    found = getattr(tree, "_read_from_donor_names", None)
    if found is None:
        found = {rec["file"] for p in tree.projects.values() for h in p.harnesses.values()
                 for _, rec in h.builds(published_only=False)
                 if isinstance(rec, dict) and isinstance(rec.get("file"), str)}
        tree._read_from_donor_names = found
    return found


def read_from_own_pin(comments, builds):
    """True where one of the file's `Read from:` comments names a build of its own fuzz target and every SHA-256 it
    holds is that build's pin: the line a relocated file gains for the image its own numerals were read from.  A
    build whose record gives no pin (a withheld one, or one with no sha256 at all) cannot be matched, so it never
    makes this true: a pin that cannot be read is not a pin that matched.  comments: [(name, the text after it)]."""
    for name, rest in comments:
        if name not in builds:
            continue
        pin = builds[name][1].get("sha256")
        if not isinstance(pin, str):
            continue
        digests = READ_FROM_DIGEST.findall(rest)
        if digests and all(d == pin for d in digests):
            return True
    return False


def scan_read_from(text, where, tree):
    """read-from.  The findings on the proof file `text` at `where`: each `(* Read from: ... *)` comment names a
    binary its own fuzz target's harness.yaml records, and every SHA-256 it holds outside the unstripped twin's
    clause is the size-and-SHA-256 pin harness.yaml gives that build.  A withheld build shows no digest at all (the
    `withheld` rule says so), so a comment that names one is left alone: there is nothing to compare it with.  A
    relocated file's donor line, which names another fuzz target's binary, is exempt only where the same file also
    carries a line of its own fuzz target's that matches that unit's pin (read_from_own_pin); it comes back as a
    READ_FROM_DONOR item, which split_donors counts and reports and never fails."""
    if "Read from:" not in text:
        return []
    builds = read_from_builds(tree, where)
    if builds is None:
        return []
    found = [(m.start(), m.group(1), READ_FROM_TWIN.sub("", m.group(2))) for m in READ_FROM.finditer(text)]
    own_pin = read_from_own_pin([(name, rest) for _, name, rest in found], builds)
    out = []
    for start, name, rest in found:
        at = "%s:%d" % (where, text.count("\n", 0, start) + 1)
        if name not in builds:
            if own_pin and name in read_from_donor_names(tree):
                out.append(Finding(READ_FROM_DONOR, at,
                                   "reads %s, which is another fuzz target's binary; this file also names the "
                                   "pinned build of %s, so it is a relocated file keeping the donor's line"
                                   % (name, layout.unit_of(where))))
                continue
            out.append(Finding("read-from", at, "reads %s, which is no build of %s: its builds are %s"
                               % (name, layout.unit_of(where),
                                  ", ".join(sorted(builds)) if builds else "none")))
            continue
        build, rec = builds[name]
        pin = rec.get("sha256")
        if not isinstance(pin, str):
            continue   # a withheld build: harness.yaml gives no digest to compare with
        digests = READ_FROM_DIGEST.findall(rest)
        if not digests:
            out.append(Finding("read-from", at, "reads %s and names no SHA-256 of it, so it pins no build: "
                                                "harness.yaml pins the %s build at sha256 %s (%s bytes)"
                               % (name, build, pin, rec.get("bytes"))))
            continue
        for d in digests:
            if d != pin:
                out.append(Finding("read-from", at,
                                   "reads %s at sha256 %s, but harness.yaml pins the %s build of %s at sha256 %s "
                                   "(%s bytes)" % (name, d, build, layout.unit_of(where), pin, rec.get("bytes"))))
    return out


def donors_by_unit(donors):
    """[(fuzz target, how many exempt donor `Read from:` lines its files carry)], sorted by fuzz target: what
    `oft lint` prints of them unless it is asked for each one (--list-donors)."""
    return sorted(collections.Counter(finding_unit(f) for f in donors).items())


def split_donors(found, donors=None):
    """The exempt donor lines of found (READ_FROM_DONOR) go to donors, a list, when one is given, and never to the
    result: a relocated file's donor line does not fail, and the population stays visible instead of becoming
    invisible.  This is how a pending licence finding is reported (apply_pending), for the same reason."""
    kept = []
    for f in found:
        if f.rule == READ_FROM_DONOR:
            if donors is not None:
                donors.append(f)
        else:
            kept.append(f)
    return kept


# --------------------------------------------------------- paths, withheld

# What may hold binary bytes (a NUL byte): a counterexample's and a finding's runs, in either layout (layout.py), a
# mutant run's input kept as evidence in a fuzz target's provenance and a statement's instance (the same kind of file:
# a fuzz input), and the tests' fixtures; and a classifier program that its proof.yaml pins (classifier_programs),
# which is proof data its proof verifies on its own.  Binary data anywhere else is a release asset, not a file in git.
BINARY_OK = tuple("%s/%s" % (d, run) for lay in layout.LAYOUTS
                  for d in (layout.counterexample_dir("*", "*", "*", lay), layout.finding_dir("*", "*", "*", lay))
                  for run in ("input.bin", "control.bin")) + (
    "projects/*/*/proofs/provenance/evidence/mutants/*/input.bin",
    "projects/*/*/proofs/provenance/evidence/instances/*", "tools/oft/tests/**")
NUL_BYTE = "a NUL byte: binary data is a release asset, not a file in git"


def classifier_programs(tree):
    """{path: (sha256, proof directory)} of each classifier program a proof.yaml pins (classifier.elf and
    classifier.sha256): the one ELF file, and the one binary file, a proof directory may hold."""
    return {pd.path + "/" + pd.data["classifier"]["elf"]: (pd.data["classifier"]["sha256"], pd.path)
            for pd in tree.proofs.values() if pd.data.get("classifier")}

# the ELF files the tests of oft symbols read (tests/test_symbols.py), small and built as their README.md says: the
# only ELF files kept in git outside a classifier program its proof.yaml pins (their NUL bytes are under
# tools/oft/tests/**, which BINARY_OK holds).  The four named ones are the fixtures of revision 3 of the symbol fact
# (OSSV-591), listed here a pull request before the one that adds them, since pr.yml lints a change by its base's rules
ELF_FIXTURES = ("tools/oft/tests/fixtures/elf/two.stripped", "tools/oft/tests/fixtures/elf/two.unstripped",
                "tools/oft/tests/fixtures/elf/computed_goto_global.elf",
                "tools/oft/tests/fixtures/elf/computed_goto_biased.elf",
                "tools/oft/tests/fixtures/elf/named.stripped", "tools/oft/tests/fixtures/elf/named.unstripped",
                "tools/oft/tests/fixtures/elf/named-moved.stripped",
                "tools/oft/tests/fixtures/elf/named-moved.unstripped")
# Where a tracked symbolic link is allowed, and nowhere else: the lane tools of dev/stream/, which mirror
# `cold/tools` on the lane VM path for path and hold links because that directory holds them (the drift check of
# pull request 666 compares a live path with its lane path directly, so flattening a link breaks the mirror).  It is
# inside release_tree.INTERNAL, so no release carries it -- and a release is what the rule protects, since the views
# the gate builds of a released tree refuse a link.  The target must stay inside this directory and name a file
# git has in its index, and be a file rather than another link: a link that escapes the directory, that dangles,
# that names a link, or that names itself, is still a finding (496, round 5.2, R5-2, and the review of 669).
LINKS_ALLOWED = "dev/stream/lane/"

# Where a derived file may be tracked, and nowhere else: the same lane tools, for the reason that
# scoped the link rule there.  dev/stream/lane/ mirrors `cold/tools` on the lane VM path for path,
# and the drift check of pull request 666 compares a live path with its lane path directly, so a
# file the box holds and the lane does not is reported as held by no object -- which is what
# leaving `twin-controls/C_reac_ctrl_build_asLib.6df2c242679.glob` out would do, after that count
# first reached zero on 2026-11-01.  That .glob is not a build product nobody meant to commit: the
# tracked dev/stream/lane/tools/twin-controls/README.md names it as one of the two controls the
# twin test reads.  The rule stands everywhere else, because what it protects is a released tree
# and `oft release-tree` cuts this directory whole (release_tree.INTERNAL), so nothing a release
# carries can reach it (669, and the review of 672).
#
# Narrower than it looks: dev/stream's own checker refuses `*.pyc` and a `__pycache__` directory
# anywhere under it (its tools check's REFUSED_FILE_PATTERNS and REFUSED_DIR_PATTERNS), and
# `__pycache__` stays a finding here whatever directory it is in.
DERIVED_ALLOWED = LINKS_ALLOWED


# What `index_files` answers when it asked git and git could not answer, which is neither "the index holds it"
# nor "there is no index here".  An error that becomes a permission is how a check stops checking: four of them
# were found in one evening (a manifest blob that would not read scoring as "no manifest", `uv export --frozen`
# exiting 0 on a stale lock, a file of planted cases under a `main()` nobody called, and a job skipped behind an
# unrelated red), so a link whose target this cannot check against the index is a finding (the review of 669).
INDEX_UNREADABLE = object()


def index_files(root):
    """Every path in git's index; None where root is no git checkout; INDEX_UNREADABLE where git could not say.

    `walk` lists the untracked files .gitignore does not exclude as well, which is right for "what could be
    committed" and wrong for "what a link may point at": a link to a file that is on this disk and in nobody's
    index passes here and fails in CI, and a check that disagrees with CI teaches people to distrust CI.

    The two absences are different and are kept apart.  A tree with no `.git` (a fixture, an unpacked release)
    has no index to disagree with, and the other conditions still judge the link.  A tree that HAS one and whose
    git will not read it is a question this cannot answer, and the caller refuses rather than allows.
    """
    if not os.path.exists(os.path.join(root, ".git")):
        return None
    try:
        r = subprocess.run(["git", "-C", root, "ls-files", "-z", "--cached"], capture_output=True)
    except OSError:
        return INDEX_UNREADABLE
    if r.returncode != 0:
        return INDEX_UNREADABLE
    return {p for p in r.stdout.decode().split("\0") if p}


def index_links(root, among):
    """The paths of `among` that git's index holds as symbolic links (mode 120000): a sparse checkout leaves them off
    disk, so only the index says what they are.  Empty when among is empty or root is no git checkout."""
    if not among or not os.path.exists(os.path.join(root, ".git")):
        return set()
    r = subprocess.run(["git", "-C", root, "ls-files", "-z", "-s", "--cached"], capture_output=True)
    if r.returncode != 0:
        raise IndexUnreadable(r.stderr.decode("utf-8", "replace").strip())
    out = set()
    for rec in r.stdout.decode().split("\0"):
        meta, _, rel = rec.partition("\t")
        if rel in among and meta.startswith("120000 "):
            out.add(rel)
    return out


def _link_refusal(full, rel, indexed):
    """Why the tracked symbolic link `rel` is a finding, or None when it is an allowed lane link.

    `walk` already fails the whole lint where git will not answer, so the INDEX_UNREADABLE branch is the second
    line rather than the first: this function is also called directly, and a git that fails between the two
    reads must not become a permission here either.
    """
    if not rel.startswith(LINKS_ALLOWED):
        return "a symbolic link"
    if indexed is INDEX_UNREADABLE:
        return "a symbolic link whose target could not be checked against git's index"
    leaves = "a symbolic link whose target leaves %s or is no file of the index" % LINKS_ALLOWED
    target = os.readlink(full)
    if os.path.isabs(target):
        return leaves
    dest = os.path.normpath(os.path.join(os.path.dirname(rel), target))
    if not dest.startswith(LINKS_ALLOWED) or (indexed is not None and dest not in indexed):
        return leaves
    whole = os.path.join(os.path.dirname(full), target)
    if not os.path.lexists(whole):
        return leaves   # a name the tree does not hold, whether or not git has an index here
    # and a file, not another link: `dest in indexed` is true of a link too, so without this a lane link may name
    # another one, or itself, and a cycle reads as "names a file" (the review of 669, N2)
    if os.path.islink(whole) or not os.path.isfile(whole):
        return "a symbolic link whose target is not a regular file of %s" % LINKS_ALLOWED
    return None


# Hand-written files that only lint judges, kept here rather than in paths.TABLE because paths.py is part of the
# checker (keys.NOT_THE_CHECKER does not name it), so a pattern added there re-keys every unit.  The two skills that
# move here from the shared skills plugin: how to find the proved statement a new statement ports from, and how to
# restate a text without copying it; the commit that adds their files also adds both to release_tree.INTERNAL, which
# cuts them from a release.  And toolchain/requirements.txt, the PyYAML pin the checker image installs
# (toolchain/checker.Dockerfile), which the release that moves tools/oft/ to oft/ and oftdev/ gives a paths.TABLE row.
# And toolchain/rocq-patches/*.patch, the kernel patches the checker image builds Rocq 9.2.0 with (OSSV-644; the
# Dockerfile pins each by its SHA-256): here first, since pr.yml lints a change by its base's rules, and the change that
# adds the patches can pass only a lint whose base admits them.
# And dev/licence/, the shared licence-record generator (OSSV-400) and its tests, which every unit's made_from.py calls:
# lint admits it, and pr.yml lints a change by its base's rules; it is outside tools/, so keys.checker, which lists
# tools/ alone, holds none of it; and a release carries it, since release_tree.INTERNAL does not name it.
# And the files of the three checks that each pull request of the public repository gets, which OSSV-553's change,
# the one after this one, adds: here first, since pr.yml lints a change by its base's rules.  The held-content
# workflow scans the text a pull request adds for keys and names that must stay private; its scanner, its pattern
# table, the lines no pattern may match and the digest of its private patterns are under .github/held/, and
# held-content-private.yml runs the private patterns.  The statement-freeze and pin-coherence workflows have their
# scripts under .github/guards/.  Each is named by its exact path, so a new file in .github/held/ or .github/guards/
# has no class until a change names it; and a release carries them, since release_tree.INTERNAL does not name them.
# The tests of the three checks, which OSSV-553 adds under tools/oft/tests/, have the class of a paths.TABLE row.
# And the files of the public repository's review that Dispatch issue OSSV-612 adds and that no paths.TABLE row
# matches (a row of paths.TABLE matches its other new files, such as docs/review-answer.md).  Under .github/review/:
# rules.py, the rules of the review that code applies, whatever the model wrote; trim.py, the fresh reader that trims
# a text before it is posted; and the three skills that the review loads, each copy with its licence where it has one.
# And two workflows: .github/workflows/rescreen.yml, the rescreen pass; and .github/workflows/screen-start.yml, which
# OSSV-612 makes the one workflow of the public repository that starts on pull_request_target.  Here first, since
# pr.yml lints a change by its base's rules.  Each is named by its exact path, so a new file in .github/review/ has no
# class until a change names it; and a release carries them, since release_tree.INTERNAL does not name them.
# And .github/workflows/workflow-size.yml, which Dispatch issue OSSV-841 adds: a workflow of its own that fails a pull
# request or a merge queue group in which any workflow file is over 490,000 bytes.  GitHub starts no run of a workflow
# file over 500 KB, so pr.yml's own guard cannot run once pr.yml is past that, and this small file still starts.  Here
# first, since pr.yml lints a change by its base's rules; a release carries it, as it carries pr.yml, which it guards.
# And the scripts of pr.yml's steps under .github/scripts/pr/, which OSSV-841 moves there so that pr.yml stays well under
# that limit: each holds one step's run text byte for byte, and the step's whole `run:` calls it from the commit the
# workflow runs from.  Here first, since pr.yml lints a change by its base's rules.  Each is named by its exact path, so
# a new file in .github/scripts/ has no class until a change names it; a release carries them, as it carries pr.yml.
# And a project's NOTICE (PROJECT_NOTICE), which a maintainer writes for a project whose proof files are under it
# (private_projects, scan_licence): here first, since pr.yml lints a change by its base's rules, and the change that
# adds a NOTICE can pass only a lint whose base admits it.  No key reads it (keys.py reads a project's project.yaml
# and harness.yaml files alone).  The release cut keeps nothing of a `release: private` project but its project.yaml
# in the held form and its page (release_tree), so a NOTICE ships only with a project that is not private: check_paths
# refuses one there.
LINT_ONLY_HAND = (".claude/skills/porting-released-proofs/SKILL.md",
                  ".claude/skills/porting-released-proofs/references/*.md",
                  ".claude/skills/clean-room-restatement/SKILL.md",
                  ".claude/skills/clean-room-restatement/references/*.md",
                  "toolchain/requirements.txt",
                  "toolchain/rocq-patches/*.patch",
                  "dev/licence/**",
                  ".github/workflows/held-content.yml",
                  ".github/workflows/held-content-private.yml",
                  ".github/held/held_content_scan.py",
                  ".github/held/detectors.tsv",
                  ".github/held/must-pass-lines.txt",
                  ".github/held/private-detectors.sha256",
                  ".github/workflows/statement-freeze.yml",
                  ".github/guards/statement_freeze.py",
                  ".github/workflows/pin-coherence.yml",
                  ".github/guards/pin_coherence.py",
                  ".github/review/rules.py",
                  ".github/review/trim.py",
                  ".github/review/skills/asd-ste100/LICENSE",
                  ".github/review/skills/asd-ste100/SKILL.md",
                  ".github/review/skills/asd-ste100/examples/before-after.md",
                  ".github/review/skills/asd-ste100/references/writing-rules.md",
                  ".github/review/skills/ce-noslop/LICENSE",
                  ".github/review/skills/ce-noslop/SKILL.md",
                  ".github/review/skills/ce-noslop/references/patterns.md",
                  ".github/review/skills/ce-noslop/references/terminology.md",
                  ".github/review/skills/write-to-maintainer/SKILL.md",
                  ".github/review/skills/write-to-maintainer/judge.md",
                  ".github/workflows/rescreen.yml",
                  ".github/workflows/screen-start.yml",
                  ".github/workflows/workflow-size.yml",
                  ".github/scripts/pr/check-build-files.sh",
                  ".github/scripts/pr/lint-left-out.sh",
                  ".github/scripts/pr/lint-since.sh",
                  ".github/scripts/pr/lint-strip.sh",
                  ".github/scripts/pr/made-from-records.sh",
                  ".github/scripts/pr/made-from-tests.sh",
                  ".github/scripts/pr/plan-elsewhere.sh",
                  ".github/scripts/pr/plan-lint-gate.sh",
                  ".github/scripts/pr/stream-tools-base-tree.sh",
                  ".github/scripts/pr/stream-tools-entry-points.sh",
                  ".github/scripts/pr/stream-tools-history.sh",
                  ".github/scripts/pr/stream-tools-pins.sh",
                  PROJECT_NOTICE)
# What only this repository has, as paths.TABLE's internal rows are, that only lint judges, here for the same reason:
# a row of paths.TABLE is part of the checker, and the INTERNAL of paths.py is made of those rows.  dev/enroll/, the
# place of the scripts that carry a merged theorem-labs/oss-verify enrollment into these facts, which enroll.yml and
# enroll-build.yml run and no check opens: outside tools/, so keys.checker, which lists tools/ alone, holds none of
# them (OSSV-276; they leave tools/enroll/, whose paths.TABLE row is internal, in the commit after this one, since
# pr.yml lints a change by its base's rules).  And .github/rekey-window, the file on main whose bytes say whether a
# re-key window is open (pr.yml's rekey job reads it from the base's tree): only this repository opens such a window
# (OSSV-413).  release_tree.INTERNAL is each entry of this list (a directory with its trailing /, a file as
# it is), then the INTERNAL of paths.py, then release_tree.SKILLS
# (test_release_tree.test_every_internal_path_is_one_the_cut_removes), so the cut removes dev/enroll/ whole and the
# window file, and is_internal reads them for secrets alone, as it reads tools/enroll/.
# paths.TABLE's tools/enroll/** row then matches nothing.  A dev/enroll/** row and a .github/rekey-window row of
# paths.TABLE could take the place of the first two entries.  Dispatch issue OSSV-424 changed paths.py and kept them
# here: its R5 names this list as the place of the scan workflow (.github/workflows/held-refscan.yml), and it moves
# no other entry.
# dev/gateway-model/, the model gateway's formal model (OSSV-498): Rocq definitions and an extracted checker that no
# checker unit reads and its own build script builds, which no release carries, so the cut removes it whole and no
# unit's key moves; and .github/workflows/gateway-model.yml, the workflow that builds and checks it.
# dev/evals/, the tools that run this repository's evals (OSSV-643: dev/evals/paired-run/, the runner and the
# sandbox of a paired run), which no check opens and no release carries, so the cut removes it whole and no unit's
# key moves; and .github/workflows/paired-run.yml, the workflow that runs the paired run's tests.
# The two files of OSSV-299, which moves the proof checks to the shared Rocq build service:
# .github/workflows/rocq-release.yml, the release test on the service's test instance, the one workflow whose token the
# service's release-test account accepts (INFRA-4207); and .github/theorem-rule-classes.tsv, the table of memory classes
# that the service's client `theorem check` reads at the commit it checks (OSSV-654).  `oft check` opens neither, so no
# release carries them.  No public check reads the table: the public checks run the public README's command with no
# build service.  And a commit with no table gives every action `std`, which can make an action fail at its memory limit
# but never make a check pass.
# The two files of the CI reviewer, which the pull request of Dispatch issue OSSV-774 adds:
# .github/workflows/ci-review.yaml, the caller that runs agent-infra's CI reviewer on each pull request that Legion does
# not run, and .github/ci-review.md, the rules file that holds this repository's own check for that reviewer.
# `oft check` opens neither.  No release carries them, because the public repository can use neither: the caller calls a
# workflow of agent-infra, and the rules file holds this repository's own check for agent-infra's CI reviewer.
# .github/workflows/held-refscan.yml, the daily scan of the public refs for held fuzz targets, which the pull request
# of Dispatch issue OSSV-377 adds: the cut removes it too.
# .github/workflows/verdicts.yml, the one writer of the store of build-cluster results (Dispatch issue OSSV-832), which
# no check opens and no release carries: here first, since pr.yml lints a change by its base's rules, and the cut
# removes it too.
# .github/README.md, the page GitHub shows on this repository's front page in place of the root README.md, which
# OSSV-668 stops committing: here first, since pr.yml lints a change by its base's rules.  It is internal, so the cut
# removes it, and a release's front page is its own rendered README.md.  It is named by its exact path.
LINT_ONLY_INTERNAL = ("dev/enroll/**", ".github/rekey-window", "dev/gateway-model/**",
                      ".github/workflows/gateway-model.yml", "dev/evals/**", ".github/workflows/paired-run.yml",
                      ".github/workflows/rocq-release.yml", ".github/theorem-rule-classes.tsv",
                      ".github/workflows/ci-review.yaml", ".github/ci-review.md", ".github/workflows/held-refscan.yml",
                      ".github/workflows/verdicts.yml", ".github/README.md")


def classify_path(rel):
    """paths.classify, then LINT_ONLY_HAND (hand) and LINT_ONLY_INTERNAL (internal) for a path no paths.TABLE pattern
    matches."""
    m = paths.classify(rel)
    if m:
        return m
    return ([("hand", p, b) for p in LINT_ONLY_HAND if (b := paths.match(p, rel)) is not None]
            + [("internal", p, b) for p in LINT_ONLY_INTERNAL if (b := paths.match(p, rel)) is not None])


def is_internal(rel):
    """paths.is_internal, or a path of LINT_ONLY_INTERNAL: what only this repository has, which no release carries."""
    return paths.is_internal(rel) or any(paths.match(p, rel) is not None for p in LINT_ONLY_INTERNAL)


def check_paths(tree, files, unread=()):
    """paths: every file's name, and the bytes of every file on disk.  unread: the tracked files a sparse checkout
    leaves off disk (left_out).  Their names are judged as every other file's (pattern, project, harness, statement,
    case, layout), so a stray path under a proof library still fails; their bytes are not read, and a symbolic link
    among them is a finding, since its target cannot be judged.  pr.yml's pull-request lint takes such a checkout
    (lint_files_left_out) only when it reads only the changed files, and the lint job then checks out each left-out
    file that changed: a file still left out did not change, and keeps the verdict its bytes had there.  The merge
    queue's lint reads the whole tree."""
    out, notes = [], []
    programs = classifier_programs(tree)
    indexed = index_files(tree.path(""))
    unread = {rel for rel in unread if not paths.ignored(rel)}
    links = index_links(tree.path(""), unread)
    every_name = sorted(set(files) | unread)
    # the files the patch entries of each project name, in its patches folder (facts.Project.patch_path)
    entry_files = {p: {proj.patch_path(e["file"]) for e in proj.data.get("patches", [])}
                   for p, proj in tree.projects.items()}
    for rel in every_name:
        if tree.projects and rel.startswith("notes/") and rel[len("notes/"):-len(".md")] not in tree.projects:
            notes.append(Finding("paths", rel, "notes for a project this release does not list"))
        if QUOTED_NAME.search(rel):
            # git lists such a name quoted (even with core.quotePath=false), and the changed-path list CI reads
            # (pr.yml, check_changes, oft plan) holds it in that form: no path pattern can judge it
            out.append(Finding("paths", rel, "a name with a '\"', a '\\' or a control character"))
            continue
        m = classify_path(rel)
        if len(m) != 1:
            out.append(Finding("paths", rel, "matches no path pattern" if not m else
                               "matches %d path patterns: %s" % (len(m), [x[1] for x in m])))
            continue
        cls, pat, b = m[0]
        p = b.get("project")
        if p is not None and p not in tree.projects:
            out.append(Finding("paths", rel, "no project %r" % p))
            continue
        h = b.get("harness")
        if h is not None:
            proj = tree.projects[p]
            if h not in proj.harnesses:
                out.append(Finding("paths", rel, "no included harness %r in %s" % (h, p)))
                continue
            s = b.get("statement")
            if s is not None and s not in proj.harnesses[h].statements:
                out.append(Finding("paths", rel, "no statement %r" % s))
            build = os.path.basename(rel)[:-len(".tsv")] if pat == SYMBOL_FACT else None
            if build is not None and build not in dict(proj.harnesses[h].builds()):
                out.append(Finding("paths", rel, "%r is no build %s/%s publishes" % (build, p, h)))
        if pat.endswith(".opam") and os.path.basename(rel) != names.opam_package(tree.opam_stem, p) + ".opam":
            out.append(Finding("paths", rel, "the opam file of %s is %s.opam"
                               % (p, names.opam_package(tree.opam_stem, p))))
        if pat in PATCH_PATTERNS and rel not in entry_files[p]:
            out.append(Finding("paths", rel, "no patches entry of %s names it" % p))
        if pat == PROJECT_NOTICE and tree.projects[p].data.get("release") != "private":
            out.append(Finding("paths", rel, "a project's NOTICE is the licence of the proof files of a project whose "
                                             "project.yaml says `release: private` (docs/adding-a-proof.md, "
                                             "requirement 7): %s's does not, so a release would publish this file"
                                             % p))
        if rel in unread:
            if rel in links:
                out.append(Finding("paths", rel, "a symbolic link this sparse checkout leaves out: its target is not "
                                   "judged here"))
            continue
        full = tree.path(rel)
        st = os.lstat(full)
        if stat.S_ISLNK(st.st_mode):
            refusal = _link_refusal(full, rel, indexed)
            if refusal is not None:
                out.append(Finding("paths", rel, refusal))
            continue
        if not stat.S_ISREG(st.st_mode):
            out.append(Finding("paths", rel, "not a regular file"))
            continue
        size, cap = st.st_size, facts.file_cap(rel)
        if size > cap:
            out.append(Finding("paths", rel, "%d bytes, over the %d-byte cap" % (size, cap)))
        derived = rel.endswith(DERIVED_SUFFIXES) and not rel.startswith(DERIVED_ALLOWED)
        if derived or "__pycache__" in rel.split("/"):
            out.append(Finding("paths", rel, "a derived file (.vo, .hex, .pyc, ...): these are never stored"))
        try:
            with os.fdopen(facts.open_bounded(full, max(size, cap)), "rb") as f:
                head = f.read(64)
                digest = hashlib.sha256(head) if rel in programs else None
                nul = b"\0" in head
                for chunk in iter(lambda: f.read(1 << 20), b""):
                    nul = nul or b"\0" in chunk
                    if digest is not None:
                        digest.update(chunk)
                    elif nul:
                        break
        except facts.BoundedFileError as e:
            out.append(Finding("paths", rel, str(e)))
            continue
        if digest is not None:
            if digest.hexdigest() != programs[rel][0]:
                out.append(Finding("paths", rel, "a classifier program whose SHA-256 is not the classifier.sha256 of "
                                   "%s/proof.yaml" % programs[rel][1]))
        elif head.startswith(b"\x7fELF") and rel not in ELF_FIXTURES:
            out.append(Finding("paths", rel, "an ELF file: binaries are release assets, not files in git"))
        elif nul and not any(paths.match(p, rel) is not None for p in BINARY_OK):
            out.append(Finding("paths", rel, NUL_BYTE))
        if head.startswith(LFS_POINTER):
            out.append(Finding("paths", rel, "a Git LFS pointer"))
        if rel == ".gitattributes" and size <= cap:   # over its cap, it is a finding already and is not read
            attributes = facts.read(full)
            if "filter=lfs" in attributes:
                out.append(Finding("paths", rel, "an LFS filter"))
            # a checkout in another encoding than the blob's hides a file's text from the text rules
            if "working-tree-encoding" in attributes:
                out.append(Finding("paths", rel, "a working-tree-encoding"))
    # A checkout on a case-insensitive file system (macOS, Windows) keeps one of two paths equal up to case and
    # silently drops or overwrites the other: every path, and every directory on it, must differ from the rest in more
    # than case.
    spellings = collections.defaultdict(list)
    for rel in every_name:
        parts = rel.split("/")
        for n in range(1, len(parts) + 1):
            p = "/".join(parts[:n])
            seen = spellings[p.lower()]
            if p not in seen:
                if seen:
                    out.append(Finding("paths", p, "equal up to case to %s: a case-insensitive checkout keeps only one"
                                       % seen[0]))
                seen.append(p)
    out += notes
    # an unported pull request lays old-layout files over a per-project base: `oft port-layout` moves them
    if any(layout.of_path(rel) == layout.NEW for rel in every_name):
        out += [Finding("paths", rel, "an old-layout path in a per-project tree: run ./oft port-layout")
                for rel in every_name if layout.of_path(rel) == layout.OLD]
    for sid, pd in tree.proofs.items():
        total = sum(os.path.getsize(os.path.join(dp, f)) for dp, _, fs in os.walk(tree.path(pd.path)) for f in fs)
        if total > PROOF_DIR_CAP:
            out.append(Finding("paths", pd.path, "%d bytes of proof, over the %d-byte cap" % (total, PROOF_DIR_CAP)))
    return out


def check_symbols(tree, files):
    """schema: a build's symbol fact (`oft symbols`) reads whole, and is of the binary harness.yaml pins for the build:
    a rebuild that changes the binary leaves the fact stale until `oft symbols` runs again.  Only a fact among files
    is read, and symbols.load reads no symbolic link, special file or file over its cap: check_paths reports each."""
    listed = set(files)
    out = []
    for h in tree.harnesses():
        for build, rec, rel in h.symbol_facts():
            if rel not in listed:
                continue
            try:
                sha256, _rows = symbols.load(tree.path(rel))
            except facts.BoundedFileError:
                continue
            except ValueError as e:
                out.append(Finding("schema", rel, str(e)))
                continue
            pin = rec.get("sha256")
            if sha256 != pin:
                out.append(Finding("schema", rel, "of the binary with sha256 %s, but harness.yaml pins builds.%s.sha256"
                                   " %s: run oft symbols again for this build" % (sha256, build, pin)))
    return out


def check_deviation(tree):
    """schema: a fuzz target of a project in shapes.REQUIRED carries `deviation`, and every `deviation` says what
    its build record (deviation.from_recipe) and the TLS scans of its builds that are not withheld
    (deviation.load_scans, deviation.compare) say.  A build record that from_recipe cannot read is a finding that names
    the file and the line."""
    out = []
    for h in tree.harnesses():
        rel = "%s/harness.yaml" % h.dir
        record = h.data.get("deviation")
        if record is None:
            if h.project.name in shapes.REQUIRED:
                out.append(Finding("schema", rel, "deviation: required for project %s" % h.project.name))
            continue
        builds = h.data.get("builds")
        if not isinstance(record, dict) or not isinstance(builds, dict):
            continue   # rules.check reports the shape
        try:
            derived = deviation.from_recipe(tree, h)
        except ValueError as e:
            out.append(Finding("schema", rel, "deviation: the build record cannot be read: %s" % e))
            continue
        out += [Finding("schema", rel, msg)
                for msg in deviation.compare(record, derived, deviation.load_scans(tree, h), builds)]
    return out


def _instance(tree, h, name, inst):
    """The messages of statement name's instance record inst: its file is a regular file of fewer than
    facts.INSTANCE_MAX_BYTES bytes whose size and SHA-256 are the record's, and on which the driver does what `path`
    says: it refuses a file of max_input_bytes or more (theories/Driver.v), and calls the harness only on a file of its
    whole header (facts.driver_calls)."""
    field = "statements.%s.instance." % name
    if not isinstance(inst.get("file"), str) or not re.fullmatch(r"[A-Za-z0-9._-]+", inst["file"]):
        return []   # rules.check reports the name
    rel = layout.instance_path(h.project.name, h.name, tree.unit_layout("%s/%s" % (h.project.name, h.name)),
                               inst["file"])
    try:
        listed = os.lstat(tree.path(rel))
    except OSError:
        return [field + "file: %s is not in the tree" % rel]
    if stat.S_ISLNK(listed.st_mode):
        return [field + "file: %s is a symbolic link, not a regular file" % rel]
    if not stat.S_ISREG(listed.st_mode):
        return [field + "file: %s is not a regular file" % rel]
    if listed.st_size >= facts.INSTANCE_MAX_BYTES:
        return [field + "bytes: %s has %d bytes, but the driver refuses a file of %d bytes or more "
                "(theories/Driver.v, max_input_bytes)" % (rel, listed.st_size, facts.INSTANCE_MAX_BYTES)]
    try:
        f = facts.read_instance(tree.path(rel))
    except facts.BoundedFileError as e:
        return [field + "file: %s cannot be read: %s" % (rel, e)]
    out = []
    if inst.get("bytes") != f.bytes:
        out.append(field + "bytes: is %s, but %s has %d bytes" % (inst.get("bytes"), rel, f.bytes))
    if inst.get("sha256") != f.sha256:
        out.append(field + "sha256: is %s, but %s has sha256 %s" % (inst.get("sha256"), rel, f.sha256))
    if inst.get("path") == "reaches-harness" and facts.driver_calls(f.data) is None:
        if f.bytes < facts.DRIVER_HEADER_MIN:
            out.append(field + "path: reaches-harness, but %s has %d bytes, fewer than the driver's %d-byte header: "
                       "the driver exits 2 without calling the harness (theories/Driver.v)"
                       % (rel, f.bytes, facts.DRIVER_HEADER_MIN))
        else:
            need = facts.driver_header_bytes(f.data)
            out.append(field + "path: reaches-harness, but %s has %d bytes, and its config word asks for %d "
                       "config bytes after it, so %d bytes: the driver exits 2 without calling the harness "
                       "(theories/Driver.v)" % (rel, f.bytes, need - facts.DRIVER_HEADER_MIN, need))
    return out


def check_instances(tree):
    """schema: every statement of a project in shapes.REQUIRED carries `instance`, and each `instance` names a
    regular file in evidence/instances/ of the build record's folder, of fewer than facts.INSTANCE_MAX_BYTES bytes,
    with the record's size and SHA-256, on which the driver calls the harness when the record's path is
    reaches-harness (at least the driver's header and the config bytes it asks for; refused-by-driver runs with no
    input file argument, so any size is that path).  Each message names the field.  A classifier statement
    (shapes.CLASSIFIER_KINDS) is left out: it has no instance form, so it takes none (rules._classifier_statement)."""
    out = []
    for h in tree.harnesses():
        rel = "%s/harness.yaml" % h.dir
        statements = h.data.get("statements")
        for name, s in sorted(statements.items()) if isinstance(statements, dict) else ():
            if isinstance(s, dict) and s.get("kind") in shapes.CLASSIFIER_KINDS:
                continue
            inst = s.get("instance") if isinstance(s, dict) else None
            if inst is None:
                if h.project.name in shapes.REQUIRED:
                    out.append(Finding("schema", rel, "statements.%s.instance: required for project %s"
                                       % (name, h.project.name)))
            elif isinstance(inst, dict):
                out += [Finding("schema", rel, msg) for msg in _instance(tree, h, name, inst)]
    return out


def check_project_pages(tree):
    """Every project folder holds the project page `oft generate` renders.  Only a release tree must: on the line
    the page is the render's after the merge (paths.SHARED), so a new project's facts pull request does not carry
    it, and a release cut renders every file."""
    out = []
    for proj in tree.projects.values():
        if not os.path.isfile(tree.path(proj.dir, "README.md")):
            out.append(Finding("paths", proj.dir, "no README.md (run ./oft generate)"))
    return out


def _ledger(root):
    """The findings files of the tree at root, in either layout (each fuzz target's findings folder and each project's
    unpatched.yaml), by their path in the new layout (layout.canonical): {that path: [its paths at root]}.  Outside
    the ignored folders, and the bin/ of each old-layout findings/<p>/, which `oft fetch --findings` filled.  The
    pull-request workflow sparse-checks out the base's findings beside the base's tools just for this ledger
    comparison; never load it as facts, since the head's trusted tools judge the proposed tree."""
    found = []
    for dp, dns, fns in os.walk(os.path.join(root, "findings")):
        rel = os.path.relpath(dp, root).replace(os.sep, "/")
        if rel.count("/") == 1:
            dns[:] = [d for d in dns if d != "bin"]
        found += [rel + "/" + fn for fn in fns]
    for dp, dns, fns in os.walk(os.path.join(root, "projects")):
        rel = os.path.relpath(dp, root).replace(os.sep, "/")
        depth = rel.count("/")   # 1: projects/<p>, 2: projects/<p>/<h>, 3 and more: its findings folder
        dns[:] = [d for d in dns if not paths.ignored(rel + "/" + d) and (depth != 2 or d == "findings")]
        found += [rel + "/" + fn for fn in fns if depth >= 3 or depth == 1 and fn == "unpatched.yaml"]
    out = {}
    for rel in found:
        out.setdefault(layout.canonical(rel), []).append(rel)
    return out


_FINDING_FILE = re.compile(layout.FINDING_FILE_RE)
_UNPATCHED_FILE = re.compile(layout.UNPATCHED_FILE_RE)
# What a finding's runs are of: CI re-runs its record against these, so they never change once the base has it.
# Its state, summary, upstream and patch text may.
_FIXED_FILES = ("input.bin", "control.bin")


def _ledger_yaml(root, rel, cap=facts.FINDING_FILE_CAP):
    return yamlio.load(facts.read_bounded(os.path.join(root, rel), cap).decode(), where=os.path.join(root, rel))


def _runner(release):
    """images.runner of a release.yaml's YAML: the image CI re-runs findings in."""
    images = release.get("images") if isinstance(release, dict) else None
    return images.get("runner") if isinstance(images, dict) else None


def _fixed_evidence(tree, base, ledger, held):
    """Each finding the base has keeps its input.bin and control.bin, its statements include the base's (a longer list
    makes a stronger claim, and CI checks each), and the unpatched pin of each build its statements name stays as it
    is; a pin for another build may be added or changed.  Its recorded runs of those builds stay as they are too,
    unless the proposed tree's runner image (release.yaml's images.runner) differs from the base's: the base is
    checked, so its runs are what that runner gave on those pins, and only another runner gives others.  The builds
    are read from the base record's statement names (names.statement_builds), as `oft ledger` reads them.  ledger and
    held are the findings files of the base and of the proposed tree (_ledger), so a file is compared with itself
    wherever the proposed tree moved it, and each change is reported where the proposed tree has it.  A file the
    proposed tree deleted is reported as a deletion, and one the loader refused as a tree error, so neither is
    compared here."""
    out = []
    ran = {}   # (project, harness) -> the builds a base finding of it names
    base_runner = _runner(_ledger_yaml(base, "release.yaml", facts.file_cap("release.yaml")))
    new_runner = None not in (base_runner, _runner(tree.release)) and _runner(tree.release) != base_runner
    for key in sorted(ledger):
        if not (_FINDING_FILE.match(key) and key.endswith("/finding.yaml")):
            continue
        d = key[:-len("/finding.yaml")]
        _, p, h, _, s = d.split("/")
        was = _ledger_yaml(base, ledger[key][0])
        builds = {b for st in was["statements"] for b in names.statement_builds(st) or ()}
        ran.setdefault((p, h), set()).update(builds)
        for name in _FIXED_FILES:
            fixed = d + "/" + name
            for now in held.get(fixed, ()) if fixed in ledger else ():
                try:
                    proposed = facts.read_bounded(tree.path(now), facts.FINDING_INPUT_CAP)
                except facts.BoundedFileError:
                    continue
                if proposed != facts.read_bounded(os.path.join(base, ledger[fixed][0]), facts.FINDING_INPUT_CAP):
                    out.append(Finding("paths", now, "a finding's %s is never changed: %s" % (name, now)))
        head = tree.findings.get("%s/%s/%s" % (p, h, s))
        rel = head.path + "/finding.yaml" if head else ledger[key][0]
        dropped = sorted(set(was["statements"]) - set(head.data["statements"])) if head else []
        if dropped:
            out.append(Finding("paths", rel, "a finding's statements only grow: %s no longer names %s"
                               % (rel, ", ".join(dropped))))
        # a state only moves forward from one whose patch the pinned build carries (rules.SERIES_STATES): for an
        # enrolled project an open finding holds back only its statements, so a return to open would release most of
        # a hold while that build still carries the patch.  A pruned or not-a-defect finding has no such build, and a
        # defect found in it later must be able to go back to open.
        if head and head.data.get("state") == "open" and was.get("state") in rules.SERIES_STATES:
            out.append(Finding("paths", rel, "a finding's state never returns to open: %s was %s"
                               % (rel, was["state"])))
        for which in ("input", "control") if head and "input" in was and not new_runner else ():
            for b in sorted(builds & set(was[which]), key=schema.BUILDS.index):
                if (head.data.get(which) or {}).get(b) != was[which][b]:
                    out.append(Finding("paths", rel, "a finding's recorded runs are never changed: %s %s.%s"
                                       % (rel, which, b)))
    for p in sorted({p for p, _ in ran}):
        was_at = ledger.get(layout.unpatched_path(p, layout.NEW))
        head = tree.unpatched.get(p)
        if was_at is None or head is None:
            continue
        pinned = _ledger_yaml(base, was_at[0])["harnesses"]
        rel = tree.unpatched_paths[p]
        for (q, h), builds in sorted(ran.items()):
            if q != p:
                continue
            was, now = pinned.get(h, {}), head["harnesses"].get(h, {})
            for b in sorted(builds & set(was), key=schema.BUILDS.index):
                if was[b] != now.get(b):
                    out.append(Finding("paths", rel, "a finding's unpatched pins are never changed: %s harnesses.%s.%s"
                                       % (rel, h, b)))
    return out


SHARED_FILE = ("a shared generated file: only a release pull request changes it, to the render; the line's render "
               "after the merge writes it (./oft generate --skip-shared renders every other generated file)")
SHARED_DIFFERS = ("a shared generated file that differs from the render: a release pull request carries one only as "
                  "./oft generate renders it from this tree (run ./oft generate)")
SHARED_UNRENDERED = ("a shared generated file, and ./oft generate renders nothing from this tree (%s): a release pull "
                     "request carries one only as the render writes it")


def _shared_render(tree):
    """{path: bytes} of each shared generated file (paths.SHARED) as `oft generate` writes it for tree: the text that
    generate.render_all gives, which generate.run writes and `generate --check` compares, in UTF-8 with no newline
    translation.  Where generate.run renders nothing for tree, the reason in words instead: the facts have an error,
    there is no release.yaml, a sparse checkout leaves out a proof library (layout.unwritten_libraries), or the
    render stops (a symbol fact that does not load: rules.symbol_facts, which check_symbols reports)."""
    if tree.errors:
        return "the facts have %d error(s)" % len(tree.errors)
    if tree.release is None:
        return "there is no release.yaml"
    missing = layout.unwritten_libraries(tree.root, sorted("%s/%s" % (h.project.name, h.name)
                                                           for h in tree.harnesses()))
    if missing:
        return "this checkout leaves out the proof library %s" % missing[0][1]
    try:
        rendered = generate.render_all(tree)
    except (ValueError, facts.BoundedFileError) as e:
        return "the render stops: %s" % e
    return {rel: text.encode("utf-8") for rel, text in rendered.items() if paths.is_shared(rel)}


def _is_render(tree, rel, rendered):
    """Whether the file at rel is a regular file whose bytes are its render, rendered[rel] (_shared_render)."""
    try:
        return rel in rendered and facts.read_bounded(tree.path(rel), facts.file_cap(rel)) == rendered[rel]
    except facts.BoundedFileError:
        return False


def check_changes(tree, changed, kind, base=None):
    """The pull-request half of `paths`.  kind: release | maintainer | contributor.  base is the trusted base tree
    when CI compares the findings ledger: every record remains in the proposed tree, the unpatched pins remain while
    its project has a base finding, and what a base finding's runs are of stays as it is (_fixed_evidence).  The base
    is walked as well as changed read, since a diff that detects renames lists a moved file only where it went.  A
    file is the same in either layout (layout.canonical): a finding the pull request moves to the other layout is
    neither deleted nor free to change.  A pull request carries no shared generated file (paths.SHARED), except a
    release, which carries each one byte for byte as `oft generate` renders it from the proposed tree
    (_shared_render, made once, and only for a release that carries one): the public line has no render after the
    merge, so the release commit is that render."""
    out = []
    ledger = _ledger(base) if base else {}
    held = _ledger(tree.root)
    render = None   # _shared_render of the proposed tree, made at the first shared generated file a release carries
    with_finding = {key.split("/")[1] for key in ledger if _FINDING_FILE.match(key) and key.endswith("/finding.yaml")}
    gone = {rel for rel in list(changed) + [rel for rels in ledger.values() for rel in rels]
            if not os.path.lexists(tree.path(rel)) and layout.canonical(rel) not in held}
    for rel in sorted(gone):
        if _FINDING_FILE.match(rel):
            out.append(Finding("paths", rel, "a finding is never deleted: %s" % rel))
        m_unpatched = _UNPATCHED_FILE.fullmatch(rel)
        if m_unpatched and (m_unpatched.group(1) or m_unpatched.group(2)) in with_finding:
            out.append(Finding("paths", rel, "a finding's unpatched pins are never deleted: %s" % rel))
    if base:
        out += _fixed_evidence(tree, base, ledger, held)
    for rel in changed:
        m = paths.classify(rel)
        cls = m[0][0] if len(m) == 1 else None
        if cls == "facts" and kind != "release":
            out.append(Finding("paths", rel, "an exported fact: only a release pull request changes it"))
        if kind == "contributor" and cls not in ("contrib", "gen") and not rel.startswith("docs/"):
            out.append(Finding("paths", rel, "outside the proofs and counterexamples folders, docs/ and generated "
                                             "files"))
        if kind != "release" and (rel.startswith("theories/") or rel.startswith("toolchain/")):
            out.append(Finding("paths", rel, "changes every statement: only a release pull request changes it"))
        # A shared generated file is the line's render's.  A deletion passes: the render puts it back on the line,
        # and on main they go for good.  Any pull request but a release leaves the file to the line's render after
        # the merge.  A release carries the file only as `oft generate` renders it from this tree: the public line
        # has no render after the merge, so the release commit is that render.
        if not (paths.is_shared(rel) and os.path.lexists(tree.path(rel))):
            continue
        if kind != "release":
            out.append(Finding("paths", rel, SHARED_FILE))
            continue
        render = _shared_render(tree) if render is None else render
        if isinstance(render, str):
            out.append(Finding("paths", rel, SHARED_UNRENDERED % render))
        elif not _is_render(tree, rel, render):
            out.append(Finding("paths", rel, SHARED_DIFFERS))
    return out


WITHHELD_FLAG = {"source-bundle": "source_bundle", "not-yet-published": "unpublished"}
BUILD_DETAIL = ("bytes", "sha256", "segments")


def check_disclosure(tree):
    """withheld: a withheld item shows no detail, and the project says, by
    reason and without counting, that it withholds something.  A withheld
    build carries no size, digest or segment count (a digest of a build that
    is not published would let anyone test a guess at its bytes), and a
    withheld statement carries no evidence and no fingerprint."""
    out = []
    for proj in tree.projects.values():
        reasons = set()
        for h in proj.harnesses.values():
            where = os.path.join(h.dir, "harness.yaml")
            for b, r in h.data["builds"].items():
                if r.get("withheld"):
                    reasons.add(r["withheld"])
                    shown = [k for k in BUILD_DETAIL if k in r]
                    if shown:
                        out.append(Finding("withheld", where, "builds.%s is withheld but shows %s" % (b, ", ".join(shown))))
                else:
                    missing = [k for k in BUILD_DETAIL if k not in r]
                    if missing:
                        out.append(Finding("withheld", where, "builds.%s is published but has no %s" % (b, ", ".join(missing))))
            # an image a project withholds (a classifier, an original) asks for the project's flag as a build does;
            # rules._published_image checks that it shows no pin
            images = ([rec for _role, _b, rec in h.classifier_builds(False)]
                      + [rec for _b, rec in h.original_builds(False)])
            reasons.update(rec["withheld"] for rec in images if rec.get("withheld"))
            for s in h.statements.values():
                if s.data["status"] == "withheld":
                    reasons.add(s.data.get("withheld"))
                    if s.fingerprint:
                        out.append(Finding("withheld", where, "statements.%s is withheld but has a fingerprint" % s.name))
        wh = proj.data.get("withheld") or {}
        for reason, flag in WITHHELD_FLAG.items():
            if reason in reasons and not wh.get(flag):
                out.append(Finding("withheld", proj.dir, "withholds an item (%s) but does not say so: add withheld.%s"
                                   % (reason, flag)))
            if wh.get(flag) and reason not in reasons:
                out.append(Finding("withheld", proj.dir, "withheld.%s, but nothing is withheld for that reason" % flag))
    return out


PLACEHOLDER_VALUE = re.compile(r"(?<![0-9a-f])0{40}(?:0{24})?(?![0-9a-f])")


def check_placeholders(tree):
    """schema: a digest or commit of all zeros is a placeholder for something not
    published yet (an image, a tag).  It must never read as a pin, so each line
    that still holds one is a finding until the real value replaces it.  The
    finding names the line and what it pins, so that replacing one placeholder
    visibly clears its finding while the others stay."""
    out = []
    for rel in ["release.yaml"] + [os.path.join(p.dir, "project.yaml") for p in tree.projects.values()]:
        p = tree.path(rel)
        if not os.path.isfile(p):
            continue
        for no, line in enumerate(facts.read(p).splitlines(), 1):
            if PLACEHOLDER_VALUE.search(line):
                what = re.split(r"[:=@]", line.strip().lstrip("-").strip(), maxsplit=1)[0].strip() or "a value"
                out.append(Finding("schema", "%s:%d" % (rel, no), "%s is a placeholder digest or commit (all "
                                   "zeros): replace it with the published value before a release" % what))
    return out


# ---------------------------------------------------- records, model, pins

# The classes a build recipe's patch may have, each one build glue: a release's recipe fixes no defect
# (docs/adding-a-proof.md, requirement 4).
GLUE = ("Build adaptation.", "Reproducible build.", "Portability.", "Platform adaptation.", "Harness output.",
        "Harness reporting.", "Fuzz harness.")
UNFINISHED = re.compile(r"\b(?:pending|NOASSERTION|TODO)\b")
COPYLEFT = re.compile(r"\bL?GPL")
# licence.source_bundle as a build record writes it (Contract C1, tools/enroll/README.md): a list of entries, each a
# file by name and the SHA-256 the facts pin it with, and no release (project.yaml's assets and release.yaml name those)
BUNDLE_ENTRY = ("file", "sha256")
SHA256 = re.compile(r"[0-9a-f]{64}")
COMMIT = re.compile(r"[0-9a-f]{40}")
IMAGE_DIGEST = re.compile(r"(?:\S+@)?sha256:[0-9a-f]{64}")
# what a build record names an archive by (Contract C1): project.yaml's assets are the one place that names its release
PIN = ("file", "bytes", "sha256")
STATIC_ASAN = "https://github.com/theorem-labs/static-asan"
DOCKERFILE = "toolchain/checker.Dockerfile"
LPS_PATHS = "toolchain/lps-core.paths"
MODEL_PIN = re.compile(r"^ARG LPS_TREE_SHA256=(.*)$", re.M)


def record_units(tree):
    """[(project, harness)] of every fuzz target with a proof directory or a build record."""
    units = {tuple(sid.split("/")[:2]) for sid in tree.proofs}
    return sorted(units | set(tree.records_at))


def record_path(tree, project, harness):
    """The build record of a fuzz target, in the layout its proofs folder is in (layout.py)."""
    return layout.record_path(project, harness, tree.unit_layout("%s/%s" % (project, harness)))


def _read_record(tree, where):
    """The build record at where, as a mapping, or None: one that is missing, is not a bounded regular file or is
    not a YAML mapping (facts.load has reported the last two)."""
    try:
        r = yamlio.load(facts.read_bounded(tree.path(where), facts.file_cap(where)).decode("utf-8"), where)
    except (facts.BoundedFileError, UnicodeDecodeError, yamlio.YamlError):
        return None
    return r if isinstance(r, dict) else None


def _mapping(v):
    return v if isinstance(v, dict) else {}


def _unfinished(x, path=""):
    """Each unfinished value of a build record, by its path: a string with pending, NOASSERTION or TODO in it, or a
    key `pending: true`; never under a key whose name ends in _in_release_records, which says what an earlier
    release's records held."""
    if isinstance(x, dict):
        for k, v in x.items():
            if str(k).endswith("_in_release_records"):
                continue
            if k == "pending" and v is True:
                yield "%s.pending: true" % path
            else:
                yield from _unfinished(v, "%s.%s" % (path, k))
    elif isinstance(x, list):
        for i, v in enumerate(x):
            yield from _unfinished(v, "%s[%d]" % (path, i))
    elif isinstance(x, str) and UNFINISHED.search(x):
        yield "%s: %s" % (path, x[:70])


def _pin(value, where, kind="asset"):
    """(file, bytes and sha256 of value, None) when they are a release asset pin as the definition kind of
    project.yaml's schema states one, less its release, else (None, why not).  A build record names each archive by
    file, bytes and SHA-256 only (Contract C1): project.yaml's assets are the one place that names its release.  A
    record written before C1 still names one, so the pin returned then holds that release too (_is_pin compares it)."""
    picked = {k: value[k] for k in ("release",) + PIN if k in value} if isinstance(value, dict) else value
    s = schema.load_schema("project")
    spec = s["defs"][kind]
    spec = dict(spec, fields=dict(spec["fields"], release=dict(spec["fields"]["release"], optional=True)))
    problems = []
    schema._check(spec, picked, where, s["defs"], problems)
    return (None, "; ".join(problems)) if problems else (picked, None)


def _is_pin(pin, asset):
    """Whether pin (a build record's archive, as _pin returns it) is asset, an archive project.yaml's assets pin: the
    same file, bytes and sha256, and the same release when the record names one."""
    return isinstance(asset, dict) and pin == {k: asset.get(k) for k in pin}


def _record_builds(binaries):
    """({build: (sha256, bytes)} of a build record's binaries, None), or (None, why they are not one typed entry for
    each build they name)."""
    if not isinstance(binaries, list):
        return None, "binaries is %.80r, not a list" % (binaries,)
    out = {}
    for i, b in enumerate(binaries):
        at = "binaries[%d]" % i
        build = _mapping(b).get("build")
        if not isinstance(build, str) or build not in schema.BUILDS:
            return None, "%s.build is %.40r, not one of %s" % (at, build, ", ".join(schema.BUILDS))
        if build in out:
            return None, "binaries names the build %s more than once" % build
        problems = schema.validate_def("harness", "build", {k: b[k] for k in ("file", "bytes", "sha256") if k in b}, at)
        problems += ["%s: missing key %r" % (at, k) for k in ("bytes", "sha256") if k not in b]
        if problems:
            return None, "; ".join(problems)
        out[build] = (b["sha256"], b["bytes"])
    return out, None


def bundle_pins(tree, proj):
    """{(file, sha256)} of every file a build record of proj's may cite in its licence.source_bundle: the archives
    proj's project.yaml pins (bin, src, src_manifest, port) and its binary archive's recipe, release.yaml's recipes,
    and release.yaml's source archives (sources.toolchain, sources.sysroot)."""
    a = (proj.data.get("assets") or {}) if proj else {}
    pins = list(a.values()) + [(a.get("bin") or {}).get("recipe")] + list(facts.release_recipes(tree))
    sources = (tree.release or {}).get("sources") or {}
    pins += [sources.get(k) for k in ("toolchain", "sysroot")]
    return {(v["file"], v["sha256"]) for v in pins if isinstance(v, dict) and "file" in v and "sha256" in v}


def bundle_problems(bundle, project, pins):
    """Why a build record's licence.source_bundle is not the corresponding source of its GPL- or LGPL-licensed
    component ([] when it is): Contract C1's list of {file, sha256} entries, which names <project>-src.tar.zst, each
    file once, and each with the SHA-256 that pins ({(file, sha256)}, bundle_pins) gives it."""
    if not (isinstance(bundle, list) and bundle and all(
            isinstance(e, dict) and sorted(e) == sorted(BUNDLE_ENTRY) and isinstance(e["file"], str)
            and isinstance(e["sha256"], str) and SHA256.fullmatch(e["sha256"]) for e in bundle)):
        return ["a GPL- or LGPL-licensed component, and licence.source_bundle is %.80r, not a list of {file, sha256} "
                "entries (Contract C1; tools/enroll/c1-source-bundle writes it from the text before)" % (bundle,)]
    out = []
    files = [e["file"] for e in bundle]
    if "%s-src.tar.zst" % project not in files:
        out.append("licence.source_bundle does not cite %s-src.tar.zst, the project's source archive" % project)
    twice = sorted({f for f in files if files.count(f) > 1})
    if twice:
        out.append("licence.source_bundle cites %s more than once" % ", ".join(twice))
    unpinned = ["%s (sha256 %s)" % (e["file"], e["sha256"]) for e in bundle if (e["file"], e["sha256"]) not in pins]
    if unpinned:
        out.append("licence.source_bundle cites %s, which neither projects/%s/project.yaml's assets nor release.yaml's "
                   "recipes and sources pin with that sha256" % (", ".join(unpinned), project))
    return out


def static_asan_commits(tree):
    """({commit: [record]}, {commit: [record]}): the full commit ids of static-asan the build records name, each with
    the records that name it: toolchain.static_asan.commit of each record a recipe or a port built, and
    fallback.static_asan.public_commit of each fallback record (whose original binaries the unpublished internal
    recipe built)."""
    own, fallback = {}, {}
    for p, h in record_units(tree):
        where = record_path(tree, p, h)
        r = _read_record(tree, where)
        if r is None:
            continue
        if r.get("fallback"):
            named, c = fallback, _mapping(_mapping(r["fallback"]).get("static_asan")).get("public_commit")
        else:
            named, c = own, _mapping(_mapping(r.get("toolchain")).get("static_asan")).get("commit")
        if isinstance(c, str) and COMMIT.fullmatch(c):
            named.setdefault(c, []).append(where)
    return own, fallback


def check_records(tree):
    """records (with --release): every fuzz target with a proof has a build record, and each record is complete and
    says what the facts say: no unfinished value; its binaries are the published builds of its harness.yaml, all four;
    what built them (a builder image of release.yaml that its project.yaml's build.builder names, images.builder[0]
    when a recipe built them, since both publish paths rebuild every recipe-built target in that image; the one
    static-asan commit every record of its kind names; a port record's port and port archive those of its
    project.yaml; a fallback record's complete fallback block);
    its binary and source archives those of its project.yaml, by file, bytes and sha256 (Contract C1: a record names
    no release, and one written before C1 names project.yaml's); LICENSES/ exactly the texts its components name; the
    upstream licence; for a GPL- or LGPL-licensed component, a source bundle (Contract C1's list of {file, sha256})
    that cites the project's source archive and only files its project.yaml or release.yaml pins with those sha256s
    (the release gate asks more: that each is published on its release); build glue only among its recipe's patches;
    and its overlay files as recipe/MANIFEST.tsv pins them.  The recipe a record cites is the schema rule's
    (rules._records).  A port-built project's binary archive also goes with its port archive (assets.port)."""
    out = []
    release = tree.release or {}
    builders = (release.get("images") or {}).get("builder") or []
    for p, h in record_units(tree):
        where = record_path(tree, p, h)
        base = os.path.dirname(where)
        add = lambda msg: out.append(Finding("records", where, msg))   # noqa: E731
        if not os.path.isfile(tree.path(where)):
            add("no build record: every fuzz target with a proof has one, which says what built its binaries")
            continue
        r = _read_record(tree, where)
        if r is None:
            continue
        proj = tree.projects.get(p)
        har = proj.harnesses.get(h) if proj else None
        project_yaml = "projects/%s/project.yaml" % p
        pending = list(_unfinished(r))
        if pending:
            add("unfinished values, which a published record never has (pending, NOASSERTION or TODO): %s"
                % "; ".join(pending[:4]))
        # the binaries: each side typed before they are compared, by each build's sha256 and bytes
        recb, error = _record_builds(r.get("binaries") or [])
        if error:
            add(error)
        harness_yaml = "projects/%s/%s/harness.yaml" % (p, h)
        hb = {b: (rec.get("sha256"), rec.get("bytes")) for b, rec in har.builds()} if har else {}
        if not hb:
            add("%s has no published builds, and the record names binaries of them" % harness_yaml)
        elif len(hb) != len(schema.BUILDS):
            add("%s publishes %d builds, not %d" % (harness_yaml, len(hb), len(schema.BUILDS)))
        if recb is not None and hb and recb != hb:
            add("binaries differ from the published builds of %s (each build's sha256 and bytes): %s"
                % (harness_yaml, ", ".join(b for b in schema.BUILDS if recb.get(b) != hb.get(b))))
        if recb is not None and len(recb) != len(schema.BUILDS):
            add("%d binaries, not %d: a record has one of each build" % (len(recb), len(schema.BUILDS)))
        # what built them
        fb = r.get("fallback")
        tc = _mapping(r.get("toolchain"))
        if fb:
            fb = _mapping(fb)
            fsa, rb = _mapping(fb.get("static_asan")), _mapping(fb.get("rebuild"))
            digest = lambda s: isinstance(s, str) and IMAGE_DIGEST.fullmatch(s)   # noqa: E731
            if not (fb.get("reason") and isinstance(fb.get("recipe_commit"), str)
                    and COMMIT.fullmatch(fb["recipe_commit"]) and digest(fb.get("builder_image"))
                    and (fb.get("toolchain_image") is None or digest(fb.get("toolchain_image")))):
                add("fallback: a reason, the recipe commit, and the builder image (and toolchain image, if given) by "
                    "digest: recipe %.12s, builder %s" % (fb.get("recipe_commit"), str(fb.get("builder_image"))[-20:]))
            for k in ("internal_commit", "public_commit"):
                if not (isinstance(fsa.get(k), str) and COMMIT.fullmatch(fsa[k])):
                    add("fallback.static_asan.%s is %.50r, not a full commit id" % (k, fsa.get(k)))
            if not (rb.get("verdict") == "identical x4" and isinstance(rb.get("evidence"), str)
                    and rb["evidence"].strip()):
                add("fallback: the rebuild gave identical x4, with its evidence: %s: %s"
                    % (rb.get("by"), rb.get("verdict")))
        else:
            ported = r.get("port") is not None
            if ported:
                port = _mapping(r["port"])
                if r.get("recipe") is not None:
                    add("the record names a port and a recipe: a port built the binaries, or a recipe did")
                named = facts.port(proj) if proj else None
                if named is None or {k: port.get(k) for k in ("repository", "commit", "path")} != named:
                    add("port is not %s's build.oss_verify" % project_yaml)
                pin, error = _pin(port.get("asset"), "port.asset")
                want = (proj.data.get("assets") or {}).get("port") if proj else None
                if error or not _is_pin(pin, want):
                    add("port.asset is not %s's assets.port%s" % (project_yaml, ": " + error if error else ""))
            image = tc.get("builder_image")
            own = ((proj.data.get("build") or {}).get("builder") if proj else None)
            if image not in builders:
                add("toolchain.builder_image %s is not one of release.yaml's images.builder" % str(image)[-20:])
            elif not ported and image != builders[0]:
                add("toolchain.builder_image %s is not release.yaml's images.builder[0]: both publish paths rebuild a "
                    "recipe-built target in images.builder[0]" % str(image)[-20:])
            elif image != own:
                add("toolchain.builder_image %s is not %s's build.builder" % (str(image)[-20:], project_yaml))
            c = _mapping(tc.get("static_asan")).get("commit")
            if not (isinstance(c, str) and COMMIT.fullmatch(c)):
                add("toolchain.static_asan.commit is %.50r, not a full commit id" % (c,))
        # the archives they ship in, and their source
        pa = (proj.data.get("assets") or {}) if proj else {}
        pin, error = _pin(r.get("binary_asset"), "binary_asset")
        if error or not _is_pin(pin, pa.get("bin")):
            add("binary_asset is not %s's assets.bin%s" % (project_yaml, ": " + error if error else ""))
        record_src, errors = {}, []
        for k, kind in (("src", "asset"), ("src_manifest", "manifest_asset")):
            if _mapping(r.get("source_asset")).get(k):
                pin, error = _pin(r["source_asset"][k], "source_asset." + k, kind)
                record_src[k] = pin
                errors += [error] if error else []
        project_src = [k for k in ("src", "src_manifest") if pa.get(k)]
        if errors or sorted(record_src) != project_src or not all(_is_pin(record_src[k], pa[k]) for k in project_src):
            why = errors or [("the record has %ssource_asset.%s, and project.yaml has %sassets.%s"
                              % ("" if k in record_src else "no ", k, "" if k in project_src else "no ", k))
                             for k in ("src", "src_manifest") if (k in record_src) != (k in project_src)]
            add("source_asset is not %s's assets.src and assets.src_manifest%s"
                % (project_yaml, ": " + "; ".join(why) if why else ""))
        # the licences: every component's texts in LICENSES/ and nothing else, and the upstream licence
        lic = _mapping(r.get("licence"))
        comps = [c for c in lic.get("components") or [] if isinstance(c, dict)] \
            if isinstance(lic.get("components"), list) else []
        texts = {t for c in comps for t in c.get("texts") or [] if isinstance(t, str)}
        files = set()
        for dp, dns, fns in os.walk(tree.path(base, "LICENSES")):
            files |= {os.path.relpath(os.path.join(dp, n), tree.path(base)).replace(os.sep, "/")
                      for n in fns + [d for d in dns if os.path.islink(os.path.join(dp, d))]}
        if not files or files != texts:
            why = (["not named " + ", ".join(sorted(files - texts))] if files - texts else []) + \
                (["missing " + ", ".join(sorted(texts - files))] if texts - files else []) + \
                ([] if files else ["no file under LICENSES/"])
            add("LICENSES/ is not the texts licence.components names: " + "; ".join(why))
        upstream = _mapping(r.get("upstream")).get("licence")
        if upstream in (None, "", "NOASSERTION", "pending"):
            add("upstream.licence is %r: the record names the upstream licence" % (upstream,))
        # a GPL- or LGPL-licensed component ships with its corresponding source, which the facts pin, so the
        # publishing workflow downloads and checks it, and attaches it to a public release before the commit
        if any(COPYLEFT.search(str(c.get("licence"))) for c in comps):
            for problem in bundle_problems(lic.get("source_bundle"), p, bundle_pins(tree, proj)):
                add(problem)
        # the recipe: build glue only, and its overlay files as recipe/MANIFEST.tsv pins them
        recipe = _mapping(r.get("recipe"))
        if r.get("port") is None:
            patches = recipe.get("patches") or []
            bad = ["%s (%s)" % (x.get("patch"), x.get("class")) if isinstance(x, dict) else repr(x)
                   for x in (patches if isinstance(patches, list) else [patches])
                   if not (isinstance(x, dict) and x.get("class") in GLUE)]
            if bad:
                add("recipe.patches are not all build glue: %s" % "; ".join(bad[:3]))
        overlay = recipe.get("overlay") or []
        if overlay:
            try:
                manifest = facts.read_bounded(tree.path(base, "recipe", "MANIFEST.tsv"),
                                              facts.MAX_BYTES).decode("utf-8")
            except (facts.BoundedFileError, UnicodeDecodeError):
                manifest = ""
            pins = {l.split("\t")[0]: l.split("\t")[1] for l in manifest.splitlines()[1:] if l.count("\t") >= 2}
            bad = []
            for f in overlay if isinstance(overlay, list) else [overlay]:
                rel = "%s/recipe/%s" % (base, f)
                try:
                    ok = (isinstance(f, str) and not f.startswith("/") and ".." not in f.split("/")
                          and hashlib.sha256(facts.read_bounded(tree.path(rel), facts.file_cap(rel))).hexdigest()
                          == pins.get(f))
                except facts.BoundedFileError:
                    ok = False
                if not ok:
                    bad.append(str(f))
            if bad:
                add("recipe.overlay files missing, or not of the sha256 recipe/MANIFEST.tsv gives: %s"
                    % "; ".join(bad))
    # every record of a kind names one static-asan commit: the one commit most of them name, if one is, else each
    for what, named in zip(("toolchain.static_asan.commit", "fallback.static_asan.public_commit"),
                           static_asan_commits(tree)):
        top = max((len(w) for w in named.values()), default=0)
        leaders = [c for c, w in named.items() if len(w) == top]
        for c, wheres in sorted(named.items()) if len(named) > 1 else ():
            if leaders == [c]:
                continue
            others = ", ".join("%s (%d)" % (o, len(named[o])) for o in sorted(named) if o != c)
            out += [Finding("records", w, "%s is %s, and other build records name %s: every build record names the "
                            "one static-asan commit its kind of record was built with" % (what, c, others))
                    for w in wheres]
    for name, proj in sorted(tree.projects.items()):
        a = proj.data.get("assets") or {}
        if "bin" in a and facts.port(proj) and "port" not in a:
            out.append(Finding("records", "projects/%s/project.yaml" % name, "a port-built project's binary archive "
                               "goes with its port archive, and assets.port is missing"))
    return out


# `enrolled` as the enrollment writes it (tools/enroll/facts.py, enrolled_fields): a primary_contact that is a
# person, and not the `n/a` of a seeded project or of a pipeline test's fixture.  No module of tools/oft imports
# tools/enroll (keys.NOT_THE_CHECKER), so the rule is written out again here, word for word, and
# test_records.Enrolled pins the pair of them, case by case.
# `null` is in both because they read the same file with different loaders: yamlio takes only the lower-case
# spelling as YAML's null and leaves `NULL` and `Null` as text, where PyYAML, which the enrollment uses, makes all
# three None.  Without it the lint would ask for `enrolled: true` on a file the enrollment read as naming nobody.
# A quoted "null" is no address either side.
def takes_part(contact):
    """Whether a maintainers' project.yaml names a primary_contact that is a person."""
    return contact is not None and str(contact).strip().lower() not in ("", "n/a", "null")


def check_enrolled(tree):
    """schema: `enrolled` says what the maintainers' own project.yaml says, and nothing else sets it.

    The field is not the enrollment list: that list is theorem-labs/oss-verify's `projects/`, and a project of it
    is in this repository only once its facts are written.  Here the field says that the maintainers of a project
    this repository holds take part, and it is written from one file: the copy of the OSS Verify port that each
    build record keeps, `<record>/port/<path>/projects/<project>/project.yaml`, which is the maintainers' own file
    at the commit `build.oss_verify` names.  `enrolled: true` goes in exactly when that file names a
    primary_contact that is a person; a seeded project, whose contact is `n/a` or absent, gets no field, and
    `enrolled: false` is never written: absence is the negative (docs/facts.md, tools/oft/schemas/project.yaml).

    The field weakens a hold -- an open finding of an enrolled project holds back only the statements it names,
    not the whole project (facts.hold) -- so a hand-written `true` would publish statements that a release must
    not carry, and a lost one holds back a project that may ship.  Nothing re-read it after the enrollment wrote
    it; this rule does, on every lint.

    Only a record whose `port` is the project's own build.oss_verify is read: a record of another port commit says
    nothing about the maintainers at this one.  A recipe-built project has no such copy, and no finding here."""
    out = []
    for name, proj in sorted(tree.projects.items()):
        where = "projects/%s/project.yaml" % name
        field = proj.data.get("enrolled")
        if field is not None and field is not True:
            out.append(Finding("schema", where, "enrolled is %.50r: the only value is true, and a project whose "
                               "maintainers do not take part has no such field" % (field,)))
        named = facts.port(proj)
        if named is None:
            continue
        says = {}
        for h in sorted(proj.harnesses):
            record = record_path(tree, name, h)
            r = _read_record(tree, record)
            if r is None:
                continue
            port = _mapping(r.get("port"))
            if {k: port.get(k) for k in ("repository", "commit", "path")} != named:
                continue
            copied = os.path.join(os.path.dirname(record), "port", named["path"], "project.yaml")
            enrol = _read_record(tree, copied)
            if enrol is None:
                continue
            says.setdefault(takes_part(enrol.get("primary_contact")), []).append(copied)
        if len(says) > 1:
            out.append(Finding("schema", where, "the build records disagree on the maintainers' primary_contact: "
                               "%s names one, and %s names none or n/a"
                               % (min(says[True]), min(says[False]))))
        elif says and bool(field) is not next(iter(says)):
            party, copy = next(iter(says.items()))
            out.append(Finding("schema", where, "%s names %s primary_contact, so %s"
                               % (min(copy), "a person as" if party else "no",
                                  "add `enrolled: true` after status" if party
                                  else "remove `enrolled`, which no seeded project has")))
    return out


# The form of a name in a project's private_harnesses: the harness half of HELD_ENTRY, the form of a held entry
# `<project>/<harness>` that every reader of the held entries takes (tools/publish/release_pins.py,
# dev/stream/bin/release_pins.py), each of which refuses the whole list for one entry outside it.  The schema's
# harness-name is wider.  The scanners look for the bare name in every published file (disclosure.held_forms), so a
# held name has HELD_NAME_MIN characters or more: a short name also matches text that does not name the harness.
HELD_NAME = re.compile(r"[a-z0-9][a-z0-9_-]*")
HELD_NAME_MIN = 8
HOLD_WHOLE = "Hold a harness that this list cannot name with its whole project instead (`release: private`)."
# The way out for a field that holds every fuzz target of its project that builds: the project publishes no binary
# then, so a person holds the whole project.
HOLD_PROJECT = "Hold the whole project with `release: private` instead."


def _fuzz_targets_that_build(proj):
    """The names of the fuzz targets of proj (a loaded facts.Project) that its private_harnesses may not all hold,
    sorted: each one with a published build (facts.Harness.builds).  The cut removes the held fuzz targets and then
    runs the rules of rules.py, and its refusal of "'assets' with every binary withheld" uses this same test."""
    return sorted(h.name for h in proj.harnesses.values() if h.builds())


def check_private_harnesses(tree):
    """schema: each project's `private_harnesses` names harnesses that every reader of the held entries can hold, and
    leaves its project a fuzz target that builds, unless the project is `release: private`.

    The field names the fuzz targets of its project that no public repository may hold while the rest of the project
    publishes, and `oft generate` writes them as `<project>/<harness>` lines to tools/publish/private-harnesses.txt.
    This rule refuses a field that is not a list.  It refuses each name of the list that is one of these five:

    1. A name outside HELD_NAME, or a name of fewer than HELD_NAME_MIN characters.
    2. A name that is a harness of another project (a folder with a harness.yaml, or an entry of that project's
       project.yaml).  The scanners match a held harness by its bare name, so they would also hold back the files of
       the other harness.
    3. A name that the bare form of the match rule (disclosure.held_match) finds, whole or in part, in the name of
       another harness of any project or in the name of any project, its own project included in both.  The scanners
       would also hold back the files of that name, and the cut stops on a kept file that names it ("nothing
       changed").  The bare form matches only where no letter, digit or `_` is next to the name, so `held_target`
       is found in `held_target-v2` and not in `held_target_v2`.
    4. A name whose Rocq module (`<project>.<harness>`, each part by names.ident) is also the module of a kept harness
       of its own project when case is ignored.  A kept harness is a harness of the project (a folder with a
       harness.yaml, or an entry of its project.yaml) that the field does not name.  names.ident writes each
       character outside [A-Za-z0-9_] as `_`, so zlib's held `url_fuzzer` has the module of a kept `URL_FUZZER`,
       `url-fuzzer`, `url.fuzzer` or `url+fuzzer`.  The cut looks for the module of each held fuzz target in every
       kept file (disclosure.needles) and ignores case, so it stops on the Statements.v of that kept harness
       ("nothing changed").  The match rule of 3 does not find these names: it is case-sensitive, and `-`, `.` and
       `+` are not `_` to it.
    5. A name that the cut or a scanner finds in what the release keeps (disclosure.held_name_stops): in the name, the
       entry form, the path or the rendered Rocq module of a fuzz target of any project that no field holds, or in the
       name or the path of any project.  The cut reads them with its own needles of the held entry (its module, case
       folded, and the entry by held_match), and both ossv-binscan --held read them in lower case.  So json keeping
       url-fuzzer (module json.url_fuzzer) or PARSE_CBOR_X, or zlib keeping an entry zlib.Url_Fuzzer, is refused when
       zlib holds url_fuzzer or parse_cbor_x: the cut or the gate would stop every publication on those files, and no
       exceptions row clears a held hit.  Rule 4 is a case of this one.  Rules 2 and 3 also cover the harnesses that a
       field holds.

    A name has at most one of these findings: the first that applies.  The rule also refuses a name given more than
    one time.  And it refuses a project that is not `release: private` and has a fuzz target that builds
    (_fuzz_targets_that_build) when its field holds every such fuzz target, whatever the field does with a fuzz
    target that does not build: the cut then keeps no published binary of the project, and rules.py refuses its
    'assets' ("'assets' with every binary withheld").  The cut holds a `release: private` project back whole, so such
    a project may hold every fuzz target in its field.  A name may come before its harness's files exist.  The
    message of the refusal of a field that holds every fuzz target that builds tells a person to hold the whole
    project (HOLD_PROJECT).  Each other message tells a person to hold such a harness with its whole project
    (HOLD_WHOLE).

    facts.load does not load a project.yaml that the schema refuses, so this rule reads the field of such a file
    from the file itself: the schema finding says what the shape breaks, and this one gives the way out.  Such a
    project has no loaded fuzz target, so the refusal of a field that holds every fuzz target that builds does not
    judge it.  The field given two times makes the file unreadable (yamlio refuses a repeated key), so then the schema
    finding alone speaks.

    disclosure is imported in this function and not at load: disclosure imports this module at load, so an import at
    load is a cycle."""
    from . import disclosure

    pdir = tree.path("projects")
    folders = sorted(n for n in os.listdir(pdir) if os.path.isdir(os.path.join(pdir, n))) \
        if os.path.isdir(pdir) else []
    data = {}
    for name in folders:
        if name in tree.projects:
            data[name] = tree.projects[name].data
            continue
        rel = os.path.join("projects", name, "project.yaml")
        try:
            raw = yamlio.load_file(tree.path(rel)) if os.path.isfile(tree.path(rel)) else None
        except (OSError, yamlio.YamlError):
            continue   # the schema rule names the file (facts.load)
        if isinstance(raw, dict):
            data[name] = raw
    held = {name: d["private_harnesses"] for name, d in data.items() if "private_harnesses" in d}
    if not held:
        return []
    harnesses = {}   # project -> the name of each folder with a harness.yaml and of each entry of its project.yaml
    for name in folders:
        d = os.path.join(pdir, name)
        found = {h for h in os.listdir(d) if h != "bin" and os.path.isfile(os.path.join(d, h, "harness.yaml"))}
        entries = data.get(name, {}).get("harnesses")
        found |= {e["name"] for e in entries if isinstance(e, dict) and isinstance(e.get("name"), str)} \
            if isinstance(entries, list) else set()
        harnesses[name] = found
    # each name in which the scanners could find a held name, as (label, name): the name of each project, and the
    # name of each harness of it
    every_name = [("project %s" % p, p) for p in folders] + \
        [("harness %s/%s" % (p, x), x) for p in folders for x in sorted(harnesses[p])]
    # what the release keeps of each project and of each fuzz target that no field holds, as (label, text): the
    # project's name and path, and the fuzz target's name, entry, path and rendered Rocq module, which its files hold
    held_all = {(p, h) for p, f in held.items() if isinstance(f, list) for h in f if isinstance(h, str)}
    kept_texts = [("project %s" % p, t) for p in folders for t in (p, "projects/%s/" % p)] + \
        [("harness %s/%s" % (p, k), t) for p in folders for k in sorted(harnesses[p]) if (p, k) not in held_all
         for t in (k, "%s/%s" % (p, k), "projects/%s/%s/" % (p, k), names.rocq_harness(tree.namespace, p, k))]
    out = []
    for name, field in sorted(held.items()):
        where = os.path.join("projects", name, "project.yaml")
        if not isinstance(field, list):
            out.append(Finding("schema", where, "private_harnesses is %.50r, not a list of harness names. %s"
                               % (field, HOLD_WHOLE)))
            continue
        listed = []
        for h in field:   # each name one time, in its order: a repeat has a finding of its own (below)
            if not (isinstance(h, str) and h in listed):
                listed.append(h)
        # the Rocq module name (names.ident) in lower case of each harness of the project that the field does not name
        kept = {k: names.ident(k).lower() for k in harnesses[name] if k not in listed}
        for h in listed:
            if not isinstance(h, str) or not HELD_NAME.fullmatch(h):
                why = "which is not of the form %s that every reader of the held entries takes" % HELD_NAME.pattern
            elif len(h) < HELD_NAME_MIN:
                why = ("which has fewer than %d characters: the scanners look for the bare name in every published "
                       "file, and a short name also matches text that does not name the harness" % HELD_NAME_MIN)
            else:
                others = sorted(p for p, hs in harnesses.items() if p != name and h in hs)
                if others:
                    why = ("which is also a harness of %s: the scanners match a held harness by its bare name, so "
                           "they would also hold back the files of that harness" % ", ".join(others))
                else:
                    entry = "%s/%s" % (name, h)
                    # the other two forms of entry match only where its bare name matches too: this is the bare form
                    inside = sorted(label for label, text in every_name
                                    if label != "harness " + entry and disclosure.held_match(text, [entry]))
                    if inside:
                        why = ("which the scanners also find in the name of %s: they match the bare name of a held "
                               "harness wherever no letter, digit or `_` is next to it, so they would also hold back "
                               "the files of that name" % ", ".join(inside))
                    else:
                        module = names.ident(h).lower()
                        twins = sorted("harness %s/%s" % (name, k) for k, ident in kept.items() if ident == module)
                        if twins:
                            why = ("whose Rocq module %s.%s is also the module of %s when case is ignored: the cut "
                                   "looks for the module of each held harness in every kept file and ignores case, so "
                                   "it would stop on the files of that kept harness"
                                   % (names.ident(name), names.ident(h), ", ".join(twins)))
                        else:
                            stops = disclosure.held_name_stops(entry, kept_texts)
                            if not stops:
                                continue
                            why = ("which the cut or the scanners find in the name, the path or the Rocq module of %s: "
                                   "the cut looks for the held entry and its module in every kept file, and the "
                                   "scanners look for the held entry in lower case, so each would stop every "
                                   "publication on the files of that name" % ", ".join(stops))
            out.append(Finding("schema", where, "private_harnesses names %.50r, %s. %s" % (h, why, HOLD_WHOLE)))
        for h in sorted({h for h in field if isinstance(h, str) and field.count(h) > 1}):
            out.append(Finding("schema", where, "private_harnesses names %r more than one time: name each held "
                               "harness one time. %s" % (h, HOLD_WHOLE)))
        proj = tree.projects.get(name)
        built = _fuzz_targets_that_build(proj) if proj and proj.data.get("release") != "private" else []
        if built and all(h in listed for h in built):
            out.append(Finding("schema", where, "private_harnesses holds every fuzz target of %s that publishes a "
                               "build (%s), so the cut would keep no published binary of %s and would stop (\"'assets' "
                               "with every binary withheld\"). %s" % (name, ", ".join(built), name, HOLD_PROJECT)))
    return out


# The directory that only the internal tree has: the cut removes it whole (release_tree.INTERNAL).
PUBLISH_DIR = "tools/publish"
NO_PORT = ("is %s, which only the cut writes: it stands for the port's internal copy of a project with a held fuzz "
           "target. This tree has %s/, so it is not a cut. Name the repository of the port: %s or %s"
           % (schema.NO_PORT_REPOSITORY, PUBLISH_DIR, schema.OSS_VERIFY_REPOSITORY, schema.INTERNAL_PORT_REPOSITORY))


def check_port_none(tree):
    """schema: in a tree that has tools/publish/ (the internal tree), no project.yaml's build.oss_verify.repository
    and no build record's port.repository is `none` (schema.NO_PORT_REPOSITORY).  The cut writes `none` in place of
    the port's internal copy for a project with a held fuzz target, so a tree without tools/publish/ (a release)
    takes it.  In the internal tree these fields name the repository that holds the port.  This rule is in lint, not
    in rules.py, because rules.check also runs inside `oft check`'s views."""
    if not os.path.isdir(tree.path(PUBLISH_DIR)):
        return []
    out = []
    for name, proj in sorted(tree.projects.items()):
        if (facts.port(proj) or {}).get("repository") == schema.NO_PORT_REPOSITORY:
            out.append(Finding("schema", "projects/%s/project.yaml" % name, "build.oss_verify.repository " + NO_PORT))
    for _unit, rel in sorted(tree.records_at.items()):
        r = _read_record(tree, rel)
        if r is not None and _mapping(r.get("port")).get("repository") == schema.NO_PORT_REPOSITORY:
            out.append(Finding("schema", rel, "port.repository " + NO_PORT))
    return out


def _text(tree, rel):
    """The text of the regular file at rel of at most its cap, or None."""
    try:
        return facts.read_bounded(tree.path(rel), facts.file_cap(rel)).decode("utf-8", "replace")
    except facts.BoundedFileError:
        return None


def check_model(tree, public):
    """model (with --release): the checker image's model is the one release.yaml names.  The cut of the model at
    semantics.commit (the files toolchain/lps-core.paths lists, or without it package/), as public reads it, hashes
    to the LPS_TREE_SHA256 toolchain/checker.Dockerfile pins, and model.yaml requires that hash of the commit."""
    sem = (tree.release or {}).get("semantics")
    if not sem:
        return []
    pins = MODEL_PIN.findall(_text(tree, DOCKERFILE) or "")
    if len(pins) != 1 or not re.fullmatch(r"[0-9a-f]{64}", pins[0].strip()):
        return [Finding("model", DOCKERFILE, "no ARG LPS_TREE_SHA256=<sha256>: the checker image pins the hash of the "
                        "model's files" if not pins else "ARG LPS_TREE_SHA256 is not one sha256: the checker image "
                        "pins one hash of the model's files")]
    pin = pins[0].strip()
    specs = [l for l in (_text(tree, LPS_PATHS) or "").splitlines() if l.strip() and not l.startswith("#")] or None
    try:
        got = public.cut_sha256(sem["repository"], sem["commit"], specs)
        want, line = public.required_tree(sem["repository"], sem["commit"])
    except model.ModelError as e:
        return [Finding("model", "release.yaml", "could not read the model: %s" % e)]
    if got == pin == want:
        return []
    return [Finding("model", DOCKERFILE, "LPS_TREE_SHA256 is %s, the %s cut of semantics.commit %s hashes to %s, and "
                    "tools/oft/model.yaml requires %s (the %s cut) of that commit: the three are one hash"
                    % (pin, LPS_PATHS if specs else model.PACKAGE, sem["commit"], got, want, line))]


def check_pins(tree, public):
    """pins (with --release): each commit the release pins in another repository is on a branch or tag of that
    repository, as public reads it: release.yaml's semantics.commit in the model's, and the static-asan commits of the
    build records (static_asan_commits) in theorem-labs/static-asan."""
    out = []

    def on_a_ref(url, commit, where, what):
        try:
            if not public.containing(url, commit):
                out.append(Finding("pins", where, "%s is on no branch or tag of %s" % (what, url)))
        except model.ModelError as e:
            out.append(Finding("pins", where, "could not read %s" % e))

    sem = (tree.release or {}).get("semantics")
    if sem:
        on_a_ref(sem["repository"], sem["commit"], "release.yaml", "semantics.commit %s" % sem["commit"])
    for what, named in zip(("toolchain.static_asan.commit", "fallback.static_asan.public_commit"),
                           static_asan_commits(tree)):
        for c, wheres in sorted(named.items()):
            on_a_ref(STATIC_ASAN, c, wheres[0], "%s %s, which %d build record(s) name," % (what, c, len(wheres)))
    return out


def check_free_text(tree):
    """free-text: a free-text field the rendering has no place for would still be
    published, as YAML; refuse it."""
    out = []
    pb = facts.PHRASEBOOK
    for proj in tree.projects.values():
        d = proj.data
        t = (d.get("reason_args") or {}).get("text")
        if t is not None and d["status"] != "available":
            shape = pb["projects"][d["status"]]["reasons"].get(d.get("reason"), "")
            if "{text}" not in shape:
                out.append(Finding("free-text", proj.dir, "reason_args.text is not used by the sentence for %s/%s"
                                   % (d["status"], d.get("reason"))))
        for e in proj.entries():
            t = (e.get("reason_args") or {}).get("text")
            if t is not None and "{text}" not in pb["harnesses"].get(e.get("reason", ""), ""):
                out.append(Finding("free-text", proj.dir, "%s: reason_args.text is not used by its sentence" % e["name"]))
    return out


# --------------------------------------------------------------- exceptions

EXCEPTIONS = "tools/oft/lint-exceptions.yaml"
# The entry kinds (`rule`) apply_exceptions reads; apply_pending reads the `licence-pending` ones.  The lint job
# judges a pull request's tree with the base's tools, so a pull request that adds the lint of a new kind together with
# its entries must pass a lint that does not know that kind.
EXCEPTION_RULES = ("proofs", "private-data")


def load_exceptions(root):
    p = os.path.join(root, EXCEPTIONS)
    if not os.path.isfile(p):
        return []
    data = yamlio.load_file(p)
    return data.get("exceptions") or []


# A licence-pending entry of lint-exceptions.yaml: a fuzz target whose proof files' licence lines its own series applies
# later (apply_pending), written as the file's other entries are:
#   - unit: <project>/<fuzz target>
#     rule: licence-pending
#     due: 'YYYY-MM-DD'
#     series: pending            (or '#<number>', the internal pull request of the unit's series)
#     reason: its licence lines are applied in its own series
# An entry whose series is '#<number>' may name a unit that has no licence finding yet, while its due date has not
# passed: the pull request it names is the one that brings the unit's files, and the findings arrive with them.
# After the due date that entry is a finding, as any other entry is.
PENDING = "licence-pending"
_PENDING_KEYS = {"unit", "rule", "due", "series", "reason"}
_UNIT = re.compile(r"[A-Za-z0-9][A-Za-z0-9._+-]*/[A-Za-z0-9][A-Za-z0-9._+-]*")
_SERIES = re.compile(r"pending|#[1-9][0-9]*")
_DUE = re.compile(r"[0-9]{4}-[0-9]{2}-[0-9]{2}")


def utc_today():
    """Today's date in UTC: the date a licence-pending entry's due date is compared with."""
    return datetime.datetime.now(datetime.timezone.utc).date()


def _due(text):
    """The date a licence-pending entry's due names, written YYYY-MM-DD, or None."""
    if not isinstance(text, str) or _DUE.fullmatch(text) is None:
        return None
    try:
        return datetime.date.fromisoformat(text)
    except ValueError:
        return None


def finding_unit(f):
    """The fuzz target, "<project>/<harness>", of the file a finding names, or None."""
    return layout.unit_of(f.where.rsplit(":", 1)[0])


def pending_by_unit(pending):
    """[(fuzz target, how many of the pending findings name its files)], sorted by fuzz target: what `oft lint` prints
    of the pending findings unless it is asked for each one (--list-pending)."""
    return sorted(collections.Counter(finding_unit(f) for f in pending).items())


# the message of an expired licence-pending entry (apply_pending)
_EXPIRED = re.compile(r"unit \S+: its licence series \S+ was due \S+")


def is_expired(f):
    """Whether finding f is an expired licence-pending entry's."""
    return f.rule == "paths" and f.where == EXCEPTIONS and _EXPIRED.fullmatch(f.msg) is not None


def base_pending_entries(root):
    """The licence-pending entries of the base commit, {unit: entry}, for apply_pending: root is a git checkout of
    that commit (pr.yml's sparse one serves), and its HEAD's tools/oft/lint-exceptions.yaml is read through git, not
    from the checkout's files.  None of them when that file cannot be read there, so every entry counts as new."""
    r = subprocess.run(["git", "-C", root, "show", "HEAD:" + EXCEPTIONS], capture_output=True)
    if r.returncode:
        return {}
    data = yamlio.load(r.stdout.decode("utf-8"), EXCEPTIONS)
    entries = (data.get("exceptions") if isinstance(data, dict) else None) or []
    return {e.get("unit"): e for e in entries if isinstance(e, dict) and e.get("rule") == PENDING}


def apply_pending(found, entries, scope=None, today=None, pending=None, base=None, present=None, changed=None,
                  expired=None, unread=frozenset()):
    """The licence findings of a fuzz target that a licence-pending entry of lint-exceptions.yaml lists do not fail:
    they go to pending, a list, when one is given, and not to the result.  The entry stays until the series that
    applies the unit's licence lines removes it, and the list only shrinks.  An entry is itself a finding:
      - when it is not exact: other keys than unit, rule, due, series and reason, a unit that is not
        <project>/<fuzz target>, a due date that is not a date written YYYY-MM-DD, a series that is neither `pending`
        nor #<number>, an empty reason, or a second entry for its unit (its unit's findings then fail);
      - after its due date (today: by default utc_today()), so nothing stays pending without a new decision; but it
        fails only a lint with no change to judge (changed None: a local or a release run), a change that touches
        its unit (layout.unit_of, in either layout), and a change of lint-exceptions.yaml that adds or edits this
        entry (compared with base; without base, any change of the file), and goes to expired, a list, when one is
        given, for any other change, which it does not fail: a series that deletes its own entry fails on no other;
      - when its unit has no licence finding, but only when the per-file rules read every file (scope None), the
        unit has a Rocq file in the tree (present: the units that have one; None: every unit), so an entry may wait
        for a unit whose proofs have not come yet, and none of the unit's files is left out of a sparse checkout
        (unread: those units, left_out); and not while an entry whose series is the pull request that
        brings the unit's files ('#<number>') is within its due date, since those findings arrive with that pull
        request.  After the due date the rule applies to it as it does to any other entry;
      - with base (base_pending_entries: the base commit's entries, in a pull request's lint), when the base does not
        list its unit and the pull request changes a file of a fuzz target's proofs folder (changed): a proof pull
        request adds no entry, for any unit; a tools pull request adds one, and review judges it."""
    today = utc_today() if today is None else today
    units, out = {}, []
    for e in entries:
        if (set(e) != _PENDING_KEYS or not all(isinstance(e[k], str) and e[k] for k in _PENDING_KEYS)
                or _UNIT.fullmatch(e["unit"]) is None or _SERIES.fullmatch(e["series"]) is None
                or _due(e["due"]) is None or e["unit"] in units):
            out.append(Finding("paths", EXCEPTIONS, "an exception for licence-pending %s must have exactly unit "
                               "(<project>/<fuzz target>), rule, due (YYYY-MM-DD), series (pending or #<number>) and "
                               "reason, once per unit" % e.get("unit")))
            continue
        units[e["unit"]] = e
    kept, with_licence = [], set()
    for f in found:
        unit = finding_unit(f) if f.rule == "licence" else None
        if unit is not None:
            with_licence.add(unit)
            if unit in units:
                if pending is not None:
                    pending.append(f)
                continue
        kept.append(f)
    proof_change = base is not None and any(PROOFS_FOLDER.match(rel) for rel in changed or ())
    if changed is None:
        touched = None
    else:
        touched = {layout.unit_of(rel) for rel in changed}
        if EXCEPTIONS in changed:
            # the entries the change adds or edits; with no base to compare with, all of them
            touched = None if base is None else touched | {u for u, e in units.items() if base.get(u) != e}
    for unit, e in sorted(units.items()):
        late = _due(e["due"]) < today
        if late:
            finding = Finding("paths", EXCEPTIONS, "unit %s: its licence series %s was due %s"
                              % (unit, e["series"], e["due"]))
            if touched is None or unit in touched:
                kept.append(finding)
            elif expired is not None:
                expired.append(finding)
        # an entry whose series is the pull request that brings the unit's files waits for it until its due date
        waiting = e["series"] != "pending" and not late
        if (scope is None and unit not in with_licence and (present is None or unit in present) and not waiting
                and unit not in unread):
            kept.append(Finding("paths", EXCEPTIONS, "unit %s has no licence finding: its licence series %s removes "
                                "its licence-pending entry" % (unit, e["series"])))
        if proof_change and unit not in base:
            kept.append(Finding("paths", EXCEPTIONS, "unit %s: a licence-pending entry that the base does not have, "
                                "in a pull request that changes proof files: a tools pull request adds an entry, and "
                                "review judges it" % unit))
    return kept + out


def apply_exceptions(findings, exceptions, own, scope=None, unread=frozenset()):
    """A private-data finding in an upstream copy (a host path in its authors' comments, say) or in a port record's
    copied project.yaml (the project's own address, say), or an e-mail address in any other file of a port record's
    copy of the port's project files (port/projects/<project>/: the enrollment author's copyright line, say), or the
    one shape a directory no release carries still reports (internal_only: the stand-in key or token in the tests of
    the stream's own secret scanner), may be
    cleared by a reviewed entry naming (path, rule, key) and how often; an OSS Verify target's source (under one of
    `own`, oss_verify_sources) is not an upstream copy.  A host path or a URL's user information in a copied build
    script stays a finding.

    A `proofs` finding of a notation token may be cleared only by an entry that names it exactly: its path, its
    line, its message and its key (the token's string literal, as the proof has it), with count 1.  A `proofs` entry
    without those, or with another count, is itself a finding, and so is one that matches no finding (the token moved
    or left that line).

    Nothing else can be cleared.  An entry left unused is a finding, unless its path is outside `scope` (when the
    per-file rules read only some files: the paths that differ from the base, deleted ones among them) or among
    `unread` (the files a sparse checkout leaves out, left_out: no rule read them).
    An entry whose rule is not one of EXCEPTION_RULES (a later lint's kind, which may have no path) clears nothing and
    is not reported; a `licence-pending` entry is apply_pending's.

    An entry names its file in either layout and clears the finding on that file in either, and `scope` names a file
    in either (layout.canonical): the entries stay in the old layout's form, since the base's lint judges a pull
    request's tree and matches them by path, and keep clearing their findings once the tree moves.  A message names
    an entry as it is written."""
    budget, exact, out = {}, {}, []
    for e in exceptions:
        if e.get("rule") not in EXCEPTION_RULES:
            continue
        if e.get("rule") == "proofs":
            if (set(e) != {"path", "rule", "line", "message", "key", "count", "reason"}
                    or type(e["count"]) is not int or e["count"] != 1 or type(e["line"]) is not int
                    or not all(isinstance(e[k], str) and e[k] for k in ("path", "message", "key", "reason"))
                    or ("%s:%d" % (layout.canonical(e["path"]), e["line"]), e["message"], e["key"]) in exact):
                out.append(Finding("paths", EXCEPTIONS, "an exception for proofs %s must name exactly its path, line, "
                                   "message and key, with count 1 and a reason, once" % e.get("path")))
                continue
            exact[("%s:%d" % (layout.canonical(e["path"]), e["line"]), e["message"], e["key"])] = e
        else:
            budget[(layout.canonical(e["path"]), e["rule"], e["key"])] = e
    used = {}
    kept = []
    for f in findings:
        path = f.where.rsplit(":", 1)[0]
        at = layout.canonical(path) + f.where[len(path):]
        if f.rule == "proofs" and f.key is not None and (at, f.msg, f.key) in exact \
                and (at, f.msg, f.key) not in used:
            used[(at, f.msg, f.key)] = 1
            continue
        key = (layout.canonical(path), f.rule, f.key)
        clearable = f.rule == "private-data" and (PORT_PROJECT_YAML.match(path)
                                                   or (PORT_PROJECT_FILE.match(path)
                                                       and f.msg == "an e-mail address")
                                                   or internal_only(path)
                                                   or (verbatim(path) and not oss_verify_source(own, path)))
        if clearable and key in budget and used.get(key, 0) < budget[key]["count"]:
            used[key] = used.get(key, 0) + 1
            continue
        kept.append(f)
    scope = None if scope is None else {layout.canonical(rel) for rel in scope}
    unread = {layout.canonical(rel) for rel in unread}
    for key, e in budget.items():
        if used.get(key, 0) < e["count"] and (scope is None or key[0] in scope) and key[0] not in unread:
            kept.append(Finding("paths", EXCEPTIONS, "an exception for %s %s that is not used %d time(s)"
                                % (e["rule"], e["path"], e["count"])))
    for key, e in exact.items():
        path = layout.canonical(e["path"])
        if key not in used and (scope is None or path in scope) and path not in unread:
            kept.append(Finding("paths", EXCEPTIONS, "an exception for proofs %s:%d that is not used 1 time(s)"
                                % (e["path"], e["line"])))
    return kept + out


# the finding for a file that still names the default namespace in a tree whose release.yaml renames it (OSSV-162): a
# lane that keeps generating files with the old name gets told which file and the command that fixes it
OLD_NAMESPACE = ("names the Rocq namespace OssFuzzTheorems, which this release renames to %s: run ./oft "
                 "rename-namespace, or ./oft port-branch for a branch")


def scan_namespace(text, rel, tree):
    """paths.  In a tree whose release.yaml names another namespace than names.NAMESPACE_DEFAULT, a file that holds
    the default one, outside the files the rename leaves alone (nsrename.EXEMPT) and the shared generated files."""
    if (tree.namespace == names.NAMESPACE_DEFAULT or names.NAMESPACE_DEFAULT not in text or nsrename.exempt(rel)
            or paths.is_shared(rel)):
        return []
    return [Finding("paths", rel, OLD_NAMESPACE % tree.namespace)]


# --------------------------------------------------------------------- run

def scan_file(root, rel, tree, known, own, targets=None, contracts=None, third_party=None, private=None):
    """(the findings of the per-file text rules on rel, whether it is a text file, whether it is a proof file that
    carries no licence line: bare_licence, which no rule reads and a whole-tree run counts).  A binary file, or one
    that is not a regular file of at most its cap, is not read.  known: the links the facts record (fact_urls); own:
    the source directories of the fuzz targets OSS Verify builds (oss_verify_sources); tree: the facts, which say
    which project.yaml and build records may name the port's internal copy (_internal_port_lines) and which lines may
    name a private project's own library (_own_library); targets: the fuzz targets whose build record lists every
    licence text that a file made from the upstream proofs ships with (anthropic_targets), or None to leave the
    records unchecked (scan_licence); contracts: the symbol facts of the fuzz targets whose contract files are read
    (contract_symbols), or None to leave the contract files unchecked (scan_contract); third_party: the rows of the
    table of third-party proof files (load_third_party), or None for none; private: the projects that are
    `release: private`, each with whether it has a NOTICE (private_projects, scan_licence).  A text of PINNED_VERBATIM
    is held to its pin whether it is read as text or not (scan_pinned)."""
    path = os.path.join(root, rel)
    pinned = scan_pinned(path, rel)
    text = read_text(path, facts.file_cap(rel))
    if text is None:
        # Rocq compiles a file that holds a NUL byte (in a comment, say), so a Rocq file the proof rules cannot read is
        # refused, not skipped
        if proof_rocq(rel) or rel.endswith(".v") and rel.startswith("projects/"):
            return [Finding("proofs", rel, "a Rocq file that is not read as text (it holds a NUL byte, or it is not a "
                                           "regular file of at most its cap) is not allowed")], False, False
        return pinned, False, False
    out = pinned + scan_namespace(text, rel, tree)
    src = verbatim(rel, text)
    inside = internal_only(rel)
    own_source = oss_verify_source(own, rel)
    port_text = port_record(rel)
    proof_v = proof_rocq(rel)
    # In a proof, a string literal holds encoded data whose random byte runs can take the shape of an address or a
    # link: the e-mail and link checks read the file with string literals blanked (comments are still read).
    blanked = None
    if proof_v and (EMAIL.search(text) or URL.search(text) or GHCR.search(text)):
        blanked = rocq.strip(text, comments=False)
    # A third-party proof file's row of THIRD_PARTY decides, in one step, whether the file is under the row's licence
    # and which of its lines the private-data rule reads (_row_licence).  Every other rule reads it as any proof's.
    row = third_party.get(layout.canonical(rel)) if third_party and proof_v else None
    row_found, shapes_text, email_text, licence = _row_licence(root, rel, path, text, blanked, row)
    library = _own_library(tree, rel, text)
    out += scan_shapes(shapes_text, rel, source=src and not own_source, internal=inside, email_text=email_text,
                       internal_port_lines=_internal_port_lines(tree, rel, text),
                       host_paths=not rel.startswith(CHANGE_LEDGERS), own_library=library)
    # the link rule judges a link by what a reader's browser would open; no reader opens this directory's text
    # (internal_only), and its lock file pins every package by its URL
    if (not src or own_source) and not inside:
        out += scan_links(text if blanked is None else blanked, rel, known,
                          strict=link_strict(rel) and not port_text and not own_source, own_library=library)
    if PORT_MANIFEST.match(rel):
        out += scan_port_manifest(text, rel)
    bare = False
    if proof_v:
        out += scan_proof(text, rel) + row_found
        if licence is not _REFUSED:
            out += scan_licence(text, rel, targets, licence, private)
        # a bare file of a private project with a NOTICE is a licence finding (scan_licence), not a count (bare_licence)
        unit = layout.unit_of(rel)
        bare = bare_licence(text) and not (private or {}).get(unit.split("/")[0] if unit else None)
        # a build record's copy of someone else's text ships as it is and describes the donor's image, not this
        # fuzz target's: the recipe slice and the licence texts (`src`), and the port's own files (`port_text`)
        if not src and not port_text:
            out += scan_read_from(text, rel, tree)
        builds = None if contracts is None or not CONTRACT_FILE.match(rel) else contracts.get(unit)
        if builds:
            out += scan_contract(text, rel, builds)
    elif rel.startswith("projects/") and rel.endswith(".v"):
        out += scan_project_rocq(text, rel)
    if not proof_v and wall_clock_scanned(rel):
        out += scan_wall_clock(text, rel)
    return out, True, bare


_FORKED = None  # the function of forked_map in one of its workers, set by _forked_init

# Memory.  Each process of lint watches its own resident memory, and a run stops (ResourceStop) when one holds more
# than --max-rss-gib (run's max_rss_gib), so that lint never takes the memory its neighbours run in; the default
# number of processes is what the available memory holds at WORKER_GIB each.  WORKER_GIB is measured on a whole lint
# of the line of 30 October (223,000 files): a text-rule worker peaks at 0.25 GiB, so 1 GiB leaves room.
MAX_RSS_GIB = 4
WORKER_GIB = 1
MAX_RSS_EXIT = 3   # the exit status of a process that passes its bound, and of `oft lint` when the run stops so
WATCH_SECONDS = 0.2
_MAX_RSS = None   # bytes: the bound of each process of the current run (run sets it; forked workers inherit it)


class ResourceStop(Exception):
    """lint stopped with no verdict: one of its processes passed --max-rss-gib, or a worker process ended without its
    result (the system's out-of-memory killer, say)."""


def rss():
    """This process's resident memory, in bytes (VmRSS of /proc/self/status), or 0 where the system has none."""
    try:
        with open("/proc/self/status") as f:
            for line in f:
                if line.startswith("VmRSS:"):
                    return int(line.split()[1]) * 1024
    except OSError:
        pass
    return 0


def _over(held, limit):
    return "process %d holds %.2f GiB, over --max-rss-gib %.4g" % (os.getpid(), held / 2 ** 30, limit / 2 ** 30)


def check_rss():
    """In lint's own process: stop the run (ResourceStop) when the process holds more than its bound."""
    held = rss()
    if _MAX_RSS is not None and held > _MAX_RSS:
        raise ResourceStop("oft lint: %s; the run stops" % _over(held, _MAX_RSS))


def _watch(limit):
    """In a worker process: a daemon thread that reads the process's resident memory every WATCH_SECONDS and, above
    limit (bytes), says so on stderr and ends the process at once with exit status MAX_RSS_EXIT; its parent then stops
    the other workers and the run (forked_map)."""
    def watch():
        while True:
            held = rss()
            if held > limit:
                os.write(2, ("oft lint: %s: it stops\n" % _over(held, limit)).encode())
                os._exit(MAX_RSS_EXIT)
            time.sleep(WATCH_SECONDS)
    threading.Thread(target=watch, daemon=True).start()


def _forked_init(fn, limit):
    global _FORKED
    _FORKED = fn
    if limit is not None:
        _watch(limit)


def _forked_one(item):
    return _FORKED(item)


# A cgroup's memory.current counts the page cache, which the kernel hands back rather than failing an allocation,
# so memory.max less memory.current is not what the processes in it may take: a pod that has just checked this
# repository out holds nearly its whole limit in cache and so reads as having almost none left (OSSV-470: 0.68 GiB
# of a 16 GiB pod, one process on 16 CPUs, 4,335 s against 758 s).  RECLAIMABLE is what counts as free again:
# inactive_file, the term Kubernetes and cadvisor leave out of a cgroup's working set, so the figure here is the one
# the platform itself judges the pod by; less the shmem in it (tmpfs, /dev/shm), which lies on the same lists but
# which no swap can reclaim.  active_file and slab_reclaimable are reclaimable too and are deliberately left in:
# they are the cache this lint is reading and the directory entries it is walking, and a pool sized over what its
# cgroup holds is killed, which is worse than slow.
#
# memory.current and memory.stat are two files, so two moments, and nothing makes them agree.  Crediting cache the
# cgroup took on after memory.current was read counts the same bytes twice: 8 GiB of anonymous memory that never
# moves and 8 GiB of cache arriving between the two reads read as a whole 16 GiB limit free, twice the pool the
# memory supports, which is the direction that ends in a killed worker (the first review of pull request 2579).
# So memory.stat is read twice, on either side of memory.current, and the credit is the SMALLER of the two, cut
# again to the chosen memory.current less the larger anon either reading saw.  Cache that moves once cannot then
# be credited against a total read without it; cache that moves repeatedly can still leave the bounded excess
# the paragraph below names.
#
# What this deliberately does not do is rebuild memory.current out of the fields of memory.stat.  Two reviews of
# that pull request each found a field such a sum leaves out -- `kernel`, which no kernel printed before Linux
# 5.19, and `sock`, which is not inside `kernel` at all -- and each omission reads as memory that is free when it
# is held: 12 processes where 8 fit, both times.  A kernel may add another field tomorrow.  memory.current is the
# one total the kernel itself keeps, so it is the only total used here.
#
# A reading that is not there subtracts nothing -- the low side, and never silently none at all: memory_reading
# says which reading was missing and default_jobs prints it.
# the fields a credit needs: the cache a cgroup can hand back by its own accounting, and the anonymous memory
# that bounds it.  Every one is needed, since a field that is not there would otherwise be read as a zero.
RECLAIMABLE = ("inactive_file", "shmem", "file", "anon")
MemoryReading = collections.namedtuple("MemoryReading", "available why")


def _gib(n):
    return "%.2f GiB" % (n / 2 ** 30)


def _reclaimable(stat):
    """One reading of a cgroup's memory.stat (at path stat): (the cache the kernel can hand back -- inactive_file,
    no more than the file total beside it, less the shmem no swap can reclaim -- the anonymous memory it says is
    held, which no credit may be taken out of, and how both were read).  (None, None, why) where the file, or a
    field the credit needs, is not there."""
    held = {}
    try:
        with open(stat) as f:
            for line in f:
                field, _, value = line.partition(" ")
                try:
                    held[field] = int(value)
                except ValueError:
                    pass
    except OSError:
        return None, None, "no memory.stat beside it"
    absent = [field for field in RECLAIMABLE if field not in held]
    if absent:
        return None, None, "its memory.stat has no " + " and no ".join(absent)
    return (max(0, min(held["inactive_file"], held["file"]) - held["shmem"]), held["anon"],
            "inactive_file %s of file %s, less shmem %s, beside anon %s"
            % (_gib(held["inactive_file"]), _gib(held["file"]), _gib(held["shmem"]), _gib(held["anon"])))


def memory_reading(proc="/proc", cgroup="/sys/fs/cgroup"):
    """What this process and its workers may take, and where the figure came from: MemoryReading(available, why).
    available is bytes: MemAvailable of proc/meminfo, and no more than the narrowest cgroup (version 2) that holds
    this process allows, at any level -- its memory.max, less its memory.current, plus the cache the kernel can
    hand back (RECLAIMABLE).  A level with a readable finite memory.max and a first memory.current is read five
    times -- memory.stat, memory.max, memory.current, memory.stat, memory.current -- taking the total at the
    larger of its two readings and the cache at the smaller of its two; a level without a usable finite limit or
    first total is skipped before the second stat and current reads.
    available is None when, and only when, proc/meminfo has no MemAvailable.  why is one line, naming MemAvailable
    and the readings of the one cgroup that bound the answer -- not of every level looked at -- and naming a
    reading that was not there in place of the figure it would have given."""
    try:
        with open(os.path.join(proc, "meminfo")) as f:
            avail = next(int(line.split()[1]) * 1024 for line in f if line.startswith("MemAvailable:"))
    except (OSError, StopIteration, ValueError):
        return MemoryReading(None, "%s has no MemAvailable, so how much memory there is is unknown"
                                   % os.path.join(proc, "meminfo"))
    host = "MemAvailable %s" % _gib(avail)
    try:
        with open(os.path.join(proc, "self", "cgroup")) as f:
            parts = [p for p in next(line for line in f if line.startswith("0::"))[3:].strip().split("/") if p]
    except (OSError, StopIteration):
        return MemoryReading(avail, "%s; no cgroup v2 line in %s"
                                    % (host, os.path.join(proc, "self", "cgroup")))
    capped = []
    for i in range(len(parts), -1, -1):
        where = os.path.join(cgroup, *parts[:i])
        before, anon_before, how_before = _reclaimable(os.path.join(where, "memory.stat"))
        try:
            with open(os.path.join(where, "memory.max")) as f:
                text = f.read().strip()
            with open(os.path.join(where, "memory.current")) as f:
                first = int(f.read())
            limit = None if text == "max" else int(text)
        except (OSError, ValueError):
            continue
        if limit is None:
            continue
        after, anon_after, how_after = _reclaimable(os.path.join(where, "memory.stat"))
        try:
            with open(os.path.join(where, "memory.current")) as f:
                current, again = max(first, int(f.read())), True
        except (OSError, ValueError):
            current, again = first, False
        # Each figure at its least favourable reading, because no two of these files can be read at one moment:
        # the five readings of a level run memory.stat, memory.max, memory.current, memory.stat, memory.current,
        # and the total is taken at the larger of its two and the cache at the smaller of its two.  A cgroup that
        # moves once while they are made cannot then have cache credited against a total that was read without
        # it, in either direction.  The credit is never more than the total, since nothing can be handed back
        # that is not held, and never more than what is left of the total once the anonymous memory either
        # reading saw is set aside, since none of that is cache whatever moved when.  A total that could not be
        # read a second time credits nothing, rather than falling back to the one reading this was built to stop
        # trusting alone.
        #
        # What this is not: a guarantee.  Measured over every interleaving of a family of readings, a cgroup
        # that moves once or twice while the five are made never comes out above what it holds; one that moves
        # three times or more can, by no more than the cache that moved (the fifth review of pull request 2579,
        # 5.7 million readings, worst excess 7 GiB on a 16 GiB limit).  The alternative to a bounded credit is
        # no credit, which is the 5.7x this exists to remove.  No clamp to the limit sits under any of it, and
        # no sum of memory.stat's own fields stands in for memory.current (the comment above).
        free = (None if before is None or after is None or not again else
                max(0, min(before, after, current - max(anon_before, anon_after))))
        # A cgroup over its limit may still have cache to hand back, so this floors the figure at none rather
        # than reading a total above the limit as a debt: it is the arithmetic, not a claim that there is nothing.
        here = max(0, limit - current + (free or 0))
        capped.append((here, "cgroup /%s memory.max %s less memory.current %s plus reclaimable %s (%s) = %s"
                             % ("/".join(parts[:i]), _gib(limit), _gib(current),
                                "none" if free is None else _gib(free),
                                "its memory.current could not be read a second time" if not again else
                                how_before if how_before == how_after else
                                "%s before memory.current and %s after it" % (how_before, how_after), _gib(here))))
    if not capped:
        return MemoryReading(avail, "%s; no cgroup memory limit on %s or above it"
                                    % (host, os.path.join(cgroup, *parts)))
    here, why = min(capped, key=lambda cap: cap[0])
    return MemoryReading(min(avail, here), "%s; %s" % (why, host))


def default_jobs(explain=False, proc="/proc", cgroup="/sys/fs/cgroup"):
    """The default number of processes of forked_map: the CPUs this process may run on (facts.cpus),
    but no more than the available memory (memory_reading) holds at WORKER_GIB each, and at least 1.
    With explain, one line on stderr: the number, the CPUs, the memory it was sized from and memory_reading's
    account of where that came from -- MemAvailable and the one cgroup that bound it -- so that a run on one
    process says whether the machine is small or the reading of it was."""
    cpus, reading = facts.cpus(), memory_reading(proc, cgroup)
    avail = reading.available
    jobs = cpus if avail is None else max(1, min(cpus, avail // int(WORKER_GIB * 2 ** 30)))
    if explain:
        print("oft lint: %d process(es) for the per-file rules: %d CPU(s), %s available at %g GiB each; %s"
              % (jobs, cpus, "unknown" if avail is None else _gib(avail), WORKER_GIB, reading.why), file=sys.stderr)
    return jobs


def forked_map(fn, items, jobs, chunksize=16):
    """[fn(item) for item in items], on up to jobs processes, each taking chunksize items at a time (small chunks: a
    file runs from a few bytes to megabytes).  The workers are forked from this process, so each starts with fn and
    what it reads as they are here, never pickled; the results come back in the order of items, so the result is the
    same as one process's.  Each worker watches its own memory (_watch).  A worker that dies (past its bound, or ended
    by the out-of-memory killer) stops the others and fails the run (ResourceStop) instead of hanging it."""
    if jobs <= 1 or len(items) < 2 or "fork" not in multiprocessing.get_all_start_methods():
        return [fn(item) for item in items]
    try:
        with concurrent.futures.ProcessPoolExecutor(min(jobs, len(items)),
                                                    mp_context=multiprocessing.get_context("fork"),
                                                    initializer=_forked_init, initargs=(fn, _MAX_RSS)) as pool:
            return list(pool.map(_forked_one, items, chunksize=chunksize))
    except concurrent.futures.process.BrokenProcessPool as e:
        raise ResourceStop("oft lint: a worker process ended without its result (past --max-rss-gib, as it says "
                           "above, or ended by the system): the run stops") from e


def scan_files(root, tree, known, own, files, jobs, targets=None, contracts=None, third_party=None, private=None):
    """scan_file for each of files, in their order, on up to jobs processes (forked_map), each starting with the tree
    loaded here."""
    return forked_map(lambda rel: scan_file(root, rel, tree, known, own, targets, contracts, third_party, private),
                      files, jobs)


class ChangedOnlyError(Exception):
    """--changed-only cannot say which files differ from its base: lint stops rather than read too few."""


def changed_since(root, base):
    """The paths that differ from commit `base`: changed, added, renamed or deleted since it, staged or not, and the
    untracked files .gitignore does not exclude.  root must be the top of a git checkout: git names every path from
    there, and walk names them from root.  base must name a commit: a word that names a path instead would compare
    the index with the work tree, an empty change after a commit."""
    top = subprocess.run(["git", "-C", root, "rev-parse", "--show-toplevel"], capture_output=True)
    if top.returncode != 0 or os.path.realpath(top.stdout.decode().rstrip("\n")) != os.path.realpath(root):
        raise ChangedOnlyError("%s is not the top of a git checkout: git names the files that differ from %s "
                               "relative to the top" % (root, base))
    commit = subprocess.run(["git", "-C", root, "rev-parse", "--verify", "--quiet", base + "^{commit}"],
                            capture_output=True) if not base.startswith("-") else None
    if commit is None or commit.returncode != 0:
        raise ChangedOnlyError("%r names no commit of %s" % (base, root))
    diff = subprocess.run(["git", "-C", root, "diff", "--name-only", "--no-renames", "-z",
                           commit.stdout.decode().strip(), "--"],
                          stdout=subprocess.PIPE, check=True).stdout.decode().split("\0")
    new = subprocess.run(["git", "-C", root, "ls-files", "-z", "--others", "--exclude-standard", "--"],
                         stdout=subprocess.PIPE, check=True).stdout.decode().split("\0")
    return {p for p in diff + new if p}


def read_by_every_verdict(rel):
    """Whether a change to rel can change the per-file rules' verdict on another file.  Four files are read by every
    verdict: a project's project.yaml and a harness's harness.yaml (facts), a finding's finding.yaml, whose links
    fact_urls records and whose state decides which project.yaml and build records may name the port's internal copy
    (_internal_port_lines, as a project.yaml's private_harnesses and release do), and lint-exceptions.yaml, whose
    entries clear findings in other files (an entry removed there leaves a finding in a file that did not change).  A
    build record decides the licence rule on its own fuzz target's proof files (anthropic_targets), a project's NOTICE
    (PROJECT_NOTICE) the licence rule on its project's proof files (private_projects), the table of third-party proof
    files (THIRD_PARTY) the licence and private-data rules on each file a row names (load_third_party), a licence text
    lint pins (PINNED_VERBATIM), added or removed, the licence rule on each row's file under that licence
    (scan_third_party_text), and a symbol fact (which paths.py classes as facts) the contract-literals rule on its fuzz
    target's contract files (contract_symbols).  The set is wider on purpose, a margin, so that it does not lose a file
    a later rule reads: every file paths.py classes as facts, every build record (which facts.load reads too, and which
    re-reads the whole tree rather than only its fuzz target's files), and every .gitattributes, which changes the
    bytes git checks out for a file whose blob did not change (line ends, encoding).  CHANGELOG.md is the one fact left
    out: no rule reads it but as a file of its own (fact_urls reads projects, harnesses and findings, and facts.load
    does not parse it), so a change to it alone has the per-file rules read that one file."""
    return (rel in (EXCEPTIONS, THIRD_PARTY) or rel in PINNED_VERBATIM or os.path.basename(rel) == ".gitattributes"
            or (rel != "CHANGELOG.md" and any(cls == "facts" for cls, _, _ in paths.classify(rel)))
            or (_FINDING_FILE.match(rel) is not None and rel.endswith("/finding.yaml"))
            or _BUILD_RECORD.match(rel) is not None or paths.match(PROJECT_NOTICE, rel) is not None)


def running_tools(root):
    """The directory of the code running this lint, relative to root, when it is inside root (a local ./oft lint), or
    None (CI runs the base's tools, outside the tree it judges).  A change under it can change any file's verdict."""
    rel = os.path.relpath(os.path.realpath(HERE), os.path.realpath(root))
    return None if rel == ".." or rel.startswith(".." + os.sep) else rel.replace(os.sep, "/")


def run(root, changed=None, pr_kind=None, base=None, skeleton=False, release=False, changed_only=None, jobs=None,
        public=None, pending=None, today=None, max_rss_gib=MAX_RSS_GIB, pending_base=None, expired=None,
        donors=None):
    """All findings for the tree at root.  skeleton=True accepts a tree with
    no facts at all (no release.yaml, no projects/): the text rules still run
    over every file (unless changed_only narrows them), which is how the
    repository's own tools are checked before a release has been exported
    into it.  release=True adds what only a release must satisfy: no
    placeholder digest or commit is left, every project folder holds its
    project page (on the line that page is the render's after the merge),
    every build record is complete (records), and, read from the
    public repositories through public (default: a model.Public, which reads
    GitHub), the checker image pins the model's files (model) and every commit
    the release pins is public (pins).  base: the trusted base tree CI
    compares the findings ledger with (check_changes).  changed_only=BASE runs the
    per-file text rules only over the files that differ from commit BASE, or
    over every file when one that a verdict may read differs from it
    (read_by_every_verdict) or the code running this lint does
    (running_tools), and says so on stderr; the rules over the whole tree
    still run.  root must then be the top of a git checkout and BASE a commit
    of it (ChangedOnlyError).  The per-file text rules read an internal path
    (is_internal), which no release carries, for secrets alone
    (scan_internal_secrets).  jobs: how many processes run the text rules
    (default: default_jobs(), bounded by the CPUs
    and the memory available, for at least PARALLEL_FILES files to read);
    the findings do not depend on it.  max_rss_gib: the resident memory each
    process of the run may hold (None: no bound); one that holds more stops
    the run (ResourceStop).  The licence findings
    of a fuzz target that a licence-pending entry lists go to pending (a
    list, when given), not to the result (apply_pending); today is the date
    an entry's due date is compared with (default: utc_today()); an expired
    entry that a change does not touch goes to expired (a list, when given);
    and a pull request's lint (changed and pending_base given: a git
    checkout of the base commit, which may be sparse) compares the entries
    with the base commit's (base_pending_entries).  The exempt donor
    `Read from:` lines of relocated proof files go to donors (a list, when
    given), not to the result (split_donors)."""
    global _MAX_RSS
    previous, _MAX_RSS = _MAX_RSS, None if max_rss_gib is None else int(max_rss_gib * 2 ** 30)
    try:
        return _run(root, changed, pr_kind, base, skeleton, release, changed_only, jobs, public, pending, today,
                    pending_base, expired, donors)
    finally:
        _MAX_RSS = previous


def _run(root, changed, pr_kind, base, skeleton, release, changed_only, jobs, public, pending, today, pending_base,
         expired, donors):
    root = os.path.abspath(root)
    since = None if changed_only is None else changed_since(root, changed_only)   # first: it may refuse the run
    tree = facts.load(root)
    if skeleton and not tree.projects and not os.path.exists(tree.path("release.yaml")):
        tree.errors = []
    rules.check(tree)
    found = [Finding("schema", e.split(":", 1)[0], e.split(":", 1)[1].strip() if ":" in e else e)
             for e in tree.errors]
    try:
        files = walk(root)
        unread = left_out(root)
    except IndexUnreadable as err:
        return [Finding("paths", root, "git could not list this checkout's files (%s), so nothing was examined"
                        % (str(err) or "no message"))]
    if unread:
        print("oft lint: %d tracked file(s) are left out of this sparse checkout (%s first): the paths rules judge "
              "their names and read no byte of them, no other rule reads them, and an exception or a licence-pending "
              "entry that names one, or its unit, is left to a lint of the whole tree" % (len(unread), min(unread)),
              file=sys.stderr)
    # a file that differs from the commit --changed-only compares with is read by this lint, so it must be on disk
    changed_unread = sorted(unread & since) if since is not None else []
    if changed_unread:
        found.append(Finding("paths", changed_unread[0], "this file differs from %s, and this sparse checkout leaves "
                             "it out (%d such file(s)): check it out, or lint the whole tree"
                             % (changed_only, len(changed_unread))))
    check_rss()
    if not files:
        return [Finding("paths", root, "no files: nothing examined")]
    found += check_paths(tree, files, unread)
    found += check_symbols(tree, files)
    found += check_deviation(tree)
    found += check_instances(tree)
    found += check_disclosure(tree)
    found += check_enrolled(tree)
    found += check_private_harnesses(tree)
    found += check_port_none(tree)
    found += check_free_text(tree)
    third_party, table_found = load_third_party(root)
    found += table_found
    found += check_notice(tree)
    if release:
        found += check_placeholders(tree)
        found += check_project_pages(tree)
        found += check_records(tree)
        reader = public or model.Public()
        try:
            found += check_model(tree, reader)
            found += check_pins(tree, reader)
        finally:
            if public is None:
                reader.close()
    if changed is not None:
        found += check_changes(tree, changed, pr_kind or "maintainer", base)
    known = fact_urls(tree)
    own = oss_verify_sources(tree)
    # the per-file text rules read an internal path for secrets alone (scan_internal_secrets, below): no release
    # carries it, and dev/stream/bin/ holds the publishing scanner's needles, host paths and addresses on purpose.  The
    # directories the cut removes whose files keep a row of their own (paths.INTERNAL_DIRS) are read as those rows
    # say: dev/stream/ by internal_only, docs/reference/ and changes/ by every rule.
    internal = [rel for rel in files if is_internal(rel) and not rel.startswith(paths.INTERNAL_DIRS)]
    secret_only = set(internal)
    scanned, scope = [rel for rel in files if rel not in secret_only], None
    if since is not None:
        # a file's verdict reads the facts, the findings and the lint exceptions (the links they record, the sources
        # that are OSS Verify's own, the projects a finding holds back, the findings an entry clears), and is made by
        # the running code: a change to one can change the verdict on a file that did not change, so then every
        # file is read
        tools = running_tools(root)
        every = sorted(rel for rel in since if read_by_every_verdict(rel)
                       or (tools is not None and (tools == "." or rel.startswith(tools + "/"))))
        if every:
            what = every[0] if len(every) == 1 else "%s and %d more" % (every[0], len(every) - 1)
            print("oft lint --changed-only: %s changed, and the verdict on a file that did not change can depend on "
                  "%s: the per-file rules read every file" % (what, "it" if len(every) == 1 else "them"),
                  file=sys.stderr)
        else:
            scanned, scope = [rel for rel in scanned if rel in since], since
            internal = [rel for rel in internal if rel in since]
    contracts = contract_symbols(tree, scanned)
    check_rss()   # before the workers fork: each starts with what this process holds
    n_text = 0
    bare = collections.Counter()
    if jobs is None:   # a run told --jobs knows its own number; one that chose it says so, on stderr (default_jobs)
        jobs = default_jobs(explain=True) if len(scanned) >= PARALLEL_FILES else 1
    targets = None if pr_kind == "contributor" else anthropic_targets(root)
    private = private_projects(tree)
    for rel, (file_found, is_text, is_bare) in zip(scanned, scan_files(root, tree, known, own, scanned, jobs, targets,
                                                                       contracts, third_party, private)):
        found += file_found
        n_text += is_text
        if is_bare:
            bare[layout.unit_of(rel)] += 1
    # The proof files that carry no licence line: a count, not a finding (bare_licence).  Only a whole-tree run says
    # it, since over the changed files alone the number is of those files and not of the tree, which reads as a
    # smaller debt than there is.
    if bare and scope is None:
        print(bare_report(bare), file=sys.stderr)
    found += scan_internal_secrets(root, internal)
    check_rss()
    # The canary: a whole tree always holds a text file, so none read back means the reading itself broke.  Under
    # --changed-only the files to read are the changed ones, and a change of binary files alone (a finding's
    # input.bin) legitimately holds no text, so the canary cannot speak there.
    if not n_text and scope is None:
        found.append(Finding("private-data", root, "no text files: nothing examined"))
    exceptions = load_exceptions(root)
    found = apply_exceptions(found, [e for e in exceptions if e.get("rule") != PENDING], own, scope, unread)
    present = {layout.unit_of(rel) for rel in files if _PROJECT_PROOF.match(rel)}   # the units with a Rocq file
    return split_donors(
        apply_pending(found, [e for e in exceptions if e.get("rule") == PENDING], scope, today, pending,
                      base_pending_entries(pending_base) if changed is not None and pending_base else None, present,
                      changed, expired, {layout.unit_of(rel) for rel in unread} - {None}),
        donors)
