"""oft lint: the rules that keep this repository what it says it is.

    paths         every path has exactly one owner (tools/oft/paths.py), a pull
                  request changes only what its kind of pull request may change,
                  no derived file, binary, NUL byte, LFS pointer or link is
                  stored, but where binary data belongs (BINARY_OK, and a
                  classifier program its proof.yaml pins), no old-layout path
                  lies beside a per-project one (layout.py), and a symbol fact
                  is named for a build its harness.yaml publishes
    schema        closed schemas and the rules between facts (schema.py, rules.py),
                  and each symbol fact reads whole and is of the binary
                  harness.yaml pins (check_symbols)
    private-data  no host paths (but in the change ledgers, changes/, which
                  the release removes), private network addresses, private host
                  names, private theorem-labs repositories named in a path,
                  e-mail addresses, private keys or access tokens in what this
                  repository wrote, and no build host in a port build record
    links         links point only where they may: never to a machine on a
                  private network or to a private theorem-labs repository
    free-text     every free-text field has a place in the rendering
    proofs        no axioms, admits, plugins or file effects in a fuzz target's
                  proofs folder, no file reads (Load, Cd, Extra Dependency) in
                  the generated Rocq files of projects/, and no wall-clock
                  limits in a Rocq file
    licence       a proof file's licence lines agree with NOTICE (scan_licence)
    contract-literals
                  a contract file (lib/[UAB/]Prog/**/<fn>_c.v) of a fuzz
                  target with a symbol fact writes no numeral, hexadecimal
                  or decimal, inside an allocated section of one of its
                  builds, and
                  names only what its build's Symbols.v defines
                  (scan_contract)
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
"""
import bisect
import collections
import concurrent.futures
import concurrent.futures.process
import datetime
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

from . import facts, layout, model, names, nsrename, paths, rocq, rules, schema, symbols, urls, yamlio

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
# made from a bundle under Apache-2.0 OR MIT.  A changed byte makes any of them ordinary text, held to every rule.
PINNED_VERBATIM = {
    "LICENSES/anthropic-proofs-LICENSE": "cfc7749b96f63bd31c3c42b5c471bf756814053e847c10f3eb003417bc523d30",
    "LICENSES/anthropic-proofs-LICENSE-MIT": "2e6105c36a95f04adbc36000b7b1ce65544385e27f8febb1b2f53b61fdb62bca",
    "LICENSES/anthropic-proofs-NOTICE": "f4cbf47ffed57359084432af1ca4b22347ecb995fcf7a2e4e346f180d2e5001d",
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
PUBLIC_REPOS = ("oss-verify", "oss-verify-proofs", "rocq-linux-process-semantics", "rocq-read-file", "asan-static",
                "static-asan")
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


def _internal_port_lines(tree, where, text):
    """The lines of a held project's build.oss_verify.repository, the sole
    field that may name the port's internal copy: no other field of that file
    may name it."""
    parts = where.split("/")
    if len(parts) != 3 or parts[0] != "projects" or parts[2] != "project.yaml":
        return frozenset()
    project = tree.projects.get(parts[1])
    if project is None or project.name not in facts.hold(tree).held:
        return frozenset()
    node = yamlio.compose(text)
    for key in ("build", "oss_verify", "repository"):
        node = yamlio.mapping_value(node, key)
        if node is None:
            return frozenset()
    if getattr(node, "value", None) != schema.INTERNAL_PORT_REPOSITORY:
        return frozenset()
    return frozenset(range(node.start_mark.line + 1, node.end_mark.line + 2))


def _repository_value(line, match):
    """Whether match is the YAML value of a repository key, in block or flow
    form, rather than a comment or another free-text use."""
    before, after = line[:match.start()], line[match.end():]
    return ("#" not in before
            and re.search(r"(?<![\w-])repository\s*:\s*(?:['\"])?$", before) is not None
            and re.match(r"(?:['\"])?\s*(?:[,}]|#|$)", after) is not None)


# What the text rules read in an internal path (is_internal: INTERNAL of paths.py, and LINT_ONLY_INTERNAL): a private
# key or an access token, which is as bad there as in a shipped file.  The rest of private-data, and links and proofs,
# judge the published text: no release carries an internal path, and tools/publish/ holds the publishing scanner's
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
                host_paths=True):
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
    still counts."""
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
                        if name in PUBLIC_REPOS or (no in internal_port_lines and bare and name == INTERNAL_PORT_REPO
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


def judge(u, known, strict=True, full=True, ref=None):
    """Whether a parsed link (urls.parse) may stay: it must not name a machine on a private network or a theorem-labs
    repository that is not public.  A full link in rendered text, docs and facts (strict) must also be https and be
    one of ours, OSS-Fuzz's, one the facts record, or one of the two pages ASan's runtime prints, written as
    sanitizer_url wants it: ref, the link urls.links read, not the page it opens.  A link that opens nothing
    (None) is judged by its text alone."""
    if u is None:
        return True
    if u.host and (u.scheme in WEB_SCHEMES or NETWORK_HOST.fullmatch(u.host)) and private_host(u.host):
        return False
    if any(r not in PUBLIC_REPOS for r in theorem_repositories(u)):
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


def scan_links(text, where, known, strict=True):
    """links.  Every link a reader can follow (urls.links), judged by what a browser opens for it: an absolute URL
    alone, a Markdown or HTML link against each page that shows the file, and another reading of the same text
    (GitHub's extent of a bare URL, the text with character references decoded, a line of Markdown as GitHub shows
    its text) for privacy only.  A URL urls.parse cannot read for sure is refused wherever this rule reads; one that
    opens nothing, only in rendered text, docs and facts (strict), and only as an absolute URL.  One finding per line
    and target."""
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
                ok = judge(target, known, strict, full=link.kind != "reading", ref=link.ref)
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
# (PROGRAM_LINES) and has no other licence lines, since its code keeps the program's licences.
ANTHROPIC_TEXTS = ("LICENSES/anthropic-proofs-LICENSE", "LICENSES/anthropic-proofs-LICENSE-MIT",
                   "LICENSES/anthropic-proofs-NOTICE")
ANTHROPIC_LICENCE = "Apache-2.0 OR MIT"
PROOF_LICENCES = (ANTHROPIC_LICENCE, "MIT")
PROGRAM_LINES = ("(* Machine-generated data computed from the task's compiled program image",
                 "(* This file states or restates instruction words of the task's compiled program")
HEADER_LINES = 10
# a licence tag wherever it is on its line, in any comment style: a tag the rule cannot see ships the wrong licence.  A
# carriage return before a line feed is part of the line end, here and in _ANTHROPIC_COPYRIGHT.
_SPDX = re.compile(r"SPDX-License-Identifier:[ \t]*(.*?)[ \t\r]*(?:\*\)|$)", re.M)
_ANTHROPIC_COPYRIGHT = re.compile(r"^\(\* Copyright \d{4} Anthropic PBC \*\)[ \t]*\r?$", re.M)
# each copyright of Anthropic a line names: one that is not exactly _ANTHROPIC_COPYRIGHT was changed, unless it restates
# that line's words in a file that has it (_ANTHROPIC_RESTATED)
_ANTHROPIC_NAMED = re.compile(r"Copyright\b[^\n]*?\bAnthropic\b", re.I)
# Anthropic's copyright in its own words, ending there: how a doc comment under the licence lines restates the notice
_ANTHROPIC_RESTATED = re.compile(r"Copyright \d{4} Anthropic PBC(?=[ \t]*(?:[.;,]|\*\)|\r?$))", re.M)
# a licence tag or a copyright of Anthropic, changed or not, wherever it is on its line: below HEADER_LINES it is out
# of place
_LICENCE_LINE = re.compile(r"SPDX-License-Identifier:|(?i:Copyright\b[^\n]*?\bAnthropic\b)")

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


def scan_licence(text, where, targets):
    """The findings of the licence rule on the proof file `text` at `where`.  targets: anthropic_targets, or None for a
    contributor's pull request, whose build records the maintainer writes before it merges
    (docs/adding-a-proof.md, requirement 7): then the licence lines are checked, and the record is not."""
    lines = text.split("\n", HEADER_LINES)
    head = "\n".join(lines[:HEADER_LINES])
    rest = lines[HEADER_LINES] if len(lines) > HEADER_LINES else ""
    # a plain search first: most files have neither (lower: a changed copyright line may spell the name in any case)
    if "SPDX-License-Identifier" in rest or "anthropic" in rest.lower():
        late = _LICENCE_LINE.search(text, len(head) + 1)
        if late:
            return [Finding("licence", "%s:%d" % (where, text.count("\n", 0, late.start()) + 1),
                            "a licence line opens the file, in its first %d lines (docs/adding-a-proof.md, "
                            "requirement 7)" % HEADER_LINES)]
    spdx_lines = list(_SPDX.finditer(head))
    anthropic = _ANTHROPIC_COPYRIGHT.search(head) is not None
    spdx = spdx_lines[0].group(1) if spdx_lines else None
    at = "%s:%d" % (where, head.count("\n", 0, spdx_lines[0].start()) + 1) if spdx_lines else where
    if lines[0].startswith(PROGRAM_LINES) and (spdx_lines or anthropic):
        return [Finding("licence", at, "a file that restates a program's instruction words or holds data computed "
                                       "from one has no other licence lines: its code keeps the program's licences "
                                       "(docs/adding-a-proof.md, requirement 7)")]
    other = next((m for m in spdx_lines[1:] if _expression(m) != _expression(spdx_lines[0])), None)
    if other is not None:   # a second tag that names the same licence restates it (a doc comment, say)
        return [Finding("licence", "%s:%d" % (where, head.count("\n", 0, other.start()) + 1),
                        "a proof file has one licence: this tag says %r, the first one %r" % (other.group(1), spdx))]
    if spdx is not None and spdx not in PROOF_LICENCES:
        return [Finding("licence", at, "%r is neither licence a proof file has: %s, with Anthropic's copyright, for "
                                       "one made from Anthropic's proofs, or MIT for one written here (NOTICE)"
                                       % (spdx, ANTHROPIC_LICENCE))]
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
    if spdx != ANTHROPIC_LICENCE or targets is None:
        return []
    unit = layout.unit_of(where)
    if unit not in targets:
        return [Finding("licence", at, "a file under %s needs a build record, %s, that lists %s under proofs.texts "
                                       "(NOTICE)" % (ANTHROPIC_LICENCE,
                                                     layout.record_path(*unit.split("/"), layout.of_path(where)),
                                                     ", ".join(ANTHROPIC_TEXTS)))]
    return []


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


# --------------------------------------------------------- paths, withheld

# What may hold binary bytes (a NUL byte): a counterexample's and a finding's runs, in either layout (layout.py), a
# mutant run's input kept as evidence in a fuzz target's provenance (the same kind of file: a fuzz input), and the
# tests' fixtures; and a classifier program that its proof.yaml pins (classifier_programs), which is proof data its
# proof verifies on its own.  Binary data anywhere else is a release asset, not a file in git.
BINARY_OK = tuple("%s/%s" % (d, run) for lay in layout.LAYOUTS
                  for d in (layout.counterexample_dir("*", "*", "*", lay), layout.finding_dir("*", "*", "*", lay))
                  for run in ("input.bin", "control.bin")) + (
    "projects/*/*/proofs/provenance/evidence/mutants/*/input.bin", "tools/oft/tests/**")
NUL_BYTE = "a NUL byte: binary data is a release asset, not a file in git"


def classifier_programs(tree):
    """{path: (sha256, proof directory)} of each classifier program a proof.yaml pins (classifier.elf and
    classifier.sha256): the one ELF file, and the one binary file, a proof directory may hold."""
    return {pd.path + "/" + pd.data["classifier"]["elf"]: (pd.data["classifier"]["sha256"], pd.path)
            for pd in tree.proofs.values() if pd.data.get("classifier")}

# the four ELF files the tests of oft symbols read (tests/test_symbols.py), small and built as their README.md says:
# the only ELF files kept in git outside a classifier program its proof.yaml pins (their NUL bytes are under
# tools/oft/tests/**, which BINARY_OK holds)
ELF_FIXTURES = ("tools/oft/tests/fixtures/elf/two.stripped", "tools/oft/tests/fixtures/elf/two.unstripped",
                "tools/oft/tests/fixtures/elf/computed_goto_global.elf",
                "tools/oft/tests/fixtures/elf/computed_goto_biased.elf")
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
LINT_ONLY_HAND = (".claude/skills/porting-released-proofs/SKILL.md",
                  ".claude/skills/porting-released-proofs/references/*.md",
                  ".claude/skills/clean-room-restatement/SKILL.md",
                  ".claude/skills/clean-room-restatement/references/*.md",
                  "toolchain/requirements.txt")
# What only this repository has, as paths.TABLE's internal rows are, that only lint judges, here for the same reason:
# a row of paths.TABLE is part of the checker, and the INTERNAL of paths.py is made of those rows.  dev/enroll/, the
# place of the scripts that carry a merged theorem-labs/oss-verify enrollment into these facts, which enroll.yml and
# enroll-build.yml run and no check opens: outside tools/, so keys.checker, which lists tools/ alone, holds none of
# them (OSSV-276; they leave tools/enroll/, whose paths.TABLE row is internal, in the commit after this one, since
# pr.yml lints a change by its base's rules).  release_tree.INTERNAL is each directory of this list, then the INTERNAL
# of paths.py, then release_tree.SKILLS (test_release_tree.test_every_internal_path_is_one_the_cut_removes),
# so the cut removes dev/enroll/ whole, and is_internal reads it for secrets alone, as it reads tools/enroll/.
# paths.TABLE's tools/enroll/** row then matches nothing; when paths.py next changes, a dev/enroll/** row there
# replaces it and this list.
LINT_ONLY_INTERNAL = ("dev/enroll/**",)


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
    only when no left-out file differs from the commit it compares with (lint_files_left_out), so each left-out file
    keeps the verdict its bytes had there, and the merge queue's lint reads the whole tree."""
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


SHARED_FILE = ("a shared generated file: no pull request changes it; the line's render after the merge writes it "
               "(./oft generate --skip-shared renders every other generated file)")


def check_changes(tree, changed, kind, base=None):
    """The pull-request half of `paths`.  kind: release | maintainer | contributor.  base is the trusted base tree
    when CI compares the findings ledger: every record remains in the proposed tree, the unpatched pins remain while
    its project has a base finding, and what a base finding's runs are of stays as it is (_fixed_evidence).  The base
    is walked as well as changed read, since a diff that detects renames lists a moved file only where it went.  A
    file is the same in either layout (layout.canonical): a finding the pull request moves to the other layout is
    neither deleted nor free to change."""
    out = []
    ledger = _ledger(base) if base else {}
    held = _ledger(tree.root)
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
        # A shared generated file is the line's render's: no pull request of any kind carries one.  A deletion
        # passes: the render puts it back on the line, and on main they go for good.
        if paths.is_shared(rel) and os.path.lexists(tree.path(rel)):
            out.append(Finding("paths", rel, SHARED_FILE))
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
    what built them (the builder image of release.yaml, the one static-asan commit every record of its kind names, a
    port record's port and port archive those of its project.yaml, a fallback record's complete fallback block);
    its binary and source archives those of its project.yaml, by file, bytes and sha256 (Contract C1: a record names
    no release, and one written before C1 names project.yaml's); LICENSES/ exactly the texts its components name; the
    upstream licence; for a GPL- or LGPL-licensed component, a source bundle (Contract C1's list of {file, sha256})
    that cites the project's source archive and only files its project.yaml or release.yaml pins with those sha256s
    (the release gate asks more: that each is published on its release); build glue only among its recipe's patches;
    and its overlay files as recipe/MANIFEST.tsv pins them.  The recipe a record cites is the schema rule's
    (rules._records).  A port-built project's binary archive also goes with its port archive (assets.port)."""
    out = []
    release = tree.release or {}
    builder = ((release.get("images") or {}).get("builder") or [None])[0]
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
            if r.get("port") is not None:
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
            if tc.get("builder_image") != builder:
                add("toolchain.builder_image is not release.yaml's images.builder[0]")
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

def scan_file(root, rel, tree, known, own, targets=None, contracts=None):
    """(the findings of the per-file text rules on rel, whether it is a text file); a binary file, or one that is not
    a regular file of at most its cap, is not read.  known: the links the facts record (fact_urls); own: the source
    directories of the fuzz targets OSS Verify builds (oss_verify_sources); tree: the facts, which say which
    project.yaml may name the port's internal copy (_internal_port_lines); targets: the fuzz targets whose build record
    lists the texts of Anthropic's licence (anthropic_targets), or None to leave the records unchecked
    (scan_licence); contracts: the symbol facts of the fuzz targets whose contract files are read
    (contract_symbols), or None to leave the contract files unchecked (scan_contract)."""
    text = read_text(os.path.join(root, rel), facts.file_cap(rel))
    if text is None:
        # Rocq compiles a file that holds a NUL byte (in a comment, say), so a Rocq file the proof rules cannot read is
        # refused, not skipped
        if proof_rocq(rel) or rel.endswith(".v") and rel.startswith("projects/"):
            return [Finding("proofs", rel, "a Rocq file that is not read as text (it holds a NUL byte, or it is not a "
                                           "regular file of at most its cap) is not allowed")], False
        return [], False
    out = scan_namespace(text, rel, tree)
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
    out += scan_shapes(text, rel, source=src and not own_source, internal=inside, email_text=blanked,
                       internal_port_lines=_internal_port_lines(tree, rel, text),
                       host_paths=not rel.startswith(CHANGE_LEDGERS))
    # the link rule judges a link by what a reader's browser would open; no reader opens this directory's text
    # (internal_only), and its lock file pins every package by its URL
    if (not src or own_source) and not inside:
        out += scan_links(text if blanked is None else blanked, rel, known,
                          strict=link_strict(rel) and not port_text and not own_source)
    if PORT_MANIFEST.match(rel):
        out += scan_port_manifest(text, rel)
    if proof_v:
        out += scan_proof(text, rel) + scan_licence(text, rel, targets)
        builds = None if contracts is None or not CONTRACT_FILE.match(rel) else contracts.get(layout.unit_of(rel))
        if builds:
            out += scan_contract(text, rel, builds)
    elif rel.startswith("projects/") and rel.endswith(".v"):
        out += scan_project_rocq(text, rel)
    if not proof_v and wall_clock_scanned(rel):
        out += scan_wall_clock(text, rel)
    return out, True


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


def memory_available(proc="/proc", cgroup="/sys/fs/cgroup"):
    """The memory, in bytes, that this process and its workers may take: MemAvailable of proc/meminfo, and less when a
    cgroup (version 2) that holds this process limits it, at any level: its memory.max less its memory.current.  None
    when proc/meminfo says nothing."""
    try:
        with open(os.path.join(proc, "meminfo")) as f:
            avail = next(int(line.split()[1]) * 1024 for line in f if line.startswith("MemAvailable:"))
    except (OSError, StopIteration, ValueError):
        return None
    try:
        with open(os.path.join(proc, "self", "cgroup")) as f:
            parts = [p for p in next(line for line in f if line.startswith("0::"))[3:].strip().split("/") if p]
    except (OSError, StopIteration):
        return avail
    for i in range(len(parts), -1, -1):
        try:
            with open(os.path.join(cgroup, *parts[:i], "memory.max")) as f:
                limit = f.read().strip()
            with open(os.path.join(cgroup, *parts[:i], "memory.current")) as f:
                current = int(f.read())
        except (OSError, ValueError):
            continue
        if limit != "max":
            avail = min(avail, max(0, int(limit) - current))
    return avail


def default_jobs():
    """The default number of processes of forked_map: the CPUs this process may run on (facts.cpus),
    but no more than the available memory (memory_available) holds at WORKER_GIB each, and at least 1."""
    cpus, avail = facts.cpus(), memory_available()
    return cpus if avail is None else max(1, min(cpus, avail // int(WORKER_GIB * 2 ** 30)))


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


def scan_files(root, tree, known, own, files, jobs, targets=None, contracts=None):
    """scan_file for each of files, in their order, on up to jobs processes (forked_map), each starting with the tree
    loaded here."""
    return forked_map(lambda rel: scan_file(root, rel, tree, known, own, targets, contracts), files, jobs)


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


_BUILD_RECORD = re.compile(layout.PROOF_HARNESS_RE + r"/provenance/PROVENANCE\.yaml$")


def read_by_every_verdict(rel):
    """Whether a change to rel can change the per-file rules' verdict on another file.  Four files are read by every
    verdict: a project's project.yaml and a harness's harness.yaml (facts), a finding's finding.yaml, whose links
    fact_urls records and whose state decides which project.yaml may name the port's internal copy
    (_internal_port_lines), and lint-exceptions.yaml, whose entries clear findings in other files (an entry removed
    there leaves a finding in a file that did not change).  A build record decides the licence rule on its own fuzz
    target's proof files (anthropic_targets), and a symbol fact (which paths.py classes as facts) the contract-literals
    rule on its fuzz target's contract files (contract_symbols).  The set is wider on purpose, a margin, so that it
    does not lose a file a later rule reads: every file paths.py classes as facts, every build record (which facts.load
    reads too, and which re-reads the whole tree rather than only its fuzz target's files), and every .gitattributes,
    which changes the bytes git checks out for a file whose blob did not change (line ends, encoding).  CHANGELOG.md is
    the one fact left out: no rule reads it but as a file of its own (fact_urls reads projects, harnesses and findings,
    and facts.load does not parse it), so a change to it alone has the per-file rules read that one file."""
    return (rel == EXCEPTIONS or os.path.basename(rel) == ".gitattributes"
            or (rel != "CHANGELOG.md" and any(cls == "facts" for cls, _, _ in paths.classify(rel)))
            or (_FINDING_FILE.match(rel) is not None and rel.endswith("/finding.yaml"))
            or _BUILD_RECORD.match(rel) is not None)


def running_tools(root):
    """The directory of the code running this lint, relative to root, when it is inside root (a local ./oft lint), or
    None (CI runs the base's tools, outside the tree it judges).  A change under it can change any file's verdict."""
    rel = os.path.relpath(os.path.realpath(HERE), os.path.realpath(root))
    return None if rel == ".." or rel.startswith(".." + os.sep) else rel.replace(os.sep, "/")


def run(root, changed=None, pr_kind=None, base=None, skeleton=False, release=False, changed_only=None, jobs=None,
        public=None, pending=None, today=None, max_rss_gib=MAX_RSS_GIB, pending_base=None, expired=None):
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
    with the base commit's (base_pending_entries)."""
    global _MAX_RSS
    previous, _MAX_RSS = _MAX_RSS, None if max_rss_gib is None else int(max_rss_gib * 2 ** 30)
    try:
        return _run(root, changed, pr_kind, base, skeleton, release, changed_only, jobs, public, pending, today,
                    pending_base, expired)
    finally:
        _MAX_RSS = previous


def _run(root, changed, pr_kind, base, skeleton, release, changed_only, jobs, public, pending, today, pending_base,
         expired):
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
    found += check_disclosure(tree)
    found += check_enrolled(tree)
    found += check_free_text(tree)
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
    # carries it, and tools/publish/ holds the publishing scanner's needles, host paths and addresses on purpose.  The
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
    if jobs is None:
        jobs = default_jobs() if len(scanned) >= PARALLEL_FILES else 1
    targets = None if pr_kind == "contributor" else anthropic_targets(root)
    for file_found, is_text in scan_files(root, tree, known, own, scanned, jobs, targets, contracts):
        found += file_found
        n_text += is_text
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
    return apply_pending(found, [e for e in exceptions if e.get("rule") == PENDING], scope, today, pending,
                         base_pending_entries(pending_base) if changed is not None and pending_base else None, present,
                         changed, expired, {layout.unit_of(rel) for rel in unread} - {None})
