"""Every path the repository may hold, and who owns it (lint rule `paths`).

Classes:
  hand      written and reviewed by maintainers, like code
  internal  written and reviewed by maintainers, and never shipped (INTERNAL)
  facts     exported facts: only a release pull request changes them
  gen       rendered by `oft generate`; CI renders again and compares
  contrib   where outside pull requests go: proofs and counterexamples

A path must match exactly one pattern.  In a pattern, `*` is one path
segment (with fnmatch wildcards inside it), `**` is any number of segments,
and `{project}`, `{harness}` and `{statement}` are one segment each, which
`paths` then checks against the facts.  A placeholder that appears twice in a
pattern matches the same segment both times.
"""
import re
from functools import lru_cache


TABLE = [
    # internal: what only this repository has, which no release carries (INTERNAL, below): `oft release-tree` removes
    # each, and lint's per-file text rules do not read them.  A row that ends in /** is a whole directory.
    # which proofs a release publishes, by fuzz target and statement; and the list of the files that need judgement or
    # that the review agent loads (.github/CODEOWNERS)
    ("internal", "approvals.yaml"),
    ("internal", ".github/CODEOWNERS"),
    # the facts review: the advisory AI review that facts-review.yml runs on a facts pull request, on this repository's
    # identity, and what that review checks (review.md)
    ("internal", ".github/workflows/facts-review.yml"),
    ("internal", ".claude/skills/review-facts/SKILL.md"),
    ("internal", "review.md"),
    # the enrollment workflows: enroll.yml runs tools/enroll/ when an enrollment's checks pass and opens its facts pull
    # request, enroll-build.yml builds the enrollment in a run of its own, facts-refresh.yml and hold-state.yml start
    # enroll.yml's redo runs, enroll-retry.yml re-runs a failed run of enroll.yml or enroll-build.yml at most two times,
    # and approvals-watch.yml, on each push to main, starts enroll.yml's approvals runs for a merged enrollment facts
    # pull request and for a conflicting approvals pull request (tools/enroll/ci/approvals_entry.py); and the scripts
    # that carry a merged theorem-labs/oss-verify enrollment into these facts (tools/enroll/README.md), which no check
    # opens, and keys.NOT_THE_CHECKER names the directory, so a change to them changes no part's key (keys.py)
    ("internal", ".github/workflows/enroll.yml"),
    ("internal", ".github/workflows/enroll-build.yml"),
    ("internal", ".github/workflows/facts-refresh.yml"),
    ("internal", ".github/workflows/hold-state.yml"),
    ("internal", ".github/workflows/enroll-retry.yml"),
    ("internal", ".github/workflows/approvals-watch.yml"),
    ("internal", "tools/enroll/**"),
    # the released-proof index: proof-index.yml runs proof-index.py when main or ossv/candidates moves,
    # and pushes the branch proof-index; and the trigger that ossv/candidates carries to start that workflow
    ("internal", ".github/workflows/proof-index.yml"),
    ("internal", ".github/proof-index.py"),
    ("internal", ".github/workflows/proof-index-trigger.yml"),
    # the render of the shared generated files after each push to the line, which runs
    # tools/oft/ci/regenerate-shared.sh (INTERNAL_FILES, below)
    ("internal", ".github/workflows/index.yml"),
    # the publishing workflow: publish-request.yml asks for a publication, publish.yml makes it and publish-gate.yml
    # runs the release gate's checks on its cut; and the tools they run (tools/publish/), with the scanner's needles,
    # host paths and addresses on purpose
    ("internal", ".github/workflows/publish-request.yml"),
    ("internal", ".github/workflows/publish.yml"),
    ("internal", ".github/workflows/publish-gate.yml"),
    ("internal", "tools/publish/**"),
    # hand
    ("hand", "LICENSE"),
    # the licence texts and notice of the proofs made from a bundle under Apache-2.0 OR MIT, verbatim (lint pins their
    # bytes)
    ("hand", "LICENSES/anthropic-proofs-LICENSE"),
    ("hand", "LICENSES/anthropic-proofs-LICENSE-MIT"),
    ("hand", "LICENSES/anthropic-proofs-NOTICE"),
    ("hand", "CITATION.cff"),
    ("hand", "CONTRIBUTING.md"),
    ("hand", "SECURITY.md"),
    ("hand", "REUSE.toml"),
    ("hand", "oft"),
    ("hand", "theorem"),
    ("hand", ".gitignore"),
    ("hand", ".gitattributes"),
    ("hand", "docs/*.md"),
    # the reference book: one router and one entry per subject, so a skill can stay short and name the entry;
    # `oft release-tree` removes docs/reference/ (INTERNAL_DIRS)
    ("hand", "docs/reference/*.md"),
    ("hand", "notes/*.md"),
    ("hand", "theories/*.v"),
    ("hand", "theories/dune"),
    ("hand", "toolchain/checker.Dockerfile"),
    ("hand", "toolchain/lps-core.paths"),
    ("hand", "toolchain/runner.Dockerfile"),
    ("hand", "tests/**"),
    # the OSS Verify stream's operational tools, which run on the stream's boxes and which no check job opens
    # (dev/stream/README.md).  They are a top level of their own, outside tools/, so that
    # keys.checker, which lists tools/ alone, holds none of them in any unit's key; `oft release-tree` removes the
    # directory whole (INTERNAL_DIRS), and lint.internal_only reads them as text no release carries
    ("hand", "dev/stream/**"),
    ("hand", "tools/oft/**"),
    ("hand", "analyses/harness-checks/README.md"),
    ("hand", "analyses/failure-handlers/README.md"),
    ("hand", "analyses/failure-handlers/failure_handlers.tsv"),
    ("hand", ".github/workflows/pr.yml"),
    ("hand", ".github/workflows/weekly.yml"),
    ("hand", ".github/workflows/release.yml"),
    ("hand", ".github/workflows/release-check.yml"),
    ("hand", ".github/workflows/fetch-drafts.yml"),
    ("hand", ".github/actions/plan-drafts/action.yml"),
    ("hand", ".github/actions/place-drafts/action.yml"),
    ("hand", ".github/workflows/ledger.yml"),
    # the workflow that builds the checker and runner images from toolchain/*.Dockerfile and pushes them to ghcr.io
    ("hand", ".github/workflows/images.yml"),
    ("hand", ".github/actionlint.yaml"),
    # the review of each pull request and new issue of the public repository by Claude (review.yml runs there alone),
    # and its rules in docs/review.md
    ("hand", ".github/workflows/review.yml"),
    # what an agent reads first, and the instructions it follows to add a proof
    ("hand", "AGENTS.md"),
    ("hand", ".claude/skills/adding-a-proof/SKILL.md"),
    # what each change cost and what it taught (oft change-ledger, tools/oft/change_ledger.py): its sessions, check
    # logs, ledger and journal, each changes/<change>/<file>; `oft release-tree` removes changes/ (INTERNAL_DIRS)
    ("hand", "changes/*/*"),
    # findings: library bugs found while proving, on the proof branch until they are public; a maintainer's or a
    # release pull request changes them, since a change of state can release the hold on a project.  Each row of a
    # fuzz target's proofs, counterexamples and findings is in both layouts (tools/oft/layout.py): the old one, then
    # its per-project twin, with the same class (test_layout.Rows says each twin is layout.moved of its row).  TABLE
    # stays a literal: tools/enroll/ci/inputs.py reads it as one, never running this file.
    ("hand", "findings/{project}/unpatched.yaml"),
    ("hand", "projects/{project}/unpatched.yaml"),
    ("hand", "findings/{project}/{harness}/series"),
    ("hand", "projects/{project}/{harness}/findings/series"),
    ("hand", "findings/{project}/{harness}/*/finding.yaml"),
    ("hand", "projects/{project}/{harness}/findings/*/finding.yaml"),
    ("hand", "findings/{project}/{harness}/*/input.bin"),
    ("hand", "projects/{project}/{harness}/findings/*/input.bin"),
    ("hand", "findings/{project}/{harness}/*/control.bin"),
    ("hand", "projects/{project}/{harness}/findings/*/control.bin"),
    ("hand", "findings/{project}/{harness}/*/*.patch"),
    ("hand", "projects/{project}/{harness}/findings/*/*.patch"),
    # facts
    ("facts", "release.yaml"),
    ("facts", "NOTICE"),
    ("facts", "CHANGELOG.md"),
    ("facts", "toolchain/allowed-axioms.txt"),
    ("facts", "projects/{project}/project.yaml"),
    ("facts", "projects/{project}/{harness}/harness.yaml"),
    ("facts", "projects/{project}/{harness}/source/**"),
    # its body is a fact; `oft generate --check` also re-renders its header
    ("facts", "projects/{project}/{harness}/Distribution.v"),
    # a build's symbol fact, which `oft symbols` reads from its unstripped twin: symbols/<build>.tsv, for a build
    # harness.yaml publishes (lint, paths), of the binary it pins (lint, schema)
    ("facts", "projects/{project}/{harness}/symbols/*.tsv"),
    # a project's public patch text, which its patches entries name (facts.Project.patch_path), in each layout
    ("facts", "patches/{project}/*.patch"),
    ("facts", "projects/{project}/patches/*.patch"),
    # gen
    ("gen", "README.md"),
    ("gen", "dune-project"),
    ("gen", "index/STATUS.md"),
    ("gen", "index/PROOFS.md"),
    ("gen", "index/*.tsv"),
    ("gen", "analyses/harness-checks/checks.tsv"),
    ("gen", "analyses/known-issues.md"),
    ("gen", "projects/{project}/README.md"),
    # a project's opam file, rocq-<opam stem>-<project>.opam: lint holds its name to the release's stem (check_paths)
    ("gen", "projects/{project}/rocq-*.opam"),
    ("gen", "projects/{project}/{harness}/README.md"),
    ("gen", "projects/{project}/{harness}/dune"),
    ("gen", "projects/{project}/{harness}/Images.v"),
    # each build's functions by name, from its symbol fact, for a fuzz target with one (templates/Symbols.v.tmpl)
    ("gen", "projects/{project}/{harness}/Symbols.v"),
    ("gen", "projects/{project}/{harness}/Statements.v"),
    ("gen", "projects/{project}/{harness}/Characterise.v"),
    ("gen", "projects/{project}/{harness}/images/dune"),
    ("gen", "proofs/{project}/{harness}/{statement}/dune"),
    ("gen", "projects/{project}/{harness}/proofs/{statement}/dune"),
    ("gen", "proofs/{project}/{harness}/lib/dune"),
    ("gen", "projects/{project}/{harness}/proofs/lib/dune"),
    # the dune file of each per-project proofs and counterexamples folder, which shuts it out of the statement theory
    # of the folder above (templates/proof-dune.tmpl, barrier)
    ("gen", "projects/{project}/{harness}/proofs/dune"),
    ("gen", "projects/{project}/{harness}/counterexamples/dune"),
    # contrib
    ("contrib", "proofs/{project}/{harness}/{statement}/*.v"),
    ("contrib", "projects/{project}/{harness}/proofs/{statement}/*.v"),
    ("contrib", "proofs/{project}/{harness}/{statement}/proof.yaml"),
    ("contrib", "projects/{project}/{harness}/proofs/{statement}/proof.yaml"),
    ("contrib", "proofs/{project}/{harness}/{statement}/classifier/**"),
    ("contrib", "projects/{project}/{harness}/proofs/{statement}/classifier/**"),
    # a harness's proof library, shared by its proofs and compiled once (<namespace>.Proofs.<p>.<h>.lib)
    ("contrib", "proofs/{project}/{harness}/lib/**/*.v"),
    ("contrib", "projects/{project}/{harness}/proofs/lib/**/*.v"),
    # the build record of the binaries a harness's proofs are about: what built them is recipe/ (the slice of the recipe
    # that built them) or port/ (the OSS Verify port's project directory and the manifest its tools/check wrote)
    ("contrib", "proofs/{project}/{harness}/provenance/PROVENANCE.yaml"),
    ("contrib", "projects/{project}/{harness}/proofs/provenance/PROVENANCE.yaml"),
    ("contrib", "proofs/{project}/{harness}/provenance/PROVENANCE.md"),
    ("contrib", "projects/{project}/{harness}/proofs/provenance/PROVENANCE.md"),
    ("contrib", "proofs/{project}/{harness}/provenance/recipe/**"),
    ("contrib", "projects/{project}/{harness}/proofs/provenance/recipe/**"),
    ("contrib", "proofs/{project}/{harness}/provenance/port/manifest.yaml"),
    ("contrib", "projects/{project}/{harness}/proofs/provenance/port/manifest.yaml"),
    ("contrib", "proofs/{project}/{harness}/provenance/port/projects/{project}/**"),
    ("contrib", "projects/{project}/{harness}/proofs/provenance/port/projects/{project}/**"),
    ("contrib", "proofs/{project}/{harness}/provenance/LICENSES/**"),
    ("contrib", "projects/{project}/{harness}/proofs/provenance/LICENSES/**"),
    # a build record's evidence: the scripts of record, per-value tables, gate records and their MANIFEST
    ("contrib", "proofs/{project}/{harness}/provenance/evidence/**"),
    ("contrib", "projects/{project}/{harness}/proofs/provenance/evidence/**"),
    ("contrib", "counterexamples/{project}/{harness}/{statement}/input.bin"),
    ("contrib", "projects/{project}/{harness}/counterexamples/{statement}/input.bin"),
    ("contrib", "counterexamples/{project}/{harness}/{statement}/control.bin"),
    ("contrib", "projects/{project}/{harness}/counterexamples/{statement}/control.bin"),
    ("contrib", "counterexamples/{project}/{harness}/{statement}/expect.yaml"),
    ("contrib", "projects/{project}/{harness}/counterexamples/{statement}/expect.yaml"),
]

# The shared generated files: oft generate renders them from the whole tree, so every proof pull request would change
# them.  No pull request changes them (lint, paths); the checks of a pull request, a merge queue group and a push leave
# them out (oft generate --check --skip-shared); .github/workflows/index.yml renders them after each merge, through
# tools/oft/ci/regenerate-shared.sh (oft generate --shared-only).  Each is a gen row of TABLE and in no check key
# (keys.py).  dune-project and the opam files are not here: a build reads them, so they change with the facts that
# make them, in the same pull request.
SHARED = ("README.md", "index/STATUS.md", "index/PROOFS.md", "index/*.tsv", "analyses/harness-checks/checks.tsv",
          "analyses/known-issues.md", "projects/{project}/README.md")

# What only this repository has, which no release carries: the paths of TABLE's internal rows, a directory (a row that
# ends in /**) written with its trailing /, then INTERNAL_FILES, then INTERNAL_DIRS.  TABLE stays the one list of rows:
# tools/enroll/ci/inputs.py reads it as a literal.
# INTERNAL_FILES: the files the cut removes too that lie under a directory of another class, which TABLE cannot give a
# row of their own (a path matches exactly one row): the script of the render of the shared generated files after a
# merge, which only an internal line runs (index.yml); each publication renders its cut whole; the script of pr.yml's
# prove job (ci/prove-pr), which posts a check on this repository's pull requests; and the tests of those two scripts.
# INTERNAL_DIRS: the directories the cut removes whole whose files keep rows of their own (hand), so lint reads them as
# those rows say and not as internal paths (lint.run): the change ledgers (changes/), the reference book written for
# the people and agents who prove (docs/reference/), and the OSS Verify stream's operational tools (dev/stream/, which
# lint.internal_only reads as text no release carries).
INTERNAL_FILES = ("tools/oft/ci/regenerate-shared.sh", "tools/oft/tests/test_regenerate_shared.py",
                  "tools/oft/ci/prove-pr", "tools/oft/tests/test_prove_pr.py")
INTERNAL_DIRS = ("changes/", "docs/reference/", "dev/stream/")
INTERNAL = (tuple(p[:-len("**")] if p.endswith("/**") else p for cls, p in TABLE if cls == "internal")
            + INTERNAL_FILES + INTERNAL_DIRS)


def is_internal(rel):
    """Whether rel is, or is under, a path of INTERNAL: as TABLE's internal rows match it (a /** matches the directory
    itself too), one of INTERNAL_FILES, or under one of INTERNAL_DIRS."""
    return any(rel == p.rstrip("/") or (p.endswith("/") and rel.startswith(p)) for p in INTERNAL)

# Never tracked: filled by `oft fetch` (projects/<p>/bin/, and projects/<p>/unpatched-bin/ with --findings) or a build.
# findings/<p>/bin/ is where `oft fetch --findings` unpacked before the per-project layout: a checkout may still hold
# it, so it stays untracked while the tools read the old layout.
IGNORED_DIRS = ("_build", ".git")
IGNORED_PATTERNS = ("projects/*/bin/**", "projects/*/unpatched-bin/**", "findings/*/bin/**")

# A path segment that is a placeholder must not be one of these words,
# so that `projects/zlib/README.md` is not read as a harness named README.md,
# nor a project's patches/, unpatched-bin/ or unpatched.yaml as one.
_NOT_A_NAME = {"README.md", "project.yaml", "harness.yaml", "dune", "images", "source", "bin",
               "Images.v", "Symbols.v", "Statements.v", "Characterise.v", "Distribution.v", "lib", "provenance",
               "patches", "unpatched-bin", "unpatched.yaml"}


def _segment(seg, seen):
    """The regex of one pattern segment, with its trailing slash (a path is matched with a slash appended).  A
    placeholder already in `seen` matches the segment it matched before."""
    if seg.startswith("{") and seg.endswith("}"):
        name = seg[1:-1]
        if name in seen:
            return "(?P=%s)/" % name
        seen.add(name)
        not_a_name = "|".join(re.escape(n) for n in sorted(_NOT_A_NAME))
        return "(?P<%s>(?!\\.)(?!(?:%s)/)[^/]*)/" % (name, not_a_name)
    if "[" in seg:
        raise ValueError("unsupported path pattern segment %r" % seg)
    return "".join("[^/]*" if c == "*" else "[^/]" if c == "?" else re.escape(c) for c in seg) + "/"


@lru_cache(maxsize=None)
def _compile(pattern):
    seen = set()
    return re.compile("".join("(?:[^/]*/)*" if s == "**" else _segment(s, seen) for s in pattern.split("/")))


def match(pattern, rel):
    """The placeholder bindings if `rel` matches `pattern`, else None."""
    m = _compile(pattern).fullmatch(rel + "/")
    return None if m is None else m.groupdict()


# The patterns of TABLE by their first segment, which is a literal in each: a path is tried only against the patterns
# that start with its own first segment.
_BY_FIRST = {}
for _cls, _pat in TABLE:
    _first = _pat.split("/", 1)[0]
    if any(c in _first for c in "*?[{"):
        raise ValueError("a path pattern's first segment is a literal: %r" % _pat)
    _BY_FIRST.setdefault(_first, []).append((_cls, _pat, _compile(_pat)))


def classify(rel):
    """[(class, pattern, bindings)] of every pattern `rel` matches, in TABLE's order."""
    out = []
    for cls, pat, rx in _BY_FIRST.get(rel.split("/", 1)[0], ()):
        m = rx.fullmatch(rel + "/")
        if m is not None:
            out.append((cls, pat, m.groupdict()))
    return out


def ignored(rel):
    return any(p in IGNORED_DIRS for p in rel.split("/")) or any(match(p, rel) is not None for p in IGNORED_PATTERNS)


def is_gen(rel):
    m = classify(rel)
    return len(m) == 1 and m[0][0] == "gen"


def is_shared(rel):
    """Whether `rel` is one of the shared generated files (SHARED): rendered from the whole tree, so the line's
    render after a merge owns it and no pull request changes it."""
    return is_gen(rel) and any(match(p, rel) is not None for p in SHARED)
