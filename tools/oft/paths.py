"""Every path the repository may hold, and who owns it (lint rule `paths`).

Classes:
  hand     written and reviewed by maintainers, like code
  facts    exported facts: only a release pull request changes them
  gen      rendered by `oft generate`; CI renders again and compares
  contrib  where outside pull requests go: proofs and counterexamples

A path must match exactly one pattern.  In a pattern, `*` is one path
segment (with fnmatch wildcards inside it), `**` is any number of segments,
and `{project}`, `{harness}` and `{statement}` are one segment each, which
`paths` then checks against the facts.  A placeholder that appears twice in a
pattern matches the same segment both times.
"""
import re
from functools import lru_cache

TABLE = [
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
    ("hand", ".gitignore"),
    ("hand", ".gitattributes"),
    ("hand", "docs/*.md"),
    ("hand", "notes/*.md"),
    ("hand", "theories/*.v"),
    ("hand", "theories/dune"),
    ("hand", "toolchain/checker.Dockerfile"),
    ("hand", "toolchain/lps-core.paths"),
    ("hand", "toolchain/runner.Dockerfile"),
    ("hand", "tests/**"),
    ("hand", "tools/oft/**"),
    # the scripts that carry a merged theorem-labs/oss-verify enrollment into these facts (tools/enroll/README.md),
    # which enroll.yml and enroll-build.yml run; no check opens them, but keys.checker hashes them with the rest of
    # tools/, so a change to them changes every part's key (keys.py)
    ("hand", "tools/enroll/**"),
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
    # what an agent reads first, and the instructions it follows to add a proof
    ("hand", "AGENTS.md"),
    ("hand", ".claude/skills/adding-a-proof/SKILL.md"),
    # the facts review: the list of the files that need judgement or that the review agent loads (.github/CODEOWNERS),
    # the advisory AI review that facts-review.yml runs on a facts pull request, and what that review checks
    # (review.md)
    ("hand", ".github/CODEOWNERS"),
    ("hand", ".github/workflows/facts-review.yml"),
    ("hand", ".claude/skills/review-facts/SKILL.md"),
    ("hand", "review.md"),
    # the enrollment workflows: enroll.yml runs tools/enroll/ when an enrollment's checks pass and opens its facts pull
    # request, and enroll-build.yml builds the enrollment in a run of its own; this repository alone has them, and
    # `oft release-tree` removes them from the release
    ("hand", ".github/workflows/enroll.yml"),
    ("hand", ".github/workflows/enroll-build.yml"),
    # the released-proof index: proof-index.yml runs proof-index.py when main, ossv/recipes or ossv/candidates moves,
    # and pushes the branch proof-index; this repository alone has them, and `oft release-tree` removes them
    ("hand", ".github/workflows/proof-index.yml"),
    ("hand", ".github/proof-index.py"),
    # which proofs a release publishes, by fuzz target and statement; `oft release-tree` removes it from the release
    ("hand", "approvals.yaml"),
    # findings: library bugs found while proving, on the proof branch until they are public; a maintainer's or a
    # release pull request changes them, since a change of state can release the hold on a project
    ("hand", "findings/{project}/unpatched.yaml"),
    ("hand", "findings/{project}/{harness}/series"),
    ("hand", "findings/{project}/{harness}/*/finding.yaml"),
    ("hand", "findings/{project}/{harness}/*/input.bin"),
    ("hand", "findings/{project}/{harness}/*/control.bin"),
    ("hand", "findings/{project}/{harness}/*/*.patch"),
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
    # gen
    ("gen", "README.md"),
    ("gen", "dune-project"),
    ("gen", "index/STATUS.md"),
    ("gen", "index/PROOFS.md"),
    ("gen", "index/*.tsv"),
    ("gen", "analyses/harness-checks/checks.tsv"),
    ("gen", "analyses/known-issues.md"),
    ("gen", "projects/{project}/README.md"),
    ("gen", "projects/{project}/rocq-oss-fuzz-theorems-*.opam"),
    ("gen", "projects/{project}/{harness}/README.md"),
    ("gen", "projects/{project}/{harness}/dune"),
    ("gen", "projects/{project}/{harness}/Images.v"),
    ("gen", "projects/{project}/{harness}/Statements.v"),
    ("gen", "projects/{project}/{harness}/Characterise.v"),
    ("gen", "projects/{project}/{harness}/images/dune"),
    ("gen", "proofs/{project}/{harness}/{statement}/dune"),
    ("gen", "proofs/{project}/{harness}/lib/dune"),
    # contrib
    ("contrib", "proofs/lib/**"),
    ("contrib", "proofs/{project}/{harness}/{statement}/*.v"),
    ("contrib", "proofs/{project}/{harness}/{statement}/proof.yaml"),
    ("contrib", "proofs/{project}/{harness}/{statement}/classifier/**"),
    # a harness's proof library, shared by its proofs and compiled once (OssFuzzTheorems.Proofs.<p>.<h>.lib)
    ("contrib", "proofs/{project}/{harness}/lib/**/*.v"),
    # the build record of the binaries a harness's proofs are about: what built them is recipe/ (the slice of the recipe
    # that built them) or port/ (the OSS Verify port's project directory and the manifest its tools/check wrote)
    ("contrib", "proofs/{project}/{harness}/provenance/PROVENANCE.yaml"),
    ("contrib", "proofs/{project}/{harness}/provenance/PROVENANCE.md"),
    ("contrib", "proofs/{project}/{harness}/provenance/recipe/**"),
    ("contrib", "proofs/{project}/{harness}/provenance/port/manifest.yaml"),
    ("contrib", "proofs/{project}/{harness}/provenance/port/projects/{project}/**"),
    ("contrib", "proofs/{project}/{harness}/provenance/LICENSES/**"),
    ("contrib", "counterexamples/{project}/{harness}/{statement}/input.bin"),
    ("contrib", "counterexamples/{project}/{harness}/{statement}/control.bin"),
    ("contrib", "counterexamples/{project}/{harness}/{statement}/expect.yaml"),
]

# Never tracked: filled by `oft fetch` (projects/<p>/bin/, and findings/<p>/bin/ with --findings) or a build.
IGNORED_DIRS = ("_build", ".git")
IGNORED_PATTERNS = ("projects/*/bin/**", "findings/*/bin/**")

# A path segment that is a placeholder must not be one of these words,
# so that `projects/zlib/README.md` is not read as a harness named README.md.
_NOT_A_NAME = {"README.md", "project.yaml", "harness.yaml", "dune", "images", "source", "bin",
               "Images.v", "Statements.v", "Characterise.v", "Distribution.v", "lib", "provenance"}


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
