"""Every path the repository may hold, and who owns it (lint rule `paths`).

Classes:
  hand     written and reviewed by maintainers, like code
  facts    exported facts: only a release pull request changes them
  gen      rendered by `oft generate`; CI renders again and compares
  contrib  where outside pull requests go: proofs and counterexamples

A path must match exactly one pattern.  In a pattern, `*` is one path
segment (with fnmatch wildcards inside it), `**` is any number of segments,
and `{project}`, `{harness}` and `{statement}` are one segment each, which
`paths` then checks against the facts.
"""
import fnmatch

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
    ("hand", "analyses/harness-checks/README.md"),
    ("hand", ".github/workflows/pr.yml"),
    ("hand", ".github/workflows/weekly.yml"),
    ("hand", ".github/workflows/release.yml"),
    ("hand", ".github/workflows/release-check.yml"),
    ("hand", ".github/actionlint.yaml"),
    # what an agent reads first, and the instructions it follows to add a proof
    ("hand", "AGENTS.md"),
    ("hand", ".claude/skills/adding-a-proof/SKILL.md"),
    # facts
    ("facts", "release.yaml"),
    ("facts", "NOTICE"),
    ("facts", "CHANGELOG.md"),
    ("facts", "toolchain/toolchain.lock"),
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
    # the build record of the binaries a harness's proofs are about
    ("contrib", "proofs/{project}/{harness}/provenance/PROVENANCE.yaml"),
    ("contrib", "proofs/{project}/{harness}/provenance/PROVENANCE.md"),
    ("contrib", "proofs/{project}/{harness}/provenance/recipe/**"),
    ("contrib", "proofs/{project}/{harness}/provenance/LICENSES/**"),
    ("contrib", "counterexamples/{project}/{harness}/{statement}/input.bin"),
    ("contrib", "counterexamples/{project}/{harness}/{statement}/control.bin"),
    ("contrib", "counterexamples/{project}/{harness}/{statement}/expect.yaml"),
]

# Never tracked: filled by `oft fetch` or a build.
IGNORED_DIRS = ("_build", ".git")
IGNORED_PATTERNS = ("projects/*/bin/**",)

# A path segment that is a placeholder must not be one of these words,
# so that `projects/zlib/README.md` is not read as a harness named README.md.
_NOT_A_NAME = {"README.md", "project.yaml", "harness.yaml", "dune", "images", "source", "bin",
               "Images.v", "Statements.v", "Characterise.v", "Distribution.v", "lib", "provenance"}


def _match(pat, parts, binds):
    if not pat:
        return not parts
    head, rest = pat[0], pat[1:]
    if head == "**":
        return any(_match(rest, parts[i:], binds) for i in range(len(parts) + 1))
    if not parts:
        return False
    if head.startswith("{") and head.endswith("}"):
        if parts[0] in _NOT_A_NAME or parts[0].startswith("."):
            return False
        binds[head[1:-1]] = parts[0]
        return _match(rest, parts[1:], binds)
    return fnmatch.fnmatchcase(parts[0], head) and _match(rest, parts[1:], binds)


def classify(rel):
    """[(class, pattern, bindings)] of every pattern `rel` matches."""
    parts = rel.split("/")
    out = []
    for cls, pat in TABLE:
        binds = {}
        if _match(pat.split("/"), parts, binds):
            out.append((cls, pat, binds))
    return out


def ignored(rel):
    parts = rel.split("/")
    return any(p in IGNORED_DIRS for p in parts) or any(
        _match(p.split("/"), parts, {}) for p in IGNORED_PATTERNS)


def is_gen(rel):
    m = classify(rel)
    return len(m) == 1 and m[0][0] == "gen"
