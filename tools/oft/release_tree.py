"""oft release-tree: turn a checkout into the files of a release.

A release carries each proof of the checkout that nothing holds back.  This keeps the proof
directory of each statement whose fuzz target private_harnesses does not hold, whose project
facts.hold does not hold whole, that facts.hold does not hold back itself, and whose proof does
not refute (a Refutation.v), with its fuzz target's whole lib/ and build record (so a kept
statement carries everything in that lib/), and removes every other proof (a fuzz target's
whole proofs folder when it keeps none of its proofs).  Nothing reads approvals.yaml for which
proofs ship: it is a fact file, so facts.load reads it and rules.check checks it while it exists
(an invalid one stops the cut, as any error in the facts does), and the cut removes it with what
only this repository has (INTERNAL).  A fuzz target's
proofs folder is proofs/<project>/<harness>/ in the old layout and
projects/<project>/<harness>/proofs/ in the per-project one (layout.py); each fuzz target is
read in the layout its facts are in.

It leaves out what facts.hold holds back.  A project held whole (`release: private` in its
project.yaml, or a finding that holds it back) ships as a held project when OSS-Fuzz has it:
its project.yaml is rewritten to the held form (facts.held_form) and its page is rendered from
that, and everything else of it goes (the rest of projects/<p>/, its counterexamples,
patches/<p>/ or projects/<p>/patches/, notes/<p>.md, and its proofs).  A held
page says only that the project is held, so it tells a reader nothing the OSS-Fuzz issue does
not.  A project held whole that OSS-Fuzz does not have is removed whole.  An enrolled project
(`enrolled: true`) whose findings are all open keeps its page and its other statements, and
only the statements
those findings break are held back (with each held agreement's bound, decidability and
classifier statements, and each twin of a held statement), with their proofs and
counterexamples.  A fuzz target that a project's
private_harnesses holds goes whole while the rest of the project publishes: every folder of it
that layout.py gives, in both layouts (projects/<p>/<h>/, and proofs/<p>/<h>/,
counterexamples/<p>/<h>/ and findings/<p>/<h>/), with each proof of it;
its entry in project.yaml, with the comment lines directly above it; and, in each build record
the release keeps, the files of it in the copy of the port (provenance/port/) and the lines and
rows there that name it (disclosure.held_match).  The field private_harnesses goes from each
project.yaml, with its comments.  Where such a project's port is this repository's internal copy,
project.yaml (build.oss_verify) and each build record the release keeps (port) name the port
repository `none`, with the port commit's id, so no file of the release names this repository.
These edits are line edits: every other byte of the file stays.  Either way
release.yaml carries the counts and oss_fuzz.projects of the cut, and an image_libraries
entry no remaining build links goes.  It removes every finding entirely: findings/, and each
projects/<p>/<h>/findings/ and projects/<p>/unpatched.yaml (an undisclosed bug's record,
reproducer and patch never ship),
and what only this repository has (INTERNAL, the entries of lint.LINT_ONLY_INTERNAL,
paths.py's list and SKILLS written out, whose comment says why each is there; a directory is
removed whole, and never read for what is held back); it rewrites
tools/oft/lint-exceptions.yaml without each entry whose path, in either layout's form, is at or
under a path the cut removes (an entry left for it would be unused, and a lint finding in the
release), and without every licence-pending entry, so a release carries none (the lines above its
`exceptions` key stay as written); it writes .gitignore without the block of the shared
generated files (GITIGNORE_MARKER and the line of each pattern of paths.SHARED under it, which
keep them out of this repository's commits: cut_gitignore), so a release commits what its last
render writes, and a .gitignore with no such block stays as it is; and it renders
the generated files again, so the statuses in the pages and the index say what the release
holds.  It names what it holds back (each project a finding holds back whole, each statement an
open finding holds back, each fuzz target of private_harnesses, and each refuting proof of a
fuzz target that ships), and each fuzz target
whose lib/ it keeps while removing some of its statement directories (that lib/ may hold
their proofs).  It writes AGENTS.md without each marked block (from a line that holds
BEGIN-INTERNAL through the next line that holds END-INTERNAL).  Everything else (the facts,
CHANGELOG.md among them, counterexamples) is left
as it is, so the release's CHANGELOG section must describe only what the release carries.

It refuses, and changes nothing, when the facts have an error; the checkout holds a symbolic
link outside an ignored path (proofs/, .github/, .claude/ and tools/ themselves among them, as
the cut would remove through them), or a path the cut removes is one (an ignored one, such as
a held project's bin/, among them); a fuzz target's proofs folder holds a file beside its statement
directories (its generated dune file aside), a file under the old layout's proofs/ is in no fuzz target's
proofs folder (proofs/lib/ among them, which no row admits), or a kept statement
directory holds a file other than Proof.v, proof.yaml, its generated dune and the witness
record beside them, <statement>.witness.json; git tracks a
file at an ignored path; tools/publish/private-harnesses.txt is missing or does not give the
fuzz targets that the private_harnesses fields hold (a tree with tools/publish/ only); a line
edit for a held fuzz target cannot keep a file as the cut's facts have it; AGENTS.md holds a
marker line with no partner (a start inside a block, an end outside one, a start never ended,
or both texts on one line), or holds a marked block and is not UTF-8 text; the facts as the
release will have them have an error; .gitignore holds the marker line of the block of the shared
generated files but not that block (a second marker line, fewer lines under it than paths.SHARED
has, or a line under it that is not the next of them), or holds the marker and is not UTF-8; a
file the release keeps or writes, the rewritten lint-exceptions.yaml and .gitignore included,
discloses what is held back or names this internal repository (disclosure); or the generated
files are not current, the shared ones apart (paths.SHARED:
the line's render owns them, and this run's final render writes them into the cut).  Every check
runs before the first change.  It rewrites the checkout in place: run it in a scratch checkout.
"""
import copy
import glob
import io
import os
import re
import shutil
import subprocess
import sys

import yaml

from . import disclosure, facts, generate, layout, lint, paths, rules, schema, yamlio

# a project's folder name, as the facts' schema allows it: the first column of each row of failure_handlers.tsv
PROJECT_NAME = re.compile(schema.SCALARS["project-name"])

# What only this repository has, which the cut removes: each entry of lint.LINT_ONLY_INTERNAL (what only this
# repository has that lint alone judges, since a row of paths.TABLE would re-key every unit), then the INTERNAL of
# paths.py (TABLE's internal rows, then its INTERNAL_FILES and INTERNAL_DIRS), then SKILLS (below), written out here as
# a literal tuple equal to them (test_release_tree.test_every_internal_path_is_one_the_cut_removes).  SKILLS stay last:
# the publishing scan's reviewed exceptions match the tuple's text around their two lines, closing parenthesis
# included.  It is written
# out, not imported, because the release gate reads this file's INTERNAL from its syntax tree, as an assignment of a
# literal tuple of strings, and
# skips an import without a word (its R17 row: a published tree is a release-tree cut;
# test_the_release_gate_reads_every_internal_path_from_release_tree_py replays its reading).  An entry that ends in / is
# a directory, removed whole.  What each is: the list of the files that need judgement (CODEOWNERS), the automated
# facts review of a pull request and its criteria (the review runs on this repository's identity), and approvals.yaml,
# this repository's list of approved proofs, which its rules check but which does not decide the proofs a release
# carries; the pipeline that turns an enrollment into facts and its approvals (enroll.yml, enroll-build.yml,
# the workflows that start its redo runs, facts-refresh.yml and hold-state.yml, enroll-retry.yml, approvals-watch.yml
# and the tools/enroll/ directory they run), which a reader of a proof never needs; the released-proof index's workflow
# and builder, which push to this repository's branch proof-index, and the trigger that ossv/candidates carries to start
# that workflow; the render of the shared generated files after a merge (index.yml and regenerate-shared.sh), which
# only an internal line has: each publication renders its cut whole; the publishing workflows and the tools/publish/
# directory they run; the shared dune store's daily retention (store-retention.yml), which runs on this repository's
# identity against a bucket only it reaches; the change ledgers (changes/: oft change-ledger), whose sessions, costs
# and journals are this repository's own records; the reference book (docs/reference/: the worker briefs and the rules
# a proof's author follows, docs/reference/README.md), which is written for the people and agents who prove, not for a
# proof; and dev/stream/, the OSS Verify stream's operational tools (dev/stream/README.md), which run the stream rather
# than check a proof and which name this company's machines, buckets and sessions.  That last cut is what lets
# lint.internal_only read dev/stream/ as text no reader outside this company sees: the two lists are held to each other
# by tools/oft/tests/test_lint.py; and the `theorem prove` workflow (prove.yml) and its script (ci/prove-pr): the
# workflow posts a check on this repository's own pull requests with the workflow's own token, and a reader of a proof
# never needs it.  The tests that run regenerate-shared.sh, prove-pr and prove.yml go with them (a released
# test finds every file it needs: test_release_tree.ReleasedTests), and so does the test of disclosure.py's held-entry
# rule, which reads tools/publish/held-match-cases.tsv, a file the cut removes with tools/publish/.
# Last come the two skill directories of SKILLS: the porting skill
# (.claude/skills/porting-released-proofs/), which tells a prover how to find the proof a new statement ports from
# through this repository's unreleased branches, its search tools and an outside delivery, none of which a release
# carries, and the clean-room skill (.claude/skills/clean-room-restatement/), the internal method of a clean-room
# rewrite, which a reader of a proof never needs.  paths.py does not name them: it is part of the checker, whose ids
# are in every key (keys.py), so lint admits their files alone (lint.LINT_ONLY_HAND).  First of all, the entries of
# lint.LINT_ONLY_INTERNAL, a directory with its trailing / and a file as it is: dev/enroll/, the enrollment scripts'
# place outside tools/, where they move from tools/enroll/ (OSSV-276; paths.TABLE's tools/enroll/** row, and so
# tools/enroll/ here, then match nothing until paths.py next changes), .github/rekey-window, the file whose bytes
# say whether a re-key window is open, which pr.yml's rekey job reads on this repository's main and which a release,
# having no such window, never carries (OSSV-413), dev/gateway-model/, the model gateway's formal model, which no
# release carries (OSSV-498), .github/workflows/gateway-model.yml, which builds and checks it, dev/evals/, the tools
# that run this repository's evals, which no release carries (OSSV-643), .github/workflows/paired-run.yml, which
# runs the paired run's tests, the two files of OSSV-299, the two files of the CI reviewer,
# .github/workflows/held-refscan.yml, the daily scan of the public refs for held fuzz targets, which the pull request of
# Dispatch issue OSSV-377 adds, .github/workflows/verdicts.yml, the one writer of the store of build-cluster results
# (Dispatch issue OSSV-832), which no check opens and no release carries, and last .github/README.md, the page GitHub
# shows on this repository's front page in place of the root README.md, which OSSV-668 stops committing; no release
# carries the page, since a release keeps its own rendered README.md.  The two files of OSSV-299 are
# .github/workflows/rocq-release.yml, the shared Rocq build
# service's release test, the one workflow whose token its release-test account accepts (INFRA-4207), and
# .github/theorem-rule-classes.tsv, the table of memory classes that the service's client `theorem check` reads
# (OSSV-654), which no release needs: no public check reads it, since the public checks run the public README's command
# with no build service, and a commit with no table gives every action `std`, which can make an action fail at its
# memory limit but never make a check pass.  The two files of the CI reviewer, which the pull request of Dispatch issue
# OSSV-774 adds, are .github/workflows/ci-review.yaml, the caller that runs agent-infra's CI reviewer on each pull
# request that Legion does not run, and .github/ci-review.md, the rules file that holds this repository's own check for
# that reviewer.  The public repository can use neither: the caller calls a workflow of agent-infra, and the rules file
# holds this repository's own check.  So no release carries them.
INTERNAL = (
    "dev/enroll/",
    ".github/rekey-window",
    "dev/gateway-model/",
    ".github/workflows/gateway-model.yml",
    "dev/evals/",
    ".github/workflows/paired-run.yml",
    ".github/workflows/rocq-release.yml",
    ".github/theorem-rule-classes.tsv",
    ".github/workflows/ci-review.yaml",
    ".github/ci-review.md",
    ".github/workflows/held-refscan.yml",
    ".github/workflows/verdicts.yml",
    ".github/README.md",
    "approvals.yaml",
    ".github/CODEOWNERS",
    ".github/workflows/facts-review.yml",
    ".claude/skills/review-facts/SKILL.md",
    "review.md",
    ".github/workflows/enroll.yml",
    ".github/workflows/enroll-build.yml",
    ".github/workflows/facts-refresh.yml",
    ".github/workflows/hold-state.yml",
    ".github/workflows/enroll-retry.yml",
    ".github/workflows/approvals-watch.yml",
    "tools/enroll/",
    ".github/workflows/proof-index.yml",
    ".github/proof-index.py",
    ".github/workflows/proof-index-trigger.yml",
    ".github/workflows/index.yml",
    ".github/workflows/prove.yml",
    ".github/workflows/publish-request.yml",
    ".github/workflows/publish.yml",
    ".github/workflows/publish-gate.yml",
    "tools/publish/",
    ".github/workflows/store-retention.yml",
    "tools/oft/ci/regenerate-shared.sh",
    "tools/oft/tests/test_regenerate_shared.py",
    "tools/oft/tests/test_held_match.py",
    "tools/oft/ci/prove-pr",
    "tools/oft/tests/test_prove_pr.py",
    "tools/oft/tests/test_prove_workflow.py",
    "changes/",
    "docs/reference/",
    "dev/stream/",
    ".claude/skills/porting-released-proofs/",
    ".claude/skills/clean-room-restatement/",
)

# the directories of INTERNAL that paths.py does not name (lint.LINT_ONLY_HAND admits their files): the release gate
# reads only INTERNAL above, so these are written there too
SKILLS = (".claude/skills/porting-released-proofs/", ".claude/skills/clean-room-restatement/")

# the files a kept statement directory may hold: its proof, its record, and the generated dune (paths.py), and the
# witness record beside them, `<statement>.witness.json` (OSSV-360).  The record is kept, never removed:
# it is worth something only inside the tree digest the audit computes, and a release that cut it would leave that
# audit reading "no record" for a proof that has one.  It cannot be a name here, because its stem is the statement,
# so it is matched by suffix -- the same `endswith` that paths.py's `*.witness.json` row is, so the two readers of
# this one file never disagree about it.
STATEMENT_FILES = ("Proof.v", "proof.yaml", "dune")
WITNESS_SUFFIX = ".witness.json"


def _statement_file(f):
    """Whether f, a name in a kept statement directory, is a file a release carries there."""
    return f in STATEMENT_FILES or f.endswith(WITNESS_SUFFIX)


PARTIAL = "kept the lib/ of %s, while removing some of its statement directories: that lib/ may hold their proofs"


def _inside_a_cut(rel):
    """Whether `rel` is inside an INTERNAL entry this cut removes whole, rather than being that entry itself.

    The gate below exists so that no facts path the cut reads can point out of the checkout; it runs before
    `facts.load`, which is why it cannot wait for the cut.  A file inside `dev/stream/` or `tools/enroll/` is
    read by nothing here and is deleted whole by `shutil.rmtree`, which unlinks a child link rather than
    following it, so a link there can take the cut nowhere.  Gating it instead refuses the whole cut: with
    `dev/stream/lane/`'s three mirrored links in the tree, `oft release-tree` exited 1 and changed nothing, so
    the first release cut from a main carrying them would have failed (the review of pull request 669, B1).
    The entry itself is still gated: a link AT `dev/stream` is what rmtree would follow.

    The directories of INTERNAL meet that test, and all are meant: `dev/stream/`, `tools/enroll/`, `dev/enroll/`,
    `dev/gateway-model/`, `dev/evals/`, `tools/publish/`, `changes/`, `docs/reference/` and the
    two skill directories of SKILLS.  None is read by `facts.load`, `rules.check` or any later step of the cut --
    `tools/enroll/` and `dev/enroll/` are the enrollment scripts that enroll.yml runs (they move from the first to the
    second, OSSV-276), `dev/gateway-model/` the model gateway's formal model (OSSV-498), `dev/evals/` the tools that
    run this repository's evals (OSSV-643), `tools/publish/`
    the publication's own tools, `changes/` the change ledgers, `docs/reference/` the reference book and the skill
    directories agents' instructions, which this
    tool only deletes -- and each is removed by one `shutil.rmtree`.  The one INTERNAL entry this tool reads is
    `approvals.yaml`, a fact file: `facts.load` reads it and `rules.check` checks it while it exists, and no
    step of the cut reads it for the proofs the cut keeps; the rest, `.github/CODEOWNERS` and `review.md` among them,
    are only listed and deleted.  The other entries are files, not directories, so no path is ever "inside" them and the
    gate still covers every one of them; that is why this skip is of a path inside a cut entry rather than of
    INTERNAL itself, and why the cut cannot simply run before the gate.  A link under `tools/enroll/` is still
    refused by `oft lint`, whose LINKS_ALLOWED is `dev/stream/lane/` alone, so it cannot reach main in the first
    place: the two rules answer different questions and both are kept.  A directory entry of INTERNAL ends in `/`
    (as INTERNAL in paths.py writes it), and an entry is compared without it, so `dev/stream` and `dev/stream/` read
    alike.
    """
    return any(rel.startswith(entry.rstrip("/") + "/") for entry in INTERNAL)


def checkout_links(root):
    """Every symbolic link in root outside an ignored path (paths.ignored) and outside what the cut removes whole
    (_inside_a_cut), before facts.load can read through one."""
    found = []
    for d, dirs, files in os.walk(root):
        rd = os.path.relpath(d, root)
        rd = "" if rd == "." else rd + os.sep
        found += [rd + n for n in dirs + files
                  if os.path.islink(os.path.join(d, n))
                  and not paths.ignored((rd + n).replace(os.sep, "/"))
                  and not _inside_a_cut((rd + n).replace(os.sep, "/"))]
        dirs[:] = [x for x in dirs if not paths.ignored((rd + x).replace(os.sep, "/"))]
    return sorted(found)


def tracked_ignored(tree):
    """The files git tracks at an ignored path (paths.ignored), which the checks above do not read: [] when the
    checkout is not a git work tree."""
    if not os.path.exists(tree.path(".git")):
        return []
    r = subprocess.run(["git", "-C", tree.root, "ls-files", "-z"], capture_output=True)
    if r.returncode:
        return ["git ls-files failed: %s" % r.stderr.decode("utf-8", "replace").strip()]
    return sorted(rel for rel in r.stdout.decode("utf-8", "surrogateescape").split("\0") if rel and paths.ignored(rel))


def tools_problems(tree, checkout=None):
    """Why tools/oft may not be published on its own, ahead of a release, as the runner image publishes a copy of it
    (.github/workflows/images.yml): [] when it may.  These are the rules of `oft release-tree` that reach a file under
    tools/oft: facts with an error, which may hide what is held back; and a file under tools/oft that discloses what
    facts.hold holds back, by its bytes or its path (disclosure.search, the release's own search).  A file at an
    ignored path is a problem of its own here: the search does not read it, and a copy of the directory takes it
    whether or not git tracks it.  The facts are tree's; the tools/oft judged is checkout's (a directory, another
    checkout such as the public repository's), else tree's own."""
    rules.check(tree)
    if tree.errors:
        return ["the facts have an error, so what a release holds back is not known: %s" % e for e in tree.errors]
    root = tree.root if checkout is None else checkout
    tools = os.path.join(root, "tools")
    skip = [n for n in os.listdir(root) if n != "tools"]
    skip += ["tools/" + n for n in (os.listdir(tools) if os.path.isdir(tools) else []) if n != "oft"]
    try:
        needles = disclosure.needles(tree, facts.hold(tree))
    except facts.BoundedFileError as e:
        return ["a holding finding's evidence cannot be read within its cap, so what may not ship is not known: %s" % e]
    out = ["%s names %s" % (rel, label) for rel, label in disclosure.search(root, needles, skip, {})]
    for d, dirs, files in os.walk(os.path.join(tools, "oft")):
        for name in sorted(dirs + files):
            rel = os.path.relpath(os.path.join(d, name), root).replace(os.sep, "/")
            if paths.ignored(rel):
                out.append("%s: an ignored path, so it is not read, and a copy of tools/oft takes it" % rel)
    return out


LINT_EXCEPTIONS = os.path.join("tools", "oft", "lint-exceptions.yaml")
# The packer's own measured tables, which name a unit per row (pack.SWEEP_TIMES, pack.FARM_CHECKS).  The cut
# rewrites the file without the rows of units it does not keep: a row for a held project's fuzz target would say
# in the release that the target exists, which is the one thing a hold withholds, and a row for a unit the
# release does not carry weighs nothing there anyway.
PACK = os.path.join("tools", "oft", "pack.py")
PACK_TABLES = ("SWEEP_TIMES = (", "FARM_CHECKS = (")
PACK_ROW = re.compile(r'^    \("([^"/]+/[^"]+)", ')


def cut_pack_readings(tree, keep):
    """(text, the units dropped): tools/oft/pack.py without each row of its measured tables whose unit is not in
    `keep`, the units the cut carries.  Only the lines between a table's opening `NAME = (` and its closing `)`
    are read, and each of those must be a row naming a unit, so a table that stops looking like one stops the
    cut here rather than shipping rows nobody filtered.  None when no row is dropped."""
    p = tree.path(PACK)
    if not os.path.isfile(p):
        return None
    with open(p, encoding="utf-8") as f:
        lines = f.read().splitlines(True)
    out, gone, table = [], [], None
    for n, line in enumerate(lines, 1):
        if table is None:
            out.append(line)
            if line.startswith(PACK_TABLES):
                table = line
            continue
        if line.startswith(")"):
            out.append(line)
            table = None
            continue
        m = PACK_ROW.match(line)
        if m is None:
            raise ValueError("%s:%d: %r is in %s and is no row naming a unit"
                             % (PACK, n, line.strip(), table.split(" =")[0]))
        if m.group(1) in keep:
            out.append(line)
        else:
            gone.append(m.group(1))
    return ("".join(out), sorted(set(gone))) if gone else None


# analyses/failure-handlers/failure_handlers.tsv, the table of the fuzz targets whose failure_handlers is none: one
# row a unit (its project and harness columns), which facts.py writes for a private project's fuzz targets too.  The
# cut takes out the rows of the units the tree has and the release does not carry, and every row of a project held
# back whole, whether the tree still has that fuzz target or not (facts.py never removes a row): such a row would name
# in the release the project, its fuzz target and the evidence read from its private source.  A row of a unit the
# tree no longer has, of a project that ships, stays, as it always has.  The table is read as the publication gate
# (tools/publish/verify, handler_rows_held) reads it, records split at every line break, and the cut refuses what the
# gate would refuse, so a tree the cut accepts makes a release the gate accepts.
HANDLERS = os.path.join("analyses", "failure-handlers", "failure_handlers.tsv")
HANDLERS_HEADER = "project\tharness\t"


def cut_handler_rows(tree, withheld, hidden):
    """(text, the units dropped): failure_handlers.tsv without each row whose unit (project/harness, its first two
    columns) is in `withheld`, the units of the tree the cut does not carry, or whose project is in `hidden`, the
    projects held back whole.  The header stays.  A table that stops looking like one stops the cut rather than
    ship rows nobody filtered (ValueError): a header that is not HANDLERS_HEADER, a line break other than LF, or a
    line whose first column is not a project name (schema's project-name) or that has no harness.  None when no row is
    dropped."""
    p = tree.path(HANDLERS)
    if not os.path.isfile(p):
        return None
    with open(p, encoding="utf-8", newline="") as f:
        text = f.read()
    breaks = sorted({c for c in text if c != "\n" and c.splitlines() == [""]})
    if breaks:
        raise ValueError("%s: line breaks other than LF: %s" % (HANDLERS, ", ".join("U+%04X" % ord(c) for c in breaks)))
    lines = text.splitlines(True)
    if not lines or not lines[0].startswith(HANDLERS_HEADER):
        raise ValueError("%s:1: the header is not %r" % (HANDLERS, HANDLERS_HEADER + "..."))
    out, gone = [lines[0]], []
    for n, line in enumerate(lines[1:], 2):
        project, harness = (line.rstrip("\n").split("\t") + ["", ""])[:2]
        if not PROJECT_NAME.fullmatch(project) or not harness:
            raise ValueError("%s:%d: %r is no row naming a unit" % (HANDLERS, n, line.strip()[:80]))
        if project in hidden or "%s/%s" % (project, harness) in withheld:
            gone.append("%s/%s" % (project, harness))
        else:
            out.append(line)
    return ("".join(out), sorted(set(gone))) if gone else None


# AGENTS.md, what an agent reads first
AGENTS = "AGENTS.md"


def strip_internal_blocks(text):
    """text without each marked block of AGENTS.md.  A block is text for this repository only; it runs from a line that
    holds BEGIN-INTERNAL (a start) through the next line that holds END-INTERNAL (an end), in those capitals, anywhere
    in the line.  The text is split at every line break that str.splitlines knows, and each removed line goes with its
    own line ending, so an end line that is the last line with no line ending goes too, and a text that is one block
    only gives "".  Every other line stays as it is.  A marker line with no partner is a ValueError: a line that holds
    both texts, a start inside a block, an end outside one, or a start never ended.  The reading is line for line that
    of agents_md_cut_ok in tools/publish/verify and must stay so, for a tree the cut accepts must make an AGENTS.md
    that the publication gate accepts; AgentsMdCut in tools/publish/tests/test_verify.py runs both on the same texts to
    hold the two equal."""
    kept, start = [], None   # start: the line number of the start of the open block, None outside a block
    for n, line in enumerate(text.splitlines(True), 1):
        begins, ends = "BEGIN-INTERNAL" in line, "END-INTERNAL" in line
        if begins and ends:
            raise ValueError("line %d holds both BEGIN-INTERNAL and END-INTERNAL" % n)
        if begins:
            if start is not None:
                raise ValueError("line %d starts a block inside the block that line %d starts" % (n, start))
            start = n
        elif ends:
            if start is None:
                raise ValueError("line %d ends a block that no line starts" % n)
            start = None
        elif start is None:
            kept.append(line)
    if start is not None:
        raise ValueError("line %d starts a block that no line ends" % start)
    return "".join(kept)


def cut_agents_md(tree):
    """AGENTS.md as the release has it (strip_internal_blocks), or None when there is nothing to write: no regular file
    there, or a file with no marked block, whatever its bytes.  A link there is not read (checkout_links has refused it
    already).  The file is read as bytes and decoded as UTF-8 with surrogateescape, as agents_md_cut_ok reads it, so a
    line break other than LF stays as it is.  A ValueError when strip_internal_blocks refuses the text, and when the
    file holds a marked block and is not UTF-8 text, which the cut cannot write: the N of its `byte N` is the offset,
    counted from 0, of the first byte that is not UTF-8."""
    p = tree.path(AGENTS)
    if not os.path.isfile(p) or os.path.islink(p):
        return None
    with open(p, "rb") as f:
        data = f.read()
    text = data.decode("utf-8", "surrogateescape")
    cut = strip_internal_blocks(text)
    if cut == text:
        return None
    try:
        data.decode("utf-8")
    except UnicodeDecodeError as e:
        raise ValueError("it holds a marked block and is not UTF-8 text (byte %d), so the cut cannot write it"
                         % e.start) from None
    return cut


# The block of the shared generated files in .gitignore: the marker line GITIGNORE_MARKER, then SHARED_IGNORES, one
# line for each pattern of paths.SHARED ("/" and its pattern, a project's folder as *), in that order.  OSSV-668 adds
# the block to .gitignore, so that main commits none of those files: ./oft generate --shared-only renders them.  A
# release commits the files its last render writes, so the cut writes .gitignore without the block (cut_gitignore).
# tools/publish/verify holds a copy of the marker and the lines, to accept that change in a publication
# (gitignore_block_dropped), and tools/publish/tests/test_verify.py holds the two equal.  The marker is a literal
# (adjacent string literals, never an expression), since that test reads it with ast.literal_eval from this file's
# syntax tree.
GITIGNORE = ".gitignore"
GITIGNORE_MARKER = ("# The shared generated files (tools/oft/paths.py SHARED): main holds none; ./oft generate "
                    "--shared-only renders them, and oft release-tree drops these lines from a release's copy.")
SHARED_IGNORES = tuple("/" + p.replace("{project}", "*") for p in paths.SHARED)


def cut_gitignore(tree):
    """.gitignore's text without the block of the shared generated files: the marker line and the lines of
    SHARED_IGNORES under it go, each with its own line ending, and every other byte stays, a blank line next to the
    block included; a block that is the whole file leaves it empty.  The file is read as its bytes are, and a line is
    compared without its line ending (str.splitlines).  None when there is nothing to write: no .gitignore, no marker
    in its bytes (whatever they are), or no line that is the marker.  A block that is not the one the cut removes
    stops the cut (ValueError, naming the line): the marker in a file that is not UTF-8 (the line of the first byte
    that is not), a second marker line, fewer lines under the marker line than SHARED_IGNORES has (the marker line),
    or a line under it that is not the next of them."""
    p = tree.path(GITIGNORE)
    if not os.path.isfile(p):
        return None
    with open(p, "rb") as f:
        data = f.read()
    if GITIGNORE_MARKER.encode("utf-8") not in data:
        return None
    try:
        text = data.decode("utf-8")
    except UnicodeDecodeError as e:
        # the bytes before e.start are UTF-8: a character after them stands on the line of the byte at e.start
        n = len((data[:e.start].decode("utf-8") + "-").splitlines())
        raise ValueError("%s:%d: byte 0x%02x is not UTF-8, in a file that holds the marker of the shared generated "
                         "files" % (GITIGNORE, n, data[e.start]))
    lines = text.splitlines(True)
    bare = text.splitlines()
    at = [n for n, line in enumerate(bare) if line == GITIGNORE_MARKER]
    if not at:
        return None
    if len(at) > 1:
        raise ValueError("%s:%d: a second marker line of the shared generated files (the first is line %d)"
                         % (GITIGNORE, at[1] + 1, at[0] + 1))
    start, end = at[0], at[0] + 1 + len(SHARED_IGNORES)
    under = bare[start + 1:end]
    if len(under) < len(SHARED_IGNORES):
        raise ValueError("%s:%d: the marker line of the shared generated files has %d line(s) under it, not the %d of "
                         "the block" % (GITIGNORE, start + 1, len(under), len(SHARED_IGNORES)))
    for n, (read, wanted) in enumerate(zip(under, SHARED_IGNORES), start + 2):
        if read != wanted:
            raise ValueError("%s:%d: %r is under the marker line of the shared generated files, where the block has %r"
                             % (GITIGNORE, n, read, wanted))
    return "".join(lines[:start] + lines[end:])


def _under(rel, tops):
    rel = rel.replace(os.sep, "/")
    return any(rel == t or rel.startswith(t + "/") for t in (t.replace(os.sep, "/").rstrip("/") for t in tops))


def _canonical(rel):
    """rel, a file or a folder, in the per-project layout: where layout.canonical moves it, an old-layout folder whose
    files move (proofs/<p>/<h>, counterexamples/<p>/<h>, patches/<p>) going where they go."""
    rel = rel.replace(os.sep, "/").rstrip("/")
    if layout.moved(rel):
        return layout.moved(rel)
    inside = layout.moved(rel + "/-")
    return inside[:-len("/-")] if inside else rel


def _cut_entry(e, goes):
    """Why the release does not carry lint-exceptions.yaml's entry e, as the text that names it, or None: it is a
    licence-pending entry (a release carries none: lint.apply_pending), or its path is at or under a path the cut
    removes (goes)."""
    if e.get("rule") == lint.PENDING:
        return "%s %s" % (lint.PENDING, e.get("unit"))
    if goes(e["path"]):
        return e["path"]
    return None


def cut_lint_exceptions(tree, cut):
    """(text, dropped entries): tools/oft/lint-exceptions.yaml without each entry for a file the cut removes
    (_cut_entry), in either layout (lint matches an entry through layout.canonical), which the
    release does not carry (an entry left for it would be unused, and a finding in the public tree), and which may
    name what is held back, and without every licence-pending entry.  Every line above the `exceptions` key (the
    leading comment, the schema) is kept as
    written; the list, and anything after it, is written again in the canonical form, so a comment among the entries
    is not kept (an entry's why belongs in its reason).  None when no entry is dropped."""
    p = tree.path(LINT_EXCEPTIONS)
    if not os.path.isfile(p):
        return None
    with open(p, encoding="utf-8") as f:
        text = f.read()
    data = yamlio.load(text, LINT_EXCEPTIONS)
    entries = data.get("exceptions") or []
    moved = [_canonical(c) for c in cut]

    def goes(path):
        return _under(path, cut) or _under(layout.canonical(path), moved)

    gone = [g for g in (_cut_entry(e, goes) for e in entries) if g is not None]
    if not gone:
        return None
    keys = yaml.compose(text, Loader=yamlio.StrictLoader).value
    line = next(k.start_mark.line for k, _ in keys if k.value == "exceptions")
    rest = {k.value: data[k.value] for k, _ in keys if k.start_mark.line >= line}
    rest["exceptions"] = [e for e in entries if _cut_entry(e, goes) is None]
    return "".join(text.splitlines(True)[:line]) + yamlio.dump(rest), gone


def _public_release(tree, public):
    """release.yaml as the release carries it, from the cut facts `public`: its counts and oss_fuzz.projects, and
    without an image_libraries entry no build of the cut links.  None when none of that changes anything."""
    r = copy.deepcopy(tree.release)
    if not r:
        return None
    harnesses = list(public.harnesses())
    r["counts"] = rules.counts(public)
    r["oss_fuzz"]["projects"] = public.oss_fuzz_project_count()

    known = r.get("image_libraries")
    if known is not None:
        linked = {n for h in harnesses for n in facts.image_libraries(h)}
        r["image_libraries"] = {n: v for n, v in known.items() if n in linked}
        if not r["image_libraries"]:
            del r["image_libraries"]
    return None if r == tree.release else r


def private_harnesses_problem(tree, hold):
    """Why tools/publish/private-harnesses.txt (generate.PRIVATE_HARNESSES) of the checkout does not give the held
    fuzz targets of its private_harnesses fields, or None.  The cut reads the fields.  Every other reader of the held
    entries (tools/publish/ and dev/stream/) reads the file, so the two must agree before the cut removes the file.
    The expected text is generate's own rendering of the file (generate.private_harnesses_txt) from HOLD, the
    checkout's facts.hold.  Only a tree with tools/publish/ has the file, as generate.render_all writes it there alone.
    The internal tree always has tools/publish/, so a tree without it has no file to compare."""
    if not os.path.isdir(tree.path(os.path.dirname(generate.PRIVATE_HARNESSES))):
        return None
    want = generate.private_harnesses_txt(tree, hold)
    fields = ", ".join(want.split()) or "no fuzz target"
    rel = generate.PRIVATE_HARNESSES
    if not os.path.lexists(tree.path(rel)):
        return "%s is missing, and the private_harnesses fields hold %s: run ./oft generate" % (rel, fields)
    try:
        got = facts.read_bounded(tree.path(rel), facts.MAX_BYTES).decode("utf-8", "replace")
    except facts.BoundedFileError as e:
        return "%s cannot be read: %s" % (rel, e)
    if got != want:
        return ("%s lists %s, and the private_harnesses fields hold %s: run ./oft generate"
                % (rel, ", ".join(got.split()) or "no fuzz target", fields))
    return None


def _last_line(node):
    """The last line (0-based) that holds a part of the YAML node: a scalar or a flow collection ends at its end mark
    (the line before it when that mark is at the start of a line), and a block collection ends with its last item."""
    if isinstance(node, yaml.ScalarNode) or node.flow_style or not node.value:
        end = node.end_mark
        return end.line - 1 if end.column == 0 and end.line > node.start_mark.line else end.line
    last = node.value[-1]
    return _last_line(last[1] if isinstance(node, yaml.MappingNode) else last)


def _comment(line):
    """Whether line is a YAML comment line: a `#` after blanks alone."""
    return line.lstrip().startswith("#")


def _comments_above(lines, start, floor):
    """The first line of the comment lines directly above line start, not above line floor: start when there is
    none.  A blank line ends them."""
    while start > floor and _comment(lines[start - 1]):
        start -= 1
    return start


def _set_scalar(lines, node, value):
    """Write value in place of the scalar node in lines (the text's lines), every other character as it was.
    ValueError when the scalar is not on one line."""
    if not isinstance(node, yaml.ScalarNode) or node.start_mark.line != node.end_mark.line:
        raise ValueError("its value is not one scalar on one line")
    n, line = node.start_mark.line, lines[node.start_mark.line]
    lines[n] = line[:node.start_mark.column] + value + line[node.end_mark.column:]


def cut_project_yaml(text, names, port_none):
    """The text of a projects/<p>/project.yaml that the release keeps, as the cut edits it line by line (through the
    line marks of yamlio.compose): without the entry of each held fuzz target of names in `harnesses`, with the comment
    lines directly above it; without the field private_harnesses, with the comment lines directly above it, the
    comment lines indented under it and the comments on its lines; and, with port_none, with build.oss_verify.repository
    `none` (schema.NO_PORT_REPOSITORY).  Every other byte stays.  ValueError when the text is not one YAML mapping or
    the port repository is not one scalar on one line.  The caller compares the result with the cut's facts."""
    root = yamlio.compose(text)
    if not isinstance(root, yaml.MappingNode):
        raise ValueError("it is not one YAML mapping")
    lines = text.splitlines(True)
    gone = set()
    pairs = root.value
    for i, (k, v) in enumerate(pairs):
        if k.value == "private_harnesses":
            start = _comments_above(lines, k.start_mark.line, _last_line(pairs[i - 1][1]) + 1 if i else 0)
            end, below = _last_line(v), pairs[i + 1][0].start_mark.line if i + 1 < len(pairs) else len(lines)
            while end + 1 < below and _comment(lines[end + 1]) \
                    and len(lines[end + 1]) - len(lines[end + 1].lstrip()) > k.start_mark.column:
                end += 1
            gone.update(range(start, end + 1))
        elif k.value == "harnesses" and names and isinstance(v, yaml.SequenceNode):
            for j, item in enumerate(v.value):
                name = yamlio.mapping_value(item, "name")
                if isinstance(name, yaml.ScalarNode) and name.value in names:
                    floor = _last_line(v.value[j - 1]) + 1 if j else k.start_mark.line + 1
                    gone.update(range(_comments_above(lines, item.start_mark.line, floor), _last_line(item) + 1))
    if port_none:
        node = root
        for key in ("build", "oss_verify", "repository"):
            node = yamlio.mapping_value(node, key)
        _set_scalar(lines, node, schema.NO_PORT_REPOSITORY)
    return "".join(line for n, line in enumerate(lines) if n not in gone)


def cut_record_port(text):
    """The text of a build record (PROVENANCE.yaml) that the release keeps with port.repository `none` in place of
    the port's internal copy (schema.INTERNAL_PORT_REPOSITORY), every other byte as it was: what lint.check_records
    compares with the project's build.oss_verify, which the cut writes so too.  None when port.repository names
    another repository.  ValueError when the edit changes another value of the record."""
    root = yamlio.compose(text)
    node = yamlio.mapping_value(yamlio.mapping_value(root, "port"), "repository")
    if not isinstance(node, yaml.ScalarNode) or node.value != schema.INTERNAL_PORT_REPOSITORY:
        return None
    lines = text.splitlines(True)
    _set_scalar(lines, node, schema.NO_PORT_REPOSITORY)
    out = "".join(lines)
    want = yamlio.load(text)
    want["port"] = dict(want["port"], repository=schema.NO_PORT_REPOSITORY)
    if yamlio.load(out) != want:
        raise ValueError("the edit of port.repository changes another value of the record")
    return out


def _named_lines(root, entries):
    """The lines (0-based) of each part of the YAML document root that names an item of entries by the rule of
    disclosure.held_match: each key with its value, and each list item, whose key, scalar value or flow collection
    names one, or that is a list item that does.  A block mapping that is a list item starts on the item's line, so
    the whole item goes when its first key goes."""
    out = set()

    def names(node):
        if isinstance(node, yaml.ScalarNode):
            return bool(disclosure.held_match(node.value, entries))
        parts = node.value if isinstance(node, yaml.SequenceNode) else [n for pair in node.value for n in pair]
        return any(names(n) for n in parts)

    def visit(node, item=False):
        """Add the lines of each part of node that goes; True when node goes whole (the caller removes it)."""
        if isinstance(node, yaml.ScalarNode) or node.flow_style:
            return names(node)
        if isinstance(node, yaml.SequenceNode):
            for x in node.value:
                if visit(x, item=True):
                    out.update(range(x.start_mark.line, _last_line(x) + 1))
            return False
        for i, (k, v) in enumerate(node.value):
            if names(k) or visit(v):
                if item and i == 0:
                    return True
                out.update(range(k.start_mark.line, _last_line(v) + 1))
        return False
    visit(root)
    return out


def cut_port_text(name, text, entries):
    """text, the file at name (its path under port/) of a build record's copy of the port, without each line that
    names an item of entries by the rule of disclosure.held_match: in a YAML file each key or list item that names one
    goes whole, with its value (_named_lines: manifest.yaml's `targets` key and `fuzz_targets` item of the fuzz target
    among them), and then, in every file, each other line that names one (a line of build.sh, a row of a table).
    ValueError when a YAML file is not one YAML document after the cut."""
    lines = text.splitlines(True)
    root = yamlio.compose(text) if name.endswith((".yaml", ".yml")) else None
    gone = _named_lines(root, entries) if root is not None else set()
    gone |= {n for n, line in enumerate(lines) if disclosure.held_match(line, entries)}
    out = "".join(line for n, line in enumerate(lines) if n not in gone)
    if root is not None and yamlio.compose(out) is None:
        raise ValueError("it is not one YAML document after the lines that name a held fuzz target go")
    return out


def cut_port_copies(tree, records, entries):
    """(files, writes, problems) of the copy of the port (provenance/port/) of each build record of records (the
    paths of the PROVENANCE.yaml files that the release keeps), where entries are the held fuzz targets
    (<project>/<harness>).  files lists each file whose path under port/ names a held fuzz target by the rule of
    disclosure.held_match: the files of the fuzz target under port/projects/<p>/.  writes gives the new text of each
    other file that names one (cut_port_text), and problems says why a file cannot be cut so.  The cut leaves a file
    that is not UTF-8 text as it is, and the release's search reads it."""
    files, writes, problems = [], {}, []
    for record in records:
        top = os.path.join(os.path.dirname(record), "port")
        for d, dirs, fs in os.walk(tree.path(top)):
            dirs.sort()
            for f in sorted(fs):
                rel = os.path.relpath(os.path.join(d, f), tree.root)
                name = os.path.relpath(rel, top).replace(os.sep, "/")
                if disclosure.held_match(name, entries):
                    files.append(rel)
                    continue
                with open(tree.path(rel), "rb") as fh:
                    data = fh.read()
                try:
                    text = data.decode("utf-8")
                except UnicodeDecodeError:
                    continue
                if disclosure.held_match(text, entries):
                    try:
                        writes[rel] = cut_port_text(name, text, entries)
                    except ValueError as e:
                        problems.append("%s: %s" % (rel, e))
    return files, writes, problems


def _files(tree, rel):
    """rel when it is a file, else every file under it, sorted."""
    if not os.path.isdir(tree.path(rel)):
        return [rel]
    return sorted(os.path.relpath(os.path.join(d, f), tree.root) for d, _, fs in os.walk(tree.path(rel)) for f in fs)


def _plan(tree, keep):
    """(kept, removed, partial, stray) for a checkout with no symbolic link (checkout_links).  keep is the set of the
    ids of the proofs that ship (run: each proof that nothing holds back and that does not refute).  Each fuzz target's
    proofs folder is read through the facts, in the layout they are in: kept and removed list a statement's proof
    directory, or the whole proofs folder when it keeps none of its proofs.
    partial lists each fuzz target whose lib/ is kept while some of its statement directories are removed.  stray lists
    every file where only a directory belongs: beside the statement directories (a generated file aside), and anywhere
    under the old layout's proofs/ outside a fuzz target's proofs folder (proofs/lib/ among it, which no row admits);
    and anything in a kept statement directory that is not a file of STATEMENT_FILES or a witness record
    (_statement_file)."""
    kept, removed, partial, stray = [], [], [], []
    sids = {}   # fuzz target -> the ids of its proofs
    for sid in sorted(tree.proofs):
        sids.setdefault(sid.rsplit("/", 1)[0], []).append(sid)
    folders = set()
    for unit in sorted(u for u, kinds in tree.unit_kinds.items() if "proofs" in kinds):
        p, h = unit.split("/")
        d = layout.proofs_dir(p, h, tree.unit_layout(unit))
        folders.add(d)
        bad = [os.path.join(d, e) for e in sorted(os.listdir(tree.path(d)))
               if not os.path.isdir(tree.path(d, e)) and not paths.is_gen(os.path.join(d, e))]
        if bad:
            stray += bad
            continue
        shipped = [sid for sid in sids.get(unit, ()) if sid in keep]
        if not shipped:
            removed.append(d)
            continue
        for sid in shipped:
            sd = tree.proofs[sid].path
            stray += [os.path.join(sd, f) for f in sorted(os.listdir(tree.path(sd)))
                      if not _statement_file(f) or not os.path.isfile(tree.path(sd, f))]
        kept += [tree.proofs[sid].path for sid in shipped]
        cut = [tree.proofs[sid].path for sid in sids[unit] if sid not in keep]
        removed += cut
        if cut and unit in tree.proof_libs:
            partial.append(unit)
    # the old layout's proofs/ holds only fuzz targets' proofs folders, proofs/<project>/<harness>/
    base = tree.path("proofs")
    for p in sorted(os.listdir(base)) if os.path.isdir(base) else []:
        if not os.path.isdir(tree.path("proofs", p)):
            stray.append(os.path.join("proofs", p))
            continue
        for h in sorted(os.listdir(tree.path("proofs", p))):
            if os.path.join("proofs", p, h) not in folders:
                stray += _files(tree, os.path.join("proofs", p, h))
    return kept, removed, partial, stray


def _findings(tree):
    """Every finding's place in the checkout, which no release carries: findings/, each projects/<p>/<h>/findings/,
    each projects/<p>/unpatched.yaml, and each projects/<p>/unpatched-bin/ that `oft fetch --findings` filled (untracked,
    as findings/<p>/bin/ was, which went with findings/)."""
    found = glob.glob(tree.path(layout.findings_dir("*", "*", layout.NEW)))
    found += glob.glob(tree.path(layout.unpatched_path("*", layout.NEW)))
    found += glob.glob(tree.path(layout.unpatched_bin_dir("*")))
    return ((["findings"] if os.path.lexists(tree.path("findings")) else [])
            + sorted(os.path.relpath(f, tree.root) for f in found))


def _remove(tree, rel, out):
    """Remove rel, a file or a directory, and each parent below the top level that this leaves empty."""
    if os.path.isdir(tree.path(rel)):
        shutil.rmtree(tree.path(rel))
        print("removed %s/" % rel, file=out)
    else:
        os.remove(tree.path(rel))
        print("removed %s" % rel, file=out)
    parent = os.path.dirname(rel)
    while os.sep in parent and not os.listdir(tree.path(parent)):
        os.rmdir(tree.path(parent))
        parent = os.path.dirname(parent)


def run(root, out=sys.stdout):
    root = os.path.abspath(root)
    # A facts path is untrusted until this check says it cannot point outside root. facts.load and rules.check inspect
    # source/ and finding files, so this precedes every checkout read.
    links = checkout_links(root)
    if links:
        for rel in links:
            print("error: %s: a symbolic link, which the cut could follow out of the checkout" % rel, file=out)
        print("oft release-tree: %d path(s) that are not plain directories or expected files; nothing changed"
              % len(links), file=out)
        return 1
    tree = facts.load(root)
    rules.check(tree)
    if tree.errors:
        for e in tree.errors:
            print("error: " + e, file=out)
        print("oft release-tree: %d error(s) in the facts; nothing changed" % len(tree.errors), file=out)
        return 1
    held = facts.hold(tree)
    problem = private_harnesses_problem(tree, held)
    if problem:
        print("error: " + problem, file=out)
        print("oft release-tree: the held fuzz targets of %s are not those of the private_harnesses fields; nothing "
              "changed" % generate.PRIVATE_HARNESSES, file=out)
        return 1
    held_ids, held_units = held.ids, held.entries
    # a proof ships when nothing holds it back (its fuzz target is not one of private_harnesses, its project is not held
    # whole, its statement is not held back) and it does not refute: a release carries no Refutation.v
    # (STATEMENT_FILES).  refuting lists each proof that its refutation alone leaves out.
    unheld = {sid: pd for sid, pd in tree.proofs.items() if sid not in held_ids
              and sid.partition("/")[0] not in held.whole and sid.rsplit("/", 1)[0] not in held_units}
    keep = {sid for sid, pd in unheld.items() if not pd.refutes}
    refuting = sorted(set(unheld) - keep)
    kept, removed, partial, stray = _plan(tree, keep)
    problems = ["%s: a file a release cannot carry there" % rel for rel in stray]
    problems += ["%s (tracked by git at an ignored path): a file a release cannot carry" % rel
                 for rel in tracked_ignored(tree)]
    if problems:
        for p in problems:
            print("error: " + p, file=out)
        print("oft release-tree: %d path(s) that are not plain directories or expected files; nothing changed"
              % len(problems), file=out)
        return 1
    hidden = sorted(held.whole)
    # the facts as the release will have them, checked before the first change; the cut decides which projects held
    # whole keep a held page
    kept_dirs = set(kept)
    shipped = {sid for sid, pd in tree.proofs.items() if pd.path in kept_dirs}
    public = facts.load(root)
    held_page = facts.cut(public, shipped, held)
    # the one removal path: what a release leaves out of each project
    dropped = [os.path.join("projects", p) for p in hidden if p not in held_page]
    dropped += [os.path.join("projects", p, x) for p in held_page
                for x in sorted(os.listdir(tree.path("projects", p))) if x not in ("project.yaml", "README.md")]
    for p in hidden:
        # its counterexamples, in the layout of each fuzz target, and its patches in either layout
        dropped += [layout.counterexamples_dir(p, u.split("/")[1], lay)
                    for u, lay in sorted(tree.unit_layouts.items()) if u.split("/")[0] == p]
        dropped += [layout.patches_dir(p, layout.OLD), layout.patches_dir(p, layout.NEW),
                    os.path.join("notes", p + ".md")]
    # a statement an open finding holds back takes its counterexample with it
    dropped += [layout.counterexample_dir(p, h, s, tree.unit_layout("%s/%s" % (p, h)))
                for p, h, s in (sid.split("/") for sid in sorted(held_ids))]
    # a held fuzz target (private_harnesses) of a project that publishes: each folder of it that layout.py gives, in
    # both layouts (its statement folder, which holds the per-project ones, and the proofs, counterexamples and
    # findings folders of the old layout), and its files in the copy of the port of each build record the release keeps
    for unit in sorted(held_units):
        p, h = unit.split("/")
        if p not in hidden:
            dropped.append(layout.statement_dir(p, h))
            dropped += [kind(p, h, lay) for lay in layout.LAYOUTS
                        for kind in (layout.proofs_dir, layout.counterexamples_dir, layout.findings_dir)]
    port_gone, port_writes, cut_problems = ([], {}, []) if not held_units else \
        cut_port_copies(tree, sorted(public.records_at.values()), sorted(held_units))
    dropped += port_gone
    # each path once, none inside another (a held project's own folder holds what it has in the per-project layout),
    # and none that the plan removes already (a held fuzz target's proofs folder of the old layout)
    dropped = [rel for i, rel in enumerate(dropped) if os.path.lexists(tree.path(rel)) and rel not in dropped[:i]
               and not any(rel.startswith(other + os.sep) for other in dropped) and rel not in removed]
    # checkout_links reads no ignored path (projects/<p>/bin/, a _build/), and the cut removes such a path of a held
    # project: a symbolic link there would stop rmtree after the first change, or take the cut out of the checkout
    linked = [rel for rel in removed + dropped if os.path.islink(tree.path(rel))]
    if linked:
        for rel in linked:
            print("error: %s: a symbolic link, which the cut could follow out of the checkout" % rel, file=out)
        print("oft release-tree: %d path(s) that are not plain directories or expected files; nothing changed"
              % len(linked), file=out)
        return 1
    files = [f for f in INTERNAL if os.path.lexists(tree.path(f.rstrip("/")))]
    findings = _findings(tree)
    release_yaml = _public_release(tree, public)
    if release_yaml is not None:
        public.release = release_yaml
    rules.check(public)
    if public.errors:
        for e in public.errors:
            print("error: after the cut: %s" % e, file=out)
        print("oft release-tree: %d error(s) in the facts as the release would have them; nothing changed"
              % len(public.errors), file=out)
        return 1
    # every file the cut writes, in one place: the search reads it, the walk skips the old file, and the cut writes it
    writes = {os.path.join("projects", p, "project.yaml"): yamlio.dump(public.projects[p].data) for p in held_page}
    writes.update({os.path.join("projects", unit, "harness.yaml"): yamlio.dump(public.projects[p].harnesses[h].data)
                   for unit in {sid.rsplit("/", 1)[0] for sid in held_ids} for p, h in [unit.split("/")]})
    if release_yaml is not None:
        writes["release.yaml"] = yamlio.dump(release_yaml)
    # the files a held fuzz target or the field private_harnesses changes, edited line by line so that every other byte
    # stays: the project.yaml of each project that publishes; where the project's port is the port's internal copy,
    # the build record of each of its fuzz targets that the release keeps (port.repository `none`); and each file of a
    # kept build record's copy of the port that names a held fuzz target (port_writes)
    for n, proj in sorted(tree.projects.items()):
        names = held.harnesses.get(n, ())
        if n not in public.projects or n in held_page or ("private_harnesses" not in proj.data and not names):
            continue
        rel = os.path.join("projects", n, "project.yaml")
        internal = bool(names) and (facts.port(proj) or {}).get("repository") == schema.INTERNAL_PORT_REPOSITORY
        try:
            text = cut_project_yaml(facts.read_raw(tree.path(rel)), names, internal)
            if yamlio.load(text, rel) != public.projects[n].data:
                raise ValueError("the edit gives other facts than the cut of the facts")
            writes[rel] = text
        except ValueError as e:
            cut_problems.append("%s: %s" % (rel, e))
        for record in sorted(r for (p, _), r in public.records_at.items() if p == n and internal):
            try:
                text = cut_record_port(facts.read_raw(tree.path(record)))
            except ValueError as e:
                cut_problems.append("%s: %s" % (record, e))
                continue
            if text is not None:
                writes[record] = text
    writes.update(port_writes)
    if cut_problems:
        for p in cut_problems:
            print("error: " + p, file=out)
        print("oft release-tree: %d file(s) that the cut cannot edit line by line for a held fuzz target; nothing "
              "changed" % len(cut_problems), file=out)
        return 1
    # the rewritten lint-exceptions.yaml ships, so the search reads its text as the release will have it
    exceptions = cut_lint_exceptions(tree, removed + dropped + files + findings)
    if exceptions is not None:
        writes[LINT_EXCEPTIONS] = exceptions[0]
    # the packer's measured tables and failure_handlers.tsv name one unit a row, so the cut rewrites them to the units
    # it carries before the search below reads them: a row for a held project's fuzz target names what the hold
    # withholds
    carried = {"%s/%s" % (h.project.name, h.name) for h in public.harnesses()}
    withheld = {"%s/%s" % (h.project.name, h.name) for h in tree.harnesses()} - carried
    try:
        readings = cut_pack_readings(tree, carried)
        handler_rows = cut_handler_rows(tree, withheld, set(hidden))
    except ValueError as e:
        print("error: %s" % e, file=out)
        print("oft release-tree: a table of units cannot be read row by row; nothing changed", file=out)
        return 1
    if readings is not None:
        writes[PACK] = readings[0]
    if handler_rows is not None:
        writes[HANDLERS] = handler_rows[0]
    # AGENTS.md ships without its marked blocks, which are for this repository only, so the search below reads the text
    # the release has
    try:
        agents = cut_agents_md(tree)
    except ValueError as e:
        print("error: %s: %s" % (AGENTS, e), file=out)
        print("oft release-tree: the cut cannot take the marked blocks out of %s; nothing changed" % AGENTS, file=out)
        return 1
    if agents is not None:
        writes[AGENTS] = agents
    # .gitignore without the block of the shared generated files, so that the release commits the files its last
    # render writes
    try:
        gitignore = cut_gitignore(tree)
    except ValueError as e:
        print("error: %s" % e, file=out)
        print("oft release-tree: .gitignore's block of the shared generated files is not the one the cut removes; "
              "nothing changed", file=out)
        return 1
    if gitignore is not None:
        writes[GITIGNORE] = gitignore
    # an internal path the render gives (tools/publish/private-harnesses.txt, which names each held fuzz target) is no
    # file of the release: the cut removes tools/publish/ whole, so it neither searches nor keeps one
    rendered = {rel: text for rel, text in generate.render_all(public).items() if not paths.is_internal(rel)}
    try:
        needles = disclosure.needles(tree, held)
    except facts.BoundedFileError as e:
        print("error: a holding finding's evidence cannot be read within its cap: %s" % e, file=out)
        print("oft release-tree: the evidence to search for is unreadable; nothing changed", file=out)
        return 1
    named = disclosure.search(root, needles, removed + dropped + files + list(writes) + findings,
                              {**rendered, **writes})
    if named:
        for rel, label in named:
            print("error: %s names %s" % (rel, label), file=out)
        print("oft release-tree: %d disclosure(s) of what is held back in files the release keeps; nothing changed"
              % len(named), file=out)
        return 1
    # a stale rendering would fail only after the cut: find it first.  Not the shared generated files
    # (paths.SHARED): the line's render owns them, so a line commit may carry a stale one, and this run's own final
    # render writes them into the cut.
    buf = io.StringIO()
    if generate.run(root, check=True, out=buf, shared=False):
        out.write(buf.getvalue())
        print("oft release-tree: the generated files are not current (run ./oft generate); nothing changed", file=out)
        return 1
    # every check has passed: only now does anything change
    for rel in removed + dropped:
        _remove(tree, rel, out)
    for rel, text in sorted(writes.items()):
        with open(tree.path(rel), "w", encoding="utf-8") as f:
            f.write(text)
        if rel == LINT_EXCEPTIONS:
            print("rewrote %s without the exception(s) for %s, which the release does not carry"
                  % (LINT_EXCEPTIONS, ", ".join(exceptions[1])), file=out)
        elif rel == GITIGNORE:
            print("rewrote %s without the block of the shared generated files (%d lines), which the release commits"
                  % (GITIGNORE, 1 + len(SHARED_IGNORES)), file=out)
        else:
            print("wrote %s as the release has it" % rel, file=out)
    # the generated files were current before the cut, so a generated file its facts no longer produce (the
    # Characterise.v of a harness whose agreements all went, say) is one the cut left behind; the final render writes
    # the rest
    for rel in generate.existing_generated(root):
        if rel not in rendered:
            _remove(tree, rel, out)
    # the facts were loaded, and checked, with the findings in place: only now are they cut
    for f in files:
        p = tree.path(f.rstrip("/"))
        if os.path.isdir(p) and not os.path.islink(p):
            shutil.rmtree(p)
        else:
            os.remove(p)
    gone = []
    for rel in findings:
        if not os.path.lexists(tree.path(rel)):
            continue   # a held project's own folder, removed above, held it
        if os.path.isdir(tree.path(rel)):
            shutil.rmtree(tree.path(rel))
            gone.append(rel + "/")
        else:
            os.remove(tree.path(rel))
            gone.append(rel)
    gone += files
    for p in sorted(held.held):
        print("held back by a finding that is not public: %s" % p, file=out)
    for sid in sorted(held_ids):
        print("held back by an open finding: %s" % sid, file=out)
    for unit in sorted(held_units):
        print("held back by private_harnesses: %s" % unit, file=out)
    for sid in refuting:
        print("held back as a refutation: %s" % sid, file=out)
    for unit in partial:
        print(PARTIAL % unit, file=out)
    print("oft release-tree: kept %d proof(s) of %d fuzz target(s); removed %d path(s) of proofs folders; removed %s"
          % (len(kept), len({os.path.dirname(k) for k in kept}), len(removed), " and ".join(gone)), file=out)
    rc = generate.run(root, out=out)
    if rc == 0:
        print("the cut's statements, for its CHANGELOG.md section: %s" % generate.counts_sentence(public),
              file=out)
    return rc
