# tools/oft

The tools of this repository: Python 3, PyYAML and, for `./oft lint`, idna
(`requirements.txt`, pinned by hash), nothing else.  Run them as
`./oft <command>` from the repository root; `./theorem <command>` passes its
arguments to `./oft`, for a developer's `./theorem prove`.

`./oft` finds those two packages in this order: the interpreter itself, where it
already imports them (a runner that installed `requirements.txt`, and the checker
image, which is run with `PYTHONPATH=/pydeps`, so a check in it reads nothing outside
the tree); else a virtual environment of its own, which `uv` builds once from
`requirements.txt` under `$OFT_VENV_ROOT` (default
`${XDG_CACHE_HOME:-$HOME/.cache}/oft-venv`), in a directory named for that file and
for the `python3` of this box, on which it is built, so a box that ships neither
package runs `./oft lint` with no install by hand, every later run reuses it and
needs no network, and a change to `requirements.txt`, or an upgrade or move of
`python3`, builds a new directory beside the old one.  A directory whose interpreter
has gone is built again.  Where neither holds, the run names the
requirement it could not import, the line of `requirements.txt` that pins it and every
directory it looked in, instead of a bare `ModuleNotFoundError`
([`__main__.py`](__main__.py)).

| command | what it does |
|---|---|
| `./oft generate [--check] [--skip-shared \| --shared-only]` | renders every generated file from the facts; `--check` compares instead of writing, and is what CI runs. The *shared generated files* (`tools/oft/paths.py` `SHARED`: `README.md`, `index/*`, `analyses/harness-checks/checks.tsv`, `analyses/known-issues.md`, each `projects/<p>/README.md`) are rendered from the whole tree, so every proof pull request would change them. `--skip-shared` renders or compares every other generated file, and is what a pull request, a merge queue group and a push run; `--shared-only` renders the shared files alone, which `.github/workflows/index.yml` does after each merge. A release cut renders every file |
| `./oft lint [--release] [--changed-only BASE] [--pending-base DIR] [--list-pending] [--jobs N] [--max-rss-gib G]` | the repository's rules (below); `--release` adds what only a release must satisfy (no placeholder digest, and the rules `records`, `model` and `pins`, the last two read from GitHub); a licence finding of a fuzz target that [`lint-exceptions.yaml`](lint-exceptions.yaml) lists as `licence-pending` is counted, on one line per fuzz target marked `pending` (each finding with `--list-pending`) and on the last line, and does not fail, and so is an expired entry that the change does not touch, printed with the mark `expired` and as a GitHub `::warning::` line; `--pending-base` names a git checkout of the pull request's base commit, which may be sparse (`pr.yml` passes its own), whose HEAD's `lint-exceptions.yaml` lint reads through git: a pull request that changes proof files has no `licence-pending` entry that the base commit lacks; when the text rules read 256 files or more they run on every CPU the process may run on (its affinity set, so `taskset` narrows it), but on no more processes than the available memory holds at 1 GiB each (`MemAvailable`, less under a cgroup limit above the process); `--jobs` sets the number of processes, 1 or more, and the findings do not depend on it; each process stops the run when it holds more resident memory than `--max-rss-gib` (default 4), and the run then exits 3 with no verdict; `--root` may be a sparse worktree: lint lists the files with `git ls-files` and reads only those on disk, so it judges the files present as a full checkout does, but a lint without `--changed-only` reports an exception whose file is not checked out as unused; `--changed-only` runs the per-file text rules (`private-data`, `links`, `proofs`, `licence`) only over the files that differ from commit `BASE`, and reports an unused exception only for a path that differs from it, or, saying so on stderr, runs them over every file when a fact (a file [`paths.py`](paths.py) classes as facts, but `CHANGELOG.md`, which no other file's verdict reads), a finding's `finding.yaml`, a build record (`provenance/PROVENANCE.yaml` in a fuzz target's proofs folder), a `.gitattributes`, [`lint-exceptions.yaml`](lint-exceptions.yaml) or the running tools (this directory, when it is inside the tree) differ from it, since these decide what a file may hold; the rules over the whole tree still run. It needs `--root` at the top of a git checkout and a `BASE` that names a commit, and fails otherwise. Its verdict on an unchanged file is the one that file had at `BASE`: `pr.yml` passes it for each change into main (a pull request, a merge queue group, a push), each judged on its own change, and lints every file for a pull request into any other branch and for a push with no base to compare with |
| `./oft ledger --base REV [--tip REV]` | the findings ledger over the history `REV..TIP` (below) |
| `./oft fetch <project>...` | downloads a project's binaries from its release asset and checks the archive's SHA-256 and every file's; `--findings` fetches the unpatched binaries its findings run on instead, into `projects/<project>/unpatched-bin/` (never tracked). A release that is not public (a draft, or a release of another repository) has no download URL: with `OFT_RELEASES_REPO=<owner>/<repo>` and a token in `GH_TOKEN` or `GITHUB_TOKEN`, the assets come from that repository's release of the same tag through the GitHub API, a draft included, with the same checks |
| `./oft verify-sha <project>...` | checks fetched binaries against their `harness.yaml` |
| `./oft check <project>/<harness>...` | builds the images and statements and has the kernel type each statement `harness.yaml` lists that `Statements.v` carries and print what they assume, checks every proof through a wrapper and every assumption the wrapper prints against `toolchain/allowed-axioms.txt`, and re-runs every counterexample; `--parts findings` re-runs every finding on the unpatched binaries and compares each run with its record, and `--record` prints the runs of a finding that has none yet, only when its input shows each statement false and its control shows none false; `--rocqchk` adds an independent re-check with `rocqchk`, which can take hours for one proof and is not part of the verdict. `--proof-jobs N` builds a harness's proof library once, then checks each statement's proof in a process of its own (`python3 -m oft.check UNIT --parts proofs --statements S --lib DIR`), N at once; a statement passes only when its process exits 0 and prints the statement's own line, and with `--rocqchk` the proofs stay in one process. Without `--parts` it checks each of statements, proofs and counterexamples that the unit has. It fails on a unit it examined nothing in: one whose `Statements.v` is missing, lacks one of those statements, states one as an axiom (`Axiom`, `Parameter`, `Admitted`) or makes them assume an axiom outside the allowlist, or has none to define (each withheld or withdrawn), and one with no proof when `--parts` names proofs (`ci/check-units.sh` checks the units a job's `proof_units` leaves out with `--parts statements`). Every check first loads the facts of the whole tree and checks its rules; two options split that from the rest, so that a unit can be checked in a view that holds only its own files. `--facts-to DIR` loads the facts and checks the rules of the whole tree, writes the facts each unit's check reads (and nothing of another unit or of the whole tree but the release's namespace and opam stem, which a view holds no `release.yaml` to give) to `DIR/<project>/<harness>.yaml` with the SHA-256 of each unit file they came from and the list of the unit's proof, counterexample and finding directories, and builds and runs nothing. `--facts-from DIR` checks each unit as a plain check would, with its facts from `DIR` and without loading the tree or checking its rules, so `--root` may be a view of the unit; it fails a unit whose file is missing, malformed, of another format version or of another unit, or whose namespace does not give `harness.yaml`'s `rocq`, or, for a part it checks, whose facts came from a file that is missing under `--root` or differs, or whose directories differ. It compares nothing else; the rules read more, in the unit (`source/`, `Distribution.v`, `proofs/<p>/<h>/provenance/`) and in the rest of the tree (`theories/Shapes.v`), so it cannot show that the facts and the view come from one tree. So the facts must be written from the checkout the views are made from, `DIR` must not be writable by a unit's check (mount it read-only), or one unit's check could change the facts it or another unit is checked with, and a unit's check gets only its own file, since another unit's file holds that unit's facts. The file's format is part of the checker, so a change to it re-keys every unit. CI runs it as `python3 -m oft.check`, which loads the checker and none of the other commands' modules. Before the `statements` and `proofs` parts it sets the stack's soft limit to the smaller of the hard limit and 2 GiB, refuses no hard limit, measures the stack it got with `stackprobe.c` (compiled with `cc`), and prints one line, `stack: <N> MiB usable (soft <S>, hard <H>; started with soft <s0>, hard <h0>; runtime <gvisor|linux>)`; a step that runs out of stack fails as `stack exhausted at <N> MiB`, a class apart from `does not compile` ([docs/checking.md](../../docs/checking.md#stack-size)) |
| `./oft plan [--base REV] [--pr-kind KIND] [--store REV] [--units FILE] [--explain PROJECT/HARNESS \| --contracts PROJECT/HARNESS]` | the parts CI checks, as JSON for its job matrix. Each part of each harness (`build`: its statements and proofs, for a harness with published builds and a statement `Statements.v` carries; `counterexamples`; `findings`) has a content key: the SHA-256 of the git object ids, and the checkout attributes, of what that part's check reads, with the checker image or the runner image and the checker itself, every file of `tools/` but the files that `keys.NOT_THE_CHECKER` names ([keys.py](keys.py)). A part is checked when its key has no recorded pass at `--store`, a commit of the branch `check-results`, and, with `--base`, when its key differs from its key at the base: so a change is checked on what it changes, and a change to a file no check opens checks nothing. For `--pr-kind maintainer` or `contributor` the statements are the base's, as `pr.yml`'s check job takes them; `--tools REV` names the tools the check jobs run (default: the base, else `HEAD`). Each part's row says why it is or is not checked; `--explain` prints one harness's rows with every input of each key. `--contracts` prints, as JSON, the work key of each contract file of one harness (a `<fn>_c.v` under `Prog/` of its proof library) at `--change`: which contracts need an agent after a change, never a basis for verdict reuse (a proof imports its harness's whole image module, which the key does not hold), so it refuses `--store`. The key is the SHA-256 of the id of the contract file; the code (`rocq.code`: comments and layout left out) of each file it requires (its `Require` commands, transitively), of the proof library (`lib/<path>`) or of the statement library (`harness/<file>`: `Statements.v`, `Images.v`, `Characterise.v`, `Distribution.v`); the proof environment as the build key holds it (`theories/`, `toolchain/allowed-axioms.txt`, the project's `dune-project` stanzas, the statement folder but its `harness.yaml`, `images/`, `symbols/`, `Symbols.v`, `source/` and those Rocq files); for each function, data object or section it or those files name from `Symbols.v`, its masked bytes (`masked` in the symbol fact) or bytes, and its size when it has no bytes or a `Size.` reference names it, never its address; the checker and the checker image. A contract that uses a module of `Symbols.v` as a whole (`Import Symbols.Plain`, `Module S := Symbols.Plain`, `Import Symbols`, `Module S := Symbols`), or names from it what cannot be resolved (a build with no symbol fact, a name its fact gives no identifier), has the state `unknown` and no key. Each row has its `state`, `key` and `unknown` (why the key is unknown, and where); its `references`, each with its `build`, its path in the build's module as `written` (`s_x`, `Size.s_x`, `Sec.s_x`), and `status` `resolved` with the `name` and `kind` of the symbol it names, or `unresolved` (an identifier is never read as a symbol's name); `base` (`no base`, `not at the base`, `unknown at the base` with `base_unknown`, or `keyed at the base`); `changed`, when both keys are known, each component whose id differs from the base's with its `type` (`contract`, `library`, `environment`, `symbol`) and, for a symbol, its `build`, `name` and `kind` and `size` at each commit (`before`, `after`); and `why`, text written from them ([contracts.py](contracts.py) `contract_keys`). No CI job reads these keys: every check compiles every proof. Each job lists its `check_units` (whose build it checks) and, of those, its `proof_units` (with a proof of one of their statements). The checked units are dealt into jobs by [`pack.py`](pack.py): first each harness with proofs that [`proof-times.tsv`](proof-times.tsv) gives fewer CPUs than its most, alone in its own job; then the other harnesses with proofs longest first, each to the job with the least measured time so far (an unlisted one counts as their median); then the rest, each to the job with the fewest. Each job's `cpus`, which `ci/check-units.sh` gives its checker container, is the fewest the table gives any of the harnesses whose proofs it checks, and 0, every CPU of the runner, when each of them passed at the table's full width |
| `./oft lps-impact --commit SHA --checker-image REF --out DIR` | checks every unit in a checker image built from an LPS commit and says what each unit's first error is, for an LPS move: it runs `oft check` of each unit in that image as the unit check of [`ci/check-units.sh`](ci/check-units.sh) runs it (`--parts statements,proofs` for a unit with a proof, `--parts statements` for one with none, no network, dune's cache off), but over the whole tree and not over that unit's view, so a unit is checked here with more of the tree readable than CI gives it and the run loads the tree's facts once per unit. Each arm is read proof by proof, never unit by unit: `oft check` runs every step and names each step it failed (`FAIL <proof path>: ...`) and each proof that passed, so a statement whose own proof passed in a run its unit failed reads `pass`. `--control-image REF` checks a failing unit again in the release checker, and a statement reads `pre-existing` only when its own proof fails in that image too, so a unit with one proof that was broken before the model moved does not hide the proofs the move broke; a control check that could not run, or that ended before this statement's proof, reads `control-infra`, which attributes the failure to nothing. `--units proved` checks only the units with a proof; `--shard K/N` takes the K-th of N disjoint parts, for a run over several machines; `--first FILE` checks the units that file lists before the others, each named unit once; `--jobs N` checks N units at once, and from 2 each worker checks in a copy of the tree of its own, since one `_build` and one dune workspace lock serve one build at a time and `oft check` renders each proof library's `lib/dune` into the tree it checks. It writes `DIR/units.tsv` (a first line naming the model commit, the image, the proofs tree and the scope, then `unit parts result stage exit first_error proofs_pass proofs_fail wall_s control control_stage control_exit`), `DIR/impact.tsv` (one row per statement: `id kind reading status revision_change proof recheck class stage first_error`), a log per unit and per control run under `DIR/logs/`, and under `DIR/logs/<unit>.d/` every log `oft check` wrote inside the container: the container's `TMPDIR` is `DIR/work/<unit>` of this host, mounted, because a `--rm` container takes with it the Rocq log that each error names, and without it every failure is one line naming a file that is gone. `DIR/work/<unit>` is removed once its logs are copied out.  The container is the thing being measured, so it does not choose what the host reads back: only a regular file is copied, never a link, and the log an error names is read only when it resolves inside that unit's own `logs/<unit>.d/`. Outside `DIR` the run writes only `--work` (default `/var/tmp/lps-impact`): the per-worker trees and a dune cache per image; at `--jobs 1` the check also builds `_build` in the checkout itself and renders `lib/dune` there, and the run clears that `_build` before it starts. A unit whose check could not run (the image, docker, the out-of-memory killer, a worker tree that could not be made, a host or docker-client error while the unit was checked, a non-zero exit with no `FAIL` line, or a run the checker refused before its first step: it could not raise the stack limit, read the unit's facts, or find the part `--parts` names) reads `infra`, never `fail`, in `result` and in `recheck` alike, and its class is `infra`, never a failure class; it has no failure to attribute, so the control image is not spent on it; `stage` and `exit` say what stopped it, so that a row which could not run is never read as a finding of the model. A check that ran past `--timeout` has its container removed, so that it cannot go on building in the tree the next unit is checked in, and reads `timeout`. A statement with no proof of its own in a unit that failed in another statement's proof reads `not-attributed`, never `fail`. It opens no file of the checker, so it changes no unit's key |
| `./oft release-tree` | turns a checkout into the files of a release, in place: keeps the proof of each statement `approvals.yaml` lists, with its fuzz target's whole `lib/` and build record, removes every other proof; leaves out what the hold (`facts.hold`) holds back: by one removal path, turns each project held whole (`release: private` in its `project.yaml`, or a finding `patched` or `reported`, or `open` in a project that is not enrolled) that OSS-Fuzz has into a held project (its `project.yaml` rewritten to `schema`, `project`, `homepage`, `language`, `oss_fuzz`, `status: held`, `reason: held`, and the rest of `projects/<p>/`, its counterexamples and patches, `notes/<p>.md` and proofs removed), and removes whole one OSS-Fuzz does not have (a held page for a project never released would tell the reader that a finding exists), printing `held back by a finding that is not public: <project>` for each project a finding holds whole; for an enrolled project (`enrolled: true`) whose holding findings are all `open`, removes only the statements they name and every agreement or halts statement their recorded input shows false, with each held agreement's bound and decidability statements, their proofs and counterexamples (a hold that would leave a harness with no statement, or a harness that publishes a build with only withheld statements, or in a project with a proof library, `proofs/<p>/<h>/lib/`, which ships unchecked, or in one with a published binary that `findings/<p>/unpatched.yaml` does not pin as the one its findings run on, holds the whole project instead); writes `release.yaml`'s `counts` and `oss_fuzz.projects` as the cut leaves them, and drops each `image_libraries` entry no build of the cut links; removes every finding entirely (`findings/`, each `projects/<p>/<h>/findings/` and each `projects/<p>/unpatched.yaml`) and what only this repository has (`INTERNAL` of [`paths.py`](paths.py), then the two skill directories of `release_tree.SKILLS`, which paths.py does not name, written out as [`release_tree.INTERNAL`](release_tree.py), whose comment says why each is there; a directory it removes whole and never reads for what is held back; a test the release keeps finds each file it needs there, or checks that the file exists and skips without it, which `test_release_tree.ReleasedTests` checks by reading each test's code: it takes any existence call on the path as that check, whether or not a skip follows, and it does not see a path reached through a name another module defines); rewrites `tools/oft/lint-exceptions.yaml` without each entry whose path, in either layout's form, is at or under a path the cut removes, and without every `licence-pending` entry, so a release carries none (the lines above its `exceptions` key stay as written); renders again and prints the cut's statement counts for its CHANGELOG section; it reports a listed statement with no proof, and each fuzz target whose `lib/` it keeps while removing some of its statement directories; and it changes nothing, since every check runs before the first change, when the facts have an error (an entry of a held or private project, a held statement or a listed refutation among them), the checkout holds a symbolic link outside an ignored path, a path the cut removes is a symbolic link (an ignored one, `projects/<p>/bin/` or a `_build/` of a held project, among them), git tracks a file at an ignored path, a fuzz target's proofs folder holds a file beside its statement directories (its generated `dune` aside), a file under `proofs/` is in no fuzz target's proofs folder (`proofs/lib/`, which no path pattern admits, among them), a kept statement directory holds anything but `Proof.v`, `proof.yaml` and `dune`, the facts as the release will have them have an error, a holding finding's evidence cannot be read within its cap, the generated files are not current, or a file the release keeps or writes (the held page, a rewritten `harness.yaml`, the rewritten `lint-exceptions.yaml`, `release.yaml` and every generated file, as the cut's facts render them) discloses what is held back, whole or in part, and each refusal names the file, the kind of what it holds and the finding or project it belongs to. That search ([`disclosure.py`](disclosure.py)) reads nothing when nothing is held, and otherwise runs on lint's forked file scanner, so a worker that dies fails the cut. What it catches is a closed list, frozen on 2026-10-26: findings never ship, a held project is removed or cut to its held page, and every release pull request is reviewed, so the search is a safety net for the common accident. It catches a copy of a holding finding's evidence (1) whole, or any part of 32 or more letters and digits, or a whole short unit (a hunk's lines, its added text or its removed text, or a printable run of 8 or more characters of an input's payload); (2) with changes of white space, line endings, case or Unicode normal form; (3) in UTF-8, UTF-16 or UTF-32; (4) through HTML character references, percent escapes and the backslash escapes of C, Python, JSON and YAML, octal and YAML's `\0`, `\a`, `\e` and `\_` among them; (5) with the line prefixes of Markdown quoting and code comments; (6) as hex in the layouts of `xxd -p` and `xxd` (with item 5's marks on each line, too), and as a C array of bytes (`xxd -i`, Python's `hex()`, or decimal items); and (7) by an input's exact bytes or its SHA-256; and it catches the names below. Each item applies on its own: a combination of items is out of scope, and so is everything else: word and colour diffs, quoted-printable, a URL query's `+` for a blank, the layouts of `od` and `hexdump`, per-line decorations such as `cat -n`, `cat -A`, `git blame` and `git grep`, base64 (YAML's `!!binary` among them), and anything retyped or paraphrased. It reads each file's text by its byte order mark, or as UTF-8 and as UTF-16 and UTF-32 from every offset, with HTML character references, percent escapes and backslash escapes (JSON's `\uXXXX`, and `\f`, `\v`, `\b`, `\a`, `\e`, `\0` and YAML's `\_`, `\N`, `\L` and `\P` as the characters they stand for, among them; a backslash before an octal digit as C and Python read it, and, when an input holds a NUL before an octal digit, also as YAML reads `\0` then; a backslash before a line break keeps the break, and the bytes below join the lines) decoded until nothing changes (at most eight rounds, by a decoder that never raises: a numeric reference of more than seven digits after its leading zeros stays as it is), NFKC-normalised and case-folded, and compares it in three forms. In the long form, only its letters and digits, so comment prefixes (`//`, `#`, `*`, `>`, `|`), quotes, doubled quotes, punctuation, white space, zero-width characters and soft hyphens all read the same, it compares evidence in windows: every run of 32 characters of a holding finding's summary (whole and each sentence), of each patch's subject and commit message, of each hunk's removed lines joined and of its added lines joined, of each hunk's new side (its context and added lines in file order) where the run holds a character the change adds or spans the place of one it removes, of the printable text of each input's payload, and of the hex of each input and each digest, is a key of one hash table, except a run of fewer than 8 different characters, which is chance text, and a run made only of the outcome vocabulary (`disclosure.OUTCOME_WORDS`: build names, outcomes, connectives and digits), which every counterexample note writes; a 16-character index of the windows is probed every 17 positions of a file's long text and each hit is checked against the windows around it, so every 32-character copy is found, and the upstream context lines a harness quotes never count by themselves. In the punctuation form, each line without the marks a copy puts at its ends (diff's `+`, `-`, `<` and `>`, a reply quote's `>`, a table's `|`, a comment's `#`, `//`, `*`, `;` or `(* *)`, a string's quotes; a backslash before a line break keeps the break here, so each line keeps its marks) and then without white space, with a run of one quote read as one, short evidence counts whole, from 8 characters and whatever its characters: each hunk's lines in diff order (context included), its removed text and its added text, and each printable run of each input's payload, so a fix of a few characters and a reproducer that is mostly punctuation count; it counts in the plain form too, the text without white space alone, so a copy rewrapped, or folded by YAML's writer, counts where a new line begins with a character a mark would take (`(*t`). In the bytes a file spells, one byte per character (its own; the text of each decoding round, and of each decoder alone, so that none reads the bytes another wrote, a backslash before a line break there joining the lines and the blanks after it, as YAML's writer folds a string; `\0` before an octal digit read as YAML reads it, a NUL and the digit, when an input holds that byte pair; percent escapes read one byte each; each of these with adjacent string literals joined and with each `0xNN` or `0xN` item of a C array read as its byte, and as it is; and the bytes of its `xxd` and `xxd -p` lines and of its decimal arrays in brackets or braces), each input's bytes and every run of 32 of them with at least 8 different bytes count, so a copy as Python's `repr`, a C string of `\x` or octal escapes, YAML's escapes and this repository's YAML writer, percent escapes, `xxd`, `xxd -p` or `xxd -i` writes it counts. An input that is the driver's header alone counts not at all, and neither does the SHA-256 of empty output. It looks for names at a name boundary, so that a prefix of another name never matches and a name followed by a source or header suffix (`openssl/x509.h`) is read as a file's name, in the file's path and its text with each path resolved (`.`, `..`, repeated slashes), each line break and each blank beside a `/` deleted, and every dash read as `_`: each fuzz target of a project held whole, as `<project>/<harness>` and as its Rocq module with or without its namespace (`<namespace>.`, release.yaml's); the slug, each patch file name (every `*.patch` of its directory, whether or not a field names it) and each recorded output digest of a finding that holds its project back, and the SHA-256 of each non-empty input; each held statement as `<project>/<harness>/<statement>`, by its Rocq names with or without the root, as `<harness>/<statement>` (not after a `/`, where it ends another fuzz target's name), and, in a file of its own fuzz target (under its directories or the project's notes, or one that names its Rocq module), as `<statement>` or `<statement>_holds` |
| `./oft approvals FILE --approved-by LOGIN --date DATE` | writes `approvals.yaml`: one entry for each line of FILE whose fuzz target has a proof in the checkout: a line with a submission's record names the proofs that record covers (it must name them, and each must be a statement of the fuzz target), a bare line names every other proof of its fuzz target; a fuzz target may have one bare line and record lines with different records and disjoint statements; a refutation, or a fuzz target of a private project, is never listed; a fuzz target of a project a finding holds back is omitted and printed as `held by a finding that is not public: <project>/<harness>`, and a statement an open finding of an enrolled project holds back as `held by an open finding: <project>/<harness>/<statement>` (a line whose every proof is held gets only those lines); an existing entry for the same fuzz target, origin and record whose content is unchanged keeps its approver and date |
| `./oft revisions PREVIOUS [--write-pins] [--repin-changed] [--write-revisions] [--earlier OLDER...]` | fingerprints this tree and `PREVIOUS`, a checkout of the previous release, with the same tools, and gives each statement's meaning (same, changed, re-rendered: these tools render other code for it than `PREVIOUS`'s did, or model-changed: the model's name, version or commit, or the Rocq package or version, differs), the revision it must have and what happens to its proof; fails when a revision is wrong; `--write-pins` sets the pin of each proof that carries forward to its statement's fingerprint here; `--repin-changed` does the same, and also sets the pin of each re-checked or new proof that holds its statement's fingerprint in `PREVIOUS` when that fingerprint changed: only for a change whose re-check is the next corpus run (a change to the code of `theories/Shapes.v`), never to silence a proof that failed; a re-checked or new proof whose pin is neither fingerprint keeps it; against a commit that is not a release (a proof branch's base before that change) only the pins count, and the revision errors and the exit status, which compare with that commit, are to be ignored there; `--write-revisions` sets each wrong revision in `harness.yaml` to the one the statement must have (a `revision:` line after `status:`, none for revision 1), every file computed before any is written, names the render to run next (`./oft generate`, with `--skip-shared` when the tree's own tools offer it), and then does not fail on it. It fails, and writes nothing, when `PREVIOUS` or an `OLDER` holds a file that `oft release-tree` removes from every release (`approvals.yaml`, `review.md`, ...), since against any commit but a release the revision it writes is wrong, or when a new statement's revision is above 1 (name with `--earlier` the release that has it, or, if no release has it, remove its `revision:` line); `--earlier` names the releases before `PREVIOUS`, strictly newest first (by date, and on one date by release, a candidate `-rc.N` by N and before its release; another order compares nothing), so that a statement `PREVIOUS` left out (held back by a finding, or private) is compared with the newest of them that has it instead of counting as new ([docs/versioning.md](../../docs/versioning.md)) |
| `./oft port-layout [--dry-run]` | moves the old layout of a checkout to the per-project one (below), in place: every file under `proofs/<project>/<harness>/`, `counterexamples/<project>/<harness>/`, `findings/<project>/<harness>/` and `patches/<project>/`, and each `findings/<project>/unpatched.yaml`, whatever its name; it moves everything or nothing: it refuses, and moves nothing, when any path has no place in the per-project layout (`proofs/lib/`, `proofs/lib-lean/`, a file directly under `proofs/<project>/`), is a symbolic link, or would land on a path that holds other content; a second run moves nothing; `./oft generate` then writes the new folders' `dune` files. `--commit REV` does the same to REV's tree without a checkout and prints the id of the tree it writes into the repository |
| `./oft port-branch BRANCH [--layout-commit LC] [--namespace-commit NC] --worktree DIR [--onto REF]` | ports an old-layout branch or pull request head onto the per-project layout in DIR (a worktree of BRANCH): merges `LC^1` (the last old-layout commit) when BRANCH lacks it, rendering generated files again where they conflict, ports the merged tree with `port-layout --commit`, commits it with LC (the pure move, whose tree is `port-layout --commit LC^1`) as second parent, checks that the change against LC is the change against `LC^1` with every path moved, merges REF (default `origin/main`) and runs DIR's own `./oft generate` (the tools the branch now has, which its CI runs), with `--skip-shared` when an option line of those tools' `generate --help` lists it; with `--skip-shared` it then gives each shared generated file (those tools' `paths.is_shared`) REF's version and removes the ones REF lacks, so the port carries none, as lint's `paths` rule requires of a pull request; it prints the `git push` and `gh pr comment` commands and runs neither. The push it prints is `git -c pack.useSparse=false push`, because git's default sparse object walk sends every moved file again with a commit on top of the move (a 2.41 GB push against 462 KB, over GitHub's 2 GB limit). With `--namespace-commit NC` (the commit `./oft rename-namespace` made: its tree is its first parent's renamed), after the layout when both are given, it merges `NC^1` when BRANCH lacks it, takes NC's tree with each file BRANCH changed against `NC^1` taken from BRANCH and renamed as `rename-namespace` renames it (an opam file of the old stem is removed; no whole-tree rename runs), commits that with NC as second parent, and checks it file by file: every file BRANCH did not change is NC's, every file it changed is the rename of BRANCH's, and NC changed no file BRANCH changed by more than the rename (else that change would be lost); a BRANCH that already holds NC has the files it changed since renamed. Exit 0 ported, 2 a conflict the owner resolves, 3 a refused path (or a file the rename refuses), 4 the check found a difference, 5 no merge base with `LC^1` (or `NC^1`) |
| `./oft symbols --unstripped U --stripped S --lines L --harness P/H --build B` | writes build B's symbol fact, `projects/P/H/symbols/B.tsv` ([`symbols.py`](symbols.py)): every function (kind `func`), of size 0 too, and every data object with a size (kind `object`) of the symbol table of U, the build's unstripped twin (aliases each under its own name), and every allocated section of S (kind `section`, named with its leading `.`), with its address and its size. A function with a size also gets the SHA-256 of its bytes in S, exact and with its address immediates masked (a jal's or a branch's displacement whose target leaves the function, auipc, a lui whose every use as a base forms an address inside an allocated section of S, and the 12-bit low halves and gp-relative offsets that complete them, where a register holds a high half on every path inside the function: an auipc's also through the frame slot the compiler spills it to; a jump through a register goes only to the targets of a jump table proven from the code and the bytes S cannot write, and leaves the function as a tail call when its target is a loaded pointer or a number the code makes that is no address inside it, S (outside its unwind tables and the entries of the jump tables proven from a function's code, which are offsets) holds the address of none of its instructions but its entry, the function forms an address of itself only to call itself or jump to its entry, and no value an auipc or a lui makes in it, at any distance, goes into arithmetic other than a 12-bit immediate or into memory; when every such tail call is through a loaded pointer, that last rule is narrower: no such value is stored, and none that arithmetic moved (but a stack address plus a number, or a comparison's 0 or 1) is moved to an FP register, passed to a call or a tail call (a jal that leaves the function too), or given back; any other one may go anywhere in the function; a call to a global or weak function `symbols.NORETURN` names, or to a sanitizer runtime's function `symbols.NORETURN_RUNTIME` names (`__sanitizer::CheckFailed`, which a static link makes local), does not return, and after any other call no register the callee may overwrite holds a high half; and no register holds one in a function with landing pads, an FDE of S's `.eh_frame` with an LSDA), and its source lines from L, the output of `llvm-dwarfdump --debug-line U` run in the toolchain image of `release.yaml`; a function of size 0 (musl's `_start`) gets `-` for all three. A data object or a section gets the SHA-256 of its bytes in S, or `-` for one with no file contents (`.bss`), and `-` for masked bytes and lines. One case is still trusted as a tail call: a GNU C label address biased far from the function (`lla a0,.L2+8192`) and passed as a call argument to a callee that does the label arithmetic and stores the result, which the function then loads and jumps to; no path then leads from that jump to the label, so a field offset at the label can be masked as a low half and a changed function can read as `moved`. That is acceptable because a function's class only directs agents to the proofs to revisit, and Rocq checks every proof whatever the class; closing it (a value an auipc or a lui makes, passed as a call argument, takes the tail calls) made 610 of the 1,814 functions with a jump through a register in libreac's 36 v1.9.0 builds conservative under the rule of Ruling 53, which made 264; 122 are conservative now (`changes/masker/scan-tables-tools-fixes.txt`). Refuses an S whose SHA-256 is not the one `harness.yaml` pins for B, and a pair whose `.text`, a data object's bytes, or an allocated section (its bytes too, but a note's: each link writes its own build-id) differ. No check reads the fact: `elf.py` and `symbols.py` are not the checker (`keys.NOT_THE_CHECKER`) |
| `./oft classify BASE.tsv HEAD.tsv [--json]` | compares two builds' symbol facts ([`classify.py`](classify.py)) and prints one row per function, with its class, its names and its address and size in each build, then a count per class (`--json`: the rows, with each build's row of the fact, and the counts). Data objects, sections and functions of size 0, which have no bytes to compare, are not classified. A function is the names that share an address and a size (a name and its aliases). Functions are matched through their names: first each name with one function in each build matches those two; then a name with more than one function in either build (static functions of different files) matches each of them with the one an alias of that function already matched it with, so aliases stay together, then by bytes: the same address and exact bytes first, then the same masked bytes. A function is `identical` (the same bytes at the same address), `moved` (the same masked bytes), `changed` (other masked bytes), `added` (a name only HEAD has, or a duplicate with no match) or `removed` (a name only BASE has, or a duplicate with no match). Exits 1 naming a fact that does not load. No check runs it: `classify.py` is not the checker (`keys.NOT_THE_CHECKER`) |
| `./oft prove PROJECT/HARNESS --base REF [--head REF] [--json] [--post-check OWNER/REPO@SHA]`, or `./theorem prove ...` | a change's functions, contracts and source lines in one report ([`prove.py`](prove.py)), between commit `REF` of `--base` and `--head` (default `HEAD`): the class of each function of each build with a symbol fact at either commit (`oft classify`; a build with a fact at one commit only has every function added or removed) and a count per class over every build; each changed, added or removed function with its source lines from the head's symbol fact (a removed function's from the base's); and each contract file of the fuzz target at the head with its state, the first that holds: `changed contract` (its own file is new or changed), `needs work` (a function it names from `Symbols.v` is changed, added or removed; a reference the head's fact cannot resolve is resolved through the base's identifiers, never read as a symbol's name), `unknown` (its work key, `oft plan --contracts`, cannot be computed at the head or at the base), `needs work` (its work key differs from the base's in another component: a file it requires, the proof environment, a function's or a data symbol's kind or size), `data changed` (its work key differs only in the bytes of data objects or sections it names, each of the same kind and size at both commits: Rocq decides, and no agent is predicted) or `unchanged` (its work key is the base's), with why; then each contract file of the base that the head lacks, `removed`. The state is a prediction of which proofs need an agent, never a verdict: Rocq checks every proof. Prints Markdown; `--json` prints every function with its class, names, source lines and place in each build, and every contract with its state, why, `base`, `changed` and `references` as `oft plan --contracts` gives them, and `functions`, the class and source lines of each function it names, for the change ledger. `--post-check` also posts the report as the pull request check `theorem/prove: PROJECT/HARNESS` (each fuzz target's check run has a name of its own, so a pull request that changes two shows both), a GitHub check run on commit `SHA` (the full commit id of the pull request's head) of `OWNER/REPO` ([`check_run.py`](check_run.py)): `action_required` when a contract needs work, is a changed contract, is removed or is unknown; `neutral` when every other contract is `data changed` (the summary says Rocq decides); else `success`. Its title is `<n> contracts need work, <m> functions changed` (n: needs work, changed contract and removed; m: the changed, added and removed functions of every build), then `, <k> data changed` and `, <u> unknown` when there are any; its summary is the Markdown, cut to GitHub's limit of 65,535 characters when it is longer: the counts stay whole, then come the rows of the contracts that are changed contracts, removed, need work or are unknown, then the changed, added and removed functions, then the other contracts, and a last line says how many rows are left out (the full report is the command's output, and every row is in `--json`). The token is `GH_TOKEN`, a GitHub App installation token or a workflow's `GITHUB_TOKEN` with `checks: write` on `OWNER/REPO`, and the API is `GITHUB_API_URL` (default `https://api.github.com`); a line on stderr, after the report, names the check run and its page, or GitHub's answer and the permission it asks for. A token that holds whitespace, a control character or a non-ASCII character is refused unsent and is not shown. In the stderr line, `[token]` stands for each whole copy of the token in GitHub's message, its body (when it has no message, cut to 200 characters after the token is replaced), a header or an error; a part of the token, or the token written in another form (escaped or encoded), is not found. Exits 0 with a report (and, with `--post-check`, a check run), whatever its states, and 1 naming a unit that is not `PROJECT/HARNESS` or has no symbol fact and no contract file, a commit git does not have, a symbol fact that does not parse, `--post-check` with no `GH_TOKEN` or a malformed one (both before the report), or a check run GitHub did not make (its refusal, no answer, or an answer cut short). No check runs it: `prove.py`, `check_run.py` and `ci/prove-pr` are not the checker (`keys.NOT_THE_CHECKER`). On a pull request, `pr.yml`'s `prove` job runs it for each unit the plan names (below) |
| `./oft change-ledger tag CHANGE --step STEP --session ID --host HOST --transcript PATH [--vm NAME]... [--from TIME] [--until TIME]`, `./oft change-ledger check CHANGE --step STEP --time-log PATH`, `./oft change-ledger no-work CHANGE --step STEP --why TEXT`, `./oft change-ledger sum CHANGE [--unit PROJECT/HARNESS --base REF [--head REF]] [--vm-samples FILE]... [--vm-deletions FILE]...` | what one change cost, from the records that hold it ([`change_ledger.py`](change_ledger.py)), in `changes/CHANGE/`, which only this repository has (`oft release-tree` removes `changes/`). `tag` records in `sessions.tsv` an agent session that worked on a step of the change, the machine it ran on, the VMs it drove and its window (`--from`, `--until`: ISO 8601 times with a time zone; `-` is no bound); the transcript must be the session's own, and a session counts in one step of one change. A session that worked on several steps or changes (a walk over upstream commits, one change each) is tagged once for each, each tag with a window, no two windows of one session overlapping: each transcript entry counts in the one tag whose window holds its timestamp (`--from` is in the window, `--until` is not; a turn counts whole in the window of its own timestamp) and in no change when none does, so no cost is summed twice and none is a typed share; with a window, a usage with no timestamp is not measured, and a window that holds no entry is refused. A resumed agent's transcript, `X-2.jsonl` beside `X.jsonl`, is a fragment of the same session (under a new session id or its first): it is tagged in the same step (or with a window apart from the others'), `sessions` counts the session once, an entry a fragment repeats counts once, by its id, and a fragment's wall time and machine span are those of its own entries. `check` records in `checks.tsv` the GNU `time -v` log of a check. `no-work` records in `no-work.tsv` that a step needed no work and why (`--why`, such as `oft prove` finding no function changed between the upstream commits): its row reads 0 for the agent figures, `vcpu_hours` and `check_seconds`, `-` for its wall time, and `gaps.tsv` names nothing for it; the total reads so when every step needed no work. A step with a tagged session or a check log did work and is refused; a step with no record at all still reads `not measured`. `sum` checks each tag again (the transcript's own session, one step of one change per session or windows apart, no session or check log in a step that needed no work), then writes `ledger.tsv`, one row per step and then `total`, with the columns `step, sessions, wall_start, wall_end, agent_hours, input_tokens, output_tokens, cache_read, cache_write, cost_usd, vcpu_hours, check_seconds, proof_lines_added, proof_lines_removed, identical, moved, changed, added, removed, contracts_changed, contracts_needing_work, edits_address, edits_layout, edits_content`; `session-totals.tsv`, each tag of a session with its window, the model it asked for and the models that answered; `gaps.tsv`, each figure not read in full and why; `inputs.tsv`, the unit, the commits and the sample and deletion files it read, and when; with `prove.json` (`oft prove --json`, saved when the change was made and before any contract was edited), `contracts.tsv`, each contract's predicted state against whether its file was edited; and, when it is missing, `journal.md` from [`templates/journal.md.tmpl`](templates/journal.md.tmpl). The tokens and `cost_usd` are each assistant turn's `message.usage` (omp's price of the call) and those of omp's own calls for the session (`model_usage`); `agent_hours` is each assistant turn's time from the transcript entry just before it, a turn over 10 minutes left out, and a turn with no timestamp, after an entry with none or timed before it not measured; `vcpu_hours` is the samples (`--vm-samples`: `notes/compute-ledger.tsv`, `notes/idle-stop.tsv`) of each session's host and VMs inside the session's span, each interval between two samples under 45 minutes apart times the vCPUs its machine type names (`<series>-<class>-<vcpus>` or a custom type; any other form names none); two samples of different lives of a VM (`idle-stop.tsv`'s `created` and `last_start`; a sample with no life takes that of the latest start before it, unless a recorded deletion ended that life first) make no interval, and a life counts from its last start; a deletion the compute inventory records (`--vm-deletions`: `gone=`, which `bin/ossv-vm` writes; one that a later sample of a running life contradicts is another VM's) ends the life it falls in, and less than 45 minutes after the life's last sample the time up to it counts; each part of a span in which a machine may have run with no measurement (a sampling gap of 45 minutes or more, the time after a life's last sample up to its deletion if one is recorded, the stretch between two deletions with no sample between them, the time after a deletion before the next sample of a life of no known start, a machine type with no vCPU count, a machine with no sample) is named in `gaps.tsv`, and so is a span in which no record shows a machine running; a `vcpu_hours` with no measured interval is `not measured`, never 0.00; `check_seconds` is each time log's elapsed time; with `--unit`, the proof lines are `git diff --numstat` over the unit's proofs folder, the function classes and `contracts_changed` are `oft prove`'s, and each rewritten line pair of `git diff -U0` there is `edits_address` (equal with its hex literals masked), `edits_layout` (equal with every number masked) or `edits_content`. A figure no record holds is `not measured`, one read in part `<sum> + not measured`, never zero (0 is written only for a step `no-work.tsv` records); `-` does not apply to its row (the git figures are on the total row). A transcript cut by a crash (a tail of zero bytes or half a line) counts what it holds, and `gaps.tsv` names it; a tagged transcript or check log that cannot be read, a malformed line in a transcript, a tag that breaks `tag`'s rules, or a `prove.json` of another unit or base exits 1 and writes nothing. No check runs it: `change_ledger.py` is not the checker (`keys.NOT_THE_CHECKER`) |
| `./oft rename-namespace --to NAME --opam-stem STEM [--check] [--jobs N]` | renames the Rocq namespace and the opam stem (release.yaml's `namespace` and `opam_stem`, the defaults when it names neither) in every tracked file of the checkout but the tools, `CHANGELOG.md`, `docs/versioning.md`, `docs/statements.md`, `tests/negative/old_namespace/`, each fuzz target's `proofs/provenance/evidence/` and the shared generated files, the three stored proof encodings among them (below); sets both in `release.yaml`, removes the opam files of the old stem and runs `./oft generate --skip-shared`. It writes nothing unless every file passed: it refuses a tree whose `release.yaml` already names NAME, a tracked path that holds the old name, a file that already holds NAME or `rocq-STEM` (the rename must be one-to-one), and any file it cannot rename, each with its path and line. Then no file but those it leaves alone may hold the old name or `rocq-<old stem>`. It lists each blob it leaves unparsed and the count per fuzz target. `--check` runs the refusals and the before-gate and writes nothing. `--verify A B` instead compares commit B with the rename of commit A, by each one's `release.yaml` names, and exits 0 only with no problem |

## `./oft check` reads the whole tree

`./oft check <project>/<harness>` loads the facts of the whole checkout and checks
their rules before it looks at the fuzz target it was given, as `generate`, `lint`,
`plan`, `approvals` and `release-tree` do (`ledger` and `change-ledger` read the
history instead, and load no tree).  So a partial tree -- one project copied into an
empty directory, a bundle cut down to the unit under test -- fails that reading, and
never reaches Rocq.  What it prints is a wall of two kinds of line, one per fuzz
target the tree no longer holds:

    error: release.yaml: image_libraries lists ...
    error: approvals.yaml: ... is not an included fuzz target

and no Rocq error at all, because nothing was compiled.  Read a run that ends that way
as a tree that is short of files, not as a proof that failed, and send the whole tree
to the check: a `git archive` of the commit, or a clone of it.

A unit genuinely does have a check of its own files alone, and it is `--facts-to` and
`--facts-from` ([`check.py`](check.py)): one run over the whole tree writes each unit's
facts to a directory, and each later run reads its unit's facts from there and checks
it in a view that holds only that unit's files, loading no tree.  A cut-down tree
without `--facts-from` is not that; it is the error above.

## Where a fuzz target's files live

Each fuzz target's statements, proofs, counterexamples and findings live in its own folder,
`projects/<project>/<harness>/` ([`layout.py`](layout.py) spells every path):

| path | contents |
|---|---|
| `projects/<project>/<harness>/` | the facts and the rendered statements (`harness.yaml`, `Statements.v`, `Images.v`, `images/`, `source/`, and each build's symbol fact, `symbols/<build>.tsv`, with `Symbols.v` rendered from them) |
| `projects/<project>/<harness>/proofs/<statement>/` | one statement's proof: `Proof.v` (or `Refutation.v`), `proof.yaml`, `dune` |
| `projects/<project>/<harness>/proofs/lib/` | the fuzz target's proof library |
| `projects/<project>/<harness>/proofs/provenance/` | the build record of its binaries |
| `projects/<project>/<harness>/counterexamples/<statement>/` | one statement's counterexample |
| `projects/<project>/<harness>/findings/` | its findings (`<slug>/`) and their `series` |
| `projects/<project>/unpatched.yaml`, `projects/<project>/patches/` | a project's unpatched pins and its patches |

A generated `dune` file in each `proofs/` and `counterexamples/` folder shuts it out of the statement theory of the
folder above.  The tools also read the old layout, in which these lived under `proofs/<project>/<harness>/`,
`counterexamples/<project>/<harness>/`, `findings/<project>/<harness>/`, `findings/<project>/unpatched.yaml` and
`patches/<project>/`; a fuzz target with files in both layouts is an error, and so is an old-layout path in a tree
that holds per-project ones.  `./oft port-layout` and `./oft port-branch` move a tree or a branch from one to the
other.  Lint exceptions match a path in either layout.

## The facts, and what is rendered from them

The facts are `release.yaml`, `projects/<project>/project.yaml`, public patch
text in `projects/<project>/patches/` (`patches/<project>/` in the old layout;
each `patches` entry names its file there), `projects/<project>/<harness>/harness.yaml`
(with the harness's `source/` copy, `Distribution.v` and the symbol facts `oft
symbols` writes beside it), and the proof and counterexample directories. Their
YAML schemas are in [`schemas/`](schemas/), in a small closed vocabulary
that [`schema.py`](schema.py) reads: any key a schema does not list is an
error.  [`rules.py`](rules.py) adds the rules that relate one fact to
another; among them, a statement's name follows from its fields, and the
header of `Distribution.v` must agree with the definitions in its body.
`rules.symbol_facts`, which `oft generate` runs and `oft check` does not
(`symbols.py` is not the checker), refuses a symbol fact that does not load,
and two names of one that give one identifier of `Symbols.v`.

From the facts, `generate` renders `Statements.v`, `Characterise.v`,
`Images.v`, `Symbols.v`, `images/dune`, the per-harness `dune` file, the opam
files, `dune-project`, every README, `index/`, and the header of each
`Distribution.v`.  `Symbols.v` (`<namespace>.<p>.<h>.Symbols`), for a fuzz
target with a symbol fact, has a module for each build with one (`Plain`,
`Ubsan`, `Asan`, `AsanUbsan`) that defines `s_<name> : Z`, the address of each
function and data object, and, in its module `Size`, `s_<name> : Z`, its size,
with each character of the name outside `[A-Za-z0-9_]` written `_`, and the
same in its module `Sec` for each allocated section, less the leading `.` of
its name (`names.symbol_idents`); a name that two or more functions or
objects, or two or more sections, of the build share has no identifier there,
and the module says so.  A contract names a function or an object as
`Symbols.<Build>.s_<name>`, its size as `Symbols.<Build>.Size.s_<name>`, and
data no symbol names, such as a GOT slot, as a section and an offset,
`Symbols.<Build>.Sec.s_got + 0x10`, never by its address (lint's
`contract-literals` rule).  All of
the prose is in [`templates/`](templates/) and
[`phrasebook.yaml`](phrasebook.yaml); [`shapes.py`](shapes.py) is the one
place that maps a statement's fields to the definition of
`theories/Shapes.v` it uses, and refuses a combination it does not list.
Rendering is deterministic, and `render_all` is importable, so a tree and its
preview are rendered by the same code.

Proved, refuted and counterexample statuses are never written in the facts:
they follow from each fuzz target's proofs and counterexamples.

`approvals.yaml`, in a checkout that has one, lists the proofs a release
carries, by fuzz target and statement, with one entry per source of a fuzz target's proofs
([`schemas/approvals.yaml`](schemas/approvals.yaml)). `./oft release-tree`
removes it, so a release never holds it. An entry that the merge of a project's enrollment
pull request on the OSS Verify port writes (`origin: enrollment`, with an `enrollment` block
that names the merge) is a ceiling: it lists the statements that the enrollment's facts pull
requests wrote, and a release carries the proofs of those that exist, are not held back and
do not refute. No such entry lists a fuzz target whose build record names a package: that
error stops every `./oft` command that checks the facts, `./oft approvals` among them, which
keeps each `enrollment` entry as written, so such an entry must be removed from
`approvals.yaml` by hand.
`./oft release-tree` names each statement of another entry that has no proof, and only counts
those of enrollment entries.

So what the command table above and the `schema` rule below say of an `approvals.yaml` entry
holds for an entry of origin `this-repository` or `submission`. In an `enrollment` entry, a
held or private project, a held or refuted statement, and a fuzz target or statement that no
longer exists are no error: `./oft release-tree` keeps none of their proofs and goes on. An
`enrollment` block goes with that origin and no other, as `record`
goes with `submission`. `./oft approvals` keeps every `enrollment` entry as written, and a bare
line names only the proofs that its fuzz target's `enrollment` entries do not list; it writes
nothing when `approvals.yaml` cannot be read, or an `enrollment` entry in it does not match its
schema.

A finding, a library bug found while proving, is kept on the proof branch as
`projects/<project>/<harness>/findings/<slug>/` (old layout: `findings/<project>/<harness>/<slug>/`):
`finding.yaml` (the statements it shows false, its state, its summary, its patch and its recorded runs),
`input.bin`, `control.bin` and its patch.  `projects/<project>/unpatched.yaml` (old layout:
`findings/<project>/unpatched.yaml`) pins the binaries built without the patches, which the findings run on, and
the fuzz target's findings `series` lists the patches in build order.  A
finding's `input.bin` and `control.bin` are whole driver inputs, header and
payload, so they may be as large as 1 MiB (a harness may read a payload of 64
KiB or more); every other file of the findings is at most 64 KiB.  A public
finding's patch ships as an entry in its project's `patches` list, and a build
patch with no finding can be listed there with its upstream state;
[`docs/facts.md`](../../docs/facts.md) ("Public patches") says what each entry,
and the copied port record of a port build that can ship, must agree with.
A finding is never deleted.  It stops holding its project only through a checked
state change to `pruned`, `not-a-defect` or `public`.  No rendered file reads
the findings, and they never ship: `./oft release-tree` removes them.  A project
with a finding that is `patched` or `reported` ships only as `status: held`,
`reason: held`.  An enrolled project (`enrolled: true` in its `project.yaml`)
whose holding findings are all `open` ships without the statements they name, and without any their recorded input shows false (with each held agreement's bound and decidability statements). The whole project is held instead if that would leave a harness with no statement, or a harness that publishes a build with only withheld statements, if the project has a proof library (`lib/` in a fuzz target's proofs folder, which ships unchecked), or if it publishes a binary that its `unpatched.yaml` does not pin as the one its findings run on, since that build may carry the fix;
once one is `patched` or `reported`, its binaries carry the fix, and the whole
project is held.  A state never returns to `open` from `patched`, `reported` or
`public`, whose patch the pinned build carries; it may from `pruned` or
`not-a-defect`.

A proof branch takes pushes and merges, so a finding could be added and then
deleted or rewritten between the two trees a pull request compares.
`./oft ledger` judges the history instead.  A record (a directory with
`finding.yaml`) is anchored at its first version that is evidence, decided by
its own files alone: its `input.bin` and `control.bin` are regular files of at
most 1 MiB that begin with a complete driver header, each of its `statements`
is an agreement or halts statement by its name, and its input and control each
hold a run of every build those statements name, of the shape `oft check
--record` prints.  Any recorded runs of that shape anchor a record, whether or
not they show its statements false, so a record's runs must come only from
`oft check --record`, which prints them only when each run has that shape (no
timeout, no signal a finding does not record), the input shows each statement
false and the control shows none.  No schema, `harness.yaml` or
`unpatched.yaml` decides it, so neither another file nor a later change to
the tools turns evidence back into a draft.  Before its anchor a record is a
draft, which CI never re-ran, and may change in any way or be renamed or
deleted.  Anchors are found by ancestry, and two that differ in `input.bin`,
`control.bin`, `statements` or recorded runs are refused.  From its
anchor on, every file of the record that a commit of `BASE..TIP` or a parent
of one had is in `TIP`; its `input.bin` and `control.bin` are the anchor's, its
`statements` include the anchor's, and the unpatched pin of each build its
statements name keeps its first value after the anchor (a pin for another
build may be added).  Its recorded runs are the anchor's too: a push to a
proof branch runs no check, so a pin in the anchor commit may already name a
fixed binary, and the same binaries in the same runner give the same runs.
Only a new runner image can change an honest record's runs.  A record anchored
outside `BASE..TIP` is held to where `TIP`'s history meets `BASE`.  For each
merge base of the two (`git merge-base --all`; more than one only after a
criss-cross merge), its entry commit is the oldest commit of `BASE`'s
first-parent line that has it, which passed CI as long as `BASE` takes changes
only through checked pull requests (a branch rule on `BASE` enforces that, not
these tools).  The merge base alone may be a proof-branch commit that no check
judged, put right before main merged it.  So the reference is the merge base
when its entry commit has the same runner and recorded runs (its text may
differ), and otherwise the newest commit of that line that `TIP` has, since
the entry commit then holds main's changes too.  In a pull request both are
`BASE`; on a push to a proof branch, a
branch that lags main is held to what it has.  The record keeps the runs each
reference has, except one whose `images.runner` in `release.yaml` (the image CI
re-runs findings in) differs from `TIP`'s, as in lint's base comparison.  A
record anchored only in `BASE..TIP` keeps its anchor's runs whatever the
runner, since that commit's `release.yaml` was not checked either.  If a new
runner changes such a
record's runs, CI's re-run fails, so its branch cannot merge and its project
stays held.
Each parent of a merge counts.  The rule is net: only `TIP` is judged, so a
file beside a record that `paths.py` does not list (an old `run.sh`) may go,
and restoring what was deleted clears the finding.  No replace ref or graft is
read.  CI runs it in a pull request's lint job and on every push to a
`proofs/` branch, where a forced push fails: a proof branch is never
rewritten.

## The rules (`./oft lint`)

| rule | what | where it runs |
|---|---|---|
| `paths` | every path matches exactly one entry of [`paths.py`](paths.py), which says who owns it; CI compares the proposed findings ledger with its trusted base, file by file, so a finding and its unpatched pins are never deleted, moved or renamed, a base finding's `input.bin` and `control.bin` and the unpatched pin of each build its statements name never change, nor do its recorded runs of those builds unless the proposed `release.yaml` pins another runner image, its `statements` only grow, and its state never returns to `open` from `patched`, `reported` or `public` (its state may otherwise change, from `pruned` or `not-a-defect` back to `open` too, as may its summary, `upstream` and patch text, and a pin for another build may be added), and `./oft ledger` holds every commit of the change's history to the same rule from each record's anchor, its first version whose `input.bin` and `control.bin` are regular files that begin with a complete driver header and whose `finding.yaml` names agreement or halts statements only and records a run of every build they name, of the shape `oft check --record` prints (a draft before it may change, be renamed or be deleted, two anchors of one record that differ are refused, and only a record anchored in the base's history may record its runs again under another runner image); every finding file is a bounded regular file before the loader reads it, so links and special files are refused before their target can be opened; exported facts change only in a release pull request; a contributor's pull request touches only `proofs/`, `counterexamples/`, `docs/` and generated files, and the paths only this repository has (`INTERNAL` of `paths.py`) are a maintainer's; no pull request of any kind adds or changes a shared generated file (`SHARED`: the line's render after the merge writes them, so run `./oft generate --skip-shared`), though it may delete one; no `.vo`, `.hex`, `.pyc`, ELF file (but the small ones the tests of `oft symbols` read, in [`tests/fixtures/elf/`](tests/fixtures/elf/README.md)), LFS pointer, symbolic link or other file that is not regular (none is followed, opened or read for the text rules); no NUL byte anywhere in a file, but in a counterexample's or a finding's `input.bin` and `control.bin` (in either layout), in the tests' fixtures, and in a classifier program, which under a proof's `classifier/` is the one ELF file and the one binary file, the program its `proof.yaml` pins (`classifier.elf`, with its `classifier.sha256`); no LFS filter or `working-tree-encoding` in `.gitattributes` (a checkout in another encoding would hide a file's text from the text rules); no name with a `"`, a `\` or a control character (git lists such a name quoted, and CI could not judge it); notes only for listed projects; a symbol fact is named for a build its `harness.yaml` publishes; size caps (a file over its cap is not read for the text rules); with `--release` only, every project folder holds the project page `oft generate` renders; in a tree whose `release.yaml` renames the Rocq namespace, no file but the ones `./oft rename-namespace` leaves alone and the shared generated files holds the default one (run `./oft rename-namespace`, or `./oft port-branch` for a branch) | CI |
| `schema` | closed schemas; no repeated YAML key, no YAML alias and no YAML collection nested more than 64 deep; the rules between facts (counts, names, the images, withheld builds and statements, and a harness that publishes a build carries a statement `Statements.v` defines, unless it withdrew every one); a finding's recorded input shows each of its statements false (none, once it is pruned) and its control none, a harness's series is exactly the patches of its patched, reported and public findings; the `patches` entries and copied port records agree with the findings as [`docs/facts.md`](../../docs/facts.md) ("Public patches") says; a not-a-defect finding's statements are recorded as false, and only a project a finding holds back builds from the port's internal copy or attaches to `findings-<project>`; an asset on an enrollment commit's drafts is on the project's own, `enroll-<project>-<12 hex>` for the binaries and the same with `-src` for the rest, of one commit; `release.yaml`'s counts describe the tree the file is in, and `oft release-tree` writes the release's own into the cut; each `approvals.yaml` entry names an included fuzz target, at most once per source (origin and record), of a project no finding holds back and not private, statements it has, each in one entry of its fuzz target only, none of them refuted or held back by an open finding of an enrolled project, and, for a fuzz target whose build record says its proofs came from a package, only statements `proofs.written_here` names in a `this-repository` entry and none of them in a `submission` entry (and only such a record has `written_here`), and a record exactly when it is a submission; a symbol fact (`symbols/<build>.tsv`) reads whole and its `sha256=` is the one `harness.yaml` pins for its build, which must be one it publishes (`paths`); with `--release`, no placeholder digest is left | CI |
| `private-data` | in every NUL-free file read as text, link or not: no host path (one under `/data`, `/home` but `/home/opam`, `/srv`, `/Users`, `/root`, `/mnt/disks` or `/mnt/nvme`; the change ledgers in `changes/` may name one, since each records where its logs and inputs are on the machine that summed it and `oft release-tree` removes `changes/`), private key, access token, or `theorem-labs` repository outside the public ones (among them the OSS Verify port, `theorem-labs/oss-verify`) named as `theorem-labs/<name>` or `theorem-labs.github.io/<name>` (after `/`, `\` or `:`, in any case, also written with `%2F` or a character reference, or, in a file GitHub renders as Markdown, split by a backslash escape or an HTML comment); the port's internal copy is allowed only as the value of a held project's `build.oss_verify.repository`. Outside upstream copies (a fuzz target's source copied from upstream, the licence texts and the recipe slice of a build record), also no private IPv4 address (including Tailscale's shared range, `100.64/10`), e-mail address or private host name (a name under `localhost`, `internal`, `internal.cloudapp.net`, `local`, `corp`, `lan`, `home.arpa` or `ts.net`, in any case). A reviewed entry in [`lint-exceptions.yaml`](lint-exceptions.yaml) can clear one occurrence in an upstream copy or copied port `project.yaml`, or one e-mail address in another copied port project file (such as an author's copyright line; never a URL's user information) | CI |
| `links` | links in the files this repository wrote, in the port's files of a port build record, and in an OSS Verify target's source copy, as a regular expression reads them (in a file whose name GitHub renders as Markdown, in any case, also the forms GitHub renders as a link, and each line read again as GitHub shows its text, without backslash escapes and HTML comments), judged by what a browser opens, as [`urls.py`](urls.py) parses it after the WHATWG URL standard: never a machine on a private network, including through a non-web scheme with a DNS-shaped or IP-literal host, and a `theorem-labs` repository, on any host, only if it is a public one; a URL whose host IDNA refuses is a finding; in rendered text, docs and facts every link is one the facts record or a fixed public one (the Debian snapshot archive, which the runner image installs from, may be read over http, and the two pages AddressSanitizer's runtime names in a report, which the comparison kit copies into a build record's evidence, stand as they are written and nothing under them). Upstream source copies, licence texts and the recipe slice of a build record are not read for links; port files and an OSS Verify target's source copy are held to the private-host and private-repository checks but not the allowlist. Markdown HTML reads `href`, `src`, `srcset`, `cite` and `longdesc` | CI |
| `free-text` | no free-text field that the rendering has no place for | CI |
| `licence` | a proof file's licence lines agree with [`NOTICE`](../../NOTICE) and [docs/adding-a-proof.md](../../docs/adding-a-proof.md), requirement 7: they open the file, in its first 10 lines (a licence tag, or a copyright of Anthropic, changed or not, below them is refused); every `SPDX-License-Identifier` tag there names one licence (a second tag may restate it), `Apache-2.0 OR MIT` or `MIT`; a file with Anthropic's copyright line, `(* Copyright <year> Anthropic PBC *)`, says `Apache-2.0 OR MIT` and names no changed copyright of Anthropic beside it, and a file that says `Apache-2.0 OR MIT` has that line; such a file is in a fuzz target's proofs folder whose build record lists `LICENSES/anthropic-proofs-LICENSE`, `-LICENSE-MIT` and `-NOTICE` under `proofs.texts` (not checked in a contributor's pull request, whose record the maintainer writes); and a file that opens with the comment of a program's instruction words or of data computed from one has no other licence lines. The rule reads each file on its own: it compares no file's text with another file's, so it finds no copy. A `licence-pending` entry in [`lint-exceptions.yaml`](lint-exceptions.yaml) (`unit`, `rule`, `due`, `series`, `reason`) lists a fuzz target whose licence lines a series of its own applies: lint prints and counts that fuzz target's licence findings as pending and does not fail on them. The series removes its own entry: an entry is a finding when its fuzz target has a Rocq file and no licence finding left (judged when every file is read; an entry may wait for a fuzz target whose proofs have not come yet), and when it is not exact; after its due date (in UTC) it is a finding for a lint with no change to judge and for a change that touches its fuzz target (in either layout) or adds or edits the entry in `lint-exceptions.yaml` (compared with the base; with no base, any change of the file), and a warning for any other change, so a series that deletes its own entry fails on no other; and in a pull request's lint (`--pending-base`) an entry that the base commit does not have is a finding when the pull request changes a file of a fuzz target's proofs folder, so the list only shrinks: a proof pull request adds no entry, and a pull request of the tools adds one and its review judges it. A carriage return before a line feed is part of the line end | CI |
| `contract-literals` | a contract file (`<fn>_c.v` under `lib/Prog/`, `lib/U/Prog/`, `lib/A/Prog/` or `lib/B/Prog/` of a fuzz target's proofs folder, in subfolders too) of a fuzz target with a symbol fact writes no numeral, hexadecimal or decimal, outside comments and strings, whose value (read whole, with its fraction and its exponent: `0x1.32ap16` is `0x132a0`, and `784.96e2` is `78496`, the same number) is an integer that an allocated section (a `section` row of the fact) of one of its builds holds: that is an address, and it names the function, object or section from `Symbols.v`; the finding names the section and the first build, in the order plain, ubsan, asan, asan-ubsan, that holds it. Any other numeral (a count, a size, an offset, the image's base, a division's magic multiplier, a float's bits, a stack bound, a value that is no integer, a numeral inside a name) is no address `Symbols.v` names and passes. Each reference to `Symbols.v` it writes, `Symbols.<Build>.<path>` (under the library's path or not) or, after `Require Import Symbols`, `<Build>.s_<name>`, `<Build>.Size.…` or `<Build>.Sec.…`, read as the whole name Rocq reads (blanks and comments may stand before each `.field`), is one the build's module defines: a name the build's symbol fact lacks (a function the compiler inlined, say), a longer path under a defined name, a name two or more of its rows share, and a build with no symbol fact are findings, before any compile. A change to a symbol fact makes `--changed-only` read every file | CI |
| `proofs` | no `Axiom`, `Parameter`, `Admitted`, `admit`, `Admit Obligations`, plugin, file effect or `Unset ... Checking` in a fuzz target's proofs folder, no axiom declared another way there (`Declare Instance`, `Declare Module`, and `Variable`, `Hypothesis` or `Context` outside a Section, where a Section that the control flag `Fail` or `Succeed` opens is none, and `#[Fail]` is no such flag), no `deprecated` or `warn` attribute (its note prints where the theorem is used), no `Attributes` command and no `Reset` (but `Reset Ltac Profile`), and no `Load`, `Cd` or `Extra Dependency` in a generated Rocq file of `projects/` (comments and strings are skipped by a real lexer; in a proofs folder, a notation token or a comment that could make Rocq lex them otherwise is refused, and so is a declared token that ends in `.` (but `..`), which would end a sentence for these rules; a reviewed entry in [`lint-exceptions.yaml`](lint-exceptions.yaml) that names one such token exactly (path, line, message, its string literal, count 1) clears it; an entry less exact, or one no finding matches, is a finding; in either, a Rocq file that is not text is refused); no wall-clock limit in a Rocq file of the repository (the proofs folders, `theories/`, `projects/`, `tests/` and the `.v.tmpl` templates): no `timeout` or `timeoutf` used as a name, Ltac2's `Control.timeout` and `Control.timeoutf` among them, no `Timeout <n>` and no `Set Default Timeout <n>`, unless the line that has it ends with `(* timeout-ok: <why> *)` saying why an expiry cannot fail the check, which a reviewer judges; and a Ltac2 `@external` binds only a primitive of `lint.EXTERNAL_ALLOWED`, which no such comment clears ([docs/proving.md](../../docs/proving.md)); the wrapper's `Print Assumptions` and the allowlist are the authority | CI |
| `withheld` | a withheld item shows no detail: a withheld build has no size, SHA-256 or segment count and ships no binary, a withheld statement has no evidence and no fingerprint, and a project that withholds anything says so, by reason only | CI |
| `records` | with `--release`: every fuzz target with a proof has a build record, `provenance/PROVENANCE.yaml` in its proofs folder (in the layout its facts are in: `projects/<project>/<harness>/proofs/`, or `proofs/<project>/<harness>/` in the old one), and each record is complete and says what the facts say. It holds no value `pending`, `NOASSERTION` or `TODO`, nor `pending: true`, but under a key whose name ends in `_in_release_records`. Its `binaries` are the four published builds of its `harness.yaml`, by SHA-256 and size. Its `toolchain.builder_image` is `release.yaml`'s `images.builder[0]`, and every record a recipe or a port built names one static-asan commit (`toolchain.static_asan.commit`). A port record's `port` and `port.asset` are its `project.yaml`'s `build.oss_verify` and `assets.port`, and it names no recipe. A fallback record names a reason, the recipe commit and the builder image by digest, its two static-asan commits (every fallback record one public one), and a rebuild that gave `identical x4`, with its evidence. Its `binary_asset` and `source_asset` are its `project.yaml`'s `assets.bin`, `assets.src` and `assets.src_manifest`, and a port record's `port.asset` its `assets.port`, by file, bytes and SHA-256: a record names no release, since `project.yaml`'s assets are the one place that names one (Contract C1, [`tools/enroll/README.md`](../enroll/README.md)), and a record written before C1 that still names one names `project.yaml`'s; `LICENSES/` holds exactly the texts its `licence.components` name; `upstream.licence` is set; the `licence.source_bundle` of a GPL- or LGPL-licensed component is C1's list of `{file, sha256}` entries, which cites the project's `-src.tar.zst`, each file once, and each with the SHA-256 that its `project.yaml`'s assets or `release.yaml`'s recipes and sources pin it with, which the publishing workflow downloads and checks; every recipe patch is build glue; and each `recipe.overlay` file has the SHA-256 that `recipe/MANIFEST.tsv` gives. The recipe a record cites is the `schema` rule's. A port-built project's binary archive goes with its port archive (`assets.port`) | a release (`release.yml`, the publishing workflow) |
| `model` | with `--release`: the model the checker image builds is the one `release.yaml` names. The cut of the model at `semantics.commit` (the files `toolchain/lps-core.paths` lists, or without that file `package/`), fetched from the model's public repository and hashed as `toolchain/checker.Dockerfile` hashes it, is the `LPS_TREE_SHA256` that file pins, and the hash [`model.yaml`](model.yaml) requires of a commit on that line of the model's history | a release (`release.yml`, the publishing workflow) |
| `pins` | with `--release`, read from GitHub: `release.yaml`'s `semantics.commit` is on a branch or tag of the model's public repository, and each static-asan commit the build records name is on one of `theorem-labs/static-asan` | a release (`release.yml`, the publishing workflow) |

The per-file text rules (`private-data`, `links` and `proofs`) read a path only this repository has (`INTERNAL` of
[`paths.py`](paths.py), but its `INTERNAL_DIRS`) for a private key or an access token alone, which is as bad there as
in a shipped file: no release carries such a path, and `tools/publish/` holds the publishing scanner's needles, host
paths and addresses on purpose.

`private-data` and `links` say what a release may publish, so under
`dev/stream/`, the OSS Verify stream's operational tools, `links` reads nothing
and `private-data` reads credentials alone: `./oft release-tree`
cuts that directory whole ([`release_tree.py`](release_tree.py), `INTERNAL`),
and those tools have to name the boxes they run on, the paths they live at and
the packages their lock file pins by URL.  A private key, an access token or
a URL's user information there is still a finding, since a committed
credential is a live credential whether or not it ships, and user information
names no place; a reviewed entry in
[`lint-exceptions.yaml`](lint-exceptions.yaml) clears a stand-in one.

Every rule fails when it examined nothing, but `records` in a tree with no proof and no build record.  The tests in
[`tests/`](tests/)
plant a positive for each rule and require it to fail, and require the
fixture tree and this repository itself to pass.  `pr.yml` skips the test of
this repository when the change leaves `tools/` as it is outside the test data
in `tests/` (no Python file), `ci/` and this README, and leaves `.github/` and
every `.gitattributes` as they are: its lint job then runs the same code, over
the whole tree or, with `--changed-only`, over the changed files with every
other file's verdict as at the base.  That holds for a pull request, a merge
queue group and a push to main alike; a push with no base to compare with
runs it.  A later push to a pull request is linted with `--changed-only`
against the tree its last passing lint read, when that lint's record holds:
the record (in the Actions cache of that pull request's ref only, so never
read by the merge queue) names the kind of change (`--pr-kind`), the branch
the pull request goes into, the base's `tools/` tree, which holds
`lint-exceptions.yaml` and so the licence-pending
entries `--pending-base` reads, and the merge commit's parents and tree,
rebuilt with `git merge-tree` before it is trusted (`pr.yml`, the plan job's
`lint_since` step).  A record is not used when a file of a fuzz target that a
licence-pending entry names changed since it: only a lint of every file says
whether that entry is still needed.

In a sparse checkout lint reads only the files on disk: a tracked file the
checkout leaves out (git's skip-worktree bit) has its name judged by `paths`
(pattern, project, fuzz target, case, layout; a symbolic link left out is a
finding), and no rule reads its bytes; lint says so on stderr.  With
`--changed-only BASE`, a left-out file that differs from BASE is a finding:
check it out.  Lint concludes nothing else from such a file: an exception that
names one is not called unused, and a `licence-pending` entry whose fuzz target
has one is not called stale.  A lint of the whole tree judges those entries and
those bytes.  `pr.yml`'s lint job checks out a pull request whose lint reads
only the changed files without the proof libraries (but their `dune` files),
then checks out each left-out file that changed; a merge queue group and a push
to main check the tree out whole.  enroll.yml's facts job, which lints a
checkout without the proof libraries
([`tools/enroll/check.sh`](../enroll/check.sh)), leaves those entries to it.

## The Rocq namespace (`./oft rename-namespace`)

A text that holds neither the old namespace nor `rocq-<old stem>` is left as it
is.  Any file but a `.v` file takes the word rule: the namespace with no letter,
digit or `_` on either side, and `rocq-<stem>` before `-`, a blank, `"`, `)` or
the end, which renames opam names and never a schema tag or an image name.  A
`.v` file is read as Rocq lexes it: outside string literals it takes Rocq's
word rule (no `'` after the name either, and no primes before it that follow an
identifier character: `x'Name` is one identifier); a literal of a stored
encoding is renamed by its codec (below); any other literal that holds the
namespace is renamed component by component when its whole body is a dotted
name (`@?ident(.ident)*.?`, which no encoding can be, since their alphabets
have no `.`), and the file is refused otherwise.  A doubled quote inside a
literal is one quote, as Rocq reads it.
A word rule inside an encoded literal would rename the name and leave its
length byte, which is no word character for a next component of 10 to 16
characters.  In a tree whose `release.yaml` names another namespace, lint
names each file that still holds the old one, with the command that fixes it.

A proof stores its terms in three encodings whose decoders are in the tree it
belongs to.  All three hold a global's module path as length-prefixed text, and
two of them reach a table entry by its byte offset, so renaming the Rocq
namespace in them is not a text substitution:

| encoding | where | how the rename rewrites it |
|---|---|---|
| KReplay table | `kr_t_<unit> ()`, plain or behind `KReplay.lz_vm` | the entry is renamed in place and padded back to its old length, so every offset a stream names still lands on it |
| KReplay stream | `KReplay.run1`, `run`, their `_chk` forms and LZ-compressed in `run1z`, in the proof or in a `kr_b_<nnn> ()` side file | the two inline-global opcodes are rewritten from an opcode-level parse of the stream, which has no internal offsets and may shrink. boost-beast/http_request's `Common/KReplay.run`, a different format whose names are plain text, is left to the text rename |
| CDef table | the first argument of `CDef.cdeft` | the directory records the `zQ` streams' headers name are renamed in place and padded back |

An LZ blob is inflated by a port of the Rocq decoder that keeps its step
limits, rewritten, and compressed again; what is written is inflated once more
and compared with the text it was built from.  Before it changes anything the
command requires every table and stream to parse to its exact end, to
re-serialise byte-identically from what the parse decoded (a CDef identifier
stored in pieces keeps its pieces); afterwards it parses each rewritten blob
again and requires the old name to be gone from it.  A plain (not LZ) KReplay
table or stream whose bytes do not hold the old name is neither parsed nor
changed, and is listed as left unparsed; a CDef or LZ blob is always parsed.
CDef table bytes that no stream's header reaches are never read; those that
hold the old name are overwritten with padding.  Lengths count bytes: a blob is
read as the UTF-8 bytes Rocq sees, and a compressed blob never splits a
character.

## CI

The workflows in `.github/workflows/` run these tools from the base branch,
never from the pull request (`pr.yml`); [`ci/check-units.sh`](ci/check-units.sh)
is the part every check job shares: fetch by SHA-256, the facts and the rules
of the whole tree once, then each part of each harness in a container of its
own whose `/work` holds only that part's view ([`unitpaths.py`](unitpaths.py)):
the build in the checker image with no network, and the counterexamples and the
findings in the runner image. In `pr.yml` and `release-check.yml`, the
`fetch-drafts` job is the one job with write access: it reads draft releases'
binaries only, and the check jobs read them from its artifacts.
(`release.yml`'s publish job has write access too.)  `pr.yml`'s jobs and what
each one covers are described at the top of the workflow.

[`ci/pr-steps.sh`](ci/pr-steps.sh) rehearses a pull request's `pr.yml` run on
a full clone, before GitHub runs it: it checks out the merge commit GitHub
builds for the pull request (for a push, the pushed commit) and runs the steps
of the plan, lint, tests and required jobs that need no container, each taken
from that commit's own `pr.yml` and run as GitHub runs it (the one GitHub API
call among them, the plan job's compare of the base, is answered by a
stand-in), with one summary line per step.  It starts each job as the job's
`if:` says, reads a job's outputs through its `outputs:` block, and fails when
GitHub would start `check` or `fetch-drafts`, which it does not run; it judges
`required` with the controls job skipped, and says so when the plan's reach
step names the controls.  With `--workflow release-check`, it runs the plan
step of `release-check.yml` for a push or a dispatch.  Its header says what it
runs, what it changes in each step, and what it leaves out.

[`ci/pin-digests.sh COMMIT`](ci/pin-digests.sh) prints the two digests
[`migration-pin.yaml`](migration-pin.yaml) names for the change whose tree is
`COMMIT`'s, as `pr.yml`'s plan step computes them: `digest`, of `tools/` and
`theories/` with their checkout attributes, and `tree`, of the whole tree; both
leave the pin file out.  The pull request that sets the pin takes them from it;
with `check: deferred` the pin also defers that one tree's proof check to the
check of record it names, so `pr.yml` plans every part and runs no check job, and
`release-check.yml` plans nothing for its push (the comment in the pin file says
how).

### `theorem prove` on a pull request

`pr.yml`'s `prove` job runs, on a pull request from a branch of this
repository, the base's [`ci/prove-pr`](ci/prove-pr) for the units of the
`plan` step's `unit_list`: the head's own facts planned as a release (`oft plan
--pr-kind release --base`), so a change to a symbol fact alone or to a
project's own file alone names its units (the step's own plan judges a
branch's change by the base's statements and names none of them). It prints
the change (the merge commit the plan judged), its base
and the pull request's head; then, for each unit with a symbol fact at either
commit, the command `./theorem prove UNIT --base BASE --head MERGE
--post-check OWNER/REPO@HEAD` it runs, whose report and check-run link follow
in the log; a unit with none gets a line that says so. The check
`theorem/prove: UNIT` goes on the pull request's head, posted with the run's
`GITHUB_TOKEN`. It reports and blocks nothing: it waits for `plan` alone, no
job waits for it, and no rule requires it. The change is read as git objects,
never run. `oft release-tree` removes the script and its test,
`tests/test_prove_pr.py`, so the public repository's `pr.yml` posts nothing.

### A base that moved under a run

A pull request's run judges the merge commit GitHub built when the run
started, and takes from that merge's first parent — the base as it was then —
the tools that plan, lint and check it, the `.github/actions/` its jobs run,
and the statements its proofs are checked against. (`pr.yml` itself is the
merge commit's copy, as GitHub runs a pull request's workflow; a base change
to it is in the merge that lands.) When the base then takes such a change,
the run's green is about a base that is gone, and nothing re-checks it: a pull
request into a branch with no merge queue merges on the verdict of its own
run. So `pr.yml`'s `required` job, on a pull request that no merge queue
checks again (one into a base other than main, and one into main on
theorem-labs/oss-verify-proofs, whose main has no merge queue; a pull request
into a main that merges through a merge queue is judged again by its queue
group, on the base as it is then), runs the **base's** copy of
[`tests/stale_base.py`](tests/stale_base.py) (`PYTHONPATH=base/tools python3
-m oft.tests.stale_base`), as every other judging step of that workflow runs
the base's tools: a change's own copy must not decide whether that change may
merge, and like the shared actions it must land on the
base before the step that calls it. It reads the tip of the base branch
(`repos/<owner/name>/git/ref/heads/<branch>`), compares the two trees, and
fails when they differ in a path the checks read from the base: `tools/`,
`.github/`, `.claude/`, `toolchain/`, `theories/`, `tests/`, `release.yaml`,
every dune file and every `.gitattributes`. A base that moved only by the
files another change brings ([`layout.py`](layout.py) `is_change`: its proofs,
counterexamples, findings and unpatched pins, in both layouts, for fuzz
targets this change does not touch) or by the pages `oft generate` renders is
in no key of this change's parts, and passes.

A fuzz target's own facts (`Statements.v`, `Characterise.v`, `Distribution.v`,
`Images.v`, `Symbols.v`, `source/`, `symbols/`) and a project's files
(`project.yaml`, every fuzz target's `harness.yaml`, `unpatched.yaml`,
`patches/`) are read more narrowly, because the check of fuzz target X reads
X's own facts and its project's files, and nothing of fuzz target Y but Y's
`harness.yaml`. They fail a run only when

- they belong to a fuzz target or a project this change itself touches — a
  part's key holds a fuzz target's facts and its whole proofs folder together,
  so a base that took another change to a fuzz target this one also changes,
  through its proofs or through its `Statements.v` or `source/`, leaves the
  merged tree with a key neither run checked. A project's files are read by
  every fuzz target of it: [`keys.py`](keys.py) `_project` digests
  `project.yaml` with every `harness.yaml` of the project into one id, and
  that id is a component of every part of every unit, so a sibling fuzz
  target's `harness.yaml` moves this one's key too; or
- this run read the whole tree: the tools' tests, and the whole-tree lint with
  them, ran (`pr.yml`'s reach step, `repository_lint` and `tests`, which the
  step passes as `--whole-tree`), and then a change anywhere in the base's
  facts can change what the run found.

Read by every run instead, one statements pull request would fail `required`
on every open pull request: #427 brought five projects' statements and failed
#455's own run, and #461 is to touch 159 fuzz targets.

The base is read again after the comparison, so a pass rests on a
tip the base still had when the comparison ended. A call that fails, or a base
branch that no longer holds the commit the run was built on, fails too: a run
that cannot tell cannot be trusted.

It lives under `tests/`, beside [`parallel.py`](tests/parallel.py), which is a
runner and no test either, because `keys.NOT_THE_CHECKER` names `oft/tests/`: a
file anywhere else under `tools/` is the checker, whose id is in every unit's
key, and a new file under `.github/` needs a row in
[`paths.py`](paths.py), which is the checker too. So adding it, and changing
it, re-check no fuzz target. It imports `layout.py` and nothing else of the
package: it cannot import `keys.py`, which imports `yaml`, because the
`required` job installs no dependency.

### The shared generated files, rendered after a merge

`README.md`, `index/*`, `analyses/harness-checks/checks.tsv`,
`analyses/known-issues.md` and each `projects/<p>/README.md` are rendered from
the whole tree, so every proof pull request would change them and conflict
with the one that merged before it. They are the *shared generated files*
([`paths.py`](paths.py) `SHARED`): no pull request carries one (lint refuses
it), a pull request, a merge queue group and a push compare every other
generated file (`oft generate --check --skip-shared`), and
[`.github/workflows/index.yml`](../../.github/workflows/index.yml) renders them
after each push to `main`, through
[`ci/regenerate-shared.sh`](ci/regenerate-shared.sh) (`oft generate
--shared-only`). The script commits them onto that line, `index: render the
shared generated files at <tip12>`, with the one-line trailer
`Rendered-From: <the full sha of the line commit it renders>`. The render
commit is in no check key ([`keys.py`](keys.py)), so it voids no check of its
own.

`main` merges through its merge queue, which `GITHUB_TOKEN` may not push past,
so the render is pushed over SSH with a write deploy key of the repository,
read from the Environment `index`; a deploy key's push does start workflows,
so that render commit's first line carries the skip-ci marker (`--skip-ci`,
which only that job passes). A push straight to `main` makes GitHub rebuild
every queue group, so a push run renders only while the merge queue is empty
or the index is stale: main has had a commit after the newest render (and after
the tip of the last hourly or hand run that rendered or found nothing to
render) for more than 3 h. Any other push run
skips, with a notice in its job summary that gives the queue's count and the
index's age. The hourly run renders whatever the queue holds (a render costs a
group at most one rebuild, since the render commit is in no key), and a push or
hourly run that cannot push the render of a stale index fails (OSSV-276).

A failed run leaves the shared files as they were, and the next push runs the
render again. To repair one by hand:

    gh workflow run index.yml --ref main

A hand run renders at once, whatever the queue holds. There is no other route
for `main`: the deploy key that may push past its merge queue lives only in the
Environment `index`, which only that job reaches. On a branch that takes no
merge queue and whose own token may push, the script can also be run from a
throwaway clone — it fetches one commit deep and without blobs, so it leaves
that clone shallow and a promisor, and no clone you work in should be given to
it:

    TMPDIR=<scratch> tools/oft/ci/regenerate-shared.sh --git <throwaway clone> --branch <branch>

## The comment sweep

Before a fuzz target's approval, every whole comment line of its new Rocq
files that is neither released text nor generated text is deleted, and a check
proves that nothing else changed (OSSV-134, comment-pass rulings, item 19 and
its conditions 20-25):

    cd tools && python3 -m oft.tests.comment_sweep plan  --repo GIT --unit P/H --head REV [--keep FILE] [--citations OUT]
    cd tools && python3 -m oft.tests.comment_sweep apply --repo GIT --unit P/H --head REV --worktree DIR
    cd tools && python3 -m oft.tests.comment_sweep check --repo GIT --unit P/H --head REV --swept REV

`plan` lists each line it deletes or keeps, with the reason (the header's ten
lines, `(* Modified by` notices, `timeout-ok` lines, the fuzz target's released
lines, the owner's KEEP file of generated lines, cited lines, and lines that
keep a comment closed); `apply` writes the swept files into a checkout of the
head, adds the notice `(* Modified by Theorem Labs, 2026-11: comments
removed *)` under the last licence line of each swept file that came from a
donor (a file whose last licence line is line 10 is refused and left as it
is), and re-resolves the `File.v:N` citations of the lines it keeps; `check`
compares the swept commit with the head by code of its own and exits 1 naming
each change the rule does not allow.  Only `.v` files are swept, and the
fuzz target's approval states that scope and the count of its other new files;
it also carries the rows `plan --citations` writes, each citation the sweep
re-resolved or left, marked `checked` or `deleted` by the owner.  The
module's docstring states each definition and its evidence.  The sweep changes
the swept files' object ids, so the fuzz target re-keys and takes a new check
of record; the indexes that store `path:line` are rebuilt after the merge.  It
lives under `tests/`, as `stale_base.py` does, so that it is in no key.

## Tests

    cd tools && python3 -B -m unittest discover -s oft/tests -t .

One process per test class, which is how `pr.yml` runs them (on 16 CPUs, about
60 s in one process and 11 s this way, without the whole-tree lint test, which
takes about 5 minutes by itself).  It prints every class's output whole, in one
order whatever order the processes end in, and exits 1 naming every test that
failed:

    cd tools && python3 -B -m oft.tests.parallel [--jobs N]
