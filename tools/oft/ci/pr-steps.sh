#!/bin/bash
# tools/oft/ci/pr-steps.sh: a pull request's pr.yml run, rehearsed on a full clone of this repository: the steps of
# its plan, lint, tests, rekey and required jobs that need no container, each taken from the workflow of the commit
# the run checks out and run as GitHub runs it, and each job started or skipped as its `if:` says.  With --workflow
# release-check, release-check.yml's plan step for a push to main or a dispatch instead.
#
#   REPO=<full clone> WORK=<dir> pr-steps.sh [--event pull_request|merge_group|push] [--diag] HEAD BASE KIND OUT
#   REPO=<full clone> WORK=<dir> pr-steps.sh --workflow release-check --event push|workflow_dispatch HEAD BASE KIND OUT
#   REPO=<full clone> pr-steps.sh --merge-ref-only [--event ...] HEAD BASE
#
# HEAD and BASE are commits of REPO, or names of them (origin/main).  KIND is pr.yml's: release, maintainer or
# contributor; pr.yml makes a push and a merge queue group release, so those events take no other.  release-check.yml
# reads no KIND, and with workflow_dispatch no BASE either; both must still be given.
#
# The commit checked out is the one GitHub checks out.  For a pull request (the default event) and for a merge queue
# group, the merge of HEAD into BASE: `git merge-tree --write-tree BASE HEAD`, then `git commit-tree -p BASE -p HEAD`,
# a merge even when HEAD already has BASE, as refs/pull/<n>/merge is (and as a queue that merges by merge commits makes
# a group; a queue that squashes makes a commit with one parent, which this does not rehearse); a pull request's
# EVENT_BASE is empty (its base step reads the merge's first parent) and a group's is BASE.  For a push, and for
# release-check, HEAD itself, with BASE as the push's `before` (EVENT_BASE).  --merge-ref-only prints that commit and
# exits 0 (1 when HEAD and BASE conflict, as GitHub then builds no merge commit); it needs REPO, HEAD and BASE only, no
# KIND, OUT or WORK.  The merge commit is written into REPO's objects, as GitHub writes refs/pull/<n>/merge into the
# repository; no ref names it.
#
# Each step's script is the one that commit's own .github/workflows/pr.yml (release-check.yml) has, as GitHub reads a
# pull request's or a push's workflows, found by its job and its step id or name (STEPS, below), and run as `shell:
# bash` runs it, `bash --noprofile --norc -eo pipefail`, in the job's own workspace: WORK/run/<job>/, whose head/ is the
# checked-out commit (release-check's plan job runs in the checkout itself).  The checkout is a `git clone --shared` of
# REPO, so the base worktrees and sparse-checkout settings the steps make land in that clone, never in REPO, and go when
# the run ends.  It differs from a runner's in three ways: pr.yml's jobs share one head/ (a file one job writes there,
# a later job sees), and it has every file, each proof library (proofs/<p>/<h>/lib/, projects/<p>/<h>/proofs/lib/)
# too, and the whole history, where the plan job's and
# (without the whole-tree lint) the tests job's checkout has neither.  Two changes to the steps and their tools: a
# `git -C head fetch ...` command is replaced by `true` (REPO already holds every commit, and the run needs no GitHub
# credentials), and `gh` is a stand-in that answers only the plan base step's compare of the merge's first parent with
# the base branch, always as GitHub answers it for a merge commit built on that branch's tip (`identical`).  A step's
# script may hold no `${{ }}`, which GitHub would fill in before bash reads it: the run stops before its first step
# otherwise.
#
# A step's environment is built from nothing (no variable of the caller's reaches it but PATH, so no ANTHROPIC_* or
# CLAUDE* variable, which CI's runner does not have either): HOME (an empty directory, as a runner's has no git
# identity), PATH (the stand-in, the venv, then the caller's), LANG=C.UTF-8, CI, GITHUB_ACTIONS, GITHUB_WORKSPACE,
# RUNNER_TEMP (one per job, as on a runner), GITHUB_OUTPUT and GITHUB_STEP_SUMMARY (one each per step),
# GITHUB_EVENT_NAME, GITHUB_REPOSITORY, GITHUB_REF, GITHUB_SHA; then each `env:` of the workflow, the job and the step:
# a literal value as written, and a `${{ }}` value as GitHub evaluates it for this run (vars_for, below), from the event,
# the outputs of the steps before it in its job, and the earlier jobs' results and outputs.  A step whose `env:` names a
# variable vars_for does not give stops the run before its first step.
#
# What a job gives the jobs after it is what GitHub gives: `needs.<job>.result` (success when each of its steps ran and
# passed or was skipped by its own `if:`, failure when one failed, skipped when the job's `if:` was false), and
# `needs.<job>.outputs.<name>` read through the job's `outputs:` block, each of whose values must be exactly
# `${{ steps.<id>.outputs.<name> }}` (the run stops before its first step otherwise): the value step <id> last wrote,
# '' when it wrote none or did not run, and for a step this script does not run, its stand-in: the plan job's hold step
# gives hold=none (a pull request that is no draft and carries the label `check`), its drafts step draft_legs='[]' and
# plan='[]' (no planned binary is a draft; with units above 0 summary.txt says that this is not rehearsed).
#
# Whether GitHub starts a job is its `if:`, read from the checked-out workflow and evaluated, in needs order, with what
# the run knows: the results and outputs above, cancelled() false, success() and failure() over every job the job
# needs, directly or not (as GitHub reads them), and of github.*, only event_name, repository, ref, base_ref and, for a
# pull request, event.pull_request.base.ref (BASE_BRANCH) and event.pull_request.head.repo.full_name (the repository:
# a branch of it).  A listed step's own `if:` is evaluated the same way, as `success() && (...)` over the steps before
# it, so it may call no status function and read no `needs.<job>.result`.  An `if:` that reads anything else stops the
# run before its first step.  The evaluator is `evaluate` of tools/oft/tests/test_facts_review_gate.py in this script's
# own tree, not the checked-out commit's: the repository's tests already judge pr.yml's job conditions with it
# (tools/oft/tests/test_lint.py imports it), it refuses a token it cannot read instead of guessing, and taken from this
# tree it is the one tested with this script, and a pull request cannot change how its own conditions are read (as
# pr.yml never lets a pull request's tools judge it).  So the run, for pr.yml:
#   queue_run      never run; GitHub starts it for a push only, and its outputs are '' here (a push the merge queue did
#                  not check)
#   plan           its base, plan and reach steps
#   lint           its base, ledger, lint and generate steps
#   tests          its step, at the change, with the change's venv
#   rekey          its base and rekey steps, with the base's venv (rule D11: keys.checker of the base and of the
#                  head); the window is OSSV_REKEY_WINDOW from the caller's environment (unset: closed, as the
#                  repository variable's absence is)
#   fetch-drafts   never run: when its `if:` is true, `FAIL(-) fetch-drafts/not-run (GitHub starts it: ...)`
#   check          never run: when its `if:` is true, `FAIL(-) check/not-run (GitHub starts it: units=<N>)`
#   controls       never run, and taken as skipped: required/collect is given CONTROLS=false and
#                  CONTROLS_RESULT=skipped, and summary.txt says so when reach answered controls=true
#   stream_tools   never run: when its `if:` is true, `FAIL(-) stream_tools/not-run (GitHub starts it: ...)`;
#                  required/collect is given the plan's stream_tools answer and the job's result
#   farm_tests     never run, as stream_tools: when its `if:` is true, `FAIL(-) farm_tests/not-run (GitHub starts it:
#                  ...)`; required/collect is given the plan's farm_tests answer and the job's result
#   required       its step "every job green, and something checked when the plan named anything", with what those
#                  jobs gave (PLAN_RESULT, LINT_RESULT, TESTS_RESULT, FETCH_DRAFTS_RESULT and CHECK_RESULT, the plan's
#                  outputs, QUEUED as pr.yml computes it; for merge-pr.sh's evidence comment GH_TOKEN, an empty PR and
#                  HEAD_SHA, which the step never reads here, since the hold stand-in is none); when GitHub would start
#                  fetch-drafts or check, there is no verdict to rehearse, and the step is skipped
#   main-gate, and required's other steps: not run
# Within a job, a step after one that failed still runs when the job's base step passed (the steps after it read only
# the base step's workspace), so one rehearsal shows every failure; GitHub stops the job there, and the job's result
# here is failure all the same.  With --diag, also the plan and lint steps with the change's own tools in place of the
# base's (base/tools read as head/tools; lint's with the change's venv), which pr.yml runs only for the change the base
# pins; their results count for nothing.  For release-check: its plan job's plan step alone (the queue step is not run,
# so its outputs are '': a push the merge queue did not check; nor the drafts step, nor the jobs after the plan, of
# which summary.txt says when GitHub would start them), on a checkout of every file but the proof libraries
# (proofs/<p>/<h>/lib/ and projects/<p>/<h>/proofs/lib/), as
# release-check.yml takes it.  No job's timeout-minutes or runner is rehearsed.
#
# OUT/<job>-<step>.log is each step's output; OUT/<job>-<step>.output and .md its GITHUB_OUTPUT and job summary, when
# it wrote them; OUT/plan-plan.json the plan; OUT/run.txt what the run checked out and when; OUT/setup.log the clone,
# the checkout, the venvs and the parse of the workflow.  A run first removes those files of an earlier run from OUT.
# OUT/summary.txt has one line per step, `PASS <job>/<step> (<s> s)` or `FAIL(<rc>) ...`, or `SKIP <job>/<step>
# (<why>)`; `FAIL(-) <job>/not-run (...)` for a job GitHub starts and this script does not run; `diag: ...` for --diag's
# steps; `note: ...` for what the verdict does not cover (and the tests' own count, `ran ... (N skipped)`); and the
# plan's answers:
#   pr.yml          plan: tools=<base|head> checked_elsewhere=<true|false> units=<N>
#   release-check   plan: deferred=<true|false> units=<N> full=<true|false>
# checked_elsewhere=false when the plan job gives no such output; `-` for an answer it does not give.
# Exit 0 when every step run passed and no job GitHub starts was left unrun, 1 otherwise (or when the setup failed),
# 2 for a usage error.  The one exception is controls, which needs the checker image and a 150 GB runner: it is
# taken as skipped, with a note, and does not by itself make the exit 1.
#
# Optional environment: BASE_BRANCH, the branch BASE is the tip of, which the pull request goes into (default main;
# BASE_REF, INTO, GITHUB_REF and QUEUED follow from it); VENVS, where the venvs are (default WORK/venvs): one per
# requirements file's content, python3.12 with `pip install --require-hashes`, built once and shared, under flock, by
# the runs that name the same VENVS; GITHUB_REPOSITORY, owner/name (default: REPO's origin on GitHub).  WORK holds the
# venvs and run/, the run's workspaces, which the run removes when it ends and before it starts (an interrupted run's);
# it refuses a WORK/run it did not make (no WORK/run/.pr-steps), and an OUT inside WORK/run.  One run at a time per
# WORK.  This script changes nothing else in REPO: no ref, worktree or config.  Run it from a checkout of this
# repository (it reads the evaluator beside it); it needs git 2.38 or later (merge-tree --write-tree), python3.12 with
# its venv module (and network to PyPI for the venvs), jq and flock.
set -uo pipefail

# The steps run, one row each, tab-separated: workflow<TAB>job<TAB>short name<TAB>step id or name.  The short name
# names the step in OUT (<job>-<short>.log) and in the summary (<job>/<short>).
# tools/oft/tests/test_workflow_verdicts.PrStepsTest holds every row to one step of this repository's workflow.
STEPS=$(cat <<'STEPS'
pr.yml	plan	base	base
pr.yml	plan	plan	plan
pr.yml	plan	elsewhere	the parts a check of record outside this run checked
pr.yml	plan	reach	reach
pr.yml	lint	base	base
pr.yml	lint	ledger	the findings ledger over the change's history, by the base's rules
pr.yml	lint	lint	lint, by the base's rules
pr.yml	lint	generate	generated files equal their rendering
pr.yml	tests	tests	the tools' own tests, at this change, one process per test class
pr.yml	rekey	base	base
pr.yml	rekey	rekey	rekey
pr.yml	required	collect	every job green, and something checked when the plan named anything
release-check.yml	plan	plan	plan
STEPS
)
# the jobs whose `if:` decides what this script runs or reports, per workflow
JUDGED_PR="queue_run plan lint tests rekey fetch-drafts check stream_tools farm_tests required"
JUDGED_RC="plan fetch-drafts check"

usage() {
  [ $# -eq 0 ] || echo "pr-steps.sh: $*" >&2
  cat >&2 <<'USAGE'
usage: REPO=<full clone> WORK=<dir> pr-steps.sh [--event pull_request|merge_group|push] [--diag] HEAD BASE KIND OUT
       REPO=<full clone> WORK=<dir> pr-steps.sh --workflow release-check --event push|workflow_dispatch HEAD BASE KIND OUT
       REPO=<full clone> pr-steps.sh --merge-ref-only [--event ...] HEAD BASE
USAGE
  exit 2
}

# this script's own tools/, whose evaluator judges the `if:`s (the header says why)
TOOLS=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd) || usage "cannot find the tools/ this script is in"

workflow=pr event='' diag='' only=''
while [ $# -gt 0 ]; do
  case $1 in
    --event) [ $# -ge 2 ] || usage "--event takes a value"; event=$2; shift 2 ;;
    --workflow) [ $# -ge 2 ] || usage "--workflow takes a value"; workflow=$2; shift 2 ;;
    --diag) diag=1; shift ;;
    --merge-ref-only) only=1; shift ;;
    --) shift; break ;;
    -*) usage "unknown option $1" ;;
    *) break ;;
  esac
done
case $workflow in
  pr)
    event=${event:-pull_request}
    case $event in pull_request|merge_group|push) ;; *) usage "pr.yml's --event: pull_request, merge_group or push" ;; esac ;;
  release-check)
    case $event in push|workflow_dispatch) ;; *) usage "--workflow release-check takes --event push or workflow_dispatch" ;; esac
    [ -z "$diag" ] || usage "--diag is for pr.yml's steps" ;;
  *) usage "--workflow: pr or release-check" ;;
esac
if [ -n "$only" ]; then
  [ $# -eq 2 ] || usage "--merge-ref-only takes HEAD BASE"
else
  [ $# -eq 4 ] || usage
  KIND=$3
  OUT=$4
  case $KIND in release|maintainer|contributor) ;; *) usage "KIND: release, maintainer or contributor" ;; esac
  if [ "$workflow" = pr ] && [ "$event" != pull_request ] && [ "$KIND" != release ]; then
    usage "pr.yml's KIND for a $event is release"
  fi
  [ -n "${WORK:-}" ] || usage "WORK: a directory for the run"
fi
[ -n "${REPO:-}" ] || usage "REPO: a full clone of the repository"
prhead=$(git -C "$REPO" rev-parse --verify --quiet "$1^{commit}") || usage "HEAD: $1 is no commit of $REPO"
base=$(git -C "$REPO" rev-parse --verify --quiet "$2^{commit}") || usage "BASE: $2 is no commit of $REPO"

# checked_out: the commit the run checks out (the header says which), on stdout.  The merge commit's dates are HEAD's,
# so that the same HEAD and BASE give the same commit.
checked_out() {
  local mt date
  case $event in push|workflow_dispatch) echo "$prhead"; return 0 ;; esac
  mt=$(git -C "$REPO" merge-tree --write-tree --no-messages "$base" "$prhead") || {
    echo "pr-steps.sh: HEAD ${prhead:0:10} conflicts with BASE ${base:0:10}: GitHub builds no merge commit" >&2
    return 1
  }
  date=$(git -C "$REPO" log -1 --format=%cI "$prhead") || return 1
  GIT_AUTHOR_DATE=$date GIT_COMMITTER_DATE=$date \
    git -C "$REPO" -c user.name=pr-steps.sh -c user.email=pr-steps.sh@invalid commit-tree "${mt%%$'\n'*}" \
    -p "$base" -p "$prhead" -m "Merge ${prhead:0:10} into ${base:0:10} (a pull request's merge commit, made by pr-steps.sh)"
}
if [ -n "$only" ]; then
  checked_out || exit 1
  exit 0
fi

BASE_BRANCH=${BASE_BRANCH:-main}
repository=${GITHUB_REPOSITORY:-}
if [ -z "$repository" ]; then
  url=$(git -C "$REPO" remote get-url origin 2>/dev/null) || url=
  # https://, ssh:// or scp-like: what follows the host is owner/name
  case $url in *github.com[:/]*/*) repository=${url#*github.com[:/]}; repository=${repository%.git} ;; esac
fi
[[ "$repository" =~ ^[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+$ ]] ||
  usage "REPO's origin names no GitHub repository: set GITHUB_REPOSITORY=<owner>/<name>"
if ! { WORK=$(realpath -m -- "$WORK") && OUT=$(realpath -m -- "$OUT") && REPO=$(cd "$REPO" && pwd); }; then
  usage "WORK, OUT or REPO cannot be read"
fi
VENVS=${VENVS:-$WORK/venvs}
W=$WORK/run
case "$OUT/" in "$W/"*) usage "OUT is inside WORK/run, which every run removes" ;; esac
mkdir -p "$WORK" "$OUT" || usage "WORK or OUT cannot be made"
exec {worklock}> "$WORK/run.lock"
flock -n "$worklock" || usage "another run uses WORK $WORK"
[ ! -e "$W" ] || [ -e "$W/.pr-steps" ] || usage "$W has no .pr-steps: pr-steps.sh did not make it, and leaves it; give another WORK"
rm -rf "$W"
trap 'rm -rf "$W"' EXIT
trap 'exit 130' INT TERM
mkdir -p "$W/steps" "$W/files" "$W/home" "$W/bin"
: > "$W/.pr-steps"
: > "$W/results"
# an earlier run's files in OUT
while IFS=$'\t' read -r _wf job short _key; do
  rm -f "$OUT/$job-$short".{log,output,md,json}
done <<< "$STEPS"
rm -f "$OUT"/{plan-plan-head-tools,lint-lint-head-tools}.{log,output,md,json}
: > "$OUT/summary.txt"
: > "$OUT/run.txt"
: > "$OUT/setup.log"
say() { echo "$*" | tee -a "$OUT/summary.txt"; }
note() { echo "$*" | tee -a "$OUT/run.txt"; }
setup_fail() { say "FAIL setup: $*"; exit 1; }

# The event, as the workflow's ${{ }} expressions read it (the header says what each is).
case $workflow/$event in
  pr/pull_request) event_base='' base_ref=$BASE_BRANCH ref=refs/pull/0/merge ;;
  pr/merge_group) event_base=$base base_ref='' ref=refs/heads/gh-readonly-queue/$BASE_BRANCH/pr-0-$base ;;
  */push) event_base=$base base_ref='' ref=refs/heads/$BASE_BRANCH ;;
  release-check/workflow_dispatch) event_base='' base_ref='' ref=refs/heads/$BASE_BRANCH ;;
esac
queued=false
if [ "$event" = pull_request ] && [ "$BASE_BRANCH" = main ] && [ "$repository" != theorem-labs/oss-verify-proofs ]; then
  queued=true
fi

commit=$(checked_out 2>> "$OUT/setup.log") || setup_fail "the merge of HEAD ${prhead:0:10} into BASE ${base:0:10} (OUT/setup.log)"
note "$workflow.yml, $event, kind $KIND: HEAD $prhead, BASE $base; checked out $commit (tree $(git -C "$REPO" rev-parse "$commit^{tree}")); $(date -u +%Y-%m-%dT%H:%M:%SZ)"
[ -f "$TOOLS/oft/tests/test_facts_review_gate.py" ] ||
  setup_fail "$TOOLS/oft/tests/test_facts_review_gate.py is not there: run this script from a checkout of the repository"

# venv_for REQUIREMENTS: a venv with them installed, hash-pinned, on stdout; runs that share VENVS build each once, and
# the others wait for it
venv_for() {
  local req=$1 v lock
  mkdir -p "$VENVS" || return 1
  v=$VENVS/py3.12-$(sha256sum "$req" | cut -c1-16)
  exec {lock}> "$v.lock"
  flock "$lock"
  if [ ! -e "$v/.complete" ]; then
    rm -rf "$v"
    if ! { python3.12 -m venv "$v" >&2 && "$v/bin/pip" install --quiet --require-hashes -r "$req" >&2 &&
           touch "$v/.complete"; }; then
      rm -rf "$v"
      exec {lock}>&-
      return 1
    fi
  fi
  exec {lock}>&-
  echo "$v"
}

# The checkout, as actions/checkout gives it: pr.yml's jobs share head/ (lint reads every file), release-check's plan
# job takes every file but the proof libraries, in its workspace itself.
if [ "$workflow" = pr ]; then
  checkout=$W/head wf=pr.yml judged=$JUDGED_PR
else
  checkout=$W/plan wf=release-check.yml judged=$JUDGED_RC
fi
{ git clone -q --shared --no-checkout "$REPO" "$checkout" &&
  if [ "$workflow" = release-check ]; then
    git -C "$checkout" config core.sparseCheckout true &&
      printf '/*\n!/proofs/*/*/lib/\n!/projects/*/*/proofs/lib/\n' > "$checkout/.git/info/sparse-checkout"
  fi &&
  git -C "$checkout" checkout -q --detach "$commit"
} >> "$OUT/setup.log" 2>&1 || setup_fail "the checkout of $commit (OUT/setup.log)"

if ! { git -C "$REPO" show "$commit:tools/oft/requirements.txt" > "$W/head-requirements.txt" 2>> "$OUT/setup.log" &&
       hv=$(venv_for "$W/head-requirements.txt" 2>> "$OUT/setup.log"); }; then
  setup_fail "pip install of $commit's tools/oft/requirements.txt (OUT/setup.log)"
fi
bv=$hv
if [ "$workflow" = pr ] &&
   ! { git -C "$REPO" show "$base:tools/oft/requirements.txt" > "$W/base-requirements.txt" 2>> "$OUT/setup.log" &&
       bv=$(venv_for "$W/base-requirements.txt" 2>> "$OUT/setup.log"); }; then
  setup_fail "pip install of BASE's tools/oft/requirements.txt (OUT/setup.log)"
fi
PY=$hv/bin/python

# The steps, from the checked-out commit's own workflow: for each, <job>-<short>.sh (its script), .wd (its
# working-directory), .env (its literal env: values, NAME=VALUE), .keys (the names of its ${{ }} env: values), the
# workflow's, the job's and the step's env: together, as GitHub merges them, and .if (its own `if:`, when it has one);
# and jobs.json, each job's needs, `if:` and outputs (as step id and output name), and the step ids this run runs.
git -C "$REPO" show "$commit:.github/workflows/$wf" > "$W/workflow.yml" 2>> "$OUT/setup.log" ||
  setup_fail "$commit has no .github/workflows/$wf"
STEPS=$STEPS "$PY" - "$W/workflow.yml" "$wf" "$W" <<'PY' 2>> "$OUT/setup.log" ||
import json, os, re, sys, yaml
path, name, w = sys.argv[1:]
out = os.path.join(w, "steps")
with open(path) as f:
    wf = yaml.safe_load(f)
rows = [line.split("\t") for line in os.environ["STEPS"].splitlines() if line.startswith(name + "\t")]
def text(v):
    return "" if v is None else ("true" if v else "false") if isinstance(v, bool) else str(v)
def run_defaults(block, key):
    return (((block or {}).get("defaults") or {}).get("run") or {}).get(key)
problems = []
found = {}
jobs = {}
OUTPUT = re.compile(r"\$\{\{\s*steps\.([A-Za-z_][\w-]*)\.outputs\.([A-Za-z_][\w-]*)\s*\}\}")
for job, j in wf["jobs"].items():
    needs = j.get("needs") or []
    outputs = {}
    for k, v in (j.get("outputs") or {}).items():
        m = OUTPUT.fullmatch(text(v).strip())
        if not m:
            problems.append("job %s's output %s is %r, not ${{ steps.<id>.outputs.<name> }}" % (job, k, v))
            continue
        outputs[k] = [m.group(1), m.group(2)]
    jobs[job] = {"needs": [needs] if isinstance(needs, str) else list(needs),
                 "if": None if "if" not in j else text(j["if"]), "outputs": outputs, "steps": {}}
for _wf, job, short, key in rows:
    j = wf["jobs"].get(job)
    steps = [s for s in (j or {}).get("steps", []) if key in (s.get("id"), s.get("name"))]
    if len(steps) != 1 or "run" not in steps[0]:
        problems.append("%s/%s: %d step(s) with id or name %r and a script" % (job, short, len(steps), key))
        continue
    s = steps[0]
    run_shell = s.get("shell") or run_defaults(j, "shell") or run_defaults(wf, "shell") or "bash"
    if run_shell != "bash":
        problems.append("%s/%s: shell %r, not bash" % (job, short, run_shell))
        continue
    if "${{" in s["run"]:
        problems.append("%s/%s: its script holds ${{ }}, which GitHub fills in and this script does not" % (job, short))
        continue
    env = {}
    for block in (wf.get("env"), j.get("env"), s.get("env")):
        env.update({k: text(v) for k, v in (block or {}).items()})
    wd = s.get("working-directory") or run_defaults(j, "working-directory") or run_defaults(wf, "working-directory") or "."
    # the full clone already holds every commit, so a `git -C head fetch` is made a no-op success: the command and its
    # arguments only (a quoted argument may hold spaces), never past `||`, `&&`, `;`, `}` or `)`, so that
    # `if … && ! git -C head fetch …; then` and `git -C head fetch … || { …; exit 1; }` stay as they are
    script = re.sub(r'git -C head fetch(?:[ \t]+(?:"[^"]*"|[^\s;|&)}"]+))*', "true", s["run"])
    found[job + "-" + short] = (script, wd, env, None if "if" not in s else text(s["if"]))
    if s.get("id"):
        jobs[job]["steps"][s["id"]] = job + "-" + short
if problems:
    sys.exit("%s: %s" % (name, "; ".join(problems)))
if name == "pr.yml":
    # --diag: the plan and lint steps with the change's own tools in place of the base's
    for step in ("plan-plan", "lint-lint"):
        script, wd, env, cond = found[step]
        found[step + "-head-tools"] = (script.replace("base/tools", "head/tools"), wd, env, cond)
for step, (script, wd, env, cond) in found.items():
    with open(os.path.join(out, step + ".sh"), "w") as f:
        f.write(script if script.endswith("\n") else script + "\n")
    with open(os.path.join(out, step + ".wd"), "w") as f:
        f.write(wd + "\n")
    literal = {k: v for k, v in env.items() if "${{" not in v}
    if any("\n" in v for v in literal.values()):
        sys.exit("%s %s: an env: value of more than one line" % (name, step))
    with open(os.path.join(out, step + ".env"), "w") as f:
        f.write("".join("%s=%s\n" % kv for kv in literal.items()))
    with open(os.path.join(out, step + ".keys"), "w") as f:
        f.write("".join(k + "\n" for k in env if k not in literal))
    if cond is not None:
        with open(os.path.join(out, step + ".if"), "w") as f:
            f.write(cond)
with open(os.path.join(w, "jobs.json"), "w") as f:
    json.dump(jobs, f)
PY
  setup_fail "the steps of $commit's .github/workflows/$wf (OUT/setup.log)"
for f in "$W"/steps/*.sh; do
  bash -n "$f" 2>> "$OUT/setup.log" || setup_fail "$(basename "$f" .sh) is no bash script once its fetch is dropped (OUT/setup.log)"
done

# judge.py: the `if:`s and the job outputs (the header says how they are read).
#   judge.py check JOB...      every listed step's `if:` and the named jobs' (those the workflow has) can be read
#   judge.py if JOB            true or false, from the results so far (WORK/run/results); absent: no such job
#   judge.py step-if STEP      true or false: the listed step <job>-<short>'s own `if:`
#   judge.py output JOB NAME   needs.<JOB>.outputs.<NAME>
cat > "$W/judge.py" <<'PY'
import json, os, re, sys
sys.dont_write_bytecode = True
sys.path.insert(0, os.environ["PR_STEPS_TOOLS"])
from oft.tests.test_facts_review_gate import evaluate
W = os.environ["PR_STEPS_W"]
with open(os.path.join(W, "jobs.json")) as f:
    JOBS = json.load(f)
# the outputs of the steps this script does not run (the header says why these)
STAND_INS = {"plan": {"hold": {"hold": "none"}, "drafts": {"draft_legs": "[]", "plan": "[]"}}}
EVENT, BRANCH = os.environ["PR_STEPS_EVENT"], os.environ["PR_STEPS_BRANCH"]
REPOSITORY, REF = os.environ["PR_STEPS_REPOSITORY"], os.environ["PR_STEPS_REF"]
GITHUB = {"event_name": EVENT, "repository": REPOSITORY, "ref": REF,
          "base_ref": BRANCH if EVENT == "pull_request" else "", "event": {}}
if EVENT == "pull_request":
    GITHUB["event"] = {"pull_request": {"base": {"ref": BRANCH}, "head": {"repo": {"full_name": REPOSITORY}}}}
KNOWN = {"github.event_name", "github.repository", "github.ref", "github.base_ref",
         "github.event.pull_request.base.ref", "github.event.pull_request.head.repo.full_name"}

def results():
    r = {}
    with open(os.path.join(W, "results")) as f:
        for line in f:
            job, result = line.split()
            r[job] = result
    return r

def step_output(step, name):
    v = ""
    try:
        with open(os.path.join(W, "files", step + ".output")) as f:
            for line in f:
                if line.startswith(name + "="):
                    v = line.rstrip("\n")[len(name) + 1:]
    except FileNotFoundError:
        pass
    return v

def output(job, name):
    if name not in JOBS[job]["outputs"]:
        return ""
    step, out = JOBS[job]["outputs"][name]
    if step in JOBS[job]["steps"]:
        return step_output(JOBS[job]["steps"][step], out)
    return STAND_INS.get(job, {}).get(step, {}).get(out, "")

def ancestors(job):
    seen, todo = [], list(JOBS[job]["needs"])
    while todo:
        a = todo.pop()
        if a not in seen:
            seen.append(a)
            todo += JOBS[a]["needs"]
    return seen

def readable(expr, what):
    unknown = sorted(set(re.findall(r"github(?:\.[\w-]+)+", expr)) - KNOWN)
    if unknown:
        raise ValueError("%s reads %s, which pr-steps.sh does not know" % (what, ", ".join(unknown)))

def step_expr(step):
    path = os.path.join(W, "steps", step + ".if")
    if not os.path.exists(path):
        return None
    with open(path) as f:
        expr = f.read()
    if re.search(r"\w\(\)|\.result\b", expr):
        raise ValueError("step %s's if: calls a status function or reads a job's result: %r" % (step, expr))
    return expr

def judge_step(step, needs_of):
    expr = step_expr(step)
    if expr is None:
        return True
    readable(expr, "step %s's if:" % step)
    job = step.split("-", 1)[0]
    return evaluate(expr, {a: {"result": "success", "outputs": needs_of(a)} for a in JOBS[job]["needs"]}, False, GITHUB)

def judge_job(job, result_of, needs_of):
    expr = JOBS[job]["if"]
    expr = "success()" if expr is None else expr
    readable(expr, "job %s's if:" % job)
    return evaluate(expr, {a: {"result": result_of(a), "outputs": needs_of(a)} for a in ancestors(job)}, False, GITHUB)

def live_outputs(job):
    return {name: output(job, name) for name in JOBS[job]["outputs"]}

command, args = sys.argv[1], sys.argv[2:]
if command == "check":
    for step in sorted(os.listdir(os.path.join(W, "steps"))):
        if step.endswith(".if"):
            judge_step(step[:-3], lambda a: {})
    for job in args:
        if job in JOBS:
            judge_job(job, lambda a: "success", lambda a: {})
elif command == "if":
    job = args[0]
    if job not in JOBS:
        print("absent")
    else:
        r = results()
        def result_of(a):
            if a not in r:
                raise ValueError("job %s needs %s, which has no result yet" % (job, a))
            return r[a]
        print("true" if judge_job(job, result_of, live_outputs) else "false")
elif command == "step-if":
    print("true" if judge_step(args[0], live_outputs) else "false")
elif command == "output":
    print(output(args[0], args[1]))
else:
    sys.exit("judge.py: no command %s" % command)
PY
judge() {
  PR_STEPS_W=$W PR_STEPS_TOOLS=$TOOLS PR_STEPS_EVENT=$event PR_STEPS_REPOSITORY=$repository \
    PR_STEPS_BRANCH=$BASE_BRANCH PR_STEPS_REF=$ref "$PY" -B "$W/judge.py" "$@"
}
# shellcheck disable=SC2086 # the judged jobs are words
judge check $judged 2>> "$OUT/setup.log" || setup_fail "an if: of $wf that pr-steps.sh cannot evaluate (OUT/setup.log)"

# The stand-in gh: the two calls the steps make, both in the plan job's base step: the pull request's base branch
# (base_ref, above), and the compare of the merge's first parent with it, answered as GitHub answers it for a merge
# commit built on the base branch's tip.
{ echo '#!/bin/bash'
  printf 'base_ref=%q\n' "$base_ref"
  cat <<'GH'
for a in "$@"; do case "$a" in
  */pulls/*) echo "$base_ref"; exit 0 ;;
  */compare/*...*) b=${a##*/compare/}; b=${b%%...*}; echo "identical $b"; exit 0 ;;
esac; done
echo "gh stand-in (pr-steps.sh): unexpected call: gh $*" >&2; exit 1
GH
} > "$W/bin/gh"
chmod +x "$W/bin/gh"

declare -A rc_of=()
names_only=''
# output JOB SHORT NAME: the value the step last wrote to its GITHUB_OUTPUT for NAME, or nothing (a step of the same
# job: steps.<id>.outputs.<name>)
output() { sed -n "s/^$3=//p" "$W/files/$1-$2.output" 2>/dev/null | tail -n 1; }
# job_output JOB NAME: needs.<job>.outputs.<name>, through the job's outputs: block.  A judge.py call that fails gives
# a value no step reads as an answer, and fails the run at its end (judge_failed), whatever the steps did with it.
job_output() {
  [ -z "$names_only" ] || return 0
  judge output "$1" "$2" 2>> "$OUT/setup.log" && return 0
  : > "$W/judge-failed"
  echo "FAIL judge: needs.$1.outputs.$2 could not be read (OUT/setup.log)" >> "$OUT/summary.txt"
  echo "(judge.py failed: OUT/setup.log)"
}
judge_failed() { [ -e "$W/judge-failed" ]; }
answer() { local v; v=$(job_output "$@"); echo "${v:--}"; }
# record JOB RESULT, and job_result JOB: needs.<job>.result
record() { echo "$1 $2" >> "$W/results"; }
job_result() { sed -n "s/^$1 //p" "$W/results" | tail -n 1; }
# steps_result JOB SHORT...: success when each step ran and passed (or its own if: skipped it), failure otherwise
steps_result() {
  local job=$1 s
  shift
  for s in "$@"; do [ "${rc_of[$job/$s]:-x}" = 0 ] || { echo failure; return; }; done
  echo success
}
# decide JOB: $verdict is true, false or absent, from the job's if:
decide() {
  verdict=$(judge if "$1" 2>> "$OUT/setup.log") || setup_fail "job $1's if: (OUT/setup.log)"
}

# vars_for JOB SHORT: NAME=VALUE, one per line, for every env: name whose value is a ${{ }} expression that the step may
# name: each value as GitHub evaluates it for this run (the header says from what)
vars_for() {
  if [ "$workflow" = pr ]; then
    printf '%s\n' "KIND=$KIND" "EVENT_BASE=$event_base" "EVENT=$event"
    case $1/$2 in
      plan/base) printf '%s\n' "GH_TOKEN=pr-steps-stand-in" "PR=0" ;;
      plan/plan|plan/plan-head-tools)
        printf '%s\n' "BASE=$(output plan base base)" "ROUTED=$(output plan base routed)" ;;
      plan/reach) printf '%s\n' "ROUTED=$(output plan base routed)" ;;
      plan/elsewhere)
        # a rehearsal is no merge queue group and names no pull request (PR is empty), so this step answers false
        # before it calls gh at all, unless the base pins this tree for a deferred check, which the plan step answered
        printf '%s\n' "GH_TOKEN=pr-steps-stand-in" "BASE=$(output plan base base)" \
          "ROUTED=$(output plan base routed)" "REF_NAME=$BASE_BRANCH" "GROUP_HEAD=$prhead" \
          "VM_EVIDENCE_BY=sjawhar-agent[bot]" "DEFERRED=$(output plan plan deferred)" \
          "CHECK_OF_RECORD=$(output plan plan check_of_record)" "PLANNED_TOOLS=$(output plan plan tools)" \
          "PR=" "PR_HEAD=$([ "$event" = pull_request ] && echo "$prhead")" "HOLD=none" ;;
      lint/base) printf '%s\n' "PLAN_BASE=$(job_output plan base)" "PLAN_ROUTED=$(job_output plan routed)" ;;
      lint/ledger) printf '%s\n' "BASE=$(output lint base base)" "ROUTED=$(output lint base routed)" ;;
      lint/lint|lint/lint-head-tools)
        printf '%s\n' "BASE=$(output lint base base)" "ROUTED=$(output lint base routed)" \
          "INTO=refs/heads/$BASE_BRANCH" "PLANNED_TOOLS=$(job_output plan tools)" ;;
      tests/tests)
        printf '%s\n' "OFT_SKIP_REPOSITORY_LINT=$([ "$(job_output plan repository_lint)" = true ] && echo 0 || echo 1)" ;;
      rekey/base) printf '%s\n' "BASE=$(job_output plan base)" ;;
      rekey/rekey)
        printf '%s\n' "BASE=$(job_output plan base)" "WINDOW=${OSSV_REKEY_WINDOW:-}" \
          "BASE_REF=$([ "$event" = pull_request ] && echo "$BASE_BRANCH")" ;;
      required/collect)
        printf '%s\n' "PLAN_RESULT=$(job_result plan)" "TESTS=$(job_output plan tests)" \
          "CONTROLS=false" "REPOSITORY_LINT=$(job_output plan repository_lint)" "UNITS=$(job_output plan units)" \
          "HOLD=$(job_output plan hold)" "QUEUED=$queued" "PLANNED_TOOLS=$(job_output plan tools)" \
          "LINT_RESULT=$(job_result lint)" "TESTS_RESULT=$(job_result tests)" \
          "CONTROLS_RESULT=skipped" "CHECK_RESULT=$(job_result check)" \
          "DRAFTS_LISTED=$([ "$(job_output plan draft_legs)" != '[]' ] && echo true || echo false)" \
          "FETCH_DRAFTS_RESULT=$(job_result fetch-drafts)" \
          "CHECKED_ELSEWHERE=$(job_output plan checked_elsewhere)" \
          "CHECKED_ELSEWHERE_NOTE=$(job_output plan checked_elsewhere_note)" \
          "STREAM_TOOLS=$(job_output plan stream_tools)" "STREAM_TOOLS_RESULT=$(job_result stream_tools)" \
          "FARM_TESTS=$(job_output plan farm_tests)" "FARM_TESTS_RESULT=$(job_result farm_tests)" \
          "GH_TOKEN=pr-steps-stand-in" "PR=" "HEAD_SHA=$([ "$event" = pull_request ] && echo "$prhead")" ;;
    esac
  else
    printf '%s\n' "EVENT_BASE=$event_base"
    # a dispatch names no units here, and the queue step did not run
    case $1/$2 in plan/plan) printf '%s\n' "UNITS=" "QUEUE_CHECKED=" "QUEUE_RUNS=" ;; esac
  fi
}

# Every env: name of every step this run may start has a value here, or the run stops before the first step.
names_only=1
for f in "$W"/steps/*.keys; do
  step=$(basename "$f" .keys)
  given=$(vars_for "${step%%-*}" "${step#*-}" | sed 's/=.*//')
  while IFS= read -r key; do
    grep -qxF -- "$key" <<< "$given" ||
      setup_fail "$wf's step ${step%%-*}/${step#*-} names $key in its env:, which pr-steps.sh does not set"
  done < "$f"
done
names_only=''

# run_step JOB SHORT [diag]: runs the step in its job's workspace, as the header says, unless its own if: is false;
# its summary line, and its exit status in rc_of (a diag's in no table: it decides nothing)
run_step() {
  local job=$1 short=$2 kind=${3:-} name=$1-$2 ws=$W/$1 rc start kv key line cond
  if [ -e "$W/steps/$name.if" ]; then
    cond=$(judge step-if "$name" 2>> "$OUT/setup.log") || setup_fail "step $job/$short's if: (OUT/setup.log)"
    if [ "$cond" != true ]; then
      say "SKIP $job/$short (its if: is false)"
      [ "$kind" = diag ] || rc_of[$job/$short]=0
      return 0
    fi
  fi
  local -a env=(HOME="$W/home" PATH="$W/bin:$VENV/bin:$PATH" LANG=C.UTF-8 CI=true GITHUB_ACTIONS=true
    GITHUB_WORKSPACE="$ws" RUNNER_TEMP="$W/$job.tmp" GITHUB_OUTPUT="$W/files/$name.output"
    GITHUB_STEP_SUMMARY="$W/files/$name.md" GITHUB_EVENT_NAME="$event" GITHUB_REPOSITORY="$repository"
    GITHUB_REF="$ref" GITHUB_SHA="$commit")
  local -a given
  mapfile -t given < <(vars_for "$job" "$short")
  while IFS= read -r line; do env+=("$line"); done < "$W/steps/$name.env"
  while IFS= read -r key; do
    for kv in "${given[@]}"; do [ "${kv%%=*}" != "$key" ] || env+=("$kv"); done
  done < "$W/steps/$name.keys"
  mkdir -p "$ws" "$W/$job.tmp"
  [ "$workflow" != pr ] || [ -e "$ws/head" ] || ln -s "$W/head" "$ws/head"
  : > "$W/files/$name.output"
  : > "$W/files/$name.md"
  start=$(date +%s)
  ( cd "$ws/$(cat "$W/steps/$name.wd")" &&
    exec env -i "${env[@]}" bash --noprofile --norc -eo pipefail "$W/steps/$name.sh" ) > "$OUT/$name.log" 2>&1
  rc=$?
  [ ! -s "$W/files/$name.output" ] || cp "$W/files/$name.output" "$OUT/$name.output"
  [ ! -s "$W/files/$name.md" ] || cp "$W/files/$name.md" "$OUT/$name.md"
  line="$([ "$rc" -eq 0 ] && echo PASS || echo "FAIL($rc)") $job/$short ($(( $(date +%s) - start )) s)"
  if [ "$kind" = diag ]; then
    say "diag: $line"
  else
    rc_of[$job/$short]=$rc
    say "$line"
  fi
  return "$rc"
}
skip() { say "SKIP $1 ($2)"; }
keep_plan() { [ ! -s "$W/plan.tmp/plan.json" ] || cp "$W/plan.tmp/plan.json" "$OUT/$1.json"; }
units_note() {
  local units
  units=$(job_output plan units)
  case $units in ''|0|*[!0-9]*) ;; *)
    say "note: units=$units: the drafts step and fetch-drafts are not rehearsed (draft_legs is taken as '[]')" ;;
  esac
}

if [ "$workflow" = release-check ]; then
  VENV=$hv
  decide plan
  if [ "$verdict" = true ]; then
    run_step plan plan
    keep_plan plan-plan
    record plan "$(steps_result plan plan)"
  else
    skip plan/plan "the plan job's if: is false"
    record plan skipped
  fi
  deferred=$(job_output plan deferred)
  say "plan: deferred=${deferred:-false} units=$(answer plan units) full=$(answer plan full)"
  units_note
  for job in fetch-drafts check; do
    decide "$job"
    if [ "$verdict" = true ]; then
      say "note: GitHub starts $job (units=$(answer plan units), draft_legs=$(answer plan draft_legs)), which is not rehearsed"
      record "$job" success
    else
      record "$job" skipped
    fi
  done
  ! judge_failed || exit 1
  [ "$(job_result plan)" = success ]
  exit $?
fi

not_rehearsed=''

# queue_run: never run here; GitHub starts it for a push (its if:), which gives '' outputs here: a push the merge
# queue did not check
decide queue_run
record queue_run "$([ "$verdict" = true ] && echo success || echo skipped)"

# plan job: the base's tools and venv
VENV=$bv
decide plan
if [ "$verdict" != true ]; then
  for s in base plan elsewhere reach; do skip "plan/$s" "the plan job's if: is false"; done
  record plan skipped
else
  if run_step plan base; then
    run_step plan plan
    keep_plan plan-plan
    run_step plan elsewhere
    run_step plan reach
    if [ -n "$diag" ]; then
      run_step plan plan-head-tools diag
      keep_plan plan-plan-head-tools
    fi
  else
    skip plan/plan "the job's base step failed"
    skip plan/elsewhere "the job's base step failed"
    skip plan/reach "the job's base step failed"
  fi
  record plan "$(steps_result plan base plan elsewhere reach)"
fi
elsewhere=$(job_output plan checked_elsewhere)
say "plan: tools=$(answer plan tools) checked_elsewhere=${elsewhere:-false} units=$(answer plan units)"
note "reach: repository_lint=$(answer plan repository_lint) tests=$(answer plan tests) controls=$(answer plan controls)"

# lint job
decide lint
if [ "$verdict" != true ]; then
  for s in base ledger lint generate; do skip "lint/$s" "the lint job's if: is false"; done
  record lint skipped
else
  if run_step lint base; then
    run_step lint ledger
    run_step lint lint
    run_step lint generate
    if [ -n "$diag" ]; then
      VENV=$hv
      run_step lint lint-head-tools diag
      VENV=$bv
    fi
  else
    for s in ledger lint generate; do skip "lint/$s" "the job's base step failed"; done
  fi
  record lint "$(steps_result lint base ledger lint generate)"
fi

# tests job, at this change, with its own venv
decide tests
if [ "$verdict" != true ]; then
  skip tests/tests "the tests job's if: is false: plan $(job_result plan), lint $(job_result lint), tests=$(answer plan tests)"
  record tests skipped
else
  VENV=$hv
  run_step tests tests
  record tests "$(steps_result tests tests)"
  ran=$(sed -n 's/^\(ran [0-9][0-9]* test.*\)$/\1/p' "$OUT/tests-tests.log" | tail -n 1)
  say "note: tests: ${ran:-no 'ran ...' line in OUT/tests-tests.log}"
fi

# rekey job (rule D11), with the base's venv
decide rekey
if [ "$verdict" != true ]; then
  for s in base rekey; do skip "rekey/$s" "the rekey job's if: is false"; done
  record rekey skipped
else
  VENV=$bv
  if run_step rekey base; then
    run_step rekey rekey
  else
    skip rekey/rekey "the job's base step failed"
  fi
  record rekey "$(steps_result rekey base rekey)"
fi

# the jobs this script never runs: one GitHub starts leaves this rehearsal without a verdict
units_note
decide fetch-drafts
if [ "$verdict" = true ]; then
  say "FAIL(-) fetch-drafts/not-run (GitHub starts it: draft_legs=$(answer plan draft_legs))"
  not_rehearsed=1
  record fetch-drafts success   # so that check's if: reads it as GitHub would, had it passed
else
  record fetch-drafts skipped
fi
decide check
if [ "$verdict" = true ]; then
  say "FAIL(-) check/not-run (GitHub starts it: units=$(answer plan units))"
  not_rehearsed=1
  record check success
else
  record check skipped
fi
record controls skipped
if [ "$(job_output plan controls)" = true ]; then
  say "note: reach answered controls=true: required/collect is judged with CONTROLS=false and CONTROLS_RESULT=skipped; GitHub's required also needs the controls job, which is not run here"
fi
decide stream_tools
if [ "$verdict" = true ]; then
  say "FAIL(-) stream_tools/not-run (GitHub starts it: dev/stream/ changed)"
  not_rehearsed=1
  record stream_tools success
else
  record stream_tools skipped
fi
decide farm_tests
if [ "$verdict" = true ]; then
  say "FAIL(-) farm_tests/not-run (GitHub starts it: a file the farm runner's tests read, or their job, changed)"
  not_rehearsed=1
  record farm_tests success
else
  record farm_tests skipped
fi

decide required
if [ "$verdict" != true ]; then
  skip required/collect "the required job's if: is false"
elif [ -n "$not_rehearsed" ]; then
  skip required/collect "GitHub starts a job this script does not run (above): no verdict to rehearse"
else
  run_step required collect
fi

[ -z "$not_rehearsed" ] || exit 1
! judge_failed || exit 1
for step in "${!rc_of[@]}"; do
  [ "${rc_of[$step]}" = 0 ] || exit 1
done
exit 0
