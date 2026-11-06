#!/bin/bash
# tools/oft/ci/check-units.sh: what one CI check job does for a set of harnesses.
# Its callers run it with these tools (TOOLS), never a pull request's:
#   pr.yml             the base branch's
#   weekly.yml         the checked ref's own: the release tag's when
#                      release.yml calls it, the chosen branch's on a manual
#                      run
#   release-check.yml  the checked commit's own: main's, or on a manual run of
#                      another branch, that branch's
# On the host it runs only those tools; the tree's proofs are compiled and its
# counterexamples run only in the containers below, with no network.
#
#   WORK      the tree whose statements are checked: for a pull request, a
#             worktree of the base branch with only the pull request's proofs,
#             counterexamples and findings (either layout, layout.py) laid over
#             it, and its generated files rendered again by the base's tools
#             (pr.yml)
#   TOOLS     the tools/ directory to run, as above
#
#   UNITS     the units whose build (statements and proofs) is checked;
#             PROOF_UNITS: those of them with a proof, as a JSON string (the
#             plan job's proof_units through toJSON; "" when none has one, and
#             null, a plan that does not say, is refused);
#             PROJECTS: the projects whose binaries they and the counterexamples
#             run on; CX_UNITS: the units whose counterexamples are run;
#             FINDINGS: the units whose findings are run, including a finding
#             whose harness withholds every published build (each may be empty)
#   ASSETS    a directory for the release assets; it may arrive already holding
#             draft archives, which the workflow's fetch-drafts job checked and
#             this job's read-only token cannot download.  The
#             `[ -e "$ASSETS/$file" ] ||` skip in step 1 is that hand-off and
#             must stay: without it a draft archive is downloaded by its tag from
#             fetch.RELEASES's repository, where a release not yet published
#             fails with `release not found`
#   PYDEPS    tools/oft/requirements.txt's packages for the checker container
#             (pip install --target); the runner image has its own
#   GH_TOKEN  the workflow's own read-only token, for `gh release download` of
#             the published archives not already in ASSETS; needed although
#             that repository is public, since GitHub allows unauthenticated
#             API requests 60 an hour per IP address
#   CPUS      optional: the plan's `cpus` for this job (pack.job_cpus): the
#             fewest CPUs tools/oft/proof-times.tsv gives any unit whose proofs
#             it checks (the job's proof_units),
#             where a unit measured to pass at the runner's full width asks
#             for no limit at all.  The checker container gets that many CPUs;
#             dune and the proof compiles run as many jobs as the container
#             has CPUs.  Unset, 0, or not below this runner's CPUs: every CPU
#
# Each part of each unit (its build, its counterexamples, its findings) is
# checked in a container of its own, whose /work is a view of that part: the
# paths its content key holds and the unit's binaries, and no other file of
# the tree (python3 -m oft.unitpaths; tools/oft/unitpaths.py says which), each
# mounted read-only.  So a check cannot read another unit's files, and a change
# that its key misses cannot change its result.  `oft check --facts-to` first
# loads the facts of the whole tree and checks its rules, once, in a container
# that mounts the tree read-only; each part's check then reads its unit's
# facts with --facts-from, from a read-only mount of that unit's file alone.
# Nothing a check writes outlives its container but its unit's view directory,
# which is removed before the next view is made: no cache is shared between
# units, and dune's is off.  The one file this script writes into WORK is a
# proof library's lib/dune (step 1b), with these tools, before any view is made.
#
# Every step fails loudly; `oft check` itself fails on a unit it examined
# nothing in, and on a unit with no proof when it is asked for proofs, so a
# unit of UNITS that PROOF_UNITS leaves out is checked with --parts statements.
# Every unit is checked; the script exits with the status of the first check
# that failed.  `oft fetch`, `oft check` and the views run as
# `python3 -m oft.fetch`, `python3 -m oft.check` and `python3 -m oft.unitpaths`,
# which load the checker and none of the other commands' modules
# (tools/oft/keys.py says which files the checker is).
set -euo pipefail
: "${WORK:?}" "${TOOLS:?}" "${ASSETS:?}" "${PYDEPS:?}"
: "${PROOF_UNITS:?PROOF_UNITS is not set: the plan says which units have proofs}"
# the real path: unitpaths refuses a view path under a symbolic link, and a mount follows one
WORK="$(cd -- "$WORK" && pwd -P)"
read -r -a units <<< "${UNITS:-}"
proof_text="$(python3 -c 'import json, sys
v = json.loads(sys.argv[1])
if not isinstance(v, str):
    sys.exit("PROOF_UNITS is %s, not a JSON string: the plan does not say which units have proofs" % json.dumps(v))
print(v)' "$PROOF_UNITS")"
read -r -a proof_units <<< "$proof_text"
read -r -a projects <<< "${PROJECTS:-}"
read -r -a cx_units <<< "${CX_UNITS:-}"
read -r -a finding_units <<< "${FINDINGS:-}"
if [ "${#units[@]}" -eq 0 ] && [ "${#cx_units[@]}" -eq 0 ] && [ "${#finding_units[@]}" -eq 0 ]; then
  echo "no units, counterexamples or findings to check" >&2
  exit 1
fi
for u in "${proof_units[@]}"; do
  [[ " ${units[*]} " == *" $u "* ]] || { echo "PROOF_UNITS names $u, which UNITS does not" >&2; exit 1; }
done
# the projects whose unpatched binaries the findings run on
read -r -a finding_projects <<< "$(printf '%s\n' "${finding_units[@]%%/*}" | sort -u | tr '\n' ' ')"
fetch() { PYTHONPATH="$TOOLS" python3 -m oft.fetch --root "$WORK" "$@"; }
image() {  # the image release.yaml pins, by digest
  python3 -c 'import sys, yaml; print(yaml.safe_load(open(sys.argv[1]))["images"][sys.argv[2]])' \
    "$WORK/release.yaml" "$1"
}

# 1. The binaries: each project's release asset, and the unpatched binaries
#    its findings run on, then `oft fetch`, which checks the archive's SHA-256
#    and every file's before it moves anything into place.
#    A published archive comes from the repository oft fetch downloads pins from
#    (fetch.RELEASES), whichever repository this check runs in: in another one
#    the release of the same name may be a draft, which this job's token cannot see.
mkdir -p -- "$ASSETS"
if [ "${#projects[@]}" -gt 0 ]; then
  fetch --list "${projects[@]}" > "$ASSETS/list.txt"
else
  : > "$ASSETS/list.txt"
fi
if [ "${#finding_units[@]}" -gt 0 ]; then
  fetch --findings --list "${finding_projects[@]}" >> "$ASSETS/list.txt"
fi
[ -s "$ASSETS/list.txt" ] || { echo "no assets listed for published units or findings" >&2; exit 1; }
releases="$(PYTHONPATH="$TOOLS" python3 -c 'from oft import fetch; print("/".join(fetch.RELEASES.split("/")[3:5]))')"
while read -r rel file _; do
  case "$file" in
    *-bin.tar.zst)
      [ -e "$ASSETS/$file" ] || gh release download "$rel" --repo "$releases" --pattern "$file" --dir "$ASSETS" ;;
  esac
done < "$ASSETS/list.txt"
if [ "${#projects[@]}" -gt 0 ]; then
  fetch --source "$ASSETS" "${projects[@]}"
fi
if [ "${#finding_units[@]}" -gt 0 ]; then
  fetch --source "$ASSETS" --findings "${finding_projects[@]}"
fi

# 1b. Each proof library is built by dune with the rule these tools render
#     (`oft check` writes lib/dune itself when the tree's differs: check.py,
#     _lib_targets), whichever tools rendered the tree, as a maintainer's change
#     to the template does.  In a view the unit's proofs folder (either layout,
#     layout.py) is a read-only mount, so that write is made here, on the host,
#     by these tools, before the facts and the views; `oft check` then finds
#     lib/dune as it renders it.  A library or a lib/dune that is not a plain
#     directory or file, or that a symbolic link leads to, is left as it is:
#     `oft check` refuses it.
if [ "${#proof_units[@]}" -gt 0 ]; then
  PYTHONPATH="$TOOLS" python3 - "$WORK" "${proof_units[@]}" <<'PY'
import os, stat, sys
from oft import facts, generate, layout
root = sys.argv[1]
namespace, opam_stem = facts.read_release_names(root)   # the names this tree's release.yaml gives its theories
for unit in sys.argv[2:]:
    p, _, hn = unit.partition("/")
    if not p or not hn or "/" in hn or {p, hn} & {".", ".."}:
        sys.exit("%s: not <project>/<harness>" % unit)
    for rel in (layout.proof_lib_dir(p, hn, layout.NEW), layout.proof_lib_dir(p, hn, layout.OLD)):
        lib = os.path.join(root, rel)
        # every component of the path a directory of its own, none reached through a link (root is a real path)
        if os.path.realpath(lib) != lib or not os.path.isdir(lib):
            continue
        dune, want = os.path.join(lib, "dune"), generate.proof_lib_dune(namespace, opam_stem, p, hn).encode()
        try:
            st = os.lstat(dune)
        except FileNotFoundError:
            st = None
        if st is not None:
            if not stat.S_ISREG(st.st_mode):
                continue
            if st.st_size == len(want):
                with open(dune, "rb") as f:
                    if f.read() == want:
                        continue
        fd = os.open(dune, os.O_WRONLY | os.O_CREAT | os.O_TRUNC | os.O_NOFOLLOW, 0o644)
        with os.fdopen(fd, "wb") as f:
            f.write(want)
        print("%s: written as these tools render it, before the view is made" % os.path.join(rel, "dune"))
PY
fi

# 2. The facts of the whole tree and its rules, once, with no network: in the
#    checker image when there is a build to check, else in the runner image,
#    so that a job pulls only the images it checks in.  The images are read
#    from release.yaml here, outside any container.
checker="$(image checker)"
if [ "${#cx_units[@]}" -gt 0 ] || [ "${#finding_units[@]}" -gt 0 ]; then runner="$(image runner)"; fi
# the views and the facts, beside the tree, on its disk
scratch="$(mktemp -d "$(dirname -- "$WORK")/check-units.XXXXXX")"
trap 'rm -rf -- "$scratch"' EXIT
facts="$scratch/facts" views="$scratch/view"
mkdir -- "$facts"
read -r -a all_units <<< "$(printf '%s\n' "${units[@]}" "${cx_units[@]}" "${finding_units[@]}" | sort -u | tr '\n' ' ')"
checker_env=(-e PYTHONPATH=/tools:/pydeps -v "$PYDEPS:/pydeps:ro")
runner_env=(-e PYTHONPATH=/tools:/opt/oss-fuzz-theorems/pydeps)
if [ "${#units[@]}" -gt 0 ]; then
  docker pull --quiet "$checker"
  facts_image=("${checker_env[@]}" "$checker")
else
  docker pull --quiet "$runner"
  facts_image=("${runner_env[@]}" "$runner")
fi
docker run --rm --network none -u "$(id -u):$(id -g)" -e HOME=/tmp -e PYTHONDONTWRITEBYTECODE=1 -e PYTHONSAFEPATH=1 \
  -v "$WORK:/work:ro" -v "$TOOLS:/tools:ro" -v "$facts:/facts" -w /work \
  "${facts_image[@]}" python3 -m oft.check --root /work --facts-to /facts "${all_units[@]}"

# make_view PART UNIT: make the view of UNIT's PART in $views, and set the array
# `view` to the docker arguments that mount it at /work, with UNIT's facts
# file at /facts.  $views itself is the writable /work, where dune writes
# _build; it holds only an empty mount point for each path of the view, so
# docker creates nothing in it, and each path is a read-only mount of the
# tree's own.  The build's dune-project is the one unitpaths writes: the forms
# of the tree's that its key holds.  It returns non-zero, with a line on
# stderr, when the view cannot be made; the caller fails that unit and goes on
# (set -e does not apply inside a function called with ||, so each step is
# checked here).
make_view() {
  local part="$1" unit="$2" list rel started="$EPOCHREALTIME"
  rm -rf -- "$views" "$scratch/dune-project" && mkdir -- "$views" || return
  local dune_project=()
  [ "$part" != build ] || dune_project=(--dune-project-to "$scratch/dune-project")
  list="$(PYTHONPATH="$TOOLS" python3 -m oft.unitpaths --root "$WORK" --part "$part" "${dune_project[@]}" "$unit")" \
    || { echo "FAIL $unit: its $part view could not be made" >&2; return 1; }
  view=(-v "$views:/work")
  while IFS= read -r rel; do
    [ -n "$rel" ] || continue
    if [ -d "$WORK/$rel" ]; then
      mkdir -p -- "$views/$rel" || return
    else
      mkdir -p -- "$(dirname -- "$views/$rel")" && : > "$views/$rel" || return
    fi
    view+=(-v "$WORK/$rel:/work/$rel:ro")
  done <<< "$list"
  if [ "$part" = build ]; then
    : > "$views/dune-project" || return
    view+=(-v "$scratch/dune-project:/work/dune-project:ro")
  fi
  view+=(-v "$facts/$unit.yaml:/facts/$unit.yaml:ro")
  echo "view of $unit $part: $(grep -c . <<< "$list") paths, made in" \
    "$(awk -v a="$started" -v b="$EPOCHREALTIME" 'BEGIN { printf "%.2f", b - a }') s"
}
status=0
failed() { [ "$status" -ne 0 ] || status="$1"; }

# 3. Statements and proofs, each unit in the checker image, with no network.
if [ "${#units[@]}" -gt 0 ]; then
  cpuset=()
  if [ -n "${CPUS:-}" ]; then
    [[ "$CPUS" =~ ^[0-9]+$ ]] || { echo "CPUS is not a whole number: '$CPUS'" >&2; exit 1; }
    if [ "$CPUS" -gt 0 ] && [ "$CPUS" -lt "$(nproc)" ]; then
      cpuset=(--cpuset-cpus "0-$((CPUS - 1))")
    fi
  fi
  echo "checker CPUs: ${CPUS:-0} asked (0: every CPU), $(nproc) on this runner, cpuset: ${cpuset[*]:-none}"
  for u in "${units[@]}"; do
    # A unit the plan lists in proof_units is checked with its proofs; any other has only its statements to check.
    parts=statements
    [[ " ${proof_units[*]} " != *" $u "* ]] || parts=statements,proofs
    make_view build "$u" || { failed "$?"; continue; }
    docker run --rm --network none -u "$(id -u):$(id -g)" "${cpuset[@]}" \
      -e HOME=/tmp -e DUNE_CACHE=disabled -e PYTHONDONTWRITEBYTECODE=1 -e PYTHONSAFEPATH=1 \
      "${view[@]}" -v "$TOOLS:/tools:ro" -w /work \
      "${checker_env[@]}" "$checker" python3 -m oft.check --root /work --facts-from /facts "$u" --parts "$parts" \
      || failed "$?"
  done
fi

# 4. Counterexamples, each unit in the pinned runner image
#    (toolchain/runner.Dockerfile), with no network, by the trusted tools.
#    `oft check` runs inside the container, so qemu-riscv64 is its child.  Run
#    as the container's first process instead, qemu cannot die of the signal it
#    passes on from the program (the kernel drops a signal with no handler sent
#    to a namespace's first process), and a counterexample that ends in SIGABRT
#    hangs until the timeout instead of reproducing.
# 5. Findings, the same way: each finding's input and control on the unpatched
#    binaries, every run compared with what finding.yaml records.
for part in counterexamples findings; do
  if [ "$part" = counterexamples ]; then todo=("${cx_units[@]}"); else todo=("${finding_units[@]}"); fi
  [ "${#todo[@]}" -gt 0 ] || continue
  docker pull --quiet "$runner"
  for u in "${todo[@]}"; do
    make_view "$part" "$u" || { failed "$?"; continue; }
    docker run --rm --network none -u "$(id -u):$(id -g)" \
      -e HOME=/tmp -e PYTHONDONTWRITEBYTECODE=1 -e PYTHONSAFEPATH=1 \
      "${view[@]}" -v "$TOOLS:/tools:ro" -w /work \
      "${runner_env[@]}" "$runner" python3 -m oft.check --root /work --facts-from /facts "$u" --parts "$part" \
      || failed "$?"
  done
done
exit "$status"
