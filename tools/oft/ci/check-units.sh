#!/bin/bash
# tools/oft/ci/check-units.sh: what one CI check job does for a set of harnesses.
# Its callers run it with these tools (TOOLS), never a pull request's:
#   pr.yml             the base branch's
#   weekly.yml         the checked ref's own: main's on its schedule, the
#                      release tag's when release.yml calls it, the chosen
#                      branch's on a manual run
#   release-check.yml  the checked commit's own: main's, or on a manual run of
#                      another branch, that branch's
# On the host it runs only those tools; the tree's proofs are compiled and its
# counterexamples run only in the containers below, with no network.
#
#   WORK      the tree whose statements are checked: for a pull request, a
#             worktree of the base branch with only the pull request's proofs/,
#             counterexamples/ and findings/ laid over it, and its generated
#             files rendered again by the base's tools (pr.yml)
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
#   CACHE     a dune cache directory, restored or empty
#   GH_TOKEN  the workflow's own read-only token, for `gh release download` of
#             the published archives not already in ASSETS; needed although
#             that repository is public, since GitHub allows unauthenticated
#             API requests 60 an hour per IP address
#
# Every step fails loudly; `oft check` itself fails on a unit it examined
# nothing in, and on a unit with no proof when it is asked for proofs, so a
# unit of UNITS that PROOF_UNITS leaves out is checked with --parts statements.
# `oft fetch` and `oft check` run as `python3 -m oft.fetch` and
# `python3 -m oft.check`, which load the checker and none of the other
# commands' modules (tools/oft/keys.py says which files the checker is).
set -euo pipefail
: "${WORK:?}" "${TOOLS:?}" "${ASSETS:?}" "${PYDEPS:?}" "${CACHE:?}"
: "${PROOF_UNITS:?PROOF_UNITS is not set: the plan says which units have proofs}"
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

# 2. Statements and proofs in the checker image, with no network.  Both images are read from the facts first: the
#    container below mounts the tree writable, and this script reads nothing from that tree after it.
checker="$(image checker)"
if [ "${#cx_units[@]}" -gt 0 ] || [ "${#finding_units[@]}" -gt 0 ]; then runner="$(image runner)"; fi
if [ "${#units[@]}" -gt 0 ]; then
  docker pull --quiet "$checker"
  mkdir -p -- "$CACHE"
  # A unit the plan lists in proof_units is checked with its proofs; any other has only its statements to check.
  proved=() unproved=()
  for u in "${units[@]}"; do
    if [[ " ${proof_units[*]} " == *" $u "* ]]; then proved+=("$u"); else unproved+=("$u"); fi
  done
  for u in "${proof_units[@]}"; do
    [[ " ${units[*]} " == *" $u "* ]] || { echo "PROOF_UNITS names $u, which UNITS does not" >&2; exit 1; }
  done
  # The cache is a mount of its own, so dune's default storage, a hard link into it, fails and it stores nothing;
  # copy mode stores a copy of each file.
  check_in_checker() {
    docker run --rm --network none -u "$(id -u):$(id -g)" \
      -e HOME=/tmp -e XDG_CACHE_HOME=/cache -e DUNE_CACHE=enabled -e DUNE_CACHE_STORAGE_MODE=copy \
      -e PYTHONDONTWRITEBYTECODE=1 -e PYTHONSAFEPATH=1 -e PYTHONPATH=/tools:/pydeps \
      -v "$WORK:/work" -v "$TOOLS:/tools:ro" -v "$PYDEPS:/pydeps:ro" -v "$CACHE:/cache" -w /work \
      "$checker" python3 -m oft.check --root /work "$@"
  }
  if [ "${#proved[@]}" -gt 0 ]; then check_in_checker "${proved[@]}" --parts statements,proofs; fi
  if [ "${#unproved[@]}" -gt 0 ]; then check_in_checker "${unproved[@]}" --parts statements; fi
fi

# 3. Counterexamples, in the pinned runner image (toolchain/runner.Dockerfile),
#    with no network, by the trusted tools.  `oft check` runs inside the
#    container, so qemu-riscv64 is its child.  Run as the container's first
#    process instead, qemu cannot die of the signal it passes on from the
#    program (the kernel drops a signal with no handler sent to a namespace's
#    first process), and a counterexample that ends in SIGABRT hangs until the
#    timeout instead of reproducing.
if [ "${#cx_units[@]}" -gt 0 ]; then
  docker pull --quiet "$runner"
  docker run --rm --network none -u "$(id -u):$(id -g)" \
    -e HOME=/tmp -e PYTHONDONTWRITEBYTECODE=1 -e PYTHONSAFEPATH=1 -e PYTHONPATH=/tools:/opt/oss-fuzz-theorems/pydeps \
    -v "$WORK:/work:ro" -v "$TOOLS:/tools:ro" -w /work \
    "$runner" python3 -m oft.check --root /work "${cx_units[@]}" --parts counterexamples
fi

# 4. Findings, the same way: each finding's input and control on the unpatched
#    binaries, every run compared with what finding.yaml records.
if [ "${#finding_units[@]}" -gt 0 ]; then
  docker pull --quiet "$runner"
  docker run --rm --network none -u "$(id -u):$(id -g)" \
    -e HOME=/tmp -e PYTHONDONTWRITEBYTECODE=1 -e PYTHONSAFEPATH=1 -e PYTHONPATH=/tools:/opt/oss-fuzz-theorems/pydeps \
    -v "$WORK:/work:ro" -v "$TOOLS:/tools:ro" -w /work \
    "$runner" python3 -m oft.check --root /work "${finding_units[@]}" --parts findings
fi
