set -euo pipefail
# First, before any code of the change: actions/checkout writes the job's token into head/.git/config as
# an http extraheader unless persist-credentials is false (the checkout above).  A header there stops the
# job.  So does a config that git cannot read.
rc=0
git -C head config --local --get-regexp '^http\..*\.extraheader$' > /dev/null || rc=$?
case "$rc" in
  1) ;;
  0) echo "::error::head/.git/config holds an http extraheader, a git credential: this job runs no code of the change while it is there"; exit 1 ;;
  *) echo "::error::git config cannot read head/.git/config (exit $rc), so this job runs no code of the change"; exit 1 ;;
esac
# The plan's two lists, UNITS and PROOFS, each a JSON list: each unit is projects/<p>/<h>.  The step takes
# each list in sorted order.
for list in UNITS PROOFS; do
  python3 -c 'import json, sys
units = json.loads(sys.argv[1])
if not isinstance(units, list) or not all(isinstance(u, str) for u in units):
    sys.exit("not a JSON list of names")
sys.stdout.write("".join(u + "\0" for u in sorted(units)))' "${!list}" > "$RUNNER_TEMP/made-from-${list,,}" || {
    echo "::error::the plan named the units '${!list}' in $list, which is not a JSON list of units"; exit 1; }
done
mapfile -d '' -t units < "$RUNNER_TEMP/made-from-units"
mapfile -d '' -t proofs < "$RUNNER_TEMP/made-from-proofs"
for u in "${units[@]}" "${proofs[@]}"; do
  [[ "$u" =~ ^projects/[^/[:cntrl:]]+/[^/[:cntrl:]]+$ ]] || {
    printf '::error::the plan named the unit %q, which is not projects/<p>/<h>\n' "$u"; exit 1; }
done
case "$HOLD" in none|draft|label) ;; *)
  echo "::error::the plan answered hold '$HOLD', none of none, draft and label"; exit 1 ;;
esac
# Each unit to check, with its kind: the strict units, then the proofs-only units.  A proofs-only unit is
# checked only when the plan's hold is none.  For any other hold, the step prints one line for the unit and
# does nothing more with it.
todo=()
declare -A kind=()
for u in "${units[@]}"; do todo+=("$u"); kind[$u]=strict; done
for u in "${proofs[@]}"; do
  # a unit in both lists is strict, and todo holds it once
  [ -z "${kind[$u]:-}" ] || continue
  if [ "$HOLD" != none ]; then
    echo "$u: not checked: its proofs changed outside proofs/provenance/, and the plan's hold is $HOLD, not none"
    continue
  fi
  todo+=("$u")
  kind[$u]=proofs
done
if [ "$KIND" = contributor ]; then
  echo "KIND=contributor: this job runs no code of the change (no --unit-file, no --check, no tests), as the lint job takes a contributor's tools from the base. Code an outside contributor brings runs only in the tests job. Each unit that the step checks still fails when it holds a made_from.py or a made-from.tsv under its proofs/provenance/ anywhere but evidence/licence/, or one of the two there without the other."
fi
# one line of a workflow command: GitHub reads %0A as a new line
escape() { local s=${1//'%'/'%25'}; s=${s//$'\r'/'%0D'}; printf '%s' "${s//$'\n'/'%0A'}"; }
# What a program of the change wrote, on stdout and stderr alike.  The runner reads no workflow command
# between these two lines, and the token is this block's alone.
guard() {
  [ -n "$1" ] || return 0
  local token
  token=$(od -An -tx1 -N16 /dev/urandom | tr -d ' \n')
  echo "::stop-commands::$token"
  printf '%s\n' "$1"
  echo "::$token::"
}
rc=0
# First, for every unit to check and before any code of the change runs: its made_from.py files and its
# made-from.tsv files under proofs/provenance/.  A made_from.py reads its record only at
# proofs/provenance/evidence/licence/made-from.tsv (the job's comment says why).  So a made_from.py or a
# made-from.tsv in any other directory fails here, and so does one of the two at evidence/licence/ without the
# other.  This holds for both kinds of unit.  The step runs no made_from.py of a unit with such a file.  A
# unit that holds neither file gets one line and no check.  The step keeps each other unit, which holds both
# files at evidence/licence/ and no other such file, for the checks below.  The map kind gives the kind of
# each unit.
kept=()
for u in "${todo[@]}"; do
  files=()
  if [ -d "head/$u/proofs/provenance" ]; then
    while IFS= read -r -d '' f; do files+=("$f"); done < <(find "head/$u/proofs/provenance" \
      \( -name made_from.py -o -name made-from.tsv \) -type f -print0 | sort -z)
  fi
  if [ "${#files[@]}" = 0 ]; then
    echo "$u: no made_from.py and no made-from.tsv under its proofs/provenance/: nothing to check"
    continue
  fi
  # The step compares the paths alone.  It opens no file of the change.
  licence=head/$u/proofs/provenance/evidence/licence
  generator=false
  record=false
  refused=false
  for f in "${files[@]}"; do
    case "$f" in
      "$licence/made_from.py") generator=true ;;
      "$licence/made-from.tsv") record=true ;;
      *)
        what="a made-from record"
        if [ "${f##*/}" = made_from.py ]; then what="a made_from.py"; fi
        echo "::error::$u holds $(escape "${f#"head/$u/"}"), $what outside proofs/provenance/evidence/licence/. A unit's made_from.py reads its record only at proofs/provenance/evidence/licence/made-from.tsv, and the strip check of lint looks for it there. Keep the generator and its record there."
        refused=true ;;
    esac
  done
  if [ "$generator" = true ] && [ "$record" = false ]; then
    echo "::error::$u holds proofs/provenance/evidence/licence/made_from.py, a made_from.py with no made-from.tsv beside it, so its --check has no record to compare. Deleting or moving a record does not stop this check. Keep the record beside its generator, or delete the generator with it."
    refused=true
  elif [ "$record" = true ] && [ "$generator" = false ]; then
    echo "::error::$u holds proofs/provenance/evidence/licence/made-from.tsv, a made-from record with no made_from.py beside it, so nothing can check it. Deleting or moving a generator does not stop this check. Keep the generator beside its record, or delete the record with it."
    refused=true
  fi
  if [ "$refused" = true ]; then
    rc=1
    continue
  fi
  kept+=("$u")
done
[ "$KIND" != contributor ] || exit "$rc"
# Then the made_from.py of each unit that the step kept: the strict units, then the proofs-only units, each in
# sorted order.  The change's code runs with no command file of the runner in its environment.
for u in "${kept[@]}"; do
  if [ "${kind[$u]}" = strict ]; then
    why="strict: its provenance tree or its images/dune changed, or the change can move every record"
  else
    why="proofs only: its proofs changed outside proofs/provenance/"
  fi
  rel=$u/proofs/provenance/evidence/licence/made_from.py
  # The shared generator's check of the file: only its unit's data and one call of that generator.  A file
  # that it refuses is not data alone, so its --check does not run.  Nor does the --check of a file whose
  # call `timeout 60` stops.
  if [ -f head/dev/licence/made_from.py ]; then
    echo "dev/licence/made_from.py --unit-file $rel"
    src=0
    out=$(cd head && env -u GITHUB_OUTPUT -u GITHUB_ENV -u GITHUB_PATH -u GITHUB_STATE -u GITHUB_STEP_SUMMARY \
      timeout 60 python3 dev/licence/made_from.py --unit-file "$rel" 2>&1) || src=$?
    guard "$out"
    case "$src" in
      0) ;;
      124) echo "::error::dev/licence/made_from.py --unit-file $rel did not finish within 60 s and was stopped, so its --check does not run"; rc=1; continue ;;
      *) echo "::error::dev/licence/made_from.py --unit-file $rel exited $src: the shared generator does not accept the file as its unit's data and one call of that generator (the output above says why), so its --check does not run"; rc=1; continue ;;
    esac
  fi
  echo "checking $rel"
  started=$(date +%s)
  src=0
  out=$(cd head && env -u GITHUB_OUTPUT -u GITHUB_ENV -u GITHUB_PATH -u GITHUB_STATE -u GITHUB_STEP_SUMMARY \
    timeout 1800 python3 "$rel" --check 2>&1) || src=$?
  guard "$out"
  echo "$u: $rel --check exited $src in $(( $(date +%s) - started )) s ($why)"
  case "$src" in
    0) echo "$rel --check: the record matches its generator" ;;
    1) echo "::error::$rel --check exited 1: the record differs from what its generator gives (the rows + and - above). Either the tree changed and the record was not brought up to date, or a file's licence lines are missing and nothing declares the file, or a row was changed by hand. Do not run made_from.py --apply to clear this; a file a lane has established is its own is declared, with its reason, where the generator reads it, and the unit's owner decides the record (see the unit's provenance docs). What the record reports, and what it does not, is in the module docstring of dev/licence/made_from.py."; rc=1 ;;
    2) echo "::warning::$rel --check exited 2, so the check could not decide; nothing is failed:%0A$(escape "$out")" ;;
    # Drift: the record names no path twice, and every row that differs is one that a run gives again, for a
    # file that the record holds in no row of another kind.  It fails a strict unit, as exit 1 does.
    # A proofs-only unit gets one warning with the number of rows that differ, the lines of the output that
    # start with "- " or "+ " (a row at another place counts twice), and the first 20 of them in order.
    3)
      if [ "${kind[$u]}" = strict ]; then
        echo "::error::$rel --check exited 3: the rows that a run gives again differ from the record (the rows + and - above). made_from.py --record brings the record up to date. This unit is $why, so the job fails."; rc=1
      else
        mapfile -t rows < <(grep -E '^[-+] ' <<< "$out" || true)
        echo "::warning::$u: its made-from record is not up to date in rows that a run gives again ($rel --check exited 3). Rows that differ: ${#rows[@]}. The unit is $why, so the job does not fail for this. made_from.py --record brings the record up to date. The first 20 rows that differ:%0A$(escape "$(printf '%s\n' "${rows[@]:0:20}")")"
      fi ;;
    4) echo "::error::$rel --check exited 4: the generator refused this unit (the output above says why), so nothing is passed"; rc=1 ;;
    # A defect of the shared generator's own code (DEFECT in dev/licence/made_from.py): a run or the check
    # stopped on a fault or an uncaught exception, a run wrote no OUT or one that is not UTF-8, or its two runs
    # differ.  It fails every unit, strict or proofs only, since the check then says nothing of the record.
    5) echo "::error::$rel --check exited 5: the shared generator dev/licence/made_from.py stopped on a defect of its own code (the output above says which), so nothing is passed. The generator, not the record, is what to fix."; rc=1 ;;
    124) echo "::error::$rel --check did not finish within 1,800 s and was stopped, so nothing is passed"; rc=1 ;;
    *) echo "::error::$rel --check exited $src: the check did not finish, so nothing is passed"; rc=1 ;;
  esac
done
exit "$rc"
