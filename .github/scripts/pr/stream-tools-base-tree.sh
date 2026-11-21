set -euo pipefail
base="$EVENT_BASE"
if [ "$GITHUB_EVENT_NAME" = pull_request ]; then
  read -r -a parents <<< "$(git cat-file -p HEAD | sed -n 's/^parent //p' | tr '\n' ' ')"
  [ "${#parents[@]}" = 2 ] || {
    echo "::error::HEAD has ${#parents[@]} parent(s): not the merge commit GitHub builds for a pull request"
    exit 1; }
  base="${parents[0]}"
fi
case "$base" in ''|0000000000000000000000000000000000000000)
  echo "this run has no base to compare the counts with"
  echo "tree=" >> "$GITHUB_OUTPUT"
  exit 0 ;;
esac
# A base this clone does not hold is this step's failure and not a comparison quietly skipped: without it
# the next step has no floor, and a run that prints one count where two are the answer says nothing.
git cat-file -e "$base^{commit}" 2>/dev/null ||
  git fetch --filter=blob:none --no-tags --depth=1 origin "$base"
git worktree add --no-checkout --detach "$RUNNER_TEMP/base" "$base"
git -C "$RUNNER_TEMP/base" sparse-checkout set --cone dev/stream .github tools/oft tools/publish
git -C "$RUNNER_TEMP/base" checkout --detach "$base"
echo "the base $base: $(git -C "$RUNNER_TEMP/base" ls-files -- dev/stream .github tools/oft tools/publish |
  wc -l) file(s) of the paths this job holds"
echo "tree=$RUNNER_TEMP/base/dev/stream" >> "$GITHUB_OUTPUT"
