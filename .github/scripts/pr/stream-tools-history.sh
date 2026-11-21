set -euo pipefail
git fetch --filter=blob:none --no-tags --unshallow origin "$(git rev-parse HEAD)"
# A shallow clone here would make every baseline read fail by name rather than be read, so the run must
# not go on with one: the history of manifest.d/ and of MANIFEST.tsv is what names the commit each row was
# written at, and the path the tools tree had there.
[ "$(git rev-parse --is-shallow-repository)" = false ] || {
  echo "::error::the clone is still shallow: no import-record history to read baselines against"
  exit 1; }
echo "history: $(git rev-list --count HEAD) commit(s), of which"\
     "$(git rev-list --count HEAD -- dev/stream/manifest.d dev/stream/MANIFEST.tsv stream/MANIFEST.tsv)"\
     "wrote a row of the import's record"
# main squash-merges, so a merge queue group's commit has main as its only parent and none of the history
# the rows were written in. That history is the tag's (dev/stream/HISTORY_ROOT, docs/import.md), fetched
# here as commits and trees only. A fetch that fails is not this step's verdict: where the history is
# needed and the tag is not here, the checker fetches it in its own fetch step, and a check that still
# cannot read it says DID NOT RUN, naming the tag (tools_check.history_starts).
tag=refs/tags/ossv/stream-tools-history
git fetch --filter=blob:none --no-tags origin "+$tag:$tag" ||
  echo "::warning::$tag could not be fetched; the checker fetches it itself if it needs it, or says DID NOT RUN"
