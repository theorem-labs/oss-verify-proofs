set -euo pipefail
answer=false
# what the lint step compares with, the paths that differ from it, and whether it takes --changed-only
compared=
if [ -n "$SINCE" ]; then
  git -c core.quotePath=false -C head diff --no-renames --name-only "$SINCE" HEAD > "$RUNNER_TEMP/changed-since.txt"
  compared="$RUNNER_TEMP/changed-since.txt"
elif [ "$ROUTED" = true ]; then
  compared="$RUNNER_TEMP/changed.txt"
fi
if [ -n "$compared" ] && [ "$PLANNED_TOOLS" != head ] \
    && grep -q -- '"--changed-only"' base/tools/oft/__main__.py \
    && PYTHONPATH=base/tools python -c '
import sys
from oft import lint
changed = open(sys.argv[1], encoding="utf-8", errors="surrogateescape").read().split("\n")
every = [rel for rel in changed if rel and lint.read_by_every_verdict(rel)]
if every:
    print("a verdict on another file may read %s: lint reads every file" % every[0])
sys.exit(1 if every else 0)' "$compared"; then
  answer=true
fi
echo "lint_changed_only=$answer" >> "$GITHUB_OUTPUT"
echo "lint reads only the changed files: $answer"
# Whether the lint job checks out the tree without the proof libraries (4.56 GB of the 4.66 GB this job's
# own checkout leaves out, the checkout step above): only for a pull request whose lint reads only the
# changed files, and only when the base's tools judge the names of the files such a checkout leaves out
# (lint.check_paths takes `unread`).  The lint job then checks out every left-out file that differs from
# what it compares with, so lint reads the bytes of every changed file, and an unchanged file keeps the
# verdict its bytes had there.  A merge queue group and a push to main keep the whole tree: their lint reads
# every file's bytes, so nothing reaches main that a whole-tree lint did not read.  A pull request that
# deletes or renames proof files takes this checkout too.  On 2026-11-17 its lint job was the faster one:
# 92 s against 342 s for a change that deletes one proof file (lint jobs 134183632699 and 134184102121), and
# 143 s against 298 s for one that renames 230 (lint jobs 134182581153 and 134182706429; in the first, the
# step "the left-out files lint reads" fetched the 230 blobs in one request, in 14 s).  In those jobs the
# whole-tree checkout took 108 s and 89 s (the restore of main's object store and the checkout), on the
# 4-core runner (the lint job's runs-on), and this one 23 s and 25 s, on the standard runner.
left_out=false
if [ "$answer" = true ] && [ "${GITHUB_EVENT_NAME:-}" = pull_request ] \
    && PYTHONPATH=base/tools python -c '
import inspect, sys
from oft import lint
sys.exit(0 if "unread" in inspect.signature(lint.check_paths).parameters else 1)'; then
  left_out=true
fi
echo "lint_files_left_out=$left_out" >> "$GITHUB_OUTPUT"
echo "lint checks out the tree without the proof libraries: $left_out"
