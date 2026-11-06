#!/bin/bash
# apply-B.sh <workdir> <LIB>: copy the run's stage-out into LIB by port_core --apply's own rule (A/ always; any other file
# only when LIB lacks it), because --apply refuses while the one known FAIL row stands: rename-new-undeclared UciSyms,
# whose Record is declared in lib/B/YF0m.v (the start-up layer, never staged, so the check does not read it). Writes the
# copied paths to applied.txt beside this script. Refuses if stage-out holds a file LIB already has (nothing is overwritten).
set -euo pipefail
WORK=$1 LIB=$2
HERE=$(cd "$(dirname "$0")" && pwd)
cd "$WORK/stage-out"
: > "$HERE/applied.txt.new"
while IFS= read -r f; do
  if [ -e "$LIB/$f" ] && [ "${f%%/*}" != A ]; then echo "apply-B: $f exists in LIB: refusing to overwrite" >&2; exit 2; fi
  mkdir -p "$LIB/$(dirname "$f")"; cp "$f" "$LIB/$f"; echo "$f" >> "$HERE/applied.txt.new"
done < <(find . -name '*.v' | sed 's#^\./##' | LC_ALL=C sort)
{ echo "# files copied from the run's stage-out by --apply's rule (A/ always; others only when LIB lacks them): $(wc -l < "$HERE/applied.txt.new")"; cat "$HERE/applied.txt.new"; } > "$HERE/applied.txt"
rm "$HERE/applied.txt.new"
echo "apply-B: $(($(wc -l < "$HERE/applied.txt") - 1)) files copied"
