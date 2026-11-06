#!/bin/bash
# apply-B.sh <workdir> <LIB> [APPLIED]: copy the run's stage-out into LIB by port_core --apply's own rule (A/ always; any
# other file only when LIB lacks it), because --apply refuses while the run's known FAIL rows stand: the 15
# kept-refused-definition rows (lib_const_addr of B/YCeg.v, closed by B-ceg-const.patch; SOBUF_LO / SOBUF_HI, STDERR_BUF,
# STDOUT_BUFA and the five driver windows' SH_LO / SH_HI, each closed by an overrides-B.tsv row: 0 refusal markers are
# left), which port_core writes before it applies the overrides and patches. Writes the copied paths to APPLIED (default
# applied.txt beside this script). Refuses if stage-out holds a non-A file LIB already has (nothing is overwritten).
set -euo pipefail
WORK=$1 LIB=$2
HERE=$(cd "$(dirname "$0")" && pwd)
OUT=${3:-$HERE/applied.txt}
if grep -rl 'port_core_refused_' "$WORK/stage-out" > /dev/null; then echo "apply-B: refusal markers left in stage-out" >&2; exit 2; fi
cd "$WORK/stage-out"
: > "$OUT.new"
while IFS= read -r f; do
  if [ -e "$LIB/$f" ] && [ "${f%%/*}" != A ]; then echo "apply-B: $f exists in LIB: refusing to overwrite" >&2; exit 2; fi
  mkdir -p "$LIB/$(dirname "$f")"; cp "$f" "$LIB/$f"; echo "$f" >> "$OUT.new"
done < <(find . -name '*.v' | sed 's#^\./##' | LC_ALL=C sort)
{ echo "# files copied from the run's stage-out by --apply's rule (A/ always; others only when LIB lacks them): $(wc -l < "$OUT.new")"; cat "$OUT.new"; } > "$OUT"
rm "$OUT.new"
echo "apply-B: $(($(wc -l < "$OUT") - 1)) files copied"
