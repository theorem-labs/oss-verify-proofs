#!/bin/bash
# apply-smB.sh <workdir> <LIB>: copy run.sh's stage-out into LIB by port_core --apply's own rule (a file only when LIB
# lacks it; nothing is overwritten), because --apply refuses while core-B's known FAIL row stands: rename-new-undeclared
# WireSyms, whose Record is declared in lib/B/YF0m.v (the start-up layer, never staged). Each copied file loses its
# leading licence lines (the Copyright, SPDX and every `Modified by` line before the first line of code, the donor's and
# port_core's own): the release tool writes the licence lines of new files. Every other byte is the stage-out's, checked
# here. Writes the copied paths, with the number of licence lines removed from each, to applied.txt beside this script.
set -euo pipefail
WORK=$1 LIB=$2
HERE=$(cd "$(dirname "$0")" && pwd)
cd "$WORK/stage-out"
: > "$HERE/applied.txt.new"
while IFS= read -r f; do
  if [ -e "$LIB/$f" ]; then echo "apply-smB: $f exists in LIB: refusing to overwrite" >&2; rm "$HERE/applied.txt.new"; exit 2; fi
  mkdir -p "$LIB/$(dirname "$f")"
  n=$(python3 - "$f" "$LIB/$f" <<'EOF'
import re, sys
src, dst = sys.argv[1], sys.argv[2]
lines = open(src).read().split('\n')
lic = re.compile(r'^\(\* (Copyright |SPDX-License-Identifier: |Modified by ).*\*\)$')
k = 0
while k < len(lines) and lic.match(lines[k]):
    k += 1
rest = lines[k:]
assert not any(lic.match(l) for l in rest), 'a licence line after the first code line'
assert rest and rest[0].startswith('From '), 'the first kept line is not a Require'
open(dst, 'w').write('\n'.join(rest))
assert open(dst).read() == '\n'.join(lines[k:]) and '\n'.join(lines) .endswith('\n'.join(rest))
print(k)
EOF
)
  echo "$f	$n" >> "$HERE/applied.txt.new"
done < <(find . -name '*.v' | sed 's#^\./##' | LC_ALL=C sort)
{ echo "# files copied from the run's stage-out (none existed in LIB), with the number of leading licence lines removed: $(wc -l < "$HERE/applied.txt.new")"; cat "$HERE/applied.txt.new"; } > "$HERE/applied.txt"
rm "$HERE/applied.txt.new"
echo "apply-smB: $(($(wc -l < "$HERE/applied.txt") - 1)) files copied"
