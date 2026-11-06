#!/bin/sh
# Readers of YH03 cells: git grep -w of each name over every .v of the unit except the two YH03.v.
# Usage (from the repository root): grep-readers.sh REF NAME...
# Prints "NAME N" per name, then each reader as REF:path:line:text. A positive control follows: src0_D_ofl_lock (read
# by YI5c.v) by the same command, and the first name by git grep -w over the two YH03.v only.
set -eu
ref=$1; shift
u=proofs/libreac/fuzz_boxreg
readers() {
	git grep -n -w -e "$1" "$ref" -- "$u/*.v" ":!$u/lib/Reusable/YH03.v" ":!$u/lib/U/Reusable/YH03.v" || true
}
echo "# ref $(git rev-parse "$ref")"
echo "# readers outside the two YH03.v (git grep -w, $u/*.v)"
for n in "$@"; do
	out=$(readers "$n")
	if [ -z "$out" ]; then echo "$n 0"; else echo "$n $(printf '%s\n' "$out" | wc -l)"; printf '%s\n' "$out"; fi
done
echo "# positive control 1: src0_D_ofl_lock by the same command"
echo "src0_D_ofl_lock $(readers src0_D_ofl_lock | grep -c . || true)"
echo "# positive control 2: $1 by git grep -w over the two YH03.v only"
echo "$1 $(git grep -n -w -e "$1" "$ref" -- "$u/lib/Reusable/YH03.v" "$u/lib/U/Reusable/YH03.v" | grep -c . || true)"
