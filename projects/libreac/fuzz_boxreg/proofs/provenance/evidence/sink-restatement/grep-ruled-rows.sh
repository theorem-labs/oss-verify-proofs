#!/bin/sh
# Readers of the ruled YH03 sink rows: git grep -w of each name over every .v of the unit except the two YH03.v.
# Usage (from the repository root): grep-ruled-rows.sh REF
# A name with 0 readers prints "0"; each reader prints as REF:path:line:text. The positive controls must match.
set -eu
ref=$1
u=proofs/libreac/fuzz_boxreg
rows="src0_A_stdio_read src0_E_stdio_read src0_A_stdio_seek src0_E_stdio_seek
src0_D_str_wb src0_D_str_tmp_out_gif src0_D_str_3 src0_D_str_rwa"
readers() {
	git grep -n -w -e "$1" "$ref" -- "$u/*.v" ":!$u/lib/Reusable/YH03.v" ":!$u/lib/U/Reusable/YH03.v" || true
}
echo "# ref $(git rev-parse "$ref")"
echo "# readers outside the two YH03.v (git grep -w, $u/*.v)"
for n in $rows; do
	out=$(readers "$n")
	if [ -z "$out" ]; then echo "$n 0"; else echo "$n $(printf '%s\n' "$out" | wc -l)"; printf '%s\n' "$out"; fi
done
echo "# positive control 1: a name YI5c.v reads, by the same command"
out=$(readers src0_D_ofl_lock)
echo "src0_D_ofl_lock $(printf '%s\n' "$out" | grep -c .)"
printf '%s\n' "$out"
echo "# positive control 2: the rows themselves, by git grep -w over the two YH03.v only"
for n in $rows; do
	echo "$n $(git grep -n -w -e "$n" "$ref" -- "$u/lib/Reusable/YH03.v" "$u/lib/U/Reusable/YH03.v" | grep -c . || true)"
done
