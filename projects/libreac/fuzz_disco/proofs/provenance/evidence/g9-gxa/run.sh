#!/usr/bin/env bash
# Every re-run command of this slice. Each step writes its outputs under $OUT and compares them with cmp to the file of
# this directory, or to the shipped file in git, that they re-derive; a difference stops the run.
#   bash run.sh STEP...     STEP: g9 | twins | gxamem | addrcheck | codeid | records | gxamem_nm | gates | all
#   (all = g9 twins gxamem addrcheck codeid: they re-run from this directory, git and the images; records, gxamem_nm
#   and gates re-make the extracts from the host records they name.)
# Inputs, each an environment variable (no path of any machine is written here):
#   HUB      a git repository holding the commits named below
#   OUT      an empty scratch directory outside the checkout
#   FM_TWIN  the unstripped fm image, named fuzz_manifest.debug (sha256 fc92e86bee06...)
#   FM_PIN   the stripped fm image, named fuzz_manifest (0ba7e1695886...)
#   A_PIN, B_PIN    the stripped images of record: fuzz_disco.asan (5e39150dd810...), fuzz_disco.asan-ubsan (cee6f04ad3d4...)
#   A_TWIN, B_TWIN  their unstripped twins of the release build, same names (b8aac6eee6a6..., ead714913acd...)
#   A_REC, B_REC    the image directories the G9 tool and the build table read: fuzz_disco (= the pin) and its twin
#                   fuzz_disco.debug (ec656cf105cb... / 65947ff283f5...), and fuzz_disco.nm.txt (step gxamem_nm)
#   R_PIN    the stripped fuzz_reply asan image, named fuzz_reply (42c58610e125...)
#   R_REC    the directory of fuzz_reply.debug (d751b179ea49...) and fuzz_reply.nm.txt
#   G9_RECORDS  (records, gates) the G9 record directory: P0/, P2/, tool/OLD-VS-FIXED.tsv, route_table.tsv
#   REC_AUDIT, REC_P3, REC_MOVES, REC_MEMSET_A, REC_TABLE_A, REC_TWINS_B: (gates) the directories of the numeral
#            audit output (audit.json), the record re-check output (recheck.out), the walk move record
#            (numeral-moves.tsv), the image-A memset walk checker outputs, the A table checker outputs, the image-B
#            checker outputs; REC_INVENTORY_B: (gates) the image-B inventory note, a file
#   JOBS     (g9) parallel assemble runs, default 4; PREDICT_JOBS: parallel checker runs, default 12
# pyelftools 0.33 and capstone 5 must be importable. File names of twins and pins are part of the outputs.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
: "${HUB:?}" "${OUT:?}"
mkdir -p "$OUT"
export PYTHONDONTWRITEBYTECODE=1 PYTHONHASHSEED=0
SHIPPED=b25fd6d02e9                     # the tree compared with: the series head (PR 413, the YH03 fix, the post-ship
                                        # changes, among them the clean-room restatement 52c05855c1ae of I_strchrw.v)
TOOL_TREE=b1afc3e80791                  # the tree as PR 413 and the YH03 fix shipped it: line 1 of every file the G9
                                        # tool wrote names its job there
UNIT=proofs/libreac/fuzz_disco
same() { cmp "$1" "$2" && echo "cmp equal: ${2#"$HERE"/}"; }
same_shipped() { git -C "$HUB" show "$SHIPPED:$2" > "$OUT/shipped.tmp"; cmp "$1" "$OUT/shipped.tmp"; }

# The comparison kits (check tools, cited, not copied): 86da41d3ef68, the kit of record (commit 98e50c029045,
# tools/cmpkit/86da41d3ef68/), and 4bbd3a74be89, which it supersedes (commit 3c3e62ee278, tools/cmpkit/4bbd3a74be89/).
kit() { # DIR COMMIT ID
	if [ ! -f "$OUT/$1/SHA256SUMS" ]; then
		mkdir -p "$OUT/$1"
		git -C "$HUB" archive "$2" "tools/cmpkit/$3" | tar -x -C "$OUT/$1" --strip-components=3
	fi
	(cd "$OUT/$1" && sha256sum --quiet -c SHA256SUMS)
	[ "$(sha256sum "$OUT/$1/SHA256SUMS" | cut -c1-12)" = "$3" ]
}
cmpkit() { kit cmpkit 3c3e62ee278 4bbd3a74be89 && kit cmpkit3 98e50c029045 86da41d3ef68; }

# The address checker kit 0767e70e074a, a producing input of the G9 tool (cited, not copied): commit 088272ccecac,
# directory tools/<checker>/0767e70e074a/ (port_addr_check.py, scan_literals.py, insn-targets/insn_targets.py).
pac() {
	if [ ! -f "$OUT/pac/port_addr_check.py" ]; then
		mkdir -p "$OUT/pac"
		git -C "$HUB" archive 088272ccecac ':(glob)tools/*/0767e70e074a/**' | tar -x -C "$OUT/pac" --strip-components=3
	fi
	[ "$(sha256sum "$OUT/pac/port_addr_check.py" | cut -c1-64)" = \
		0767e70e074a7c95a7c42753b3c1232c8126b39a96c8b40081157c58a07e9f1a ]
}

step_g9() {
	: "${FM_TWIN:?}" "${FM_PIN:?}" "${A_REC:?}" "${B_REC:?}"
	pac
	# the fm branch name line 1 writes, read from a shipped file (it is a label; no file here names it)
	FM_BRANCH=$(git -C "$HUB" show "$SHIPPED:$UNIT/lib/A/FMgxaSeam.v" | sed -n '1s/^(\* Copied from [^ ]* (\([^ ]*\) .*/\1/p')
	export FM_BRANCH PAC_DIR="$OUT/pac" FM_IMAGE="$FM_PIN" FM_DEBUG="$FM_TWIN" P0_NUMERALS="$HERE/g9tool/p0-numerals.tsv" \
		A_IMAGE="$A_REC/fuzz_disco" A_DEBUG="$A_REC/fuzz_disco.debug" Y_IMAGE="$B_REC/fuzz_disco" \
		Y_DEBUG="$B_REC/fuzz_disco.debug"
	python3 "$HERE/g9tool/run_g9.py" "$SHIPPED" "$OUT/g9" --jobs-ref "$TOOL_TREE" --clean-room 52c05855c1ae \
		--jobs "${JOBS:-4}"
	same "$OUT/g9/g9-rerun.tsv" "$HERE/g9tool/g9-rerun.tsv"
	same "$OUT/g9/g9-table-disco-A.tsv" "$HERE/g9tool/g9-table-disco-A.tsv"
	same "$OUT/g9/g9-table-disco-Y.tsv" "$HERE/g9tool/g9-table-disco-Y.tsv"
	local n=0 path by
	while IFS=$'\t' read -r path _ _ _ _ _ _ by _; do
		case "$by" in fixed | first) same_shipped "$OUT/g9/v/$by/$path" "$path"; n=$((n + 1)) ;; esac
	done < <(tail -n +2 "$OUT/g9/g9-rerun.tsv")
	echo "cmp equal: $n shipped files re-made byte for byte (g9tool/g9-rerun.tsv, column 'reproduced by')"
	python3 "$HERE/g9tool/validate.py" --routes "$HERE/g9tool/route-classes.tsv" --out-dir "$OUT/validate" \
		--wt "$OUT/g9/wt" > "$OUT/validate.log"
	same "$OUT/validate/disco-A.tsv" "$HERE/g9tool/validate-disco-A.tsv"
	same "$OUT/validate/disco-Y.tsv" "$HERE/g9tool/validate-disco-Y.tsv"
}

step_twins() {
	: "${FM_TWIN:?}" "${FM_PIN:?}" "${A_REC:?}" "${B_REC:?}" "${A_PIN:?}" "${B_PIN:?}"
	python3 "$HERE/extract/twin_facts.py" "$HERE/g9tool/g9-table-disco-A.tsv" "$FM_TWIN" "$FM_PIN" \
		"$A_REC/fuzz_disco.debug" "$A_PIN" > "$OUT/twin-facts-A.tsv"
	same "$OUT/twin-facts-A.tsv" "$HERE/g9tool/twin-facts-A.tsv"
	python3 "$HERE/extract/twin_facts.py" "$HERE/g9tool/g9-table-disco-Y.tsv" "$FM_TWIN" "$FM_PIN" \
		"$B_REC/fuzz_disco.debug" "$B_PIN" > "$OUT/twin-facts-B.tsv"
	same "$OUT/twin-facts-B.tsv" "$HERE/g9tool/twin-facts-B.tsv"
}

step_gxamem() {
	: "${R_PIN:?}" "${A_PIN:?}" "${B_PIN:?}"
	mkdir -p "$OUT/gxamem"
	python3 "$HERE/gxamem/gen_tbl.py" A "$HUB" 8816cefba36 86b50358d34 "$R_PIN" "$HERE/gxamem/nm-reply.txt" \
		"$A_PIN" "$HERE/gxamem/nm-A.txt" "$OUT/gxamem/A-RT_gxa_mem_Tbl.v"
	same_shipped "$OUT/gxamem/A-RT_gxa_mem_Tbl.v" "$UNIT/lib/A/RT_gxa_mem_Tbl.v"
	echo "cmp equal: $UNIT/lib/A/RT_gxa_mem_Tbl.v"
	python3 "$HERE/gxamem/gen_tbl.py" B "$HUB" 79bf1bd8f6d 86b50358d34 "$R_PIN" "$HERE/gxamem/nm-reply.txt" \
		"$B_PIN" "$HERE/gxamem/nm-B.txt" "$OUT/gxamem/B-RT_gxa_mem_Tbl.v"
	same_shipped "$OUT/gxamem/B-RT_gxa_mem_Tbl.v" "$UNIT/lib/B/RT_gxa_mem_Tbl.v"
	echo "cmp equal: $UNIT/lib/B/RT_gxa_mem_Tbl.v"
}

step_gxamem_nm() {
	: "${R_PIN:?}" "${A_PIN:?}" "${B_PIN:?}" "${R_REC:?}" "${A_REC:?}" "${B_REC:?}"
	mkdir -p "$OUT/gxamem"
	python3 "$HERE/gxamem/nm_extract.py" reply "$R_REC/fuzz_reply.nm.txt" "$R_REC/fuzz_reply.debug" "$R_PIN" \
		> "$OUT/gxamem/nm-reply.txt"
	same "$OUT/gxamem/nm-reply.txt" "$HERE/gxamem/nm-reply.txt"
	python3 "$HERE/gxamem/nm_extract.py" disco "$A_REC/fuzz_disco.nm.txt" "$A_REC/fuzz_disco.debug" "$A_PIN" \
		> "$OUT/gxamem/nm-A.txt"
	same "$OUT/gxamem/nm-A.txt" "$HERE/gxamem/nm-A.txt"
	python3 "$HERE/gxamem/nm_extract.py" disco "$B_REC/fuzz_disco.nm.txt" "$B_REC/fuzz_disco.debug" "$B_PIN" \
		> "$OUT/gxamem/nm-B.txt"
	same "$OUT/gxamem/nm-B.txt" "$HERE/gxamem/nm-B.txt"
}

step_records() {
	: "${G9_RECORDS:?}"
	python3 "$HERE/extract/records.py" codeid-pairs "$G9_RECORDS/P0/codeid-A.tsv" "$G9_RECORDS/P0/codeid-Y.tsv" \
		> "$OUT/pairs.tsv"
	same "$OUT/pairs.tsv" "$HERE/codeid/pairs.tsv"
	python3 "$HERE/extract/records.py" p0-numerals "$G9_RECORDS/P0/numerals.tsv" > "$OUT/p0-numerals.tsv"
	same "$OUT/p0-numerals.tsv" "$HERE/g9tool/p0-numerals.tsv"
	python3 "$HERE/extract/records.py" route-classes "$G9_RECORDS/route_table.tsv" > "$OUT/route-classes.tsv"
	same "$OUT/route-classes.tsv" "$HERE/g9tool/route-classes.tsv"
}

step_codeid() {
	: "${FM_TWIN:?}" "${FM_PIN:?}" "${A_TWIN:?}" "${A_PIN:?}" "${B_TWIN:?}" "${B_PIN:?}"
	cmpkit
	local M=("$HERE/codeid/printf_core-0x890.tsv" "$HERE/codeid/lui-printf_core-0x84.tsv" "$HERE/codeid/lui-fmt_fp-0x670.tsv")
	python3 "$HERE/codeid/symcount.py" "$HERE/codeid/pairs.tsv" "$FM_TWIN" A="$A_TWIN" B="$B_TWIN" > "$OUT/symcount.tsv"
	same "$OUT/symcount.tsv" "$HERE/codeid/symcount.tsv"
	python3 "$HERE/codeid/regdef.py" "$OUT/cmpkit" printf_core 0x890 x11 --table 0x534:56 --table 0x6ac:8 \
		fm="$FM_TWIN" A="$A_TWIN" B="$B_TWIN" > "$OUT/printf_core-0x890.tsv"
	same "$OUT/printf_core-0x890.tsv" "$HERE/codeid/printf_core-0x890.tsv"
	python3 "$HERE/codeid/luiuse.py" "$OUT/cmpkit3" printf_core 0x84 --table 0x534:56 --table 0x6ac:8 \
		--callees "$HERE/codeid/callee-args.tsv" fm="$FM_TWIN" A="$A_TWIN" B="$B_TWIN" > "$OUT/lui-printf_core-0x84.tsv"
	same "$OUT/lui-printf_core-0x84.tsv" "$HERE/codeid/lui-printf_core-0x84.tsv"
	python3 "$HERE/codeid/luiuse.py" "$OUT/cmpkit3" fmt_fp 0x670 --callees "$HERE/codeid/callee-args.tsv" \
		--bias 0x6a0:0x664:0x664,0x670,0x678,0x67c,0x684,0x6a0,0x6b4,0xa8c,0xa90,0xab4,0xabc,0xaf4,0xafc,0xb04,0xddc,0xe14,0xe18,0xe1c \
		fm="$FM_TWIN" A="$A_TWIN" B="$B_TWIN" > "$OUT/lui-fmt_fp-0x670.tsv"
	same "$OUT/lui-fmt_fp-0x670.tsv" "$HERE/codeid/lui-fmt_fp-0x670.tsv"
	python3 "$HERE/codeid/scans.py" luiscan "$OUT/cmpkit3" "$HERE/codeid/pairs.tsv" "$OUT/luiscan.tsv" \
		fm="$FM_TWIN" A="$A_TWIN" B="$B_TWIN"
	same "$OUT/luiscan.tsv" "$HERE/codeid/luiscan.tsv"
	python3 "$HERE/codeid/addrsite.py" "$OUT/cmpkit3" "$HERE/codeid/pairs.tsv" --table printf_core:0x534:56 \
		--table printf_core:0x6ac:8 --table pop_arg:0x14:18 fm="$FM_TWIN" A="$A_TWIN" B="$B_TWIN" > "$OUT/addrsite.tsv"
	same "$OUT/addrsite.tsv" "$HERE/codeid/addrsite.tsv"
	python3 "$HERE/codeid/codeid_kit.py" "$OUT/cmpkit" "$OUT/cmpkit3" "$HERE/codeid/pairs.tsv" "$FM_TWIN" "$FM_PIN" \
		"${M[@]/#/--measure=}" --review "$HERE/codeid/review.tsv" --review "$HERE/codeid/review2.tsv" \
		--review "$HERE/codeid/review3.tsv" --luiscan "$HERE/codeid/luiscan.tsv" \
		--addrsite "$HERE/codeid/addrsite.tsv" --trace "$HERE/codeid/addrsite-trace.tsv" \
		A="$A_TWIN:$A_PIN" B="$B_TWIN:$B_PIN" > "$OUT/codeid-kit.tsv"
	same "$OUT/codeid-kit.tsv" "$HERE/codeid/codeid-kit.tsv"
	mkdir -p "$OUT/scans"
	python3 "$HERE/codeid/scans.py" ambiscan "$OUT/cmpkit3" "$HERE/codeid/codeid-kit.tsv" "$OUT/scans" "${M[@]}" -- \
		fm="$FM_TWIN" A="$A_TWIN" B="$B_TWIN"
	for f in lookups.tsv ambiscan-A.tsv ambiscan-B.tsv; do same "$OUT/scans/$f" "$HERE/codeid/$f"; done
}

# The gate records of the hand-relocated files: clean tables extracted from the host records (extract/gates.py).
gate_table() { # TABLE SUBCOMMAND RECORD...: extract/gates.py SUBCOMMAND RECORD... must re-make gates/TABLE
	local t=$1
	shift
	python3 "$HERE/extract/gates.py" "$@" > "$OUT/$t"
	same "$OUT/$t" "$HERE/gates/$t"
}
step_gates() {
	: "${G9_RECORDS:?}" "${REC_AUDIT:?}" "${REC_P3:?}" "${REC_MOVES:?}" "${REC_MEMSET_A:?}" "${REC_TABLE_A:?}" \
		"${REC_TWINS_B:?}" "${REC_INVENTORY_B:?}"
	gate_table numeral-audit.tsv numeral-audit "$REC_AUDIT/audit.json"
	gate_table numerals-rest.tsv numerals-rest "$G9_RECORDS/P0/numerals-rest.md"
	gate_table call-sites.tsv call-sites "$G9_RECORDS/P2/site-check.md" "$G9_RECORDS/P2/recheck-A.md" \
		"$G9_RECORDS/P2/recheck-Y.md"
	gate_table record-rows.tsv record-rows "$REC_P3/recheck.out"
	gate_table old-vs-fixed.tsv old-vs-fixed "$G9_RECORDS/tool/OLD-VS-FIXED.tsv"
	gate_table alreloc-moves.tsv alreloc-moves "$REC_MOVES/numeral-moves.tsv"
	gate_table addrcheck-A.tsv addrcheck-A "$REC_MEMSET_A" "$REC_TABLE_A"
	gate_table addrcheck-B.tsv addrcheck-B "$REC_TWINS_B"
	gate_table inventory-B.tsv inventory-B "$REC_INVENTORY_B"
}

# The address checker records (gates/addrcheck-A.tsv, addrcheck-B.tsv) re-made by the checker itself from the
# committed source and ported files and the images. The checker kit 16f8a030c869 is a check tool, cited, not copied:
# it is taken from commit 088272ccecac by its id, and addrcheck.py checks its files' sha256.
step_addrcheck() {
	: "${R_PIN:?}" "${R_REC:?}" "${A_PIN:?}" "${A_TWIN:?}" "${B_PIN:?}" "${B_TWIN:?}"
	if [ ! -d "$OUT/addrkit" ]; then
		mkdir -p "$OUT/addrkit"
		git -C "$HUB" archive 088272ccecac ':(glob)tools/*/16f8a030c869/**' | tar -x -C "$OUT/addrkit"
	fi
	python3 "$HERE/gates/addrcheck.py" "$(echo "$OUT"/addrkit/tools/*/16f8a030c869)" "$HUB" "$OUT/addrcheck" \
		R="$R_PIN:$R_REC/fuzz_reply.debug" A="$A_PIN:$A_TWIN" B="$B_PIN:$B_TWIN"
	python3 "$HERE/extract/gates.py" addrcheck-A "$OUT/addrcheck" "$OUT/addrcheck" > "$OUT/addrcheck-A.rerun.tsv"
	same "$OUT/addrcheck-A.rerun.tsv" "$HERE/gates/addrcheck-A.tsv"
	python3 "$HERE/extract/gates.py" addrcheck-B "$OUT/addrcheck" > "$OUT/addrcheck-B.rerun.tsv"
	same "$OUT/addrcheck-B.rerun.tsv" "$HERE/gates/addrcheck-B.tsv"
}

[ $# -gt 0 ] || { echo "usage: run.sh g9|twins|gxamem|addrcheck|codeid|records|gxamem_nm|gates|all ..." >&2; exit 2; }
for s in "$@"; do
	case "$s" in
		all) step_g9; step_twins; step_gxamem; step_addrcheck; step_codeid ;;
		g9 | twins | gxamem | addrcheck | codeid | records | gxamem_nm | gates) "step_$s" ;;
		*) echo "run.sh: unknown step $s" >&2; exit 2 ;;
	esac
done
