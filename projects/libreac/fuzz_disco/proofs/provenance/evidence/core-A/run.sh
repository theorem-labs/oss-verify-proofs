#!/usr/bin/env bash
# run.sh REPO A_PIN B_PIN DONOR_PIN DONOR_B_PIN GATE_SCRIPT GATE_DONORS GATE_CACHE A_TWIN D9E0_DIR OUTDIR -- re-runs
# every script of record in this directory and compares each output with the shipped file or table; exits 0 only if
# every part reports all equal.
#   REPO         a git checkout of the repository at the commit that holds this directory (with
#                proofs/libreac/fuzz_disco and proofs/cgif/cgif_file_fuzzer/lib)
#   A_PIN        the released fuzz_disco.asan            (projects/libreac/fuzz_disco/harness.yaml, asan)
#   B_PIN        the released fuzz_disco.asan-ubsan      (same file, asan-ubsan)
#   DONOR_PIN    the released cgif_file_fuzzer.asan      (projects/cgif/cgif_file_fuzzer/harness.yaml, asan)
#   DONOR_B_PIN  the released cgif_file_fuzzer.asan-ubsan (same file, asan-ubsan)
#   GATE_SCRIPT  port_addr_check.py of the address checker tag 5033540ba83b (a frozen check tool, not copied here)
#   GATE_DONORS  that checker's --donors-from directory
#   GATE_CACHE   that checker's directory of saved symbol recoveries (<image sha16>.<donors sha16>.v*.json)
#   A_TWIN       the unstripped twin of A_PIN (sha256 b8aac6eee6a6..., the twin of twin/fuzz_disco.asan.twin.txt)
#   D9E0_DIR     the port_core tag directory d9e0589898fd (a check tool here, not copied: d9e0check/run.sh)
#   OUTDIR       an empty directory for the outputs
# Needs python3 with pyelftools and capstone.
set -u
export PYTHONDONTWRITEBYTECODE=1
[ $# -eq 11 ] || { echo "usage: run.sh REPO A_PIN B_PIN DONOR_PIN DONOR_B_PIN GATE_SCRIPT GATE_DONORS GATE_CACHE A_TWIN D9E0_DIR OUTDIR" >&2; exit 2; }
REPO=$1 A_PIN=$2 B_PIN=$3 DONOR_PIN=$4 DONOR_B_PIN=$5 GATE_SCRIPT=$6 GATE_DONORS=$7 GATE_CACHE=$8 A_TWIN=$9
D9E0_DIR=${10} OUT=${11}
HERE=$(cd "$(dirname "$0")" && pwd)
mkdir -p "$OUT"
rc=0
part() {
	local name=$1; shift
	echo "== $name"
	bash "$HERE/$name/run.sh" "$@" || { echo "== $name: FAILED"; rc=1; }
}
part ab1w "$REPO" "$A_PIN" "$DONOR_PIN" "$OUT/ab1w"
part ae3i "$REPO" "$A_PIN" "$OUT/ae3i"
part af0m "$REPO" "$A_PIN" "$OUT/af0m"
part memwalks13 "$REPO" "$A_PIN" "$B_PIN" "$DONOR_PIN" "$DONOR_B_PIN" "$GATE_SCRIPT" "$GATE_DONORS" "$GATE_CACHE" "$OUT/memwalks13"
part d9e0check "$REPO" "$A_PIN" "$B_PIN" "$DONOR_PIN" "$DONOR_B_PIN" "$A_TWIN" "$D9E0_DIR" "$GATE_DONORS" "$GATE_CACHE" \
	"$OUT/memwalks13" "$OUT/d9e0check"
echo "core-A run.sh exit $rc"
exit $rc
