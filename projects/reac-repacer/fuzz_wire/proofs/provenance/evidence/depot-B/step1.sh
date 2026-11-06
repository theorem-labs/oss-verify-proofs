set -euo pipefail
usage='step1.sh <out dir, must not exist> [extra port_core args]   env: UNIT HUB TREE A_CORE REL P R [FILES1 (default knockB-files.txt here)]'
OUT=${1:?$usage}; shift
HERE=$(cd "$(dirname "$0")" && pwd)
: "${UNIT:?$usage}" "${HUB:?$usage}" "${TREE:?$usage}" "${A_CORE:?$usage}" "${REL:?$usage}" "${P:?$usage}" "${R:?$usage}"
FILES1=${FILES1:-$HERE/knockB-files.txt}
[ ! -e "$OUT" ] || { echo "step1: $OUT exists" >&2; exit 2; }
mkdir -p "$OUT/tgt"
HUB="$HUB" bash "$HERE/../core-B/mkdon.sh" 88154566652a fuzz_knock AU "$OUT/donB-knock"
. "$HERE/unit_root.sh"
RT=$(unit_root "$TREE"); RA=$(unit_root "$A_CORE")
git -C "$HUB" archive "$TREE" "$RT/lib" | tar -x -C "$OUT/tgt"
L=$OUT/tgt/$RT/lib
# the image-A core's lib/Reusable laid over the target's, whatever layout each commit has
mkdir -p "$OUT/a-core" "$L/Reusable"
git -C "$HUB" archive "$A_CORE" "$RA/lib/Reusable" | tar -x -C "$OUT/a-core"
cp -a "$OUT/a-core/$RA/lib/Reusable/." "$L/Reusable/"
rm -rf "$OUT/a-core"
n=0
while read -r f; do
  if [ -e "$L/B/$f" ]; then rm "$L/B/$f"; n=$((n + 1)); fi
done < "$FILES1"
echo "step1: target lib = $TREE lib + $A_CORE lib/Reusable; $n replaced lib/B files removed; lib/B $(ls "$L/B" | wc -l) files, lib/Reusable $(ls "$L/Reusable" | wc -l)"
set +e
S="$OUT" REL="$REL" P="$P" R="$R" bash "$HERE/run-knockB.sh" "$UNIT" "$L" "$OUT/work" "$FILES1" "$@"
echo "step1: port_core rc=$?"
