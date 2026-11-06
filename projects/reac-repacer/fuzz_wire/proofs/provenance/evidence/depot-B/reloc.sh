set -euo pipefail
usage='reloc.sh <step1 out dir> <run name> <file list> [extra port_core args]   env: UNIT REL P R [ADD_B: lib/B files the unit writes itself, laid into the target]'
S1=${1:?$usage} NAME=${2:?$usage} FILES=${3:?$usage}; shift 3
HERE=$(cd "$(dirname "$0")" && pwd)
: "${UNIT:?$usage}" "${REL:?$usage}" "${P:?$usage}" "${R:?$usage}"
[ ! -e "$S1/$NAME" ] || { echo "reloc: $S1/$NAME exists" >&2; exit 2; }
mkdir -p "$S1/$NAME"
cp -a "$S1/tgt" "$S1/$NAME/tgt"
. "$HERE/unit_root.sh"
L=$(tgt_lib "$S1/$NAME/tgt")
n=0
while read -r f; do
  if [ -e "$L/B/$f" ]; then rm "$L/B/$f"; n=$((n + 1)); fi
done < "$FILES"
for f in ${ADD_B:-}; do cp "$f" "$L/B/"; done
echo "reloc $NAME: target = step1's target lib with $n more lib/B files of $(basename "$FILES") removed; added: ${ADD_B:+$(for f in $ADD_B; do basename "$f"; done | tr '\n' ' ')}"
set +e
S="$S1" REL="$REL" P="$P" R="$R" bash "$HERE/run-knockB.sh" "$UNIT" "$L" "$S1/$NAME/work" "$FILES" "$@"
echo "reloc $NAME: port_core rc=$?"
