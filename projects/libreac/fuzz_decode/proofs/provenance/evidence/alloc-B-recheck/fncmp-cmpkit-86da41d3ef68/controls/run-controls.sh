#!/bin/bash
# controls/run-controls.sh -- runs the kit 86da41d3ef68's own controls as its README ("CONTROLS (controls/)") prescribes, and
# compares them with the outputs the kit registered (controls/compare.py). usage: run-controls.sh RUN_DIR REG_RUN_ROOT
#   RUN_DIR       an empty directory: the kit copies, the planted copies and the outputs go there
#   REG_RUN_ROOT  the directory of the kit's registered run (the prefix of the paths in its controls/ outputs)
set -euo pipefail
[ $# -eq 2 ] || { sed -n '2,6p' "$0"; exit 2; }
export PYTHONDONTWRITEBYTECODE=1
HUB="${HUB:-$(git rev-parse --show-toplevel)}"
C="$(cd "$1" && pwd)"; HERE="$(cd "$(dirname "$0")" && pwd)"
mkdir -p "$C/kitrun" "$C/oldkit" "$C/xchk"
git -C "$HUB" archive 98e50c029045 tools/cmpkit/86da41d3ef68 | tar -x -C "$C/kitrun" --strip-components=3
git -C "$HUB" archive 3c3e62ee278 tools/cmpkit/4bbd3a74be89 | tar -x -C "$C/oldkit" --strip-components=3
(cd "$C/kitrun" && sha256sum -c SHA256SUMS) && (cd "$C/oldkit" && sha256sum -c SHA256SUMS)
cp -a "$C/oldkit/." "$C/xchk/" && cp "$C/kitrun/controls/xchk/jtcheck_strict2.py" "$C/xchk/"   # the cross-check jtcheck
(cd "$C" && python3 kitrun/controls/negctl.py kitrun > negctl.out)
(cd "$C" && SUITE_OLD_KIT="$C/oldkit" SUITE_XCHK_JT="$C/xchk/jtcheck_strict2.py" \
    python3 kitrun/controls/suite.py "$C/kitrun" "$C/suite-out" "$C/planted" 16)
python3 "$HERE/compare.py" "$C" "$2" > "$C/compare.out"
cat "$C/compare.out"
