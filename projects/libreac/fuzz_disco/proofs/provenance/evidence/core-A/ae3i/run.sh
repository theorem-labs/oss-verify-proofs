#!/usr/bin/env bash
# run.sh REPO PIN_A OUTDIR -- re-derive lib/A/AE3i.v of libreac/fuzz_disco with ae3i.py and compare it with the
# shipped file. Exit status 0 only when every comparison matches.
#   REPO    root of a checkout that holds proofs/libreac/fuzz_disco
#   PIN_A   image A, the released fuzz_disco.asan (sha256 5e39150dd8104df9...)
#   OUTDIR  directory for the outputs (created when absent)
# Environment: PYTHON (default python3), with pyelftools.
#
# Run 1: template = the shipped AE3i.v. Run 2: template = the shipped AE3i.v with IMG_RO_LO, IMG_RO_HI set to 0x0
# and img_ro_chunks set to [ ], so that every derived number comes from the image and lib/A/AF0m.v only.
set -u
export PYTHONDONTWRITEBYTECODE=1
[ $# -eq 3 ] || { echo "usage: $0 REPO PIN_A OUTDIR" >&2; exit 2; }
HERE=$(cd "$(dirname "$0")" && pwd)
U="$1/proofs/libreac/fuzz_disco"
PIN=$2
OUT=$3
PY=${PYTHON:-python3}
SHIP="$U/lib/A/AE3i.v"
mkdir -p "$OUT" || exit 2
fail=0
same() { if cmp "$1" "$2"; then echo "cmp OK   $3"; else echo "cmp FAIL $3"; fail=1; fi; }

echo "image A sha256 $(sha256sum < "$PIN" | cut -d' ' -f1)"
echo "lib/A/AE3i.v sha256 $(sha256sum < "$SHIP" | cut -d' ' -f1)"
echo "lib/A/AF0m.v sha256 $(sha256sum < "$U/lib/A/AF0m.v" | cut -d' ' -f1)"

"$PY" "$HERE/ae3i.py" --tmpl "$SHIP" --owned "$U/lib/A/AF0m.v" --image "$PIN" --out "$OUT/AE3i.v" || fail=1
same "$OUT/AE3i.v" "$SHIP" "AE3i.v (run 1, shipped template) = lib/A/AE3i.v"

"$PY" - "$SHIP" "$OUT/AE3i.blank.v" <<'EOF' || fail=1
import re, sys
t = open(sys.argv[1]).read()
t, n1 = re.subn(r'(Definition IMG_RO_(?:LO|HI) : Z := )0x[0-9a-f]+\.', r'\g<1>0x0.', t)
t, n2 = re.subn(r'(Definition img_ro_chunks : list YP09\.chunk :=\n)\[.*?\]\.', r'\1[ ].', t, flags=re.S)
if (n1, n2) != (2, 1) or 'mkChunk' in t:
    sys.exit('run.sh: template blanking replaced %d IMG_RO values and %d chunk lists' % (n1, n2))
open(sys.argv[2], 'w').write(t)
EOF
if cmp -s "$OUT/AE3i.blank.v" "$SHIP"; then echo "FAIL blank template equals the shipped file"; fail=1; fi
"$PY" "$HERE/ae3i.py" --tmpl "$OUT/AE3i.blank.v" --owned "$U/lib/A/AF0m.v" --image "$PIN" --out "$OUT/AE3i.from-blank.v" || fail=1
same "$OUT/AE3i.from-blank.v" "$SHIP" "AE3i.v (run 2, template without IMG_RO_LO/HI or chunks) = lib/A/AE3i.v"

[ $fail -eq 0 ] && echo "ae3i: ALL MATCH" || echo "ae3i: FAILED"
exit $fail
