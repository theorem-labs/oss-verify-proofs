#!/bin/bash
# zify_flag_control.sh BUILT SRC FILE LIMIT -- the planted control of glue rules E6 / E7: compile lib file FILE (e.g. AFko.v)
# of the tree under test twice against BUILT (its dune _build/default): WITH its E6 / E7 line (SRC/A/FILE as laid)
# and WITHOUT it (the same text with only that line removed), each under `timeout LIMIT`; prints rc, wall time and
# the first error of each compile. Without the line the file must fail: hang (rc 124 at LIMIT) or break (rc 1).
# Run on the build VM. CHECKER_IMAGE (required): the checker image the unit's build pins, given by its local
# reference; the run refuses unless its digest is sha256:cc9ae43a9f4b0dd59d7c8d30727d36e039bfe72a2a9f9c4a99c68e413037e902.
set -uo pipefail
BUILT=${1:?usage: zify_flag_control.sh BUILT SRC FILE LIMIT}; SRC=${2:?}; F=${3:?}; LIMIT=${4:?}
E6='Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).'
E7='Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).'
T=$(mktemp -d); mkdir -p "$T/with" "$T/without"
cp "$SRC/A/$F" "$T/with/$F"
grep -vxF -e "$E6" -e "$E7" "$SRC/A/$F" > "$T/without/$F"
echo "zify_flag_control: $F with: $(grep -cxF -e "$E6" -e "$E7" "$T/with/$F") rule line(s) ($(grep -xF -e "$E6" -e "$E7" "$T/with/$F" | grep -o 'constr:([a-z]*)')); without: $(grep -cxF -e "$E6" -e "$E7" "$T/without/$F")"
PIN=sha256:cc9ae43a9f4b0dd59d7c8d30727d36e039bfe72a2a9f9c4a99c68e413037e902
img=${CHECKER_IMAGE:?set CHECKER_IMAGE to the checker image (digest $PIN)}
[ "${img##*@}" = "$PIN" ] || { echo "zify_flag_control: CHECKER_IMAGE is not the pinned digest $PIN" >&2; exit 2; }
for v in with without; do
  docker run --rm --network none -u "$(id -u):$(id -g)" -e HOME=/tmp -v "$BUILT:/ws" -v "$T/$v:/fx" -w /ws "$img" bash -c "
    ulimit -s \$(ulimit -Hs); s=\$(date +%s)
    timeout $LIMIT rocq compile -Q theories OssFuzzTheorems.Core -Q projects/reac-repacer/fuzz_wire OssFuzzTheorems.reac_repacer.fuzz_wire \
      -Q projects/reac-repacer/fuzz_wire/proofs/lib OssFuzzTheorems.Proofs.reac_repacer.fuzz_wire.lib -R /fx Fx -o /fx/${F%.v}.vo /fx/$F > /fx/log 2>&1
    r=\$?; e=\$(date +%s); err=\$(grep -v '^Warning\|^\[' /fx/log | grep -B1 -m1 '^Error' | tr '\n' ' ' | sed 's#/fx/##')
    echo \"zify_flag_control: $F $v: rc=\$r wall=\$((e - s)) s (limit $LIMIT s) \$err\""
done
rm -rf "$T"
