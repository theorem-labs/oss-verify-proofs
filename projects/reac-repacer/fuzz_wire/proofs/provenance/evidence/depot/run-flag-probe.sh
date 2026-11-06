#!/bin/bash
# run-flag-probe.sh BUILT PROBES -- compile every PROBES/P*.v (flag_probe.py make) against BUILT, the _build/default
# directory of a dune build of the tree under test, inside the unit's checker image, 24 at a time; writes
# PROBES/P<F>.out with the compile output and a last line rc=N. Run on the build VM.
# CHECKER_IMAGE (required): the checker image the unit's build pins, given by its local reference; the run refuses
# unless that image's digest is sha256:cc9ae43a9f4b0dd59d7c8d30727d36e039bfe72a2a9f9c4a99c68e413037e902.
# The unit's paths default to reac-repacer/fuzz_wire; for fuzz_grant's release tree set
# PROJ=projects/libreac/fuzz_grant PROJ_NS=OssFuzzTheorems.libreac.fuzz_grant
# LIB=proofs/libreac/fuzz_grant/lib LIB_NS=OssFuzzTheorems.Proofs.libreac.fuzz_grant.lib
set -uo pipefail
BUILT=${1:?usage: run-flag-probe.sh BUILT PROBES}
PROBES=${2:?usage: run-flag-probe.sh BUILT PROBES}
PROJ=${PROJ:-projects/reac-repacer/fuzz_wire}; PROJ_NS=${PROJ_NS:-OssFuzzTheorems.reac_repacer.fuzz_wire}
LIB=${LIB:-projects/reac-repacer/fuzz_wire/proofs/lib}; LIB_NS=${LIB_NS:-OssFuzzTheorems.Proofs.reac_repacer.fuzz_wire.lib}
PTIMEOUT=${PTIMEOUT:-300}  # seconds per probe compile; `after` probes compile whole files: give them more
PIN=sha256:cc9ae43a9f4b0dd59d7c8d30727d36e039bfe72a2a9f9c4a99c68e413037e902
img=${CHECKER_IMAGE:?set CHECKER_IMAGE to the checker image (digest $PIN)}
[ "${img##*@}" = "$PIN" ] || { echo "run-flag-probe: CHECKER_IMAGE is not the pinned digest $PIN" >&2; exit 2; }
docker run --rm --network none -u "$(id -u):$(id -g)" -e HOME=/tmp -e PROJ="$PROJ" -e PROJ_NS="$PROJ_NS" -e LIB="$LIB" \
  -e LIB_NS="$LIB_NS" -e PTIMEOUT="$PTIMEOUT" -v "$BUILT:/ws" -v "$PROBES:/fx" -w /ws "$img" bash -c '
ulimit -s "$(ulimit -Hs)"
ls /fx/P*.v | xargs -P 24 -I{} sh -c '"'"'b=$(basename {} .v); timeout "$PTIMEOUT" rocq compile -Q theories OssFuzzTheorems.Core \
  -Q "$PROJ" "$PROJ_NS" -Q "$LIB" "$LIB_NS" -R /fx Fx \
  -o /fx/$b.vo {} > /fx/$b.out 2>&1; echo rc=$? >> /fx/$b.out'"'"''
echo "run-flag-probe: $(ls "$PROBES"/P*.out | wc -l) probe(s) compiled"
