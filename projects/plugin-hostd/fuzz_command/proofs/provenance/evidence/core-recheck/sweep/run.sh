#!/usr/bin/env bash
# Symbol + offset sweep (sweep.py) over the value-gate runs and the planted controls, then triage (triage.py).
# RUNS = dir of the port_addr_check 3d2eee813cce runs (RA RB RU PA-* PB-*), RT = the Rt / Reusable runs dir,
# IMG = cgif.{A,B}.{pin,twin} cmd.{A,B}.{pin,twin}, PIMG = the plain build's images cgif.P.* cmd.P.*,
# RTIMG = the Rt runs' other donor images (disco.A, grant.A, preset.A).
set -eu
cd "$(dirname "$0")"
RUNS=${RUNS:-$W/runs}
RT=${RT:-$W/rt-reusable/runs}
IMG=${IMG:-$W/img}
PIMG=${PIMG:-work/img}
RTIMG=${RTIMG:-$W/rt-reusable/work/img}
A="$IMG/cgif.A.pin $IMG/cgif.A.twin $IMG/cmd.A.pin $IMG/cmd.A.twin"
B="$IMG/cgif.B.pin $IMG/cgif.B.twin $IMG/cmd.B.pin $IMG/cmd.B.twin"
P="$PIMG/cgif.P.pin $PIMG/cgif.P.twin $PIMG/cmd.P.pin $PIMG/cmd.P.twin"
CA="$IMG/cmd.A.pin $IMG/cmd.A.twin"
CB="$IMG/cmd.B.pin $IMG/cmd.B.twin"
mkdir -p work/ctl
# the runs of record
args=(--run RA $RUNS/RA/full.tsv $A --run RB $RUNS/RB/full.tsv $B --run RU $RUNS/RU/full.tsv $B)
[ -f $RT/RtCgifA/full.tsv ] && args+=(--run RtCgifA $RT/RtCgifA/full.tsv $A)
[ -f $RT/RtCgifB/full.tsv ] && args+=(--run RtCgifB $RT/RtCgifB/full.tsv $B)
[ -f $RT/RtDisco/full.tsv ] && args+=(--run RtDisco $RT/RtDisco/full.tsv $RTIMG/disco.A.pin $RTIMG/disco.A.twin $CA)
[ -f $RT/RtGrant/full.tsv ] && args+=(--run RtGrant $RT/RtGrant/full.tsv $RTIMG/grant.A.pin $RTIMG/grant.A.twin $CA)
[ -f $RT/RtPreset/full.tsv ] && args+=(--run RtPreset $RT/RtPreset/full.tsv $RTIMG/presetR.A.pin $RTIMG/presetR.A.twin $CA)
[ -f $RT/RtRelay/full.tsv ] && args+=(--run RtRelay $RT/RtRelay/full.tsv $CA $CB)
[ -f $RT/RUP/full.tsv ] && args+=(--run RUP $RT/RUP/full.tsv $P)
python3 sweep.py --out . "${args[@]}"
# the RU pairs resolved in the plain build's images (a measurement for RU's triage; lib/Reusable's pre-port files
# describe the plain build)
python3 sweep.py --out work --rows rows.RU-P.tsv --reresolve RU-P $RUNS/RU/full.tsv $P
# controls: the planted copies and their bases
python3 sweep.py --out work/ctl --run PA-base $RUNS/PA-base/full.tsv $A --run PA-plant $RUNS/PA-plant/full.tsv $A \
  --run PB-base $RUNS/PB-base/full.tsv $B --run PB-plant $RUNS/PB-plant/full.tsv $B
