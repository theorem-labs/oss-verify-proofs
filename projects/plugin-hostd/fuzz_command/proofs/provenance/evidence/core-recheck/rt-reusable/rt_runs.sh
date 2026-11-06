#!/usr/bin/env bash
# Value-gate runs (port_addr_check 3d2eee813cce, through the shared wrapper pac.sh) for fuzz_command's runtime files
# lib/A/Rt and lib/B/Rt whose headers say they were copied / made / moved from a donor file.
# Each run pairs a local src dir (the donor files, renamed to our file names) with a local dst dir (our files).
# Usage: rt_runs.sh prep | run NAME | controls
#   ROOT   slice dir (default: the dir of this script)   GITDIR  git object store   OURS  our unit lib extract
#   CGIF   the donor cgif_file_fuzzer lib extract          IMG / WIMG  image dirs   PAC  the wrapper
set -u
ROOT=${ROOT:-$(cd "$(dirname "$0")" && pwd)}
GITDIR=${GITDIR:-$HUB}
OURS=${OURS:-$OURS/proofs/plugin-hostd/fuzz_command/lib}      # a3c671fb9bb
CGIF=${CGIF:-$DONOR/proofs/cgif/cgif_file_fuzzer/lib}          # c8557374ad2e
IMG=${IMG:-$W/img}                  # cgif.{A,B}.{pin,twin}, cmd.{A,B}.{pin,twin}
WIMG=${WIMG:-$ROOT/work/img}              # disco.A, grant.A, presetR.A (pin + .debug twin)
PAC=${PAC:-$RUN/pac.sh}
W=$ROOT/work/rt
DI=proofs/libreac/fuzz_disco/lib/A/Rt
GR=proofs/libreac/fuzz_grant/lib/A/Rt
PR=proofs/omx-clap-core/fuzz_preset/lib/A

# put DONOR (commit:path, or a local file) into run RUN's src dir as NAME, and our SIDE/Rt/NAME into its dst dir
pair() {
  local run=$1 side=$2 donor=$3 name=$4
  mkdir -p "$W/$run/src" "$W/$run/dst"
  case $donor in
    *:*) git -C "$GITDIR" show "$donor" > "$W/$run/src/$name" || { echo "MISSING $donor" >&2; exit 2; } ;;
    *) cp "$donor" "$W/$run/src/$name" ;;
  esac
  cp "$OURS/$side/Rt/$name" "$W/$run/dst/$name"
  printf '%s\t%s\t%s\t%s\t%s\n' "$run" "$name" "$donor" "$(sha256sum < "$W/$run/src/$name" | cut -c1-12)" \
    "$(sha256sum < "$W/$run/dst/$name" | cut -c1-12)" >> "$W/pairs.tsv"
}

prep() {
  rm -rf "$W"; mkdir -p "$W"
  printf 'run\tour_file\tdonor\tdonor_sha256\tour_sha256\n' > "$W/pairs.tsv"
  # libreac/fuzz_disco lib/A/Rt (the immediate donors: closest versions by find_donor.py) -> our lib/A/Rt
  pair RtDisco A 432691c31d8c:$DI/Strnlen.v Strnlen.v
  pair RtDisco A 432691c31d8c:$DI/StrnlenChk.v StrnlenChk.v
  pair RtDisco A 432691c31d8c:$DI/StrnlenMusl.v StrnlenMusl.v
  pair RtDisco A 60fe32c8748f:$DI/StackMalloc3.v RtSM3.v
  pair RtDisco A b5cf457a8820:$DI/StackMalloc3Tbl.v RtSM3T.v
  pair RtDisco A 3b8a77d146c9:$DI/Memchr.v Memchr.v
  pair RtDisco A 3b8a77d146c9:$DI/MemchrChk.v MemchrChk.v
  pair RtDisco A 3b8a77d146c9:$DI/MemchrMusl.v MemchrMusl.v
  # cgif_file_fuzzer lib/A files the headers name (c8557374ad2e) -> our lib/A/Rt
  pair RtCgifA A "$CGIF/A/AE7d.v" Strnlen.v
  pair RtCgifA A "$CGIF/A/AE7e.v" StrnlenChk.v
  pair RtCgifA A "$CGIF/A/AE7f.v" StrnlenMusl.v
  pair RtCgifA A "$CGIF/A/AE38.v" RtSIstrlen.v
  pair RtCgifA A "$CGIF/A/AFfm.v" RtSM7Fm.v
  pair RtCgifA A "$CGIF/A/AE37.v" RtDtorExit.v
  pair RtCgifA A "$CGIF/A/AE6y.v" MemchrChk.v
  pair RtCgifA A "$CGIF/YCbq.v" RtD04d.v
  pair RtCgifA A "$CGIF/YCbq.v" RtD04n.v
  # cgif_file_fuzzer root Y twins (the asan-ubsan side) -> our lib/B/Rt
  pair RtCgifB B "$CGIF/YE7d.v" Strnlen.v
  pair RtCgifB B "$CGIF/YE7e.v" StrnlenChk.v
  pair RtCgifB B "$CGIF/YE7f.v" StrnlenMusl.v
  pair RtCgifB B "$CGIF/YE38.v" RtSIstrlen.v
  pair RtCgifB B "$CGIF/YFfm.v" RtSM7Fm.v
  pair RtCgifB B "$CGIF/YE37.v" RtDtorExit.v
  pair RtCgifB B "$CGIF/YE6y.v" MemchrChk.v
  pair RtCgifB B "$CGIF/YCbq.v" RtD04d.v
  pair RtCgifB B "$CGIF/YCbq.v" RtD04n.v
  # libreac/fuzz_grant lib/A/Rt strcmp walk -> our lib/A/Rt
  pair RtGrant A 97c611eec863:$GR/Strcmp.v RtStrcmp.v
  pair RtGrant A 30068deaa798:$GR/StrcmpChkX.v RtStrcmpChkX.v
  pair RtGrant A f537c39a0cef:$GR/StrcmpChkY.v RtStrcmpChkY.v
  pair RtGrant A f029b31e1eef:$GR/StrcmpLoop.v RtStrcmpLoop.v
  # StrcmpTbl: the version that holds sc_rodata, as ours does (find_donor ranks d8af19ee248d 54 / 30068deaa798 57
  # changed lines; d8af19ee248d lacks the sentence sc_rodata our file carries)
  pair RtGrant A 30068deaa798:$GR/StrcmpTbl.v RtStrcmpTbl.v
  # omx-clap-core/fuzz_preset lib/A -> our lib/A/Rt
  pair RtPreset A b120217aa206:$PR/FCm3r.v RtSM5T.v
  pair RtPreset A 4cda83dac850:$PR/FCxA.v RtSMxA.v
  pair RtPreset A 08f989a6b54f:$PR/AE37.v RtDtorExit.v
  # the donor's generated image file (FS3_* and FS_CALLEE_RANGES / FS_RO_CELLS, read by triage_rtru.py)
  git -C "$GITDIR" show b120217aa206:$PR/FCimg.v > "$W/preset.FCimg.v"
  git -C "$GITDIR" show 30068deaa798:$GR/StrcmpTbl.v > "$W/grant.StrcmpTbl.30068deaa798.v"
  # donor-on-donor controls: one donor file with its own image on both sides
  for c in "CtlDisco 432691c31d8c:$DI/Strnlen.v Strnlen.v" "CtlGrant 97c611eec863:$GR/Strcmp.v Strcmp.v" \
           "CtlPreset b120217aa206:$PR/FCm3r.v FCm3r.v" "CtlCmdA $OURS/A/Rt/RtStrcmp.v RtStrcmp.v"; do
    set -- $c; mkdir -p "$W/$1/src"
    case $2 in *:*) git -C "$GITDIR" show "$2" > "$W/$1/src/$3" ;; *) cp "$2" "$W/$1/src/$3" ;; esac
  done
}

I_CA="A=$IMG/cgif.A.pin:$IMG/cgif.A.twin"; I_CB="B=$IMG/cgif.B.pin:$IMG/cgif.B.twin"
I_MA="A=$IMG/cmd.A.pin:$IMG/cmd.A.twin";   I_MB="B=$IMG/cmd.B.pin:$IMG/cmd.B.twin"
I_DI="A=$WIMG/disco.A.pin:$WIMG/disco.A.twin"; I_GR="A=$WIMG/grant.A.pin:$WIMG/grant.A.twin"
# fuzz_preset: the donor files name their image in their own text (FCimg.v, AE37.v gen_ae37.py header: ELF sha256
# f0d2e8d40c7e = the unstripped twin of the asan pin d83eb25dbf0d), not the release pin 93f1eb0975d9
I_PR="A=$WIMG/presetR.A.pin:$WIMG/presetR.A.twin"
# pac.sh writes to $RUN/<NAME>; this NAME lands in ROOT/runs. On the build VM pac.sh takes an absolute
# NAME as the run dir: REL=RUNDIR=<abs dir> rt_runs.sh run ...
REL=${REL:-../out/rt-reusable/runs}
RUNDIR=${RUNDIR:-$ROOT/runs}
OURREF=a3c671fb9bb:proofs/plugin-hostd/fuzz_command/lib

run() {
  case $1 in
    RtDisco)   $PAC $REL/RtDisco   "$W/RtDisco/src"   "$W/RtDisco/dst"   "$I_DI" "$I_MA" ;;
    RtCgifA)   $PAC $REL/RtCgifA   "$W/RtCgifA/src"   "$W/RtCgifA/dst"   "$I_CA" "$I_MA" ;;
    RtCgifB)   $PAC $REL/RtCgifB   "$W/RtCgifB/src"   "$W/RtCgifB/dst"   "$I_CB" "$I_MB" ;;
    RtGrant)   $PAC $REL/RtGrant   "$W/RtGrant/src"   "$W/RtGrant/dst"   "$I_GR" "$I_MA" ;;
    RtPreset)  $PAC $REL/RtPreset  "$W/RtPreset/src"  "$W/RtPreset/dst"  "$I_PR" "$I_MA" ;;
    # our lib/A/Rt -> our lib/B/Rt (every B/Rt file with an A/Rt twin), as the relay run RAB keys it
    RtRelay)   $PAC $REL/RtRelay   "$OURREF/A/Rt" "$OURREF/B/Rt" "B=$IMG/cmd.A.pin:$IMG/cmd.A.twin" "$I_MB" ;;
    CtlDisco)  $PAC $REL/CtlDisco  "$W/CtlDisco/src"  "$W/CtlDisco/src"  "$I_DI" "$I_DI" ;;
    CtlGrant)  $PAC $REL/CtlGrant  "$W/CtlGrant/src"  "$W/CtlGrant/src"  "$I_GR" "$I_GR" ;;
    CtlPreset) $PAC $REL/CtlPreset "$W/CtlPreset/src" "$W/CtlPreset/src" "$I_PR" "$I_PR" ;;
    CtlCmdA)   $PAC $REL/CtlCmdA   "$W/CtlCmdA/src"   "$W/CtlCmdA/src"   "$I_MA" "$I_MA" ;;
    *) echo "unknown run $1" >&2; exit 2 ;;
  esac
  echo "$1 $(cat "$RUNDIR/$1/rc") $(tail -1 "$RUNDIR/$1/stderr.txt")"
}

case ${1:-} in
  prep) prep ;;
  run) shift; for r in "$@"; do run "$r"; done ;;
  *) echo "usage: $0 prep | run NAME..." >&2; exit 2 ;;
esac
