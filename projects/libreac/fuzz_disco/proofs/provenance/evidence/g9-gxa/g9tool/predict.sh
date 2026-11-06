#!/usr/bin/env bash
# port_addr_check predict, one run per file in parallel: fm.asan fuzz_manifest -> fuzz_disco.
#   PRED_DIR=<dir> ./predict.sh [--src-ref <fm sha>] disco-A|disco-Y <fm lib/A path without .v> ...
# fm text is read from the git repository HUB at --src-ref (default 0ddf65fd8cc, the fm extended route; 3e35620c52e for
# the first route), not from a checkout.  Output: <PRED_DIR>/<target>/<path>.tsv (+ .summary, whose last line names the
# src ref).  Each run writes temp files in the output directory and renames them into place only when port_addr_check
# exits 0 and read the file, so a reader sees the old complete table or the new complete table, never a partial or
# empty one; a failed run keeps the old table, leaves its log in <path>.failed, and makes predict.sh exit non-zero.
# New version of the G9 tool's predict.sh of record (sha256 e13f55b0c7ce137ca560687f466a1303ac76b8481b697001fa8dcb2447d2617a):
# every input is an environment variable instead of a constant: HUB; PAC_DIR (the address checker kit 0767e70e074a);
# FM_IMAGE / FM_DEBUG, A_IMAGE / A_DEBUG, Y_IMAGE / Y_DEBUG (each stripped image and its unstripped twin); PRED_DIR
# (required); CACHE_DIR (default <PRED_DIR>/cache); TMPDIR (default <PRED_DIR>/tmp); PREDICT_JOBS (default 12).
# pyelftools 0.33 must be importable (PYTHONPATH).
set -u
REF=0ddf65fd8cc
if [ "${1:-}" = --src-ref ]; then REF=${2:?predict.sh: --src-ref needs a commit}; shift 2; fi
T=${1:?usage: predict.sh [--src-ref SHA] disco-A|disco-Y files...}; shift
: "${HUB:?predict.sh: set HUB}" "${PAC_DIR:?predict.sh: set PAC_DIR}" "${FM_IMAGE:?}" "${FM_DEBUG:?}" "${PRED_DIR:?}"
case "$T" in
  disco-A) DST=${A_IMAGE:?} DSTD=${A_DEBUG:?} ;;
  disco-Y) DST=${Y_IMAGE:?} DSTD=${Y_DEBUG:?} ;;
  *) echo "unknown target $T (disco-A | disco-Y)" >&2; exit 2 ;;
esac
FM=$FM_IMAGE FMD=$FM_DEBUG
PAC=$PAC_DIR/port_addr_check.py
LIB=proofs/omx-clap-core/fuzz_manifest/lib
PD=$PRED_DIR
case "$PD" in /*) ;; *) PD=$PWD/$PD ;; esac
python3 -c 'import elftools' 2> /dev/null ||
  { echo "predict.sh: python3 cannot import elftools (pyelftools); fix: pip install --target <dir> pyelftools==0.33, then PYTHONPATH=<dir>" >&2; exit 2; }
GIT_NO_LAZY_FETCH=1 git -C "$HUB" cat-file -e "$REF^{commit}" 2> /dev/null ||
  { echo "predict.sh: fm $REF is not in $HUB; fetch it into $HUB" >&2; exit 2; }
CACHE=${CACHE_DIR:-$PD/cache}
TMPDIR=${TMPDIR:-$PD/tmp}
mkdir -p "$TMPDIR" "$PD/$T" "$CACHE" || exit 2
export TMPDIR T PD DST DSTD FM FMD PAC HUB CACHE REF LIB
job() {
  local f=${1%.v} o tag rc
  o=$PD/$T/$f tag=$$.$BASHPID.tmp
  if ! GIT_NO_LAZY_FETCH=1 git -C "$HUB" cat-file -e "$REF:$LIB/A/$f.v" 2> /dev/null; then
    echo "predict.sh: REFUSED $T $f: fm $REF has no $LIB/A/$f.v (wrong --src-ref?)" >&2
    echo "3 $T $f $REF" >> "$PD/$T/rcs.txt"
    return 1
  fi
  mkdir -p "$(dirname "$o")" || return 1
  cd "$PD" || return 1
  GIT_NO_LAZY_FETCH=1 python3 "$PAC" --git "$HUB" --src "$REF:$LIB" --include "A/$f.v" \
    --src-image "A=$FM:$FMD" --dst-image "A=$DST:$DSTD" --cache "$CACHE" --out "$o.tsv.$tag" --summary \
    > "$o.summary.$tag" 2>&1
  rc=$?
  echo "# src-ref $REF" >> "$o.summary.$tag"
  if [ "$rc" = 0 ] && grep -q '^# files read 0;' "$o.summary.$tag"; then
    rc=4; echo "# predict.sh: port_addr_check read 0 files" >> "$o.summary.$tag"
  fi
  if [ "$rc" = 0 ]; then
    mv -f "$o.tsv.$tag" "$o.tsv" && mv -f "$o.summary.$tag" "$o.summary" && rm -f "$o.failed"
  else
    rm -f "$o.tsv.$tag"; mv -f "$o.summary.$tag" "$o.failed"
    echo "predict.sh: FAILED $T $f at fm $REF (rc $rc, log $o.failed; the previous table, if any, is unchanged)" >&2
  fi
  echo "$rc $T $f $REF" >> "$PD/$T/rcs.txt"
  [ "$rc" = 0 ]
}
export -f job
printf '%s\n' "$@" | xargs -P "${PREDICT_JOBS:-12}" -I{} bash -c 'job "$1"' _ {}
x=$?
if [ "$x" = 0 ]; then echo "PREDICT-DONE src-ref $REF"; else echo "PREDICT-FAILED src-ref $REF (see the messages above)"; exit 1; fi
