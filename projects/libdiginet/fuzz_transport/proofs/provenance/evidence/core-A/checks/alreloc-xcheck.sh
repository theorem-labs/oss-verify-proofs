#!/bin/bash
# The alreloc a5c53bb2bed4 cross-check of every numeral port_core relocated (libdiginet/fuzz_transport image-A core,
# asan pin e89be137db17). Kind: measurement; it proves no function. alreloc decides nothing: every position the
# cross-check must not take from either tool is decided by reading the two images (alreloc_decide.py).
# Method of libdiginet/fuzz_decode's record (alreloc-xcheck.sh,
# sha256 93e6e8cff620; internal record); only pins, names and paths changed.
#
#   alreloc-xcheck.sh WORK LIB OUT [STAGE_OUT DEST]
#
# WORK       port_core's work directory (stage/ = donor text with module paths renamed, stage-out/ = relocated text)
# LIB        the target lib the run used (proofs/libdiginet/fuzz_transport/lib, start-up layer included)
# OUT        a scratch directory this script fills (wt/, fx.git/, report/, report-R/, run-*.log, out/, rows)
# STAGE_OUT  the relocated tree to compare (default WORK/stage-out; the planted control passes a copy)
# DEST       where the comparison and the decisions go (default OUT: OUT/out/, OUT/alreloc-crosscheck-rows.tsv)
#
# alreloc's two passes read only the donor text (hub, REF) and the scratch tree (LIB minus any relocated file), so they
# run once per WORK and LIB: OUT/alreloc-done.txt names the WORK and LIB they ran for; a later call with the same WORK,
# LIB and OUT only compares and decides.
#
# Environment (no host path is written here; every file's sha256 is checked; PG and TIMG name the image trees):
#   HUB             the hub repository (alreloc reads the donor files from it at REF, read only)
#   ALRELOC         alreloc.py.frozen-a5c53bb2bed4ad03; it runs from its own directory, which must hold
#                   align/keep-numerals.txt
#   GRANT_ELF       fuzz_grant.asan, the donor image (sha256 c2c7559b29bd...; default PG/bin/fuzz_grant/)
#   GRANT_SYMS      its unstripped twin (57c26f993615...; default PG/unstripped/fuzz_grant/)
#   TRANSPORT_ELF   fuzz_transport.asan, the target image A (e89be137db17...; default TIMG/stripped/)
#   TRANSPORT_SYMS  its unstripped twin (86efc3a80314...; default TIMG/unstripped/)
#   REF             the donor commit (default 25e3d17bdb50, origin/ossv/recipes)
#   UNIT_REF        the commit whose projects/libdiginet/fuzz_transport/harness.yaml pins asan e89be137db17 (default
#                   a494a3cb4a09, a released commit)
#   MODEL_LIBS      other units' libs at REF whose model text names the same check-site labels
#   MANIFEST_ELF    fuzz_manifest.asan, the image REF's projects/omx-clap-core/fuzz_manifest/harness.yaml pins
#                   (0ba7e1695886...)
#   CGIF_ELF        cgif_file_fuzzer.asan, the image REF's projects/cgif/cgif_file_fuzzer/harness.yaml pins
#                   (7093581aab04...); the two are the MODEL_LIBS units' images (alreloc_decide.py --model-elfs)
set -eu
U="usage: alreloc-xcheck.sh WORK LIB OUT [STAGE_OUT DEST]"
RUN=${1:?$U}
LIB=${2:?$U}
OUT=${3:?$U}
SO=${4:-$RUN/stage-out}
DEST=${5:-$OUT}
HUB=${HUB:?set HUB to the hub repository}
ALRELOC=${ALRELOC:?set ALRELOC to alreloc.py.frozen-a5c53bb2bed4ad03 in its own directory}
GRANT_ELF=${GRANT_ELF:-${PG:?set PG to the fuzz_grant image tree}/bin/fuzz_grant/fuzz_grant.asan}
GRANT_SYMS=${GRANT_SYMS:-$PG/unstripped/fuzz_grant/fuzz_grant.asan}
TRANSPORT_ELF=${TRANSPORT_ELF:-${TIMG:?set TIMG to the fuzz_transport image dir}/stripped/fuzz_transport.asan}
TRANSPORT_SYMS=${TRANSPORT_SYMS:-$TIMG/unstripped/fuzz_transport.asan}
REF=${REF:-25e3d17bdb5059606131377a3722d585415ab5d6}
UNIT_REF=${UNIT_REF:-a494a3cb4a0920ee15affd287a1d2051ee8ebe5a}
MODEL_LIBS=${MODEL_LIBS:-proofs/omx-clap-core/fuzz_manifest/lib,proofs/cgif/cgif_file_fuzzer/lib}
MANIFEST_ELF=${MANIFEST_ELF:?set MANIFEST_ELF to fuzz_manifest.asan 0ba7e1695886}
CGIF_ELF=${CGIF_ELF:?set CGIF_ELF to cgif_file_fuzzer.asan 7093581aab04}
MODEL_ELFS="proofs/omx-clap-core/fuzz_manifest/lib=$MANIFEST_ELF,proofs/cgif/cgif_file_fuzzer/lib=$CGIF_ELF"
export PYTHONDONTWRITEBYTECODE=1
HERE=$(cd "$(dirname "$0")" && pwd)
SRC_LIB=proofs/libreac/fuzz_grant/lib
UNIT=libdiginet/fuzz_transport
UNIT_LIB=proofs/$UNIT/lib   # the rows name files by their repository path under it
RENAMES="--rename GrantB=TransportB --rename GrantSyms=TransportSyms --rename GrantB_syms=TransportB_syms --rename GrantB_ok=TransportB_ok"

pin() {   # pin FILE SHA256-PREFIX
  s=$(sha256sum "$1" | cut -c1-${#2})
  [ "$s" = "$2" ] || { echo "alreloc-xcheck: $1: sha256 $s, expected $2" >&2; exit 2; }
}
pin "$ALRELOC" a5c53bb2bed4ad039a600ecda538d6d0a1a01ccf4d62f8da9a09031a277fa17b
pin "$GRANT_ELF" c2c7559b29bdf39c
pin "$GRANT_SYMS" 57c26f99361583f6
pin "$TRANSPORT_ELF" e89be137db17b720
pin "$TRANSPORT_SYMS" 86efc3a803149811
pin "$MANIFEST_ELF" 0ba7e16958864e92
pin "$CGIF_ELF" 7093581aab040cfd
ADIR=$(cd "$(dirname "$ALRELOC")" && pwd)
RUN=$(cd "$RUN" && pwd)
LIB=$(cd "$LIB" && pwd)
mkdir -p "$OUT"
OUT=$(cd "$OUT" && pwd)

if [ "$(cat "$OUT/alreloc-done.txt" 2>/dev/null)" != "$RUN $LIB" ]; then
  rm -rf "$OUT/alreloc-done.txt" "$OUT/wt" "$OUT/fx.git" "$OUT/fx.index" "$OUT/report" "$OUT/report-R"
  # 1. the scratch unit tree: the unit's lib minus every relocated file, so alreloc reads no port_core output
  mkdir -p "$OUT/wt/proofs/$UNIT"
  cp -a "$LIB" "$OUT/wt/proofs/$UNIT/lib"
  ( cd "$RUN/stage-out" && find . -name '*.v' -type f | sed 's|^\./||' | LC_ALL=C sort ) > "$OUT/relocated.txt"
  while read -r f; do rm -f "$OUT/wt/proofs/$UNIT/lib/$f"; done < "$OUT/relocated.txt"
  awk '/^A\//' "$OUT/relocated.txt" > "$OUT/files-A.txt"
  awk '/^Reusable\//{print "A/" $0}' "$OUT/relocated.txt" > "$OUT/files-R.txt"
  na=$(wc -l < "$OUT/files-A.txt"); nr=$(wc -l < "$OUT/files-R.txt"); nt=$(wc -l < "$OUT/relocated.txt")
  [ $((na + nr)) -eq "$nt" ] || { echo "alreloc-xcheck: $nt relocated files, $na under A/ + $nr under Reusable/" >&2; exit 2; }

  # 2. the fixture commit of pass R: REF's tree plus $SRC_LIB/A/Reusable/<X>.v = the same blob as $SRC_LIB/Reusable/<X>.v
  #    (alreloc --build asan takes only files under lib/A/ or lib/AZ/); its objects live in OUT/fx.git, the hub is
  #    not written (alreloc reads them through GIT_ALTERNATE_OBJECT_DIRECTORIES)
  git init -q --bare "$OUT/fx.git"
  echo "$(git -C "$HUB" rev-parse --path-format=absolute --git-common-dir)/objects" > "$OUT/fx.git/objects/info/alternates"
  export GIT_DIR="$OUT/fx.git" GIT_INDEX_FILE="$OUT/fx.index"
  git read-tree "$REF"
  while read -r f; do
    x=${f#A/}
    b=$(git rev-parse "$REF:$SRC_LIB/$x")
    git update-index --add --cacheinfo "100644,$b,$SRC_LIB/A/$x"
  done < "$OUT/files-R.txt"
  T=$(git write-tree --missing-ok)
  FX=$(echo "fixture: $SRC_LIB/Reusable files at A/Reusable for alreloc --build asan" | \
       GIT_AUTHOR_NAME=fixture GIT_AUTHOR_EMAIL=fixture@invalid GIT_AUTHOR_DATE='2026-01-01T00:00:00Z' \
       GIT_COMMITTER_NAME=fixture GIT_COMMITTER_EMAIL=fixture@invalid GIT_COMMITTER_DATE='2026-01-01T00:00:00Z' \
       git commit-tree "$T" -p "$REF")
  unset GIT_DIR GIT_INDEX_FILE
  echo "$FX" > "$OUT/fixture-commit.txt"

  # 3. alreloc, --dry (it writes no lib file), one pass per path class, the two in parallel; each log ends with alreloc's
  #    exit status (non-zero when it lists numerals to review: its UNMAPPED / *-UNSURE rows, which the comparison
  #    classes alreloc-unmapped)
  COMMON="--src libreac/fuzz_grant --unit $UNIT --build asan --wt $OUT/wt --dry --unit-ref $UNIT_REF
          --src-elf $GRANT_SYMS --pinned-elf $TRANSPORT_ELF --unit-elf $TRANSPORT_SYMS $RENAMES"
  # shellcheck disable=SC2046,SC2086
  ( set +e; cd "$ADIR" || exit 2; python3 "$(basename "$ALRELOC")" --ref "$REF" $COMMON --report "$OUT/report" \
      $(cat "$OUT/files-A.txt") > "$OUT/run-A.log" 2>&1; echo "rc=$?" >> "$OUT/run-A.log" ) &
  # shellcheck disable=SC2046,SC2086
  ( set +e; cd "$ADIR" || exit 2; env GIT_ALTERNATE_OBJECT_DIRECTORIES="$OUT/fx.git/objects" \
      python3 "$(basename "$ALRELOC")" --ref "$FX" $COMMON --report "$OUT/report-R" \
      $(cat "$OUT/files-R.txt") > "$OUT/run-R.log" 2>&1; echo "rc=$?" >> "$OUT/run-R.log" ) &
  wait
  echo "alreloc pass A: $(grep -h 'per-numeral report' "$OUT/run-A.log"), $(tail -1 "$OUT/run-A.log"); pass R: $(grep -h 'per-numeral report' "$OUT/run-R.log"), $(tail -1 "$OUT/run-R.log")"
  if [ ! -d "$OUT/report/$UNIT" ] || [ ! -d "$OUT/report-R/$UNIT" ]; then
    echo "alreloc-xcheck: an alreloc pass wrote no report (see $OUT/run-A.log, $OUT/run-R.log)" >&2
    exit 2
  fi
  echo "$RUN $LIB" > "$OUT/alreloc-done.txt"
fi

# 4. every numeral position paired, then decided against the images
mkdir -p "$DEST"
python3 "$HERE/alreloc_compare.py" --hub "$HUB" --ref "$REF" --src-lib "$SRC_LIB" \
  --stage "$RUN/stage" --stage-out "$SO" \
  --report-a "$OUT/report/$UNIT" --report-r "$OUT/report-R/$UNIT" $RENAMES \
  --out-dir "$DEST/out"
python3 "$HERE/alreloc_decide.py" --positions "$DEST/out/positions.tsv" \
  --hub "$HUB" --ref "$REF" --src-lib "$SRC_LIB" --stage-out "$SO" --unit-lib "$LIB" \
  --grant-elf "$GRANT_ELF" --grant-syms "$GRANT_SYMS" --target-elf "$TRANSPORT_ELF" --target-syms "$TRANSPORT_SYMS" \
  --model-libs "$MODEL_LIBS" --model-elfs "$MODEL_ELFS" \
  --out-rows "$DEST/alreloc-crosscheck-rows.tsv" --out-counts "$DEST/out/decided-counts.tsv" \
  --file-prefix "$UNIT_LIB/"
