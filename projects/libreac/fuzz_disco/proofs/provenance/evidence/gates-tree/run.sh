#!/usr/bin/env bash
# Re-runs the three whole-tree gate records of this directory, each with a planted control that the gate must catch.
#
#   REPO=<git checkout holding REF> REF=<series base commit> PIN_DIR=<directory of the four pinned fuzz_disco ELFs> \
#   SETTINGS_DIR=<directory of the settings check v10, with its controls> KIMG=<kimg_overlap.py> \
#   SNAPSHOT=<tools/elf_snapshot.py of the semantics commit release.yaml names> [OUT=<directory>] bash run.sh
#
# Writes settings-v10.txt, segments.txt and kimg-overlap.txt into OUT (default: this script's directory). Each tool's
# sha256 is checked first against the version this record cites. The unit's tree is read from REF with `git archive`,
# never from a working copy. Every path under the run's temporary directory is written as <work>, so a second run on
# the same inputs gives the same three files byte for byte.
set -euo pipefail

: "${REPO:?}" "${REF:?}" "${PIN_DIR:?}" "${SETTINGS_DIR:?}" "${KIMG:?}" "${SNAPSHOT:?}"
HERE=$(cd "$(dirname "$0")" && pwd)
OUT=${OUT:-$HERE}
UNIT=proofs/libreac/fuzz_disco
PROJ=projects/libreac/fuzz_disco

want() { # file sha256
  local got
  got=$(sha256sum "$1" | cut -d' ' -f1)
  [ "$got" = "$2" ] || { echo "REFUSED: $1 has sha256 $got, this record cites $2" >&2; exit 2; }
}
want "$SETTINGS_DIR/global_settings.py" 439f8e3bd4637640d6d40fb668716c081c3ba202aa831f31f0120de0b4e39242
want "$KIMG" 5db341e3cd628ad07bde939c902db9ecc0c3e5791fa3947434ad729031239d3a
want "$SNAPSHOT" a7f4d38c861c07ff6fe8634648cea8ab38b5f5f735357b98ad87a10f0e93b05f

WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT
COMMIT=$(git -C "$REPO" rev-parse "$REF^{commit}")
mkdir "$WORK/tree"
git -C "$REPO" archive "$COMMIT" -- "$UNIT" "$PROJ" | tar -x -C "$WORK/tree"
cp -r "$SETTINGS_DIR" "$WORK/gs"
cp "$KIMG" "$WORK/kimg_overlap.py"
cp "$SNAPSHOT" "$WORK/elf_snapshot.py"
cd "$WORK"

# ---- 1. settings check v10 over every .v file of the unit ------------------------------------------------------
git -C "$REPO" ls-tree -r --name-only "$COMMIT" -- "$UNIT" | { grep '\.v$' || true; } > vfiles
mapfile -t VFILES < vfiles
set +e
python3 gs/global_settings.py tree "${VFILES[@]}" > v10.run 2>&1
rc=$?
mkdir -p ctl/$UNIT/lib/A
{ cat tree/$UNIT/lib/A/AB01.v; printf '\nUnset Guard Checking.\n'; } > ctl/$UNIT/lib/A/AB01.v
python3 gs/global_settings.py ctl $UNIT/lib/A/AB01.v > v10.ctl 2>&1
crc=$?
set -e
{
  echo "# gate: settings check v10 (global_settings.py sha256 439f8e3bd4637640d6d40fb668716c081c3ba202aa831f31f0120de0b4e39242)"
  echo "# tree: $UNIT at commit $COMMIT, $(wc -l < vfiles) .v files"
  echo "# command: python3 global_settings.py <tree> <each .v file of $UNIT, from git ls-tree>"
  echo "# verdict: exit $rc ($( [ $rc = 0 ] && echo 'PASS: no kernel-level setting' || echo FAIL ))"
  echo "# control: the same check on a copy of $UNIT/lib/A/AB01.v with 'Unset Guard Checking.' appended: exit $crc ($( [ $crc = 5 ] && echo 'caught, as it must be' || echo 'NOT CAUGHT' ))"
  echo "# rows: below, the run's TOOL / selftest / control lines, every KERNEL or UNMEASURED row under its file, and the SUMMARY (settings_digest.py)"
  python3 "$HERE/settings_digest.py" v10.run "$WORK"
  echo "# control run:"
  python3 "$HERE/settings_digest.py" v10.ctl "$WORK" | grep -E '^(SUMMARY|REFUSE|read |   :)'
} > "$OUT/settings-v10.txt"

# ---- 2. the four pins and their 16 PT_LOAD segments ------------------------------------------------------------
H=tree/$PROJ/harness.yaml
set +e
python3 "$HERE/segment_match.py" "$H" "$PIN_DIR" elf_snapshot.py snap > seg.run 2>&1
rc=$?
python3 "$HERE/segment_match.py" "$H" "$PIN_DIR" elf_snapshot.py snapc --hex-override asan:2:0x100 > seg.ctl 2>&1
crc=$?
mkdir pinc
cp "$PIN_DIR"/fuzz_disco.* pinc/
python3 - pinc/fuzz_disco.ubsan <<'EOF'
import sys
p = sys.argv[1]; b = bytearray(open(p, 'rb').read()); b[0x3000] ^= 1; open(p, 'wb').write(b)
EOF
python3 "$HERE/segment_match.py" "$H" pinc elf_snapshot.py snapp > seg.ctl2 2>&1
crc2=$?
set -e
{
  echo "# gate: the four ELFs that $PROJ/harness.yaml pins, and the memory image the build makes of each (segment_match.py)"
  echo "# tree: harness.yaml at commit $COMMIT; snapshot tool elf_snapshot.py sha256 a7f4d38c861c07ff6fe8634648cea8ab38b5f5f735357b98ad87a10f0e93b05f"
  echo "# command: python3 segment_match.py <harness.yaml> <pin directory> <elf_snapshot.py> <work directory>"
  echo "# verdict: exit $rc ($( [ $rc = 0 ] && echo 'PASS' || echo FAIL ))"
  echo "# control 1: one byte of image asan's segment 2 hex flipped after the snapshot (--hex-override asan:2:0x100): exit $crc, $(grep '^SUMMARY' seg.ctl)"
  echo "# control 2: one byte at file offset 0x3000 of a copy of fuzz_disco.ubsan flipped: exit $crc2, $(grep '^SUMMARY' seg.ctl2)"
  cat seg.run
} > "$OUT/segments.txt"

# ---- 3. kimg_overlap on image A's start-up tables AB01 / AB03 / AD2j -------------------------------------------
A=$PIN_DIR/fuzz_disco.asan
set +e
python3 kimg_overlap.py "$REPO" "$COMMIT" $UNIT/lib/A/AB01.v "$A" "$COMMIT" $UNIT/lib/A/AB03.v "$A" \
  "$COMMIT" $UNIT/lib/A/AD2j.v "$A" > kimg.run 2>&1
rc=$?
sed 's/KImg 1552296 5056480/KImg 1552288 5056480/' tree/$UNIT/lib/A/AB01.v > ctl_AB01.v
python3 kimg_overlap.py "$REPO" FILE ctl_AB01.v "$A" > kimg.ctl 2>&1
crc=$?
set -e
{
  echo "# gate: kimg_overlap (kimg_overlap.py sha256 5db341e3cd628ad07bde939c902db9ecc0c3e5791fa3947434ad729031239d3a) on $UNIT/lib/A/AB01.v, AB03.v, AD2j.v against image A (fuzz_disco.asan)"
  echo "# command: python3 kimg_overlap.py <repo> <commit> <file> <fuzz_disco.asan> (one triple per file)"
  echo "# verdict: exit $rc ($( [ $rc = 0 ] && echo 'PASS: no contradiction, no fill' || echo FAIL ))"
  echo "# control: a copy of AB01.v whose 'KImg 1552296 5056480' is widened 8 bytes down to 1552288, over an existing KWord: exit $crc ($( [ $crc = 1 ] && echo 'caught, as it must be' || echo 'NOT CAUGHT' ))"
  sed 's/^/#   /' kimg.ctl
  cat kimg.run
} > "$OUT/kimg-overlap.txt"
echo "wrote $OUT/settings-v10.txt $OUT/segments.txt $OUT/kimg-overlap.txt"
