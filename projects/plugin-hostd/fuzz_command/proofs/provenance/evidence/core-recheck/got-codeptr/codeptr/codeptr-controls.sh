#!/usr/bin/env bash
# codeptr-controls.sh - the known answers of codeptr 12348302dfd2, run before its result on fuzz_command is used.
# The control pair of record is codeptr-controls.sh of tools/codeptr/c0ce606ed1fa (1f261d9e9ce9), which the registry
# names for 12348302dfd2 too ("codeptr-controls.sh PASS: must-find PAIRED on 6 files, must-not-flag 0x8065e"). This
# file runs the same assertions with local inputs, and once more on fuzz_command's own images:
#  (1) MUST FIND, the control of record: cgif's own UNRELOCATED A/AD1k A/AD2i A/AD2j (image A) and YD1k YD2i YD2j
#      (image B) against fuzz_scene's images, stale against cgif, paired with cgif's files: each file's line must
#      report findings > 0 AND name its paired donor file. Known answer: codeptr c0ce606ed1fa (the version the
#      registry's counts AD1k 22 / AD2i 6 / AD2j 107 come from) run on the SAME inputs must give the same count for
#      each file (12348302dfd2 changed the names reader, --not-address and the type rule; none applies to these files).
#      The registry's counts are printed beside ours for reference.
#  (2) MUST FIND on fuzz_command's images: the same six cgif files against fuzz_command.asan / .asan-ubsan: each line
#      must report findings > 0 and name its paired donor file.
#  (3) MUST NOT FLAG: cgif's YF0m.v:289 `Example tfib_hash_buckets : ... = [969124; 525918].` - 525918 = 0x8065e is a
#      bucket index. It must be listed as NOT read as an address and must not be among YF0m.v's findings, on
#      fuzz_scene's image B and on fuzz_command's image B.
# Run from the directory codeptr-run.sh uses, plus ctlimg/ = fuzz_scene.asan (pin 43654a025fd0) / .asan-ubsan (pin
# e98b1ed286c1) as scene.A.pin / scene.B.pin and their unstripped twins as scene.A.twin / scene.B.twin.
# Exit 0 only if every assertion holds; each failed assertion is printed.
set -uo pipefail
fail=0
[ "$(sha256sum < tool/codeptr.py | cut -c1-12)" = 12348302dfd2 ] || { echo "tool/codeptr.py is not 12348302dfd2"; exit 2; }
[ "$(sha256sum < c0ce/codeptr.py | cut -c1-12)" = c0ce606ed1fa ] || { echo "c0ce/codeptr.py is not c0ce606ed1fa"; exit 2; }
run() { python3 tool/codeptr.py "$@" 2>&1; }
run0() { python3 c0ce/codeptr.py "$@" 2>&1; }
count() { echo "$1" | awk -v b="$2" '$1 == b && / FINDINGS/' | sed -n 's/.*, \([0-9]*\) FINDINGS.*/\1/p'; }
must_find() {  # label image twin donor-image donor-twin donor-dir mode(c0ce | >0) files...
  local lab=$1 im=$2 tw=$3 di=$4 dt=$5 dd=$6 mode=$7; shift 7
  local out; out=$(run --image "$im" --names "$tw" --stale-image "$di" --stale-names "$dt" --stale-dir cgif/lib "$@")
  echo "$out" | sed 's/^/  /'
  local out0=''
  if [ "$mode" = c0ce ]; then
    out0=$(run0 --image "$im" --names "$tw" --stale-image "$di" --stale-names "$dt" --stale-dir cgif/lib "$@")
    echo "  -- c0ce606ed1fa on the same inputs:"; echo "$out0" | sed 's/^/  /'
  fi
  for f in "$@"; do
    local b; b=$(basename "$f")
    local line; line=$(echo "$out" | awk -v b="$b" '$1 == b && / FINDINGS/')
    local n; n=$(count "$out" "$b")
    if [ -z "$line" ] || [ -z "$n" ] || [ "$n" -eq 0 ]; then echo "FAIL must-find $lab $b: no findings ($line)"; fail=1; fi
    echo "$line" | grep -q "donor file $dd/$b:" || { echo "FAIL must-find $lab $b: the line does not name the paired donor file $dd/$b"; fail=1; }
    if [ "$mode" = c0ce ]; then
      local n0; n0=$(count "$out0" "$b")
      [ "$n" = "$n0" ] || { echo "FAIL must-find $lab $b: 12348302dfd2 $n FINDINGS, c0ce606ed1fa $n0 on the same inputs"; fail=1; }
      echo "  $lab $b: 12348302dfd2 $n, c0ce606ed1fa $n0 (same inputs), registry record $(echo "$REC" | tr ',' '\n' | awk -F= -v b="$b" '$1 == b {print $2}')"
    fi
  done
}
must_not_flag() {  # label image twin donor-image donor-twin
  local out; out=$(run --image "$2" --names "$3" --stale-image "$4" --stale-names "$5" --stale-dir cgif/lib cgif/lib/YF0m.v)
  echo "$out" | sed 's/^/  /'
  echo "$out" | grep -q '^YF0m.v .*NOT read as addresses.*0x8065e (525918)' || { echo "FAIL must-not-flag $1: 0x8065e is not listed as NOT read as an address"; fail=1; }
  echo "$out" | awk '$1 == "YF0m.v" && / FINDINGS/' | grep -q '0x8065e' && { echo "FAIL must-not-flag $1: 0x8065e is among YF0m.v's findings"; fail=1; }
}
REC='AD1k.v=22,AD2i.v=6,AD2j.v=107,YD1k.v=22,YD2i.v=6,YD2j.v=107'
echo "== (1) MUST FIND, fuzz_scene image A (control of record)"
must_find scene-A ctlimg/scene.A.pin ctlimg/scene.A.twin img/cgif.A.pin img/cgif.A.twin cgif/lib/A c0ce cgif/lib/A/AD1k.v cgif/lib/A/AD2i.v cgif/lib/A/AD2j.v
echo "== (1) MUST FIND, fuzz_scene image B (control of record)"
must_find scene-B ctlimg/scene.B.pin ctlimg/scene.B.twin img/cgif.B.pin img/cgif.B.twin cgif/lib c0ce cgif/lib/YD1k.v cgif/lib/YD2i.v cgif/lib/YD2j.v
echo "== (2) MUST FIND, fuzz_command image A"
must_find cmd-A img/cmd.A.pin img/cmd.A.twin img/cgif.A.pin img/cgif.A.twin cgif/lib/A '>0' cgif/lib/A/AD1k.v cgif/lib/A/AD2i.v cgif/lib/A/AD2j.v
echo "== (2) MUST FIND, fuzz_command image B"
must_find cmd-B img/cmd.B.pin img/cmd.B.twin img/cgif.B.pin img/cgif.B.twin cgif/lib '>0' cgif/lib/YD1k.v cgif/lib/YD2i.v cgif/lib/YD2j.v
echo "== (3) MUST NOT FLAG 0x8065e (cgif YF0m.v:289, a bucket index), fuzz_scene image B"
must_not_flag scene-B ctlimg/scene.B.pin ctlimg/scene.B.twin img/cgif.B.pin img/cgif.B.twin
echo "== (3) MUST NOT FLAG 0x8065e, fuzz_command image B"
must_not_flag cmd-B img/cmd.B.pin img/cmd.B.twin img/cgif.B.pin img/cgif.B.twin
[ $fail -eq 0 ] && echo "codeptr-controls: PASS (must-find paired on 12 file runs; on fuzz_scene the counts equal c0ce606ed1fa's on the same inputs; must-not-flag 0x8065e on 2 images)" || echo "codeptr-controls: FAILED"
exit $fail
