#!/bin/bash
# run.sh -- re-run every gate record of evidence/gates-Y on the series base against the image B pin.
# Proves no function (kind: measurement). Run from anywhere: bash run.sh [GATE ...]   (GATE: g1 .. g11 manifest;
# default all). Every input is an environment variable below; this file holds no host path. Every output goes to
# $WORK (outside the tree). The sha256 of each pin, twin and tool is checked first; a mismatch stops the run (exit 2).
#
#   GIT          a git directory that holds the series base, the series tree SERIES (g11), the cgif donor commit and
#                the codeptr control commit
#   PIN_DIR      the four released fuzz_disco pins: fuzz_disco.{asan,asan-ubsan,plain,ubsan}
#   TWIN_DIR     their unstripped twins (host binaries: never shipped; PT_LOAD 2..4 byte-equal to the pins)
#   CGIF_BIN     the four released cgif_file_fuzzer pins: cgif_file_fuzzer.{asan,asan-ubsan,plain,ubsan}
#   DONORS       root of the symbolised donor images (<project>/<build>/<target> + .debug) the address checkers use
#   PAC          port_addr_check.py, the address checker of record (sha256 efa19b81e92b...)
#   KIT5033      the frozen port_addr_check 5033540ba83b kit directory (port_addr_check.py, scan_literals.py, cfgpair.py)
#   STARTUP_SET  the start-up set of record 2026-10-30d (its SHA256SUMS must pass)
#   (codeptr-controls.sh, the codeptr control of record, reads fuzz_scene's images from its own constant PAU, its line
#    19: that control runs only where PAU holds them. run.sh takes the script itself from $GIT at CTL_REF.)
#   KIMG         kimg_overlap.py (5db341e3cd62)
#   CELLGATES    directory of cellcheck.py (cc60c6705e6f), ownedcheck.py (b663903ddda1), termeval.py (b64897421d5b)
#   SHADOWGATE   directory of the fixed shadowcheck.py (e04173f5a5a5) and its termeval.py (85060f6c7558)
#   COVCHECK     covcheck.py (595119b27d0c)
#   PAC3         port_addr_check.py 3d2eee813cce, installed 2026-10-30 16:32Z (gates g7, g8; g10 for its PIN:TWIN diff)
#   PAC0D        port_addr_check.py 0d24592683b6, installed 2026-10-30 23:46Z, in its version directory (the five files
#                its SHA256SUMS names beside it: inputs_used.py, scan_literals.py, insn-targets/, identity-quotients/)
#                (g10, g11)
#   PAC205       port_addr_check.py 205a90fd19b8, installed 2026-10-31 08:00Z, in its version directory (the same five
#                files beside it) (g11)
#   RC2          roundconst.py v2 (32b39f3b34e9); RC1: roundconst.py v1 (8ad299147f2e), its controls only (g8)
#   CGIF_TWIN_DIR the unstripped twins of the four cgif pins: cgif_file_fuzzer.{asan,asan-ubsan,plain,ubsan} (g8-g11)
#   WORK         scratch directory (written; created)
# g8, g9 and g10 read g7's table and g7 compares its rows with g1's when $WORK/g1 holds it: run `run.sh g1 g7 g8` in
# one WORK. g11 reads the series tree SERIES (the base with the unit's later code fixes), not BASE.
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
for v in GIT PIN_DIR TWIN_DIR CGIF_BIN DONORS PAC KIT5033 STARTUP_SET KIMG CELLGATES SHADOWGATE COVCHECK WORK; do
  [ -n "${!v:-}" ] || { echo "run.sh: set $v (see the header)" >&2; exit 2; }
done
BASE=b1afc3e80791ebe54b1034a568112da851f005f0      # the series base
SERIES=d57e4e79e469316d9e26c20fd6bb5ff3a086dd55    # the series tree g11 reads (BASE + the unit's code fixes)
CGIF_REF=c8557374ad2e6c079948f0813d37e31638d1c0d1  # cgif_file_fuzzer's released lib, the donor
CTL_REF=b351f103e888f71ecf6d6eefb16593945e83f7f0   # holds codeptr-controls.sh and its cgif nm texts (tools/startup/)
PIN_B=$PIN_DIR/fuzz_disco.asan-ubsan; PIN_A=$PIN_DIR/fuzz_disco.asan
TWIN_B=$TWIN_DIR/fuzz_disco.asan-ubsan; TWIN_A=$TWIN_DIR/fuzz_disco.asan
CGIF_B=$CGIF_BIN/cgif_file_fuzzer.asan-ubsan
GATES=${*:-g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 manifest}
FAIL=0
note() { echo "run.sh: $*"; }
bad() { echo "run.sh: MISMATCH: $*"; FAIL=1; }
need() { local v; for v in "$@"; do [ -n "${!v:-}" ] || { echo "run.sh: set $v (see the header)" >&2; exit 2; }; done; }

sha() {  # sha FILE SHA256: stop unless FILE has exactly that sha256
  local got; got=$(sha256sum "$1" 2>/dev/null | cut -c1-64)
  [ "$got" = "$2" ] || { echo "run.sh: $1 has sha256 '${got:-missing}', not $2" >&2; exit 2; }
}
sha "$PIN_A" 5e39150dd8104df969eb360f9cc29c4f92fe12326afd23783a679e4fb4809f46
sha "$PIN_B" cee6f04ad3d4928e242405689ae058bb9e8b6533000c90bde984a2f0d5ff5146
sha "$PIN_DIR/fuzz_disco.plain" 04988e3ab31341965e44f0ca1bb0e5ed18fe6892e2c753df7a87bec197576f7c
sha "$PIN_DIR/fuzz_disco.ubsan" 56121de6ba4cff85e0fa262e9783f384e35fb8642d057f7a3a4290bcc245b22e
sha "$TWIN_B" ead714913acd1e81835e08e021456cebcb35c09af2f87f4e7e2b6891f1b92489
sha "$TWIN_A" b8aac6eee6a62fef29b9e9a7df6154c2cda9a8f0252cbae45ad85bcc91135b6e
sha "$TWIN_DIR/fuzz_disco.plain" 115e0dcb29bc5963917708dd1d76a7b38df31bb665938ae75fd6f583c9d3d9b7
sha "$CGIF_BIN/cgif_file_fuzzer.asan" 7093581aab040cfd94ed56f83bf44a37e6ec3c34db39cc57bf467e2949e870f0
sha "$CGIF_B" 1c29845fe6058de6e1dbf3f6ec6abd566ea612d76b65ea5435d7ff77c63e08ef
sha "$CGIF_BIN/cgif_file_fuzzer.plain" 19dedd1bc682b698ffe399b1619d181c1d0786b1687ffc743c92a636a311bf8f
sha "$CGIF_BIN/cgif_file_fuzzer.ubsan" 44a34d2e23b6e2df99cf7c96a03e77f4270d5480772c3e7a0c3325d026943c06
sha "$PAC" efa19b81e92ba289e7c185d481faadf045ce7d52d092cc10642fec69924aba03
sha "$KIT5033/port_addr_check.py" 5033540ba83bdad174e9b1aa3cc21ffeda3469736e4dd0390f58db9008890546
sha "$KIT5033/scan_literals.py" ae01d69b2ee4af269258982bef0de35a38a44d2b8832b62ef217e58439cd5804
sha "$KIT5033/cfgpair.py" bc9795900868df328eebcf4f90bc7c1cbf9abf5ab9efa95474a2871bf99c5cd4
(cd "$STARTUP_SET" && sha256sum -c --quiet SHA256SUMS) || { echo "run.sh: STARTUP_SET fails its SHA256SUMS" >&2; exit 2; }
sha "$STARTUP_SET/frozen/codeptr.py.frozen-12348302dfd2" 12348302dfd2e419748bc3ad20e67b246d21b576c9c6d7887a33854785e146dd
sha "$STARTUP_SET/frozen/ifchk.py.frozen-f5cde600cc18" f5cde600cc1886bb65200495a69e1eb3afb936ea5512edb8c581edc0299847fb
sha "$STARTUP_SET/startup-set-2026-10-30d.tsv" bde9702390640d7bfc5a23702de239154ed4130e863e475ca109455c2648dbab
sha "$KIMG" 5db341e3cd628ad07bde939c902db9ecc0c3e5791fa3947434ad729031239d3a
sha "$CELLGATES/cellcheck.py" cc60c6705e6f4264ce9b15def8a3ef85225340c1b0f95c982b4183184e530e54
sha "$CELLGATES/ownedcheck.py" b663903ddda19527c05a72f47187888fdbc241cf911322ec751a13a66445cde8
sha "$CELLGATES/termeval.py" b64897421d5b1dd634a7d49986ea9503538b035a9c356381592a1c3dea3749b0
sha "$SHADOWGATE/shadowcheck.py" e04173f5a5a50913ad205152cde41f4759aff4c1ca0bd521ff32c9b3616abcb7
sha "$SHADOWGATE/termeval.py" 85060f6c7558815c5eff2149aefeab395e8e6a34b89393b38fc03013c95fa829
sha "$COVCHECK" 595119b27d0c715a6e99b21688b110154aeb7d230d7d0a29d99717c7a3370c12

# inputs from git: the base lib, the cgif donor lib, the codeptr control script and its nm texts
mkdir -p "$WORK"
LIB=$WORK/base/proofs/libreac/fuzz_disco/lib
CLIB=$WORK/cgif/proofs/cgif/cgif_file_fuzzer/lib
if [ ! -f "$WORK/inputs.ok" ]; then
  rm -rf "$WORK/base" "$WORK/cgif" "$WORK/ctl"; mkdir -p "$WORK/base" "$WORK/cgif" "$WORK/ctl/syms"
  git -C "$GIT" archive "$BASE" proofs/libreac/fuzz_disco/lib | tar -x -C "$WORK/base" || exit 2
  git -C "$GIT" archive "$CGIF_REF" proofs/cgif/cgif_file_fuzzer/lib | tar -x -C "$WORK/cgif" || exit 2
  git -C "$GIT" show "$CTL_REF:tools/startup/codeptr-controls.sh" > "$WORK/ctl/codeptr-controls.sh" || exit 2
  for b in asan asan-ubsan; do
    git -C "$GIT" show "$CTL_REF:tools/startup/syms/cgif_file_fuzzer.$b.nm" > "$WORK/ctl/syms/cgif_file_fuzzer.$b.nm" || exit 2
  done
  touch "$WORK/inputs.ok"
fi
sha "$WORK/ctl/codeptr-controls.sh" 25c012a65b96fe16406ee979efb146b6bd266770739bbedfc3b57f5fd54e3c03
sha "$WORK/ctl/syms/cgif_file_fuzzer.asan-ubsan.nm" 5b5f81784ea1ed5e8d35ab9bd5b01277536c10addbe4b545ca3f223045c95a75
CGIF_NM=$WORK/ctl/syms/cgif_file_fuzzer.asan-ubsan.nm

plant() {  # plant SRC DST OLD NEW: DST = SRC with the one occurrence of OLD replaced by NEW (OLD must occur once)
  mkdir -p "$(dirname "$2")"
  python3 - "$@" <<'EOF' || exit 2
import sys
src, dst, old, new = sys.argv[1:5]
t = open(src).read()
if t.count(old) != 1:
    sys.exit('run.sh: plant: %r occurs %d times in %s' % (old, t.count(old), src))
open(dst, 'w').write(t.replace(old, new))
EOF
}
fr() { (cd "$STARTUP_SET" && bash frozen-run.sh startup-set-2026-10-30d.tsv "$@"); }
want() { grep -qF -- "$2" "$1" || bad "$3: '$2' not in $(basename "$1")"; }   # want FILE TEXT LABEL
on() { [[ " $GATES " == *" $1 "* ]]; }

PAC_IMG=(--src-image A="$CGIF_BIN/cgif_file_fuzzer.asan" --src-image B="$CGIF_B"
  --src-image P="$CGIF_BIN/cgif_file_fuzzer.plain" --src-image U="$CGIF_BIN/cgif_file_fuzzer.ubsan"
  --dst-image A="$PIN_A" --dst-image B="$PIN_B" --dst-image P="$PIN_DIR/fuzz_disco.plain"
  --dst-image U="$PIN_DIR/fuzz_disco.ubsan")
if on g1; then
  note "g1: port_addr_check efa19b81e92b over lib/Reusable/Y* (about 30 minutes)"
  mkdir -p "$WORK/g1/plant/lib/Reusable"
  nice -n 10 python3 "$PAC" --git "$GIT" --donors-from "$DONORS" --summary --fail-on-flags \
    --src "$CGIF_REF:proofs/cgif/cgif_file_fuzzer/lib" --dst "$BASE:proofs/libreac/fuzz_disco/lib" \
    --paired-only --map A/=A/ --map =Reusable/ "${PAC_IMG[@]}" --assign '**=auto' --include 'Y*.v' \
    --cache "$WORK/g1/cache" --out "$WORK/g1/pac-Y.tsv" > "$WORK/g1/pac.out" 2> "$WORK/g1/pac.err"
  rc=$?; [ $rc -eq 4 ] || bad "g1 rc $rc (want 4: findings, each triaged)"
  want "$WORK/g1/pac.out" 'count files paired: 836' g1
  want "$WORK/g1/pac.err" 'FLAGGED 27544 rows in 13 classes' g1
  python3 "$HERE/g1_triage.py" --pac-tsv "$WORK/g1/pac-Y.tsv" --pac "$PAC" --lib "$LIB" --cgif-lib "$CLIB" \
    --pin-b "$PIN_B" --twin-b "$TWIN_B" --pin-p "$PIN_DIR/fuzz_disco.plain" --twin-p "$TWIN_DIR/fuzz_disco.plain" \
    --cgif-b "$CGIF_B" --cgif-p "$CGIF_BIN/cgif_file_fuzzer.plain" --out "$WORK/g1/G1-flagged-rows.tsv" 2> "$WORK/g1/triage.err"
  rc=$?; [ $rc -eq 0 ] || bad "g1 triage rc $rc (an UNTRIAGED or DEFECT row)"
  cmp "$WORK/g1/G1-flagged-rows.tsv" "$HERE/G1-flagged-rows.tsv" || bad "g1 G1-flagged-rows.tsv differs"
  # lib/Y and lib/B: cgif has no such subtree, zero files pair (rc 3)
  python3 "$PAC" --git "$GIT" --donors-from "$DONORS" --summary --fail-on-flags \
    --src "$CGIF_REF:proofs/cgif/cgif_file_fuzzer/lib" --dst "$BASE:proofs/libreac/fuzz_disco/lib" \
    --paired-only --map Y/=Y/ --map B/=B/ "${PAC_IMG[@]}" --assign '**=auto' --include 'Y/**' --include 'B/**' \
    --cache "$WORK/g1/cache" --out "$WORK/g1/yb.tsv" > "$WORK/g1/yb.out" 2> "$WORK/g1/yb.err"
  rc=$?; [ $rc -eq 3 ] || bad "g1 lib/Y lib/B run rc $rc (want 3: zero files paired)"
  # planted control: line 474 of YE23.v, buf+0x8 moved by 16
  python3 - "$LIB/Reusable/YE23.v" "$WORK/g1/plant/lib/Reusable/YE23.v" <<'EOF' || exit 2
import sys
L = open(sys.argv[1]).read().split('\n')
assert L[473].count('Z_to_bv 64 6277920;') == 1
L[473] = L[473].replace('Z_to_bv 64 6277920;', 'Z_to_bv 64 6277936;')
open(sys.argv[2], 'w').write('\n'.join(L))
EOF
  python3 "$PAC" --git "$GIT" --donors-from "$DONORS" --summary --fail-on-flags \
    --src "$CGIF_REF:proofs/cgif/cgif_file_fuzzer/lib" --dst "$WORK/g1/plant/lib" \
    --paired-only --map A/=A/ --map =Reusable/ "${PAC_IMG[@]}" --assign '**=auto' --include 'YE23.v' \
    --cache "$WORK/g1/cache" --out "$WORK/g1/plant.tsv" > "$WORK/g1/plant.out" 2> "$WORK/g1/plant.err"
  rc=$?; [ $rc -eq 4 ] || bad "g1 planted control rc $rc (want 4)"
  want "$WORK/g1/plant.err" 'FLAGGED 19 rows' "g1 planted control"
  awk -F'\t' '$6 == "Reusable/YE23.v" && $7 == "474" && $1 == "NON-ADDRESS-CHANGED" && $12 == "0x5fcb30"' \
    "$WORK/g1/plant.tsv" | grep -q . || bad "g1 planted control: no flagged row at YE23.v:474"
fi

if on g2; then
  note "g2: donor_decimals (new version) on lib/Reusable, lib/Y, lib/B; controls; funnel"
  D="$HERE/donordec"
  mkdir -p "$WORK/g2/plantrepo/proofs/libreac/fuzz_disco/lib/Reusable"
  DD=(--git "$GIT" --kit "$KIT5033" --donors-from "$DONORS" --cache "$WORK/g2/cache"
      --cgif-image asan="$CGIF_BIN/cgif_file_fuzzer.asan" --cgif-image asan-ubsan="$CGIF_B"
      --target-image asan="$PIN_A:$TWIN_A" --target-image asan-ubsan="$PIN_B:$TWIN_B")
  nice -n 10 python3 "$D/donor_decimals.py" "${DD[@]}" --target disco --subdirs Reusable,Y,B --tree "base=$BASE" \
    --out "$WORK/g2/scan_Y.tsv" 2> "$WORK/g2/scan.err" || bad "g2 scan rc $?"
  nice -n 10 python3 "$D/donor_decimals.py" "${DD[@]}" --target cgif --subdirs '' \
    --tree "cgif=$CGIF_REF:proofs/cgif/cgif_file_fuzzer/lib" --out "$WORK/g2/control_neg.tsv" 2> "$WORK/g2/neg.err" \
    || bad "g2 negative control rc $?"
  sed -n 471p "$CLIB/A/AE23.v" > "$WORK/g2/plant_AE23.v"
  sha "$WORK/g2/plant_AE23.v" a290a03d66dcf4fb3e1a5378f4f7e5dfe3bd25759dc7837f409ba733090d8bd2
  python3 "$D/donor_decimals.py" "${DD[@]}" --target disco --subdirs A --tree "none=$BASE@$BASE" \
    --plant "$WORK/g2/plant_AE23.v" --out "$WORK/g2/control_pos_AE23.tsv" 2> "$WORK/g2/posa.err" || bad "g2 AE23 control rc $?"
  P="$WORK/g2/plantrepo"
  python3 - "$LIB/Reusable/YE23.v" "$P/proofs/libreac/fuzz_disco/lib/Reusable/YE23.v" <<'EOF' || exit 2
import sys
L = open(sys.argv[1]).read().split('\n')
assert 'Z_to_bv 64 6277920' in L[473]
L[473] = L[473].replace('Z_to_bv 64 6277920', 'Z_to_bv 64 6265120')
open(sys.argv[2], 'w').write('\n'.join(L))
EOF
  (cd "$P" && rm -rf .git && git init -q && git add -A && git -c user.name=plant -c user.email= -c commit.gpgsign=false \
    commit -qm plant) || exit 2
  python3 "$D/donor_decimals.py" "${DD[@]}" --git "$P" --target disco --subdirs Reusable --tree plant=HEAD \
    --out "$WORK/g2/control_pos_YE23.tsv" 2> "$WORK/g2/posy.err" || bad "g2 YE23 control rc $?"
  python3 "$D/funnel.py" "${DD[@]}" "$WORK/g2/scan_Y.tsv" --cgif-lib "$CGIF_REF:proofs/cgif/cgif_file_fuzzer/lib" \
    > "$WORK/g2/funnel_Y.txt" 2> "$WORK/g2/funnel.err" || bad "g2 funnel rc $?"
  for t in scan_Y.tsv control_neg.tsv control_pos_AE23.tsv control_pos_YE23.tsv funnel_Y.txt; do
    cmp "$WORK/g2/$t" "$D/$t" || bad "g2 $t differs"
  done
fi
if on g3; then
  note "g3: codeptr 12348302dfd2, the control of record first"
  mkdir -p "$WORK/g3/ctlroot/projects/cgif/bin" "$WORK/g3/plant/Reusable"
  ln -sfn "$WORK/cgif/proofs" "$WORK/g3/ctlroot/proofs"
  ln -sfn "$CGIF_BIN" "$WORK/g3/ctlroot/projects/cgif/bin/cgif_file_fuzzer"
  ln -sf "$STARTUP_SET/frozen-run.sh" "$WORK/ctl/frozen-run.sh"
  bash "$WORK/ctl/codeptr-controls.sh" "$STARTUP_SET/startup-set-2026-10-30d.tsv" "$WORK/g3/ctlroot" > "$WORK/g3/ctl.out" 2>&1
  rc=$?; [ $rc -eq 0 ] || bad "g3 control of record rc $rc"
  want "$WORK/g3/ctl.out" 'codeptr-controls: PASS (must-find paired on all 6 files; must-not-flag 0x8065e)' g3
  want "$WORK/g3/ctl.out" 'codeptr: self-test: 27 known answers' g3
  # per-file declarations, each read from the file's own text (G3-codeptr.md gives the line of each)
  GP='gp: the value of register x3 (__global_pointer$ = 0x10800 in the image B twin .symtab), a layout constant both images link the same'
  KD='a KDisj region length (the length argument after a region base), not an address'
  LEN1M='a length: KDisj region lengths, am_len mapping lengths, (base, length) mapping-list entries and the 8-byte size value at __asan::instance+808 (0xa6140), not an address'
  LENMAP='a length: KDisj region lengths, am_len mapping lengths and (base, length) mapping-list entries, not an address'
  FLAGS='three bool flag bytes 01 01 01 at __asan::asan_flags_dont_use_directly+112 (0xa6ce8), not an address'
  R10310='start of the image B region [0x10310,0x10338) CImg 40 in its .rodata (0x102e0 + 48), from the image B collector run; the cgif region there is CImg 24'
  D_YB01=(--same "0x10800=$GP" --not-address "0x20000=$KD" --not-address "0x71c00=$KD" --not-address "0x100000=$LEN1M"
    --not-address "0x161200=$KD" --not-address "0x38e000=$LENMAP")
  D_YB03=(--same "0x10800=$GP" --not-address "0x10101=a 4-byte KWord value: $FLAGS"
    --not-address '0x1ffff=KRange upper bound 131071 on a symbolic value, not an address'
    --not-address '0x445c0=KRange upper bound 280000 on a symbolic value, not an address'
    --not-address "0x71c00=$KD" --not-address "0x100000=$LEN1M" --not-address "0x38e000=$LENMAP"
    --not-address '0x100018=a KZero length (1048600 bytes), not an address'
    --not-address '0x3fffff=KRange tid bound 1..4194303 on a symbolic value, not an address')
  D_YB05=(); D_YB12=(); D_YCej=(); D_YB1q=(); D_YF0l=()
  D_YD1k=(--same "0x10310=$R10310")
  D_YD2i=(--same "0x10800=$GP" --not-address '0x3fffff=the tid bound 1..4194303 (KRange (EVar TIDV), Lemma tid_range, mkAF), not an address')
  D_YD2j=(--same "0x10310=$R10310")
  D_YF0m=(--same "0x10800=$GP" --not-address "0x10101=a z8 cell content: $FLAGS")
  D_YB13=(--not-address '0x20000=page span of PT_LOAD 1 (0x10000..0x30000) of the image B pin, a length'
    --not-address '0x55c000=page span of PT_LOAD 4 (0xa2000..0x5fe000) of the image B pin, a length')
  CP=(--image "$PIN_B" --names "$TWIN_B" --stale-image "$CGIF_B" --stale-names "$CGIF_NM" --stale-dir "$CLIB")
  for f in YB01 YB03 YB05 YB12 YD1k YD2i YD2j YF0m YCej YB13 YB1q YF0l; do
    eval "D=(\"\${D_$f[@]}\")"
    fr codeptr.py "${CP[@]}" "${D[@]}" "$LIB/Reusable/$f.v" > "$WORK/g3/$f.out" 2>&1
    rc=$?; [ $rc -eq 0 ] || bad "g3 $f rc $rc"
    want "$WORK/g3/$f.out" ', 0 FINDINGS [stale against cgif_file_fuzzer.asan-ubsan' "g3 $f"
  done
  plant "$LIB/Reusable/YF0m.v" "$WORK/g3/plant/Reusable/YF0m.v" 'Definition TFIB_MAIN : Z := 0x80b1c.' 'Definition TFIB_MAIN : Z := 0x80020.'
  fr codeptr.py "${CP[@]}" "${D_YF0m[@]}" "$WORK/g3/plant/Reusable/YF0m.v" > "$WORK/g3/plant.out" 2>&1
  rc=$?; [ $rc -eq 1 ] || bad "g3 planted control rc $rc (want 1)"
  want "$WORK/g3/plant.out" '1 FINDINGS: 0x80020 [stale against' "g3 planted control"
fi

if on g4; then
  note "g4: ifchk f5cde600cc18"
  mkdir -p "$WORK/g4/plant"
  fr ifchk.py --owned "$LIB/Reusable/YF0m.v" --states "$LIB/Reusable/YB01.v" --ad1g "$LIB/Reusable/YD1g.v" --image "$PIN_B" > "$WORK/g4/ifchk.out" 2>&1
  rc=$?; [ $rc -eq 0 ] || bad "g4 rc $rc"
  want "$WORK/g4/ifchk.out" 'ifchk: 1461 cells (sym 22, abs 853, shadow 586) x 50 states: 73050 = stated, 0 different, 0 undetermined (None), 0 inexpressible' g4
  plant "$LIB/Reusable/YF0m.v" "$WORK/g4/plant/YF0m.v" 'z8 (ANum 0xa2618) 0x99478    ].' 'z8 (ANum 0xa2618) 0x99479    ].'
  fr ifchk.py --owned "$WORK/g4/plant/YF0m.v" --states "$LIB/Reusable/YB01.v" --ad1g "$LIB/Reusable/YD1g.v" --image "$PIN_B" > "$WORK/g4/plant.out" 2>&1
  rc=$?; [ $rc -eq 1 ] || bad "g4 planted control rc $rc (want 1)"
  want "$WORK/g4/plant.out" '73000 = stated, 50 different' "g4 planted control"
fi

if on g5; then
  note "g5: cellcheck / shadowcheck / ownedcheck / covcheck on YF0m"
  TOP=$(python3 - "$PIN_B" <<'EOF'
import struct, sys
b = open(sys.argv[1], 'rb').read(); ph = struct.unpack_from('<Q', b, 32)[0]; es, n = struct.unpack_from('<HH', b, 54)
L = [struct.unpack_from('<IIQQQQQQ', b, ph + i * es) for i in range(n)]
print(hex((max(v + m for t, _, _, v, _, _, m, _ in L if t == 1) + 0xfff) & ~0xfff))
EOF
)
  [ "$TOP" = 0x5fe000 ] || bad "g5 IMG_TOP from the pin's PT_LOADs is $TOP, not 0x5fe000"
  Y=$LIB/Reusable/YF0m.v
  mkdir -p "$WORK/g5/stage/Reusable" "$WORK/g5/plant-cell/Reusable" "$WORK/g5/plant"
  cp "$Y" "$WORK/g5/stage/Reusable/YF0m.v"
  python3 "$CELLGATES/cellcheck.py" "$WORK/g5/stage" "$PIN_B" > "$WORK/g5/cell.out" 2>&1
  rc=$?; [ $rc -eq 0 ] || bad "g5 cellcheck rc $rc"; want "$WORK/g5/cell.out" '# 743 file-backed cells, 0 mismatch' g5
  python3 "$SHADOWGATE/shadowcheck.py" "$TWIN_B" "$Y" "IMG_TOP=$TOP" > "$WORK/g5/shadow.out" 2>&1
  rc=$?; [ $rc -eq 0 ] || bad "g5 shadowcheck rc $rc"
  want "$WORK/g5/shadow.out" 'Tfib_const_shadow: 586 cells, 0 wrong' g5
  want "$WORK/g5/shadow.out" 'Tfib_zero_shadow: 25 ranges, 0 poisoned granules inside, 0 unparsed' g5
  python3 "$CELLGATES/ownedcheck.py" "$Y" "IMG_TOP=$TOP" --elf "$TWIN_B" > "$WORK/g5/owned.out" 2>&1
  rc=$?; [ $rc -eq 0 ] || bad "g5 ownedcheck rc $rc"
  want "$WORK/g5/owned.out" 'owned ranges 85, const cells 1439, UNOWNED 0, OVERCLAIM 0, UNPARSED 0' g5
  want "$WORK/g5/owned.out" 'image bounds: OK' g5
  python3 "$COVCHECK" "$Y" "IMG_TOP=$TOP" > "$WORK/g5/cov.out" 2>&1
  rc=$?; [ $rc -eq 0 ] || bad "g5 covcheck rc $rc"
  want "$WORK/g5/cov.out" 'Tfib_const_abs: 853 cells; Tfib_owned_static: 85 ranges; 0 uncovered' g5
  # planted controls: a flipped file-backed cell, a flipped shadow cell, a const cell moved into .text
  plant "$Y" "$WORK/g5/plant-cell/Reusable/YF0m.v" 'z8 (ANum 0xa2618) 0x99478    ].' 'z8 (ANum 0xa2618) 0x99479    ].'
  plant "$Y" "$WORK/g5/plant/YF0m.shadow.v" 'z1 (ANum 0x7fffc1f4) 0xf9  ;' 'z1 (ANum 0x7fffc1f4) 0xf8  ;'
  plant "$Y" "$WORK/g5/plant/YF0m.owned.v" 'z8 (ANum 0x13afa8) 0x1  ;' 'z8 (ANum 0x40000) 0x1  ;'
  python3 "$CELLGATES/cellcheck.py" "$WORK/g5/plant-cell" "$PIN_B" > "$WORK/g5/cell.plant.out" 2>&1
  rc=$?; [ $rc -eq 1 ] || bad "g5 cellcheck control rc $rc (want 1)"; want "$WORK/g5/cell.plant.out" '# 743 file-backed cells, 1 mismatch' g5
  python3 "$SHADOWGATE/shadowcheck.py" "$TWIN_B" "$WORK/g5/plant/YF0m.shadow.v" "IMG_TOP=$TOP" > "$WORK/g5/shadow.plant.out" 2>&1
  rc=$?; [ $rc -eq 1 ] || bad "g5 shadowcheck control rc $rc (want 1)"; want "$WORK/g5/shadow.plant.out" 'Tfib_const_shadow: 586 cells, 1 wrong' g5
  python3 "$CELLGATES/ownedcheck.py" "$WORK/g5/plant/YF0m.owned.v" "IMG_TOP=$TOP" --elf "$TWIN_B" > "$WORK/g5/owned.plant.out" 2>&1
  rc=$?; [ $rc -eq 1 ] || bad "g5 ownedcheck control rc $rc (want 1)"; want "$WORK/g5/owned.plant.out" 'UNOWNED Tfib_const_abs: cell 0x40000/8' g5
  python3 "$COVCHECK" "$WORK/g5/plant/YF0m.owned.v" "IMG_TOP=$TOP" > "$WORK/g5/cov.plant.out" 2>&1
  rc=$?; [ $rc -eq 1 ] || bad "g5 covcheck control rc $rc (want 1)"; want "$WORK/g5/cov.plant.out" 'UNCOVERED const cell 0x40000 width 8' g5
fi

if on g6; then
  note "g6: kimg_overlap 5db341e3cd62"
  mkdir -p "$WORK/g6/plant"
  for f in YB05 YF0m YD1k YB01 YB03 YD2j; do
    python3 "$KIMG" "$GIT" "$BASE" "proofs/libreac/fuzz_disco/lib/Reusable/$f.v" "$PIN_B" \
      --donor "$CGIF_REF:proofs/cgif/cgif_file_fuzzer/lib/$f.v" "$CGIF_B" > "$WORK/g6/$f.out" 2>&1
    rc=$?; [ $rc -eq 0 ] || bad "g6 $f rc $rc"
    want "$WORK/g6/$f.out" 'overlapping write bytes 0  contradicting bytes 0' "g6 $f"
  done
  want "$WORK/g6/YB01.out" 'states: 50, aliases 0, duplicate states 0' g6
  want "$WORK/g6/YB01.out" 'KImg ranges: 139, findings 0' g6
  want "$WORK/g6/YB03.out" 'KImg ranges: 66, findings 0' g6
  want "$WORK/g6/YD2j.out" 'regions: 81, MISMATCH 0, by design (donor same shape) 0, broken with no donor region 0' g6
  # YB05 / YF0m / YD1k: nothing the tool reads. The planted overlap below does NOT fire: the gate is VOID on them.
  plant "$LIB/Reusable/YD1k.v" "$WORK/g6/plant/YD1k.v" 'apply (CH R_A1c 66320 40)' 'apply (CH R_A1c 66300 40)'
  plant "$LIB/Reusable/YD2j.v" "$WORK/g6/plant/YD2j.v" '[ mkChunk 66320 (CImg 40) ]' '[ mkChunk 66300 (CImg 40) ]'
  plant "$LIB/Reusable/YB01.v" "$WORK/g6/plant/YB01.v" 'KWord {| a_base := ELit 0; a_off := 683312 |} 8 (ELit 0)' \
    'KWord {| a_base := ELit 0; a_off := 66320 |} 8 (ELit 0)'
  for f in YD1k YD2j YB01; do
    python3 "$KIMG" "$GIT" FILE "$WORK/g6/plant/$f.v" "$PIN_B" \
      --donor "$CGIF_REF:proofs/cgif/cgif_file_fuzzer/lib/$f.v" "$CGIF_B" > "$WORK/g6/plant_$f.out" 2>&1
    echo "rc $?" >> "$WORK/g6/plant_$f.out"
  done
  want "$WORK/g6/plant_YD1k.out" 'rc 0' "g6 YD1k control (expected NOT to fire: VOID)"
  want "$WORK/g6/plant_YD2j.out" "('R_A1c', '0x10310', '0x10338', ['chunk at 66300 overlaps or precedes 66320'])" "g6 YD2j control"
  want "$WORK/g6/plant_YD2j.out" 'rc 2' "g6 YD2j control"
  want "$WORK/g6/plant_YB01.out" 'overlapping write bytes 8  contradicting bytes 3' "g6 YB01 control"
  want "$WORK/g6/plant_YB01.out" 'rc 1' "g6 YB01 control"
fi

lplant() {  # lplant SRC DST LINE OLD NEW: DST = SRC with OLD on line LINE replaced by NEW (OLD must occur once there)
  mkdir -p "$(dirname "$2")"
  python3 - "$@" <<'EOF' || exit 2
import sys
src, dst, ln, old, new = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4], sys.argv[5]
L = open(src).read().split('\n')
if L[ln - 1].count(old) != 1:
    sys.exit('run.sh: lplant: %r occurs %d times on line %d of %s' % (old, L[ln - 1].count(old), ln, src))
L[ln - 1] = L[ln - 1].replace(old, new)
open(dst, 'w').write('\n'.join(L))
EOF
}
pac3() {  # pac3 DST_LIB INCLUDE OUT [CACHE]: port_addr_check 3d2eee813cce with G1's arguments on DST_LIB
  nice -n 10 python3 "$PAC3" --git "$GIT" --donors-from "$DONORS" --summary --fail-on-flags \
    --src "$CGIF_REF:proofs/cgif/cgif_file_fuzzer/lib" --dst "$1" --paired-only --map A/=A/ --map =Reusable/ \
    "${PAC_IMG[@]}" --assign '**=auto' --include "$2" --cache "${4:-$WORK/g7/cache}" --out "$3.tsv" > "$3.out" 2> "$3.err"
}
rows() { grep -v '^#' "$1"; }   # the rows of a port_addr_check table, without its # header lines

if on g7; then
  need PAC3
  sha "$PAC3" 3d2eee813cce41c92be6131e56292d73e473d2582156655895ff2a1ce5c73b82
  note "g7: port_addr_check 3d2eee813cce, G1's command (about 10 minutes, fresh cache)"
  mkdir -p "$WORK/g7"
  pac3 "$BASE:proofs/libreac/fuzz_disco/lib" 'Y*.v' "$WORK/g7/pac3-Y"
  rc=$?; [ $rc -eq 4 ] || bad "g7 rc $rc (want 4: findings, each triaged)"
  want "$WORK/g7/pac3-Y.out" 'count files paired: 836' g7
  want "$WORK/g7/pac3-Y.err" 'FLAGGED 27544 rows in 13 classes' g7
  if [ -f "$WORK/g1/pac-Y.tsv" ]; then
    cmp <(rows "$WORK/g7/pac3-Y.tsv") <(rows "$WORK/g1/pac-Y.tsv") || bad "g7 rows differ from g1's (recorded: 0 rows)"
  else
    note "g7: row diff against g1 skipped (no \$WORK/g1/pac-Y.tsv: run g1 in the same WORK)"
  fi
  python3 "$HERE/g1_triage.py" --pac-tsv "$WORK/g7/pac3-Y.tsv" --pac "$PAC3" --lib "$LIB" --cgif-lib "$CLIB" \
    --pin-b "$PIN_B" --twin-b "$TWIN_B" --pin-p "$PIN_DIR/fuzz_disco.plain" --twin-p "$TWIN_DIR/fuzz_disco.plain" \
    --cgif-b "$CGIF_B" --cgif-p "$CGIF_BIN/cgif_file_fuzzer.plain" --out "$WORK/g7/flagged-rows.tsv" 2> "$WORK/g7/triage.err"
  rc=$?; [ $rc -eq 0 ] || bad "g7 triage rc $rc (an UNTRIAGED or DEFECT row)"
  cmp "$WORK/g7/flagged-rows.tsv" "$HERE/G1-flagged-rows.tsv" || bad "g7 triage differs from G1-flagged-rows.tsv"
  lplant "$LIB/Reusable/YE23.v" "$WORK/g7/plant/lib/Reusable/YE23.v" 474 'Z_to_bv 64 6277920;' 'Z_to_bv 64 6277936;'
  pac3 "$WORK/g7/plant/lib" 'YE23.v' "$WORK/g7/plant"
  rc=$?; [ $rc -eq 4 ] || bad "g7 planted control rc $rc (want 4)"
  want "$WORK/g7/plant.err" 'FLAGGED 19 rows' "g7 planted control"
  awk -F'\t' '$6 == "Reusable/YE23.v" && $7 == "474" && $1 == "NON-ADDRESS-CHANGED" && $12 == "0x5fcb30"' \
    "$WORK/g7/plant.tsv" | grep -q . || bad "g7 planted control: no flagged row at YE23.v:474"
fi

if on g8; then
  need PAC3 RC2 RC1 CGIF_TWIN_DIR
  sha "$PAC3" 3d2eee813cce41c92be6131e56292d73e473d2582156655895ff2a1ce5c73b82
  sha "$RC2" 32b39f3b34e97818cd71be57afda15f6aba21ede5fe2d1016f939ede19ac26cc
  sha "$RC1" 8ad299147f2e67fbeb40ee47592152377082e6c55e745a16d9b45b65d84e27b3
  sha "$TWIN_DIR/fuzz_disco.ubsan" e2a41feb2f469916be4d94d237ae7215c4b1166e54f6ebf8365eb77422dbb410
  sha "$CGIF_TWIN_DIR/cgif_file_fuzzer.asan" 488e39500746294ebe16fb1333e50c52e2339671de22f7768a37232aaeb05ad1
  sha "$CGIF_TWIN_DIR/cgif_file_fuzzer.asan-ubsan" ce511d541cdabbe3c8df3f672dc517e8b5a7edd37b280a7483043b438de0adf7
  sha "$CGIF_TWIN_DIR/cgif_file_fuzzer.plain" 6ab540c4310895746cf793737943910fc77953f25cbe15396213e0249b04d59b
  sha "$CGIF_TWIN_DIR/cgif_file_fuzzer.ubsan" 101571498dad1c99ab0f44c55681a8b715337f4e9b3543e75b9c8e36ba8d547f
  [ -f "$WORK/g7/pac3-Y.tsv" ] || { echo "run.sh: g8 reads g7's table: run g7 first in the same WORK" >&2; exit 2; }
  note "g8: roundconst v2 on g7's table, its controls, rc_triage.py"
  mkdir -p "$WORK/g8"
  CG=(); TG=(); RCS=""; RCT=""
  for kb in A:asan B:asan-ubsan P:plain U:ubsan; do
    k=${kb%%:*}; b=${kb#*:}
    RCS="$RCS${RCS:+,}$k=$CGIF_BIN/cgif_file_fuzzer.$b:$CGIF_TWIN_DIR/cgif_file_fuzzer.$b"
    RCT="$RCT${RCT:+,}$k=$PIN_DIR/fuzz_disco.$b:$TWIN_DIR/fuzz_disco.$b"
    CG+=(--donor "$k=$CGIF_BIN/cgif_file_fuzzer.$b:$CGIF_TWIN_DIR/cgif_file_fuzzer.$b")
    TG+=(--img "$k=$PIN_DIR/fuzz_disco.$b:$TWIN_DIR/fuzz_disco.$b")
  done
  RCS1=$(echo "$RCS" | sed -E 's/:[^,]*//g'); RCT1=$(echo "$RCT" | sed -E 's/:[^,]*//g')
  gzip -kf "$WORK/g7/pac3-Y.tsv"
  nice python3 "$RC2" "$WORK/g7/pac3-Y.tsv.gz" "$RCS" "$RCT" "$WORK/g8/rc-Y" > "$WORK/g8/rc-Y.out" 2>&1 || bad "g8 roundconst rc $?"
  want "$WORK/g8/rc-Y.out" 'selected 239221 kept rows' g8
  python3 "$HERE/rc_triage.py" --rc-tsv "$WORK/g8/rc-Y.tsv" --roundconst "$RC2" --lib "$LIB" --cgif-lib "$CLIB" \
    "${TG[@]}" "${CG[@]}" --out "$WORK/g8/G8-rows.tsv" 2> "$WORK/g8/triage.err"
  rc=$?; [ $rc -eq 0 ] || bad "g8 rc_triage rc $rc (an UNTRIAGED or DEFECT row)"
  cmp "$WORK/g8/G8-rows.tsv" "$HERE/G8-rows.tsv" || bad "g8 G8-rows.tsv differs"
  # control 1: donor on donor (port_addr_check of cgif's lib against itself, cgif images on both sides)
  CIMG=(--src-image A="$CGIF_BIN/cgif_file_fuzzer.asan" --src-image B="$CGIF_B" --src-image P="$CGIF_BIN/cgif_file_fuzzer.plain"
    --src-image U="$CGIF_BIN/cgif_file_fuzzer.ubsan" --dst-image A="$CGIF_BIN/cgif_file_fuzzer.asan" --dst-image B="$CGIF_B"
    --dst-image P="$CGIF_BIN/cgif_file_fuzzer.plain" --dst-image U="$CGIF_BIN/cgif_file_fuzzer.ubsan")
  nice -n 10 python3 "$PAC3" --git "$GIT" --donors-from "$DONORS" --summary --fail-on-flags \
    --src "$CGIF_REF:proofs/cgif/cgif_file_fuzzer/lib" --dst "$CGIF_REF:proofs/cgif/cgif_file_fuzzer/lib" --paired-only \
    "${CIMG[@]}" --assign '**=auto' --include 'Y*.v' --cache "$WORK/g8/cache-self" --out "$WORK/g8/self.tsv" \
    > "$WORK/g8/self.out" 2> "$WORK/g8/self.err"
  want "$WORK/g8/self.out" 'count files paired: 1449' "g8 control 1"
  gzip -kf "$WORK/g8/self.tsv"
  nice python3 "$RC2" "$WORK/g8/self.tsv.gz" "$RCS" "$RCS" "$WORK/g8/rc-self" > "$WORK/g8/rc-self.out" 2>&1 \
    || bad "g8 control 1 roundconst rc $?"
  want "$WORK/g8/rc-self.out" 'selected 504706 kept rows' "g8 control 1"
  [ "$(awk -F'\t' 'NR > 1 && $1 != "SAME"' "$WORK/g8/rc-self.tsv" | wc -l)" = 0 ] || bad "g8 control 1: a non-SAME row"
  # controls 2-5: one numeral set back to the donor's in a copy of one file; the same file unplanted beside it
  while IFS='|' read -r p f ln old new pos val want1; do
    lplant "$LIB/Reusable/$f" "$WORK/g8/$p/plant/lib/Reusable/$f" "$ln" "$old" "$new"
    mkdir -p "$WORK/g8/$p/base/lib/Reusable"; cp "$LIB/Reusable/$f" "$WORK/g8/$p/base/lib/Reusable/$f"
    for s in base plant; do
      pac3 "$WORK/g8/$p/$s/lib" "$f" "$WORK/g8/$p/$s-pac" "$WORK/g8/cache-$p-$s"
      gzip -kf "$WORK/g8/$p/$s-pac.tsv"
      nice python3 "$RC2" "$WORK/g8/$p/$s-pac.tsv.gz" "$RCS" "$RCT" "$WORK/g8/$p/$s-v2" > /dev/null 2>&1 || bad "g8 $p v2 rc"
      nice python3 "$RC1" "$WORK/g8/$p/$s-pac.tsv.gz" "$RCS1" "$RCT1" "$WORK/g8/$p/$s-v1" > /dev/null 2>&1 || bad "g8 $p v1 rc"
    done
    nb() { awk -F'\t' -v s="$2" 'NR > 1 && $1 == s' "$1" | wc -l; }
    if [ "$p" = rc5 ]; then
      [ $(( $(nb "$WORK/g8/$p/plant-v2.tsv" SAME) - $(nb "$WORK/g8/$p/base-v2.tsv" SAME) )) = 1 ] || bad "g8 $p: not one SAME more"
      [ "$(awk -F'\t' 'NR > 1 && $1 != "SAME"' "$WORK/g8/$p/plant-v2.tsv" | sort)" = \
        "$(awk -F'\t' 'NR > 1 && $1 != "SAME"' "$WORK/g8/$p/base-v2.tsv" | sort)" ] || bad "g8 $p: non-SAME rows changed"
    else
      [ $(( $(nb "$WORK/g8/$p/plant-v2.tsv" MISMATCH) - $(nb "$WORK/g8/$p/base-v2.tsv" MISMATCH) )) = 1 ] \
        || bad "g8 $p: not one MISMATCH more"
      awk -F'\t' -v w="Reusable/$f:$ln" -v v="$val" '$1 == "MISMATCH" && $4 == w && $9 == v' "$WORK/g8/$p/plant-v2.tsv" \
        | grep -q . || bad "g8 $p: no MISMATCH row at $f:$ln"
    fi
    d1=$(( $(nb "$WORK/g8/$p/plant-v1.tsv" MISMATCH) - $(nb "$WORK/g8/$p/base-v1.tsv" MISMATCH) ))
    [ "$d1" = "$want1" ] || bad "g8 $p: v1 gives $d1 MISMATCH more (recorded $want1)"
  done <<'EOF'
rc2|YB1h.v|47|Z_to_bv 64 0x70000)|Z_to_bv 64 0x6d000)|7|0x6d000|1
rc3|YN06.v|513|unch (201312 + o)|unch (164 + o)|0|0xa4|0
rc4|YB01.v|189|++ seg HS_tfib_11_kn 387 1|++ seg HS_tfib_11_kn 212 1|10|0xd4|0
rc5|YE37.v|35|(0xa5160, 3136, [|(0xa5160, 192, [|48|0xc0|0
EOF
fi

if on g9; then
  need CGIF_TWIN_DIR
  [ -f "$WORK/g7/pac3-Y.tsv" ] || { echo "run.sh: g9 reads g7's table: run g7 first in the same WORK" >&2; exit 2; }
  note "g9: count_recompute.py over lib/Reusable/Y*.v, planted control"
  mkdir -p "$WORK/g9"
  gzip -kf "$WORK/g7/pac3-Y.tsv"
  CR=()
  for kb in A:asan B:asan-ubsan P:plain U:ubsan; do
    k=${kb%%:*}; b=${kb#*:}
    CR+=(--pin "$k=$PIN_DIR/fuzz_disco.$b" --twin "$k=$TWIN_DIR/fuzz_disco.$b"
         --cgif-pin "$k=$CGIF_BIN/cgif_file_fuzzer.$b" --cgif-twin "$k=$CGIF_TWIN_DIR/cgif_file_fuzzer.$b")
  done
  ACC=(--accept 'Reusable/YE34.v:24=DIFFERS:38 -> fixed in b0078622dec (build check pending)'
       --accept 'Reusable/YE34.v:20=DIFFERS:435 -> fixed in b0078622dec (build check pending)'
       --accept "Reusable/YB1t.v:28:0x64c74=MEASURED TRUE:decode table, 30 words inside .text, one word past internal_madvise decodes internal_close's first instruction")
  python3 "$HERE/count_recompute.py" --lib "$LIB" --cgif-lib "$CLIB" --pac "$WORK/g7/pac3-Y.tsv.gz" "${CR[@]}" "${ACC[@]}" \
    --out "$WORK/g9/G9-counts.tsv" > "$WORK/g9/counts.out" 2>&1
  rc=$?; [ $rc -eq 0 ] || bad "g9 rc $rc (an unruled DIFFERS or an UNMEASURED row)"
  cmp "$WORK/g9/G9-counts.tsv" "$HERE/G9-counts.tsv" || bad "g9 G9-counts.tsv differs"
  # planted control: five numerals set back to the donor's value in a tree of links to the base lib
  P="$WORK/g9/plant/lib/Reusable"; rm -rf "$WORK/g9/plant"; mkdir -p "$P"
  for f in "$LIB"/Reusable/Y*.v; do ln -s "$f" "$P/${f##*/}"; done
  while IFS='|' read -r f ln old new; do
    rm "$P/$f"; lplant "$LIB/Reusable/$f" "$P/$f" "$ln" "$old" "$new"
  done <<'EOF'
YB1v.v|10|tfibmusl_text_count : nat := 16102.|tfibmusl_text_count : nat := 16403.
YB12.v|26|TFIB_TEXT_N : nat := 112841.|TFIB_TEXT_N : nat := 111037.
YB13.v|128|= 458752%N.|= 446464%N.
YD2f.v|194|length IMG_B = 81%nat|length IMG_B = 33%nat
YCef.v|9|tfib_lib_count : nat := 8769.|tfib_lib_count : nat := 7052.
EOF
  python3 "$HERE/count_recompute.py" --lib "$WORK/g9/plant/lib" --cgif-lib "$CLIB" --pac "$WORK/g7/pac3-Y.tsv.gz" \
    "${CR[@]}" "${ACC[@]}" --out "$WORK/g9/counts-plant.tsv" > "$WORK/g9/counts-plant.out" 2>&1
  rc=$?; [ $rc -eq 1 ] || bad "g9 planted control rc $rc (want 1)"
  got=$(awk -F'\t' '$11 == "DIFFERS" && $14 == "" {print $1}' "$WORK/g9/counts-plant.tsv" | LC_ALL=C sort | tr '\n' ' ')
  [ "$got" = "Reusable/YB12.v:26 Reusable/YB13.v:128 Reusable/YB1v.v:10 Reusable/YCef.v:9 Reusable/YD2f.v:194:len:IMG_B " ] \
    || bad "g9 planted control: the new DIFFERS rows are '$got'"
fi

pacx() {  # pacx TOOL DST_LIB INCLUDE OUT CACHE IMAGES: port_addr_check TOOL with G1's arguments, images from array IMAGES
  local -n img=$6
  nice -n 10 python3 "$1" --git "$GIT" --donors-from "$DONORS" --summary --fail-on-flags \
    --src "$CGIF_REF:proofs/cgif/cgif_file_fuzzer/lib" --dst "$2" --paired-only --map A/=A/ --map =Reusable/ \
    "${img[@]}" --assign '**=auto' --include "$3" --cache "$5" --out "$4.tsv" < /dev/null > "$4.out" 2> "$4.err"
}

if on g10; then
  need PAC3 PAC0D CGIF_TWIN_DIR
  [ -f "$WORK/g7/pac3-Y.tsv" ] || { echo "run.sh: g10 reads g7's table: run g7 first in the same WORK" >&2; exit 2; }
  P0=$(dirname "$PAC0D")
  sha "$PAC3" 3d2eee813cce41c92be6131e56292d73e473d2582156655895ff2a1ce5c73b82
  sha "$PAC0D" 0d24592683b610123346567302caf1bf97e5ac9354cf05799dc7cfc21dc0f4fa
  sha "$P0/inputs_used.py" 3ed6c0c79f05fc9c88309dafbff092a86bb7091ba49a2b36382e993da5ed93eb
  sha "$P0/scan_literals.py" f0ec1e108ff8197188882c658fd47ebca417e9513a4e937d6f1c6e7ae3b1c8ec
  sha "$P0/insn-targets/insn_targets.py" efdf3951d4bb6aa59a825f149055f90f5c4c1f0c579f6a0a2c57cb2463e49cd7
  sha "$P0/identity-quotients/qscan.py" 7baa52331b8cecf590722504e2e18b763af3cbd367a154eaf018c725590df675
  sha "$P0/identity-quotients/imgquant.json" 7bd088dd7feda20dd02578f494d5cc82aa593c371a94ed1fb29cc3b2b23d142d
  sha "$TWIN_DIR/fuzz_disco.ubsan" e2a41feb2f469916be4d94d237ae7215c4b1166e54f6ebf8365eb77422dbb410
  sha "$CGIF_TWIN_DIR/cgif_file_fuzzer.plain" 6ab540c4310895746cf793737943910fc77953f25cbe15396213e0249b04d59b
  note "g10: port_addr_check 0d24592683b6 (G1's command and its PIN:TWIN form), 3d2eee813cce PIN:TWIN, g10_triage.py"
  mkdir -p "$WORK/g10"
  PAC_TWIN=(--src-image A="$CGIF_BIN/cgif_file_fuzzer.asan" --src-image B="$CGIF_B"
    --src-image P="$CGIF_BIN/cgif_file_fuzzer.plain" --src-image U="$CGIF_BIN/cgif_file_fuzzer.ubsan"
    --dst-image A="$PIN_A:$TWIN_A" --dst-image B="$PIN_B:$TWIN_B" --dst-image P="$PIN_DIR/fuzz_disco.plain:$TWIN_DIR/fuzz_disco.plain"
    --dst-image U="$PIN_DIR/fuzz_disco.ubsan:$TWIN_DIR/fuzz_disco.ubsan")
  while IFS='|' read -r tool out cache imgs flagged; do
    pacx "${!tool}" "$BASE:proofs/libreac/fuzz_disco/lib" 'Y*.v' "$WORK/g10/$out" "$WORK/g10/$cache" "$imgs"
    rc=$?; [ $rc -eq 4 ] || bad "g10 $out rc $rc (want 4: findings, each triaged)"
    want "$WORK/g10/$out.out" 'count files paired: 836' "g10 $out"
    want "$WORK/g10/$out.err" "$flagged" "g10 $out"
  done <<'EOF'
PAC0D|pac0d-Y|cache|PAC_IMG|FLAGGED 27572 rows in 14 classes
PAC0D|pac0dt-Y|cache-t|PAC_TWIN|FLAGGED 27573 rows in 14 classes
PAC3|pac3t-Y|cache-3t|PAC_TWIN|FLAGGED 27544 rows in 13 classes
EOF
  # g1_triage.py on both 0d24592683b6 tables: exit 1, because the rows 0d24592683b6 newly flags are UNTRIAGED there;
  # g10_triage.py takes each of them. The rows 3d2eee813cce already flagged keep their G1 rule (multiset compare).
  for t in pac0d-Y pac0dt-Y; do
    python3 "$HERE/g1_triage.py" --pac-tsv "$WORK/g10/$t.tsv" --pac "$PAC0D" --lib "$LIB" --cgif-lib "$CLIB" \
      --pin-b "$PIN_B" --twin-b "$TWIN_B" --pin-p "$PIN_DIR/fuzz_disco.plain" --twin-p "$TWIN_DIR/fuzz_disco.plain" \
      --cgif-b "$CGIF_B" --cgif-p "$CGIF_BIN/cgif_file_fuzzer.plain" --out "$WORK/g10/g1-$t.tsv" 2> "$WORK/g10/g1-$t.err"
  done
  cmp <(grep -v $'\tUNTRIAGED\t' "$WORK/g10/g1-pac0d-Y.tsv" | LC_ALL=C sort) <(LC_ALL=C sort "$HERE/G1-flagged-rows.tsv") \
    || bad "g10: g1_triage.py on the 0d24592683b6 table, less its UNTRIAGED rows, differs from G1-flagged-rows.tsv"
  python3 "$HERE/g10_triage.py" --run "pins:$WORK/g7/pac3-Y.tsv:$WORK/g10/pac0d-Y.tsv:$WORK/g10/g1-pac0d-Y.tsv" \
    --run "pin-twin:$WORK/g10/pac3t-Y.tsv:$WORK/g10/pac0dt-Y.tsv:$WORK/g10/g1-pac0dt-Y.tsv" --pac "$PAC0D" \
    --lib "$LIB" --cgif-lib "$CLIB" --pin A="$PIN_A" --pin B="$PIN_B" --pin P="$PIN_DIR/fuzz_disco.plain" \
    --twin A="$TWIN_A" --twin B="$TWIN_B" --twin P="$TWIN_DIR/fuzz_disco.plain" \
    --cgif-pin P="$CGIF_BIN/cgif_file_fuzzer.plain" --cgif-twin P="$CGIF_TWIN_DIR/cgif_file_fuzzer.plain" \
    --out "$WORK/g10/G10-rows.tsv" 2> "$WORK/g10/triage.err"
  rc=$?; [ $rc -eq 0 ] || bad "g10 g10_triage.py rc $rc (an UNTRIAGED row)"
  cmp "$WORK/g10/G10-rows.tsv" "$HERE/G10-rows.tsv" || bad "g10 G10-rows.tsv differs"
  # planted control: G1's plant, line 474 of YE23.v, buf+0x8 moved by 16
  lplant "$LIB/Reusable/YE23.v" "$WORK/g10/plant/lib/Reusable/YE23.v" 474 'Z_to_bv 64 6277920;' 'Z_to_bv 64 6277936;'
  pacx "$PAC0D" "$WORK/g10/plant/lib" 'YE23.v' "$WORK/g10/plant" "$WORK/g10/cache" PAC_IMG
  rc=$?; [ $rc -eq 4 ] || bad "g10 planted control rc $rc (want 4)"
  want "$WORK/g10/plant.err" 'FLAGGED 19 rows' "g10 planted control"
  awk -F'\t' '$6 == "Reusable/YE23.v" && $7 == "474" && $1 == "NON-ADDRESS-CHANGED" && $12 == "0x5fcb30"' \
    "$WORK/g10/plant.tsv" | grep -q . || bad "g10 planted control: no flagged row at YE23.v:474"
fi

pchk() {  # pchk TSV IMAGE FILE LINE VERDICT VALUE LABEL: the table holds that row
  awk -F'\t' -v i="$2" -v f="$3" -v l="$4" -v v="$5" -v x="$6" '$3 == i && $6 == f && $7 == l && $1 == v && $12 == x' \
    "$1" | grep -q . || bad "$7: no $5 row $6 at $3:$4 (image $2)"
}

if on g11; then
  need PAC0D PAC205 CGIF_TWIN_DIR
  for P in "$PAC0D" "$PAC205"; do
    P0=$(dirname "$P")
    sha "$P0/inputs_used.py" 3ed6c0c79f05fc9c88309dafbff092a86bb7091ba49a2b36382e993da5ed93eb
    sha "$P0/scan_literals.py" f0ec1e108ff8197188882c658fd47ebca417e9513a4e937d6f1c6e7ae3b1c8ec
    sha "$P0/insn-targets/insn_targets.py" efdf3951d4bb6aa59a825f149055f90f5c4c1f0c579f6a0a2c57cb2463e49cd7
    sha "$P0/identity-quotients/qscan.py" 7baa52331b8cecf590722504e2e18b763af3cbd367a154eaf018c725590df675
    sha "$P0/identity-quotients/imgquant.json" 7bd088dd7feda20dd02578f494d5cc82aa593c371a94ed1fb29cc3b2b23d142d
  done
  sha "$PAC0D" 0d24592683b610123346567302caf1bf97e5ac9354cf05799dc7cfc21dc0f4fa
  sha "$PAC205" 205a90fd19b85ab3b9f1910ff13f144c1d72a28fe393209e1106a3b26fcdcb69
  sha "$TWIN_DIR/fuzz_disco.ubsan" e2a41feb2f469916be4d94d237ae7215c4b1166e54f6ebf8365eb77422dbb410
  sha "$CGIF_TWIN_DIR/cgif_file_fuzzer.plain" 6ab540c4310895746cf793737943910fc77953f25cbe15396213e0249b04d59b
  note "g11: port_addr_check 205a90fd19b8 and 0d24592683b6 on the series tree (four runs at once), g11_triage.py, plants"
  SLIB=$WORK/series/proofs/libreac/fuzz_disco/lib
  if [ ! -f "$WORK/series.ok" ]; then
    rm -rf "$WORK/series"; mkdir -p "$WORK/series"
    git -C "$GIT" archive "$SERIES" proofs/libreac/fuzz_disco/lib | tar -x -C "$WORK/series" || exit 2
    touch "$WORK/series.ok"
  fi
  mkdir -p "$WORK/g11"
  PAC_TWIN=(--src-image A="$CGIF_BIN/cgif_file_fuzzer.asan" --src-image B="$CGIF_B"
    --src-image P="$CGIF_BIN/cgif_file_fuzzer.plain" --src-image U="$CGIF_BIN/cgif_file_fuzzer.ubsan"
    --dst-image A="$PIN_A:$TWIN_A" --dst-image B="$PIN_B:$TWIN_B" --dst-image P="$PIN_DIR/fuzz_disco.plain:$TWIN_DIR/fuzz_disco.plain"
    --dst-image U="$PIN_DIR/fuzz_disco.ubsan:$TWIN_DIR/fuzz_disco.ubsan")
  jobs11=()
  while IFS='|' read -r tool out cache imgs flagged; do
    pacx "${!tool}" "$SERIES:proofs/libreac/fuzz_disco/lib" 'Y*.v' "$WORK/g11/$out" "$WORK/g11/$cache" "$imgs" &
    jobs11+=("$!|$out|$flagged")
  done <<'EOF'
PAC205|pac205-Y|cache|PAC_IMG|FLAGGED 27574 rows in 14 classes
PAC205|pac205t-Y|cache-t|PAC_TWIN|FLAGGED 27575 rows in 14 classes
PAC0D|pac0d-Y|cache-0d|PAC_IMG|FLAGGED 27583 rows in 14 classes
PAC0D|pac0dt-Y|cache-0dt|PAC_TWIN|FLAGGED 27584 rows in 14 classes
EOF
  for j in "${jobs11[@]}"; do
    IFS='|' read -r pid out flagged <<< "$j"
    wait "$pid"; rc=$?; [ $rc -eq 4 ] || bad "g11 $out rc $rc (want 4: findings, each triaged)"
    want "$WORK/g11/$out.out" 'count files paired: 836' "g11 $out"
    want "$WORK/g11/$out.err" "$flagged" "g11 $out"
  done
  # g1_triage.py on all four tables (exit 1: the rows it leaves UNTRIAGED go to g11_triage.py)
  for t in pac205-Y:PAC205 pac205t-Y:PAC205 pac0d-Y:PAC0D pac0dt-Y:PAC0D; do
    tool=${t#*:}; t=${t%%:*}
    python3 "$HERE/g1_triage.py" --pac-tsv "$WORK/g11/$t.tsv" --pac "${!tool}" --lib "$SLIB" --cgif-lib "$CLIB" \
      --pin-b "$PIN_B" --twin-b "$TWIN_B" --pin-p "$PIN_DIR/fuzz_disco.plain" --twin-p "$TWIN_DIR/fuzz_disco.plain" \
      --cgif-b "$CGIF_B" --cgif-p "$CGIF_BIN/cgif_file_fuzzer.plain" --out "$WORK/g11/g1-$t.tsv" 2> "$WORK/g11/g1-$t.err"
  done
  G=$WORK/g11
  python3 "$HERE/g11_triage.py" --run "pins:$G/pac0d-Y.tsv:$G/pac205-Y.tsv:$G/g1-pac0d-Y.tsv:$G/g1-pac205-Y.tsv" \
    --run "pin-twin:$G/pac0dt-Y.tsv:$G/pac205t-Y.tsv:$G/g1-pac0dt-Y.tsv:$G/g1-pac205t-Y.tsv" \
    --pac-old "$PAC0D" --pac-new "$PAC205" --lib "$SLIB" --cgif-lib "$CLIB" \
    --pin A="$PIN_A" --pin B="$PIN_B" --pin P="$PIN_DIR/fuzz_disco.plain" --pin U="$PIN_DIR/fuzz_disco.ubsan" \
    --twin A="$TWIN_A" --twin B="$TWIN_B" --twin P="$TWIN_DIR/fuzz_disco.plain" --twin U="$TWIN_DIR/fuzz_disco.ubsan" \
    --cgif-pin A="$CGIF_BIN/cgif_file_fuzzer.asan" --cgif-pin B="$CGIF_B" \
    --cgif-pin P="$CGIF_BIN/cgif_file_fuzzer.plain" --cgif-pin U="$CGIF_BIN/cgif_file_fuzzer.ubsan" \
    --cgif-twin P="$CGIF_TWIN_DIR/cgif_file_fuzzer.plain" --out "$G/G11-rows.tsv" 2> "$G/triage.err"
  rc=$?; [ $rc -eq 0 ] || bad "g11 g11_triage.py rc $rc (an UNTRIAGED row)"
  cmp "$G/G11-rows.tsv" "$HERE/G11-rows.tsv" || bad "g11 G11-rows.tsv differs"
  # plants, each a copy of one file of the series tree (G11-address-check-205a.md, "Planted controls")
  while IFS='|' read -r name file line old new; do
    lplant "$SLIB/Reusable/$file" "$G/plants/$name/lib/Reusable/$file" "$line" "$old" "$new"
  done <<'EOF'
g1|YE23.v|474|Z_to_bv 64 6277920;|Z_to_bv 64 6277936;
rf-sys|YFkn.v|765|SLit 262144|SLit 266524
rf-arith|YD2n.v|247|/ 262144)|/ 266524)
rf-name|YG00.v|13|:= 262144.|:= 266524.
geo-bound|YB13.v|150|<? 458752)|<? 446464)
geo-name|YD1g.v|1277|+ 0x5ee000)|+ 0x5eb000)
EOF
  declare -A ran11=()
  while IFS='|' read -r name tool cache flagged img file line verdict value; do
    T=$G/plants/$name/$tool
    if [ -z "${ran11[$name.$tool]:-}" ]; then
      ran11[$name.$tool]=1
      pacx "${!tool}" "$G/plants/$name/lib" "$file" "$T" "$G/$cache" PAC_IMG
      rc=$?; [ $rc -eq 4 ] || bad "g11 plant $name $tool rc $rc (want 4)"
    fi
    want "$T.err" "$flagged" "g11 plant $name $tool"
    pchk "$T.tsv" "$img" "Reusable/$file" "$line" "$verdict" "$value" "g11 plant $name $tool"
  done <<'EOF'
g1|PAC205|cache|FLAGGED 19 rows|B|YE23.v|474|NON-ADDRESS-CHANGED|0x5fcb30
rf-sys|PAC205|cache|FLAGGED 1 rows|B|YFkn.v|765|NON-ADDRESS-CHANGED|0x4111c
rf-sys|PAC0D|cache-0d|FLAGGED 4 rows|B|YFkn.v|765|SAME-SYMBOL|0x4111c
rf-arith|PAC205|cache|FLAGGED 2 rows|B|YD2n.v|247|NON-ADDRESS-CHANGED|0x4111c
rf-arith|PAC205|cache|FLAGGED 2 rows|A|YD2n.v|247|NON-ADDRESS-CHANGED|0x4111c
rf-arith|PAC0D|cache-0d|FLAGGED 1 rows|B|YD2n.v|247|SAME-SYMBOL|0x4111c
rf-name|PAC205|cache|FLAGGED 2 rows|B|YG00.v|13|SAME-SYMBOL|0x4111c
rf-name|PAC205|cache|FLAGGED 2 rows|A|YG00.v|13|NON-ADDRESS-CHANGED|0x4111c
rf-name|PAC0D|cache-0d|FLAGGED 2 rows|B|YG00.v|13|SAME-SYMBOL|0x4111c
geo-bound|PAC205|cache|FLAGGED 2 rows|B|YB13.v|150|NON-ADDRESS-SAME|0x6d000
geo-bound|PAC0D|cache-0d|FLAGGED 2 rows|B|YB13.v|150|NON-ADDRESS-SAME|0x6d000
geo-name|PAC205|cache|FLAGGED 7 rows|B|YD1g.v|1277|NON-ADDRESS-SAME|0x5eb000
geo-name|PAC0D|cache-0d|FLAGGED 7 rows|B|YD1g.v|1277|NON-ADDRESS-SAME|0x5eb000
EOF
fi

if on manifest; then
  python3 "$HERE/mk_manifest.py" --dir "$HERE" --out "$WORK/MANIFEST" > /dev/null && cmp "$WORK/MANIFEST" "$HERE/MANIFEST" \
    || bad "MANIFEST re-generated differs"
fi
[ $FAIL -eq 0 ] && note "every check as recorded" || note "FAILED (lines above)"
exit $FAIL
