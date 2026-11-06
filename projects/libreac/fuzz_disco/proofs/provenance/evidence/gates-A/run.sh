#!/bin/bash
# gates-A: re-run every gate of this directory against image A (fuzz_disco.asan): gates 1-9 on the series base,
# gate 10 on the series tree.
# Kind: measurement; proves no function.
#
# Every input is an environment variable; no host path is written here. Outputs go to $OUT, which must lie outside
# the repository tree. Each tool's sha256 is checked before it runs (exit 2 on a mismatch).
#
#   HUB         git dir that holds BASE, SERIES and CGIF_REF (read with ls-tree / show / archive only)
#   BASE        b1afc3e80791ebe54b1034a568112da851f005f0, the series base
#   SERIES      d57e4e79e469316d9e26c20fd6bb5ff3a086dd55, the series tree: the base plus the unit owner's code fixes (gate 10)
#   CGIF_REF    c8557374ad2e6c079948f0813d37e31638d1c0d1, cgif's released commit (its cgif lib tree a1d0c41e6861 = BASE's)
#   LIB         a checkout of BASE:proofs/libreac/fuzz_disco/lib
#   CGIF_LIB    a checkout of CGIF_REF:proofs/cgif/cgif_file_fuzzer/lib
#   PINS        directory of the four fuzz_disco pins fuzz_disco.{asan,asan-ubsan,plain,ubsan} (harness.yaml sha256)
#   TWINS       directory of their unstripped twins, same file names
#   CGIF_BIN    path prefix of cgif's four pins: $CGIF_BIN.asan, .asan-ubsan, .plain, .ubsan (cgif harness.yaml sha256)
#   DONORS      root of the symbolised donor images (<project>/<build>/<target> with <target>.debug beside it)
#   PAC         port_addr_check.py efa19b81e92b
#   PAC3        port_addr_check.py 3d2eee813cce (the address checker of record now; gates addr3 and rc)
#   PAC0D24     port_addr_check.py 0d24592683b6 in its versioned directory (the modules beside it; gates addr0d24, addr205a)
#   PAC205A     port_addr_check.py 205a90fd19b8 in its versioned directory (the modules beside it; gate addr205a)
#   KIT         directory of the frozen port_addr_check 5033540ba83b kit (port_addr_check.py, scan_literals.py, cfgpair.py)
#   SET         directory of startup-set-2026-10-30d (frozen-run.sh 40cd8a4bf5bf; codeptr 12348302dfd2, ifchk f5cde600cc18,
#               af0m f8201f503394; `sha256sum -c SHA256SUMS` must pass)
#   CTL         directory holding codeptr-controls.sh 25c012a65b96, frozen-run.sh (a link to $SET/frozen-run.sh) and
#               syms/cgif_file_fuzzer.{asan,asan-ubsan}.nm (bc0bee6320e6, 5b5f81784ea1)
#   CTL_TREE    the control's tree argument: a directory with proofs/cgif/cgif_file_fuzzer/lib (CGIF_REF) and
#               projects/cgif/bin/cgif_file_fuzzer/ (cgif's pins)
#   CELLGATES   directory of cellcheck cc60c6705e6f and ownedcheck b663903ddda1 (with its termeval b64897421d5b)
#   SHADOWGATE  directory of shadowcheck e04173f5a5a5 (with its termeval 85060f6c7558)
#   CGIF_TWINS  directory of the unstripped twins of cgif's four pins, cgif_file_fuzzer.{asan,asan-ubsan,plain,ubsan}
#   RC2         roundconst.py v2 32b39f3b34e9 (the kept-donor-geometry gate, by value)
#   RC1         roundconst.py v1 8ad299147f2e (only for the v1 half of the planted controls)
#   OUT         output directory (written)
#
# Usage: run.sh GATE...    GATE = twin | addr | donordec | codeptr | ifchk | cells | addr3 | rc | counts | addr0d24 |
#                                 addr205a | all
# (addr3 compares with the table addr writes, rc reads the table addr3 writes, and addr0d24 compares with it: run them
# in that order. addr205a runs both of its versions itself, on the series tree.)
# Each gate writes $OUT/<gate>/*.out (stdout + stderr, last line rc=N) and appends one line per run to
# $OUT/verdicts.txt: `PASS` / `FAIL` for a run on a tree, `FIRED` / `VOID` for a planted control.
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
for v in HUB BASE SERIES CGIF_REF LIB CGIF_LIB PINS TWINS CGIF_BIN DONORS PAC PAC3 PAC0D24 PAC205A KIT SET CTL CTL_TREE \
         CELLGATES SHADOWGATE CGIF_TWINS RC2 RC1 OUT; do
  [ -n "${!v:-}" ] || { echo "run.sh: $v is not set" >&2; exit 2; }
done
mkdir -p "$OUT"
PIN_A=$PINS/fuzz_disco.asan
TWIN_A=$TWINS/fuzz_disco.asan
A=$LIB/A
STARTUP=(AB01 AB03 AB05 AB12 AD1k AD2i AD2j AF0m ACej)

need() {  # need FILE SHA256: refuse unless FILE has exactly this sha256
  local got; got=$(sha256sum "$1" | cut -d' ' -f1)
  [ "$got" = "$2" ] || { echo "run.sh: REFUSED: $1 has sha256 $got, want $2" >&2; exit 2; }
}
run() {  # run NAME CMD...: stdout + stderr to $OUT/NAME.out, then a last line rc=N
  mkdir -p "$(dirname "$OUT/$1.out")"
  local n=$1; shift
  "$@" > "$OUT/$n.out" 2>&1
  echo "rc=$?" >> "$OUT/$n.out"
}
expect() {  # expect KIND NAME RC REGEX: KIND base (PASS/FAIL) or control (FIRED/VOID); RC and REGEX must both hold
  local kind=$1 n=$2 rc=$3 re=$4 ok=0
  tail -n 1 "$OUT/$n.out" | grep -qx "rc=$rc" && grep -Eq -- "$re" "$OUT/$n.out" && ok=1
  if [ "$kind" = base ]; then w=$([ $ok = 1 ] && echo PASS || echo FAIL); else w=$([ $ok = 1 ] && echo FIRED || echo VOID); fi
  echo "$w $n (want rc=$rc and /$re/)" | tee -a "$OUT/verdicts.txt"
}
plant() {  # plant SRC DST LINE OLD NEW: DST = SRC with the one OLD of line LINE replaced by NEW (refuses otherwise)
  mkdir -p "$(dirname "$2")"
  python3 - "$@" <<'EOF'
import sys
src, dst, line, old, new = sys.argv[1:6]
L = open(src).read().split('\n')
i = int(line) - 1
if L[i].count(old) != 1:
    sys.exit(f'plant: {old!r} occurs {L[i].count(old)} times on line {line} of {src}, not once')
L[i] = L[i].replace(old, new)
open(dst, 'w').write('\n'.join(L))
EOF
}
frozen() { (cd "$SET" && bash frozen-run.sh startup-set-2026-10-30d.tsv "$@"); }
set_ok() {
  need "$SET/frozen-run.sh" 40cd8a4bf5bf355c4a8f506bcc1503e9c7ec4a1331831204bd36ef22a8915ab4
  need "$SET/startup-set-2026-10-30d.tsv" bde9702390640d7bfc5a23702de239154ed4130e863e475ca109455c2648dbab
  (cd "$SET" && sha256sum -c --quiet SHA256SUMS) || { echo "run.sh: REFUSED: $SET SHA256SUMS" >&2; exit 2; }
}

# ---- twin: unstripped twin vs pin, PT_LOAD 2..4 byte-equal (the address checker reads all four twins' symbols)
gate_twin() {
  : > "$OUT/twin-check.txt"
  for b in asan asan-ubsan plain ubsan; do
    echo "== fuzz_disco.$b" >> "$OUT/twin-check.txt"
    python3 "$HERE/twin_check.py" "$PINS/fuzz_disco.$b" "$TWINS/fuzz_disco.$b" >> "$OUT/twin-check.txt"
    echo "rc=$?" >> "$OUT/twin-check.txt"
  done
}

# ---- gate 1: address checker of record, lib/A against cgif's released lib, images keyed by build letter
pac() {  # pac DST OUTNAME
  nice python3 "$PAC" --git "$HUB" --donors-from "$DONORS" --summary --fail-on-flags \
    --src "$CGIF_REF:proofs/cgif/cgif_file_fuzzer/lib" --dst "$1" \
    --paired-only --map A/=A/ --map =Reusable/ \
    --src-image A="$CGIF_BIN.asan" --src-image B="$CGIF_BIN.asan-ubsan" \
    --src-image P="$CGIF_BIN.plain" --src-image U="$CGIF_BIN.ubsan" \
    --dst-image A="$PIN_A:$TWIN_A" --dst-image B="$PINS/fuzz_disco.asan-ubsan:$TWINS/fuzz_disco.asan-ubsan" \
    --dst-image P="$PINS/fuzz_disco.plain:$TWINS/fuzz_disco.plain" --dst-image U="$PINS/fuzz_disco.ubsan:$TWINS/fuzz_disco.ubsan" \
    --assign '**=auto' --include 'A/**' --cache "$OUT/addr/cache" --out "$OUT/addr/$2.tsv"
}
gate_addr() {
  need "$PAC" efa19b81e92ba289e7c185d481faadf045ce7d52d092cc10642fec69924aba03
  mkdir -p "$OUT/addr"
  run addr/pac-A pac "$BASE:proofs/libreac/fuzz_disco/lib" pac-A
  expect base addr/pac-A 4 '^FLAGGED [0-9]+ rows'
  # triage every flagged row (addr_triage.py: a class, right / DEFECT and a per-row detail; measures each block from the
  # pin, its twin, cgif's symbols and the files; the hand table covers the rest). 0 DEFECT, 0 UNTRIAGED is the gate.
  "$PAC" --list-flag-classes > "$OUT/addr/flag-classes.txt"
  run addr/triage python3 "$HERE/addr/addr_triage.py" --rows "$OUT/addr/pac-A.tsv" --flags "$OUT/addr/flag-classes.txt" \
    --lib "$LIB" --cgif-lib "$CGIF_LIB" --pin "$PIN_A" --twin "$TWIN_A" --cgif-nm "$CTL/syms/cgif_file_fuzzer.asan.nm" \
    --hand "$HERE/addr/hand-triage.tsv" --out "$OUT/addr/triage-A.tsv"
  expect base addr/triage 0 'DEFECT 0, hand rows'
  # planted control (a moved address): AE2k.v's FF_mask 0x103b8 set to _start 0x30eac (a code symbol). The row flips from
  # SAME-SYMBOL to DIFFERENT-SYMBOL with the correct value expected; a `0 FINDINGS` run or a SAME-SYMBOL row is VOID.
  plant "$A/AE2k.v" "$OUT/addr/plant/A/AE2k.v" 36 '0x103b8' '0x30eac'
  run addr/plant pac "$OUT/addr/plant" plant
  if tail -n 1 "$OUT/addr/plant.out" | grep -qx 'rc=4' && \
     awk -F'\t' '$1=="DIFFERENT-SYMBOL" && $6=="A/AE2k.v" && $12=="0x30eac"' "$OUT/addr/plant.tsv" | grep -q .; then
    echo "FIRED addr/plant (AE2k.v FF_mask 0x103b8 -> 0x30eac: DIFFERENT-SYMBOL, expected 0x103b8)" | tee -a "$OUT/verdicts.txt"
  else
    echo "VOID addr/plant" | tee -a "$OUT/verdicts.txt"
  fi
}

# ---- gate 2: by-value donor-stale numeral check (decimal literals that are a cgif address, not disco's same object)
gate_donordec() {
  need "$KIT/port_addr_check.py" 5033540ba83bdad174e9b1aa3cc21ffeda3469736e4dd0390f58db9008890546
  need "$KIT/scan_literals.py" ae01d69b2ee4af269258982bef0de35a38a44d2b8832b62ef217e58439cd5804
  need "$KIT/cfgpair.py" bc9795900868df328eebcf4f90bc7c1cbf9abf5ab9efa95474a2871bf99c5cd4
  local D=$OUT/donordec
  mkdir -p "$D"
  local ARGS=(--git "$HUB" --kit "$KIT" --donors-from "$DONORS" --cache "$D/cache"
              --cgif-image asan="$CGIF_BIN.asan" --cgif-image asan-ubsan="$CGIF_BIN.asan-ubsan"
              --cgif-image ubsan="$CGIF_BIN.ubsan" --target-image asan="$PIN_A:$TWIN_A")
  # negative control: cgif against itself over its released lib -> 0 rows
  run donordec/control-neg nice python3 "$HERE/donordec/donor_decimals.py" "${ARGS[@]}" --target cgif --subdirs '' \
    --tree cgif="$CGIF_REF:proofs/cgif/cgif_file_fuzzer/lib" --out "$D/control-neg.tsv"
  expect control donordec/control-neg 0 '^# rows 0$'
  # positive control: cgif's A/AE23.v:471 (`Z_to_bv 64 6264480`, cgif's stdout buffer) scanned as a disco lib/A file
  sed -n 471p "$CGIF_LIB/A/AE23.v" > "$D/plant_AE23.v"
  run donordec/control-pos nice python3 "$HERE/donordec/donor_decimals.py" "${ARGS[@]}" --target disco --subdirs A \
    --tree none="$BASE@$BASE" --plant "$D/plant_AE23.v" --out "$D/control-pos.tsv"
  expect control donordec/control-pos 0 '^# rows 1$'
  # the gate: lib/A at the base
  run donordec/scan-A nice python3 "$HERE/donordec/donor_decimals.py" "${ARGS[@]}" --target disco --subdirs A \
    --tree base="$BASE" --out "$D/scan-A.tsv"
  run donordec/funnel-A nice python3 "$HERE/donordec/funnel.py" "${ARGS[@]}" "$D/scan-A.tsv" \
    --cgif-lib "$CGIF_REF:proofs/cgif/cgif_file_fuzzer/lib"
  # the funnel's UNEXPLAINED values are the hand-reviewed disco-own values; every one must be in the per-value table
  run donordec/unexplained python3 "$HERE/donordec/triage_unexplained.py" "$OUT/donordec/funnel-A.out" \
    "$HERE/donordec/unexplained-safe.tsv"
  expect base donordec/unexplained 0 'all recorded disco-own: True'
  # planted control: disco's AE23.v with its stdout-buffer decimal 6276960 (disco buf+0x8) set to cgif's 6264480
  plant "$A/AE23.v" "$D/plant/AE23.v" 473 '6276960' '6264480'
  run donordec/plant nice python3 "$HERE/donordec/donor_decimals.py" "${ARGS[@]}" --target disco --subdirs A \
    --tree none="$BASE@$BASE" --plant "$D/plant/AE23.v" --out "$D/plant.tsv"
  expect control donordec/plant 0 '^# rows [1-9]'
  grep -q '	473	6264480	' "$D/plant.tsv" && echo "FIRED donordec/plant row 473 6264480" >> "$OUT/verdicts.txt"
}

# ---- gate 3: codeptr of record through the start-up set of record, the nine start-up files of image A
CODEPTR_DECL=(
  --same '0x10800=gp: __global_pointer$ is 0x10800 in fuzz_disco.asan (twin symtab) and in cgif asan; layout constant both link the same'
  --same '0x10310=region bound [0x10310, 0x10338) of AD2j / AD1k (CImg 40), in fuzz_disco.asan .rodata (PT_LOAD 1); AD2j is the region generator output from the pin'
  --same '0x103c0=region bound [0x103c0, 0x103d0) of AD2j / AD1k (CImg 16), in fuzz_disco.asan .rodata (PT_LOAD 1); end of owned row (0x103b8, 8)'
  --same '0x103b8=AF0m const cell z8 (ANum 0x103b8), in fuzz_disco.asan .rodata; owned row (0x103b8, 8); its value equals the pin bytes (cellcheck 0 mismatch)'
  --not-address '0x10101=value 65793 (flag bytes 01 01 01) stored in the collected start-up states and in AF0m cell 0xa6928, not an address'
  --not-address '0x1ffff=numeric bound 131071 in the generated start-up states AB01 / AB03 (collector output on fuzz_disco.asan), not an address'
  --not-address '0x20000=size 131072 (2^17) in the generated start-up states, not an address'
  --not-address '0x445c0=numeric bound 280000 in the generated start-up states, not an address'
  --not-address '0x71c00=byte length 465920 of a runtime mmap region / its shadow in the generated start-up states'
  --not-address '0x100000=size 1048576 (1 MiB) of the ASan runtime, same in both images, not an address'
  --not-address '0x100018=size 1048600 in the generated start-up states (1 MiB + 24), not an address'
  --not-address '0x161200=byte length 1446400 of a shadow zero-fill in the generated start-up states'
  --not-address '0x38e000=byte length 3727360 of a runtime mmap region in the generated start-up states'
  --not-address '0x3fffff=numeric bound 4194303 (2^22 - 1), a KRange length in AD2i and a bound in AB01 / AB03, not an address'
)
codeptr() {  # codeptr FILE...: against the A pin, stale against cgif asan with the donor files beside
  frozen codeptr.py --image "$PIN_A" --names "$TWIN_A" --stale-image "$CGIF_BIN.asan" \
    --stale-names "$CTL/syms/cgif_file_fuzzer.asan.nm" --stale-dir "$CGIF_LIB" "$@"
}
gate_codeptr() {
  set_ok
  need "$CTL/codeptr-controls.sh" 25c012a65b96fe16406ee979efb146b6bd266770739bbedfc3b57f5fd54e3c03
  need "$CTL/syms/cgif_file_fuzzer.asan.nm" bc0bee6320e6b74f4a2c0e7baa557a3abd07bc0ecc9727d697377c3681fa060f
  need "$CTL/syms/cgif_file_fuzzer.asan-ubsan.nm" 5b5f81784ea1ed5e8d35ab9bd5b01277536c10addbe4b545ca3f223045c95a75
  mkdir -p "$OUT/codeptr"
  # the control of record (known answers): must-find paired on 6 files, must-not-flag 0x8065e
  run codeptr/controls bash "$CTL/codeptr-controls.sh" "$SET/startup-set-2026-10-30d.tsv" "$CTL_TREE"
  expect control codeptr/controls 0 '^codeptr-controls: PASS'
  local F=(); for f in "${STARTUP[@]}"; do F+=("$A/$f.v"); done
  run codeptr/raw codeptr "${F[@]}"
  run codeptr/final codeptr "${CODEPTR_DECL[@]}" "${F[@]}"
  expect base codeptr/final 0 'ACej.v .* 0 FINDINGS'
  # planted control: ACej.v with CTX_target_alloc_init's return address 0x80c04 set to cgif's value in the same slot,
  # 0x80150 (a donor address copied unchanged); no declarations (each --not-address must match a checked file)
  plant "$A/ACej.v" "$OUT/codeptr/plant/A/ACej.v" 17 '[[0x80c04]]' '[[0x80150]]'
  run codeptr/plant codeptr "$OUT/codeptr/plant/A/ACej.v"
  expect control codeptr/plant 1 '^ACej.v .* [1-9][0-9]* FINDINGS: .*0x80150'
}

# ---- gate 4: ifchk of the start-up set of record (AF0m cells x the 50 states of AB01, AD1g's xcells)
gate_ifchk() {
  set_ok
  mkdir -p "$OUT/ifchk"
  run ifchk/base frozen ifchk.py --owned "$A/AF0m.v" --states "$A/AB01.v" --ad1g "$A/AD1g.v" --image "$PIN_A"
  expect base ifchk/base 0 'x 50 states: [0-9]+ = stated, 0 different, 0 undetermined'
  # planted control: AF0m.v with the file-backed cell z8 (ANum 0xa1200) 0x8 flipped to 0x9
  plant "$A/AF0m.v" "$OUT/ifchk/plant/AF0m.v" 104 'z8 (ANum 0xa1200) 0x8' 'z8 (ANum 0xa1200) 0x9'
  run ifchk/plant frozen ifchk.py --owned "$OUT/ifchk/plant/AF0m.v" --states "$A/AB01.v" --ad1g "$A/AD1g.v" --image "$PIN_A"
  expect control ifchk/plant 1 ' [1-9][0-9]* different'
}

# ---- gate 5: ASan cell / owned / shadow gates on AF0m.v, plus the owned read-only pin count
gate_cells() {
  set_ok
  need "$CELLGATES/cellcheck.py" cc60c6705e6f4264ce9b15def8a3ef85225340c1b0f95c982b4183184e530e54
  need "$CELLGATES/ownedcheck.py" b663903ddda19527c05a72f47187888fdbc241cf911322ec751a13a66445cde8
  need "$CELLGATES/termeval.py" b64897421d5b1dd634a7d49986ea9503538b035a9c356381592a1c3dea3749b0
  need "$SHADOWGATE/shadowcheck.py" e04173f5a5a50913ad205152cde41f4759aff4c1ca0bd521ff32c9b3616abcb7
  need "$SHADOWGATE/termeval.py" 85060f6c7558815c5eff2149aefeab395e8e6a34b89393b38fc03013c95fa829
  local C=$OUT/cells
  mkdir -p "$C/stage" "$C/plant-cell" "$C/plant-owned/lib/A" "$C/plant-owned/lib/Reusable"
  cp "$A/AF0m.v" "$C/stage/AF0m.v"
  run cells/cellcheck python3 "$CELLGATES/cellcheck.py" "$C/stage" "$PIN_A"
  expect base cells/cellcheck 0 '^# [0-9]+ file-backed cells, 0 mismatch'
  # ownedcheck reads the unit's lib/Reusable/YImgTop.v beside lib/A itself (IMG_LO / IMG_TOP checked against the pin)
  run cells/ownedcheck python3 "$CELLGATES/ownedcheck.py" "$A/AF0m.v" --elf "$PIN_A"
  expect base cells/ownedcheck 0 'UNOWNED 0, OVERCLAIM 0, UNPARSED 0'
  # IMG_TOP = 0x5fe000: the pin's highest PT_LOAD end 0x5fd930 rounded up to a page (twin-check.txt)
  run cells/shadowcheck python3 "$SHADOWGATE/shadowcheck.py" "$PIN_A" "$A/AF0m.v" IMG_TOP=0x5fe000
  expect base cells/shadowcheck 0 'Tfib_zero_shadow: [0-9]+ ranges, 0 poisoned granules inside, 0 unparsed'
  run cells/ro_pins python3 "$HERE/ro_pins.py" "$SET" "$A/AF0m.v" "$PIN_A"
  expect base cells/ro_pins 0 'unpinned 0$'
  # planted controls, one per tool
  plant "$A/AF0m.v" "$C/plant-cell/AF0m.v" 104 'z8 (ANum 0xa1200) 0x8' 'z8 (ANum 0xa1200) 0x9'
  run cells/plant-cellcheck python3 "$CELLGATES/cellcheck.py" "$C/plant-cell" "$PIN_A"
  expect control cells/plant-cellcheck 1 '^# [0-9]+ file-backed cells, 1 mismatch'
  plant "$A/AF0m.v" "$C/plant-owned/lib/A/AF0m.v" 33 'z8 (ANum 0x13abe8) 0x1' 'z8 (ANum 0x30eb0) 0x1'
  cp "$LIB/Reusable/YImgTop.v" "$C/plant-owned/lib/Reusable/YImgTop.v"
  run cells/plant-ownedcheck python3 "$CELLGATES/ownedcheck.py" "$C/plant-owned/lib/A/AF0m.v" --elf "$PIN_A"
  expect control cells/plant-ownedcheck 1 'UNOWNED 1,'
  plant "$A/AF0m.v" "$C/plant-shadow/AF0m.v" 807 'z1 (ANum 0x7fffc1f3) 0x6' 'z1 (ANum 0x7fffc1f3) 0x7'
  run cells/plant-shadowcheck python3 "$SHADOWGATE/shadowcheck.py" "$PIN_A" "$C/plant-shadow/AF0m.v" IMG_TOP=0x5fe000
  expect control cells/plant-shadowcheck 1 'Tfib_const_shadow: [0-9]+ cells, 1 wrong'
  # negative control of the earlier record: the same AF0m.v without IMG_TOP leaves the named last range UNPARSED
  run cells/control-shadow-noimgtop python3 "$SHADOWGATE/shadowcheck.py" "$PIN_A" "$A/AF0m.v"
  expect control cells/control-shadow-noimgtop 1 '1 unparsed'
  plant "$A/AF0m.v" "$C/plant-ro/AF0m.v" 142 'z8 (ANum 0x103b8) ' 'z8 (ANum 0xa1208) '
  run cells/plant-ro_pins python3 "$HERE/ro_pins.py" "$SET" "$C/plant-ro/AF0m.v" "$PIN_A"
  expect control cells/plant-ro_pins 1 'unpinned [1-9]'
}

# ---- gate 6: the address checker of record now, port_addr_check 3d2eee813cce: gate 1's command and file set
pac3() {  # pac3 DST OUTNAME
  nice python3 "$PAC3" --git "$HUB" --donors-from "$DONORS" --summary --fail-on-flags \
    --src "$CGIF_REF:proofs/cgif/cgif_file_fuzzer/lib" --dst "$1" \
    --paired-only --map A/=A/ --map =Reusable/ \
    --src-image A="$CGIF_BIN.asan" --src-image B="$CGIF_BIN.asan-ubsan" \
    --src-image P="$CGIF_BIN.plain" --src-image U="$CGIF_BIN.ubsan" \
    --dst-image A="$PIN_A:$TWIN_A" --dst-image B="$PINS/fuzz_disco.asan-ubsan:$TWINS/fuzz_disco.asan-ubsan" \
    --dst-image P="$PINS/fuzz_disco.plain:$TWINS/fuzz_disco.plain" --dst-image U="$PINS/fuzz_disco.ubsan:$TWINS/fuzz_disco.ubsan" \
    --assign '**=auto' --include 'A/**' --cache "$OUT/addr3/cache" --out "$OUT/addr3/$2.tsv"
}
gate_addr3() {
  need "$PAC3" 3d2eee813cce41c92be6131e56292d73e473d2582156655895ff2a1ce5c73b82
  [ -f "$OUT/addr/pac-A.tsv" ] || { echo "run.sh: gate addr3 compares with \$OUT/addr/pac-A.tsv: run gate addr first" >&2; exit 2; }
  mkdir -p "$OUT/addr3"
  run addr3/pac-A pac3 "$BASE:proofs/libreac/fuzz_disco/lib" pac-A
  expect base addr3/pac-A 4 '^FLAGGED [0-9]+ rows'
  # every flagged row triaged by gate 1's triage script and hand table (0 DEFECT, 0 untriaged)
  python3 "$PAC3" --list-flag-classes > "$OUT/addr3/flag-classes.txt"
  run addr3/triage python3 "$HERE/addr/addr_triage.py" --rows "$OUT/addr3/pac-A.tsv" --flags "$OUT/addr3/flag-classes.txt" \
    --lib "$LIB" --cgif-lib "$CGIF_LIB" --pin "$PIN_A" --twin "$TWIN_A" --cgif-nm "$CTL/syms/cgif_file_fuzzer.asan.nm" \
    --hand "$HERE/addr/hand-triage.tsv" --out "$OUT/addr3/triage-A.tsv"
  expect base addr3/triage 0 'DEFECT 0, hand rows'
  # the row-by-row difference from the efa19b81e92b table of gate 1 (the same file set and arguments)
  run addr3/diff python3 "$HERE/addr/run_diff.py" "$OUT/addr/pac-A.tsv" "$OUT/addr3/pac-A.tsv"
  expect base addr3/diff 0 'verdicts identical: yes$'
  # planted control: gate 1's plant (AE2k.v FF_mask 0x103b8 -> _start 0x30eac) on this version
  plant "$A/AE2k.v" "$OUT/addr3/plant/A/AE2k.v" 36 '0x103b8' '0x30eac'
  run addr3/plant pac3 "$OUT/addr3/plant" plant
  if tail -n 1 "$OUT/addr3/plant.out" | grep -qx 'rc=4' && \
     awk -F'\t' '$1=="DIFFERENT-SYMBOL" && $6=="A/AE2k.v" && $12=="0x30eac"' "$OUT/addr3/plant.tsv" | grep -q .; then
    echo "FIRED addr3/plant (AE2k.v FF_mask 0x103b8 -> 0x30eac: DIFFERENT-SYMBOL)" | tee -a "$OUT/verdicts.txt"
  else
    echo "VOID addr3/plant" | tee -a "$OUT/verdicts.txt"
  fi
}

# ---- gate 7: roundconst v2 (kept donor geometry, by value) on gate 6's full table, all four builds keyed
RC_SRC() { local s='' b; for b in A:asan B:asan-ubsan P:plain U:ubsan; do
  s+="${s:+,}${b%%:*}=$CGIF_BIN.${b#*:}:$CGIF_TWINS/cgif_file_fuzzer.${b#*:}"; done; echo "$s"; }
RC_DST() { local s='' b; for b in A:asan B:asan-ubsan P:plain U:ubsan; do
  s+="${s:+,}${b%%:*}=$PINS/fuzz_disco.${b#*:}:$TWINS/fuzz_disco.${b#*:}"; done; echo "$s"; }
rc2() { nice python3 "$RC2" "$1" "$(RC_SRC)" "${3:-$(RC_DST)}" "$2"; }   # rc2 IN.tsv.gz OUTPREFIX [TARGET_SPEC]
rcplant() {  # rcplant NAME FILE LINE OLD NEW WANT: one numeral of a copy of lib/A/FILE set back to the donor's numeral
  local n=$1 f=$2 P=$OUT/rc/$1 s
  mkdir -p "$P/base/A"
  cp "$A/$f" "$P/base/A/$f"
  plant "$A/$f" "$P/plant/A/$f" "$3" "$4" "$5"
  for s in base plant; do
    run "rc/$n/$s-pac" pac3 "$P/$s" "rc-$n-$s"
    gzip -c "$OUT/addr3/rc-$n-$s.tsv" > "$P/$s.tsv.gz"
    run "rc/$n/$s-rc2" rc2 "$P/$s.tsv.gz" "$P/$s-rc2"
    run "rc/$n/$s-rc1" nice python3 "$RC1" "$P/$s.tsv.gz" "A=$CGIF_BIN.asan" "A=$PIN_A" "$P/$s-rc1"
  done
  run "rc/$n/check" python3 "$HERE/rc/plant_check.py" --base "$P/base-rc2.tsv" --plant "$P/plant-rc2.tsv" \
    --at "A/$f:$3" --value "$7" --want "$6" --v1-base "$P/base-rc1.tsv" --v1-plant "$P/plant-rc1.tsv"
  expect control "rc/$n/check" 0 '^plant_check: FIRED'
}
gate_rc() {
  need "$PAC3" 3d2eee813cce41c92be6131e56292d73e473d2582156655895ff2a1ce5c73b82
  need "$RC2" 32b39f3b34e97818cd71be57afda15f6aba21ede5fe2d1016f939ede19ac26cc
  need "$RC1" 8ad299147f2e67fbeb40ee47592152377082e6c55e745a16d9b45b65d84e27b3
  [ -f "$OUT/addr3/pac-A.tsv" ] || { echo "run.sh: gate rc reads \$OUT/addr3/pac-A.tsv: run gate addr3 first" >&2; exit 2; }
  local R=$OUT/rc
  mkdir -p "$R"
  gzip -c "$OUT/addr3/pac-A.tsv" > "$R/pac-A.tsv.gz"
  run rc/rc-A rc2 "$R/pac-A.tsv.gz" "$R/rc-A"
  expect base rc/rc-A 0 'selected [0-9]+ kept rows equal to a donor quantity'
  # README gap 5: read every MISMATCH / MIXED row; rc_triage.py classes each by a stated, measured rule
  run rc/triage python3 "$HERE/rc/rc_triage.py" --rc "$R/rc-A.tsv" --lib "$LIB" --pin "$PIN_A" --twin "$TWIN_A" \
    --cgif-pin "$CGIF_BIN.asan" --cgif-twin "$CGIF_TWINS/cgif_file_fuzzer.asan" --hand "$HERE/rc/hand-triage.tsv" \
    --out "$R/triage-A.tsv"
  expect base rc/triage 0 'DEFECT 0, untriaged 0,'
  cmp "$R/triage-A.tsv" "$HERE/rc/triage-A.tsv" && echo "PASS rc/triage-cmp (triage-A.tsv byte-equal)" | tee -a "$OUT/verdicts.txt" \
    || echo "FAIL rc/triage-cmp" | tee -a "$OUT/verdicts.txt"
  # control 1: donor on donor (cgif's lib against itself, cgif's images on both sides): 0 non-SAME rows
  run rc/self-pac nice python3 "$PAC3" --git "$HUB" --donors-from "$DONORS" --summary --fail-on-flags \
    --src "$CGIF_REF:proofs/cgif/cgif_file_fuzzer/lib" --dst "$CGIF_REF:proofs/cgif/cgif_file_fuzzer/lib" --paired-only \
    --src-image A="$CGIF_BIN.asan" --src-image B="$CGIF_BIN.asan-ubsan" --src-image P="$CGIF_BIN.plain" --src-image U="$CGIF_BIN.ubsan" \
    --dst-image A="$CGIF_BIN.asan" --dst-image B="$CGIF_BIN.asan-ubsan" --dst-image P="$CGIF_BIN.plain" --dst-image U="$CGIF_BIN.ubsan" \
    --assign '**=auto' --include 'A/**' --cache "$OUT/addr3/cache" --out "$R/self.tsv"
  gzip -c "$R/self.tsv" > "$R/self.tsv.gz"
  run rc/self rc2 "$R/self.tsv.gz" "$R/self-rc" "$(RC_SRC)"
  if tail -n 1 "$OUT/rc/self.out" | grep -qx 'rc=0' && grep -q 'selected [0-9]* kept rows' "$OUT/rc/self.out" && \
     ! grep -Eq '^#   (MISMATCH|MIXED|NO-COUNTERPART)	' "$OUT/rc/self.out"; then
    echo "PASS rc/self (donor on donor: 0 non-SAME rows)" | tee -a "$OUT/verdicts.txt"
  else
    echo "FAIL rc/self" | tee -a "$OUT/verdicts.txt"
  fi
  # controls 2-4: a kept donor PT_LOAD length, a kept donor word count (/4), a kept donor small table length (< 0x100);
  # control 5, the gap control: a kept donor size whose value is also a right target quantity (must read SAME)
  rcplant pt AB13.v 122 '= 454656%N.' '= 446464%N.' MISMATCH 0x6d000
  rcplant wc AB01.v 181 'seg HS_tfib_10_kn 389 ' 'seg HS_tfib_10_kn 214 ' MISMATCH 0xd6
  rcplant tl AB01.v 102 'seg HS_tfib_0_kn 263 ' 'seg HS_tfib_0_kn 88 ' MISMATCH 0x58
  rcplant gap AD2j.v 31 '(CImg 112)' '(CImg 192)' SAME 0xc0
}

# ---- gate 8: every image-derived count of lib/A recomputed from the A pin and its twin
# The unit owner's rulings on the counts this gate measured DIFFERS at the base (each fixed by a series code commit;
# a re-run on a tree with those fixes has no such row, and a ruling that matches no row is a refusal)
COUNT_RULINGS=(
  --ruling "A/AB1v.v:14=DIFFERS: 16403 (cgif's) vs measured 16102 -> fixed in the series code commit (build check pending)"
  --ruling "A/AE34.v:26:0x429c4=DIFFERS: 38 (cgif's) vs measured 36 -> fixed in the series code commit (build check pending)"
  --ruling "A/AE34.v:22:0x95468=DIFFERS: 435 (cgif's) vs measured 383 -> fixed in the series code commit (build check pending)"
)
gate_counts() {
  local C=$OUT/counts
  mkdir -p "$C"
  run counts/recompute python3 "$HERE/counts/count_recompute.py" --lib "$LIB" --pin "$PIN_A" --twin "$TWIN_A" \
    --cgif-lib "$CGIF_LIB" --cgif-pin "$CGIF_BIN.asan" --cgif-twin "$CGIF_TWINS/cgif_file_fuzzer.asan" --out "$C/counts-A.tsv" \
    "${COUNT_RULINGS[@]}"
  expect base counts/recompute 0 'DIFFERS [0-9]+ \(ruled [0-9]+, unruled 0\); UNRULED 0;'
  cmp "$C/counts-A.tsv" "$HERE/counts/counts-A.tsv" && echo "PASS counts/cmp (counts-A.tsv byte-equal)" | tee -a "$OUT/verdicts.txt" \
    || echo "FAIL counts/cmp" | tee -a "$OUT/verdicts.txt"
  # planted control: AB12.v's TFIB_TEXT_N set back to the donor-end value atable wrote (112615); the own .text / 4 is 112639
  rm -rf "$C/plant"
  cp -rs "$(cd "$LIB" && pwd)" "$C/plant"     # a tree of links to LIB's files, then one real planted file
  rm "$C/plant/A/AB12.v"
  plant "$A/AB12.v" "$C/plant/A/AB12.v" 24 'TFIB_TEXT_N : nat := 112639.' 'TFIB_TEXT_N : nat := 112615.'
  run counts/plant python3 "$HERE/counts/count_recompute.py" --lib "$C/plant" --pin "$PIN_A" --twin "$TWIN_A" \
    --cgif-lib "$CGIF_LIB" --cgif-pin "$CGIF_BIN.asan" --cgif-twin "$CGIF_TWINS/cgif_file_fuzzer.asan" --out "$C/plant.tsv" \
    "${COUNT_RULINGS[@]}"
  expect control counts/plant 1 'unruled 1\)'
  awk -F'\t' '$1 ~ /^A\/AB12\.v:24(:|$)/ && $8 == "DIFFERS"' "$C/plant.tsv" | grep -q . \
    && echo "FIRED counts/plant row A/AB12.v:24 DIFFERS (112615, measured 112639)" | tee -a "$OUT/verdicts.txt"
}

# ---- gate 9: port_addr_check 0d24592683b6 (installed after 3d2eee813cce): gate 1's command and file set, against gate 6
pac0d() {  # pac0d DST OUTNAME
  nice python3 "$PAC0D24" --git "$HUB" --donors-from "$DONORS" --summary --fail-on-flags \
    --src "$CGIF_REF:proofs/cgif/cgif_file_fuzzer/lib" --dst "$1" \
    --paired-only --map A/=A/ --map =Reusable/ \
    --src-image A="$CGIF_BIN.asan" --src-image B="$CGIF_BIN.asan-ubsan" \
    --src-image P="$CGIF_BIN.plain" --src-image U="$CGIF_BIN.ubsan" \
    --dst-image A="$PIN_A:$TWIN_A" --dst-image B="$PINS/fuzz_disco.asan-ubsan:$TWINS/fuzz_disco.asan-ubsan" \
    --dst-image P="$PINS/fuzz_disco.plain:$TWINS/fuzz_disco.plain" --dst-image U="$PINS/fuzz_disco.ubsan:$TWINS/fuzz_disco.ubsan" \
    --assign '**=auto' --include 'A/**' --cache "$OUT/addr0d24/cache" --out "$OUT/addr0d24/$2.tsv"
}
gate_addr0d24() {
  need "$PAC0D24" 0d24592683b610123346567302caf1bf97e5ac9354cf05799dc7cfc21dc0f4fa
  [ -f "$OUT/addr3/pac-A.tsv" ] || { echo "run.sh: gate addr0d24 compares with \$OUT/addr3/pac-A.tsv: run gate addr3 first" >&2; exit 2; }
  mkdir -p "$OUT/addr0d24"
  run addr0d24/pac-A pac0d "$BASE:proofs/libreac/fuzz_disco/lib" pac-A
  expect base addr0d24/pac-A 4 '^FLAGGED [0-9]+ rows'
  # the row-by-row difference from gate 6's 3d2eee813cce table; the rows whose verdict moved go to moved.tsv
  run addr0d24/diff python3 "$HERE/addr/run_diff.py" "$OUT/addr3/pac-A.tsv" "$OUT/addr0d24/pac-A.tsv" \
    --moved-out "$OUT/addr0d24/moved.tsv"
  expect base addr0d24/diff 0 '^run_diff: 145 rows differ; 82 verdicts moved; verdicts identical: no$'
  # every flagged row, and every row whose verdict moved, triaged by gate 1's script and hand table (0 DEFECT, 0 untriaged)
  python3 "$PAC0D24" --list-flag-classes > "$OUT/addr0d24/flag-classes.txt"
  run addr0d24/triage python3 "$HERE/addr/addr_triage.py" --rows "$OUT/addr0d24/pac-A.tsv" \
    --flags "$OUT/addr0d24/flag-classes.txt" --lib "$LIB" --cgif-lib "$CGIF_LIB" --pin "$PIN_A" --twin "$TWIN_A" \
    --cgif-nm "$CTL/syms/cgif_file_fuzzer.asan.nm" --hand "$HERE/addr/hand-triage.tsv" \
    --also "$OUT/addr0d24/moved.tsv" --out "$OUT/addr0d24/triage-A.tsv"
  expect base addr0d24/triage 0 'DEFECT 0, hand rows'
  # planted control: gate 1's plant (AE2k.v FF_mask 0x103b8 -> _start 0x30eac) on this version
  plant "$A/AE2k.v" "$OUT/addr0d24/plant/A/AE2k.v" 36 '0x103b8' '0x30eac'
  run addr0d24/plant pac0d "$OUT/addr0d24/plant" plant
  if tail -n 1 "$OUT/addr0d24/plant.out" | grep -qx 'rc=4' && \
     awk -F'\t' '$1=="DIFFERENT-SYMBOL" && $6=="A/AE2k.v" && $12=="0x30eac"' "$OUT/addr0d24/plant.tsv" | grep -q .; then
    echo "FIRED addr0d24/plant (AE2k.v FF_mask 0x103b8 -> 0x30eac: DIFFERENT-SYMBOL)" | tee -a "$OUT/verdicts.txt"
  else
    echo "VOID addr0d24/plant" | tee -a "$OUT/verdicts.txt"
  fi
}

# ---- gate 10: port_addr_check 205a90fd19b8 (installed after 0d24592683b6) and 0d24592683b6, gate 1's command and file
# set over the SERIES tree, compared row by row on that one tree
pacs() {  # pacs TOOL DST OUTNAME CACHE
  nice python3 "$1" --git "$HUB" --donors-from "$DONORS" --summary --fail-on-flags \
    --src "$CGIF_REF:proofs/cgif/cgif_file_fuzzer/lib" --dst "$2" \
    --paired-only --map A/=A/ --map =Reusable/ \
    --src-image A="$CGIF_BIN.asan" --src-image B="$CGIF_BIN.asan-ubsan" \
    --src-image P="$CGIF_BIN.plain" --src-image U="$CGIF_BIN.ubsan" \
    --dst-image A="$PIN_A:$TWIN_A" --dst-image B="$PINS/fuzz_disco.asan-ubsan:$TWINS/fuzz_disco.asan-ubsan" \
    --dst-image P="$PINS/fuzz_disco.plain:$TWINS/fuzz_disco.plain" --dst-image U="$PINS/fuzz_disco.ubsan:$TWINS/fuzz_disco.ubsan" \
    --assign '**=auto' --include 'A/**' --cache "$4" --out "$OUT/addr205a/$3.tsv"
}
plant_row() {  # plant_row NAME VERDICT FILE LINE VALUE: rc=4 and a row VERDICT at FILE:LINE holding VALUE (dst side)
  tail -n 1 "$OUT/addr205a/$1.out" | grep -qx 'rc=[04]' && \
    awk -F'\t' -v v="$2" -v f="$3" -v l="$4" -v x="$5" '$1==v && $6==f && $7==l && $12==x' "$OUT/addr205a/$1.tsv" | grep -q .
}
gate_addr205a() {
  need "$PAC205A" 205a90fd19b85ab3b9f1910ff13f144c1d72a28fe393209e1106a3b26fcdcb69
  need "$PAC0D24" 0d24592683b610123346567302caf1bf97e5ac9354cf05799dc7cfc21dc0f4fa
  local D=$OUT/addr205a
  local SL=$D/tree/proofs/libreac/fuzz_disco/lib
  rm -rf "$D/tree"; mkdir -p "$D/tree"
  git -C "$HUB" archive "$SERIES" proofs/libreac/fuzz_disco/lib | tar -x -C "$D/tree"   # the series files the triage reads
  run addr205a/pac-A pacs "$PAC205A" "$SERIES:proofs/libreac/fuzz_disco/lib" pac-A "$D/cache"
  expect base addr205a/pac-A 4 '^FLAGGED [0-9]+ rows'
  run addr205a/pac0d24-A pacs "$PAC0D24" "$SERIES:proofs/libreac/fuzz_disco/lib" pac0d24-A "$D/cache0d24"
  expect base addr205a/pac0d24-A 4 '^FLAGGED [0-9]+ rows'
  # the row-by-row difference 0d24592683b6 -> 205a90fd19b8 on the one tree; the moved rows go to moved.tsv
  run addr205a/diff python3 "$HERE/addr/run_diff.py" "$D/pac0d24-A.tsv" "$D/pac-A.tsv" --moved-out "$D/moved.tsv"
  expect base addr205a/diff 0 '^run_diff: 374 rows differ; 328 verdicts moved; verdicts identical: no$'
  # the owner's named-symbol fail-open of 205a90fd19b8: a row 0d24592683b6 reads DIFFERENT-SYMBOL or UNMEASURED-NAME and
  # 205a90fd19b8 SAME-SYMBOL is read by hand before it counts as a pass; the gate wants none
  if grep -Eq 'verdict (DIFFERENT-SYMBOL|UNMEASURED-NAME) -> SAME-SYMBOL' "$OUT/addr205a/diff.out"; then
    echo "FAIL addr205a/named (a row moved to SAME-SYMBOL from DIFFERENT-SYMBOL / UNMEASURED-NAME)" | tee -a "$OUT/verdicts.txt"
  else
    echo "PASS addr205a/named (no row DIFFERENT-SYMBOL / UNMEASURED-NAME -> SAME-SYMBOL)" | tee -a "$OUT/verdicts.txt"
  fi
  # every flagged row, and every moved row, triaged over the series files with the series hand table
  python3 "$PAC205A" --list-flag-classes > "$D/flag-classes.txt"
  run addr205a/triage python3 "$HERE/addr/addr_triage.py" --rows "$D/pac-A.tsv" --flags "$D/flag-classes.txt" \
    --lib "$SL" --cgif-lib "$CGIF_LIB" --pin "$PIN_A" --twin "$TWIN_A" --cgif-nm "$CTL/syms/cgif_file_fuzzer.asan.nm" \
    --hand "$HERE/addr/hand-triage-series.tsv" --also "$D/moved.tsv" --out "$D/triage-A.tsv"
  expect base addr205a/triage 0 'DEFECT 0, hand rows'
  # planted controls on 205a90fd19b8. Gate 1's plant (AE2k.v FF_mask 0x103b8 -> _start 0x30eac, a moved address).
  plant "$SL/A/AE2k.v" "$D/plant/A/AE2k.v" 36 '0x103b8' '0x30eac'
  run addr205a/plant pacs "$PAC205A" "$D/plant" plant "$D/cache"
  plant_row plant DIFFERENT-SYMBOL A/AE2k.v 36 0x30eac && tail -n 1 "$D/plant.out" | grep -qx 'rc=4' \
    && echo "FIRED addr205a/plant (AE2k.v FF_mask 0x103b8 -> 0x30eac: DIFFERENT-SYMBOL)" | tee -a "$OUT/verdicts.txt" \
    || echo "VOID addr205a/plant" | tee -a "$OUT/verdicts.txt"
  # The owner's plant, a size moved as a consistent relocation (its round_fa granule 0x40000 -> 0x4051c; this tree's
  # round_fa file pairs with no donor file): G = the allocator granule 262144 as the `/` operand of AFkm.v:611 set to
  # 0x410d4 (cgif's 0x40000 is UnpoisonBeforeMain+0x80, the A pin's UnpoisonBeforeMain is 0x41054); B = the bound
  # 0x200000 of AE30.v:1395 set to 0x2030c0 (cgif theDepot+0x78128 -> the A pin's theDepot 0x18af98 + 0x78128).
  # 205a90fd19b8 must flag each NON-ADDRESS-CHANGED; 0d24592683b6 reads each SAME-SYMBOL, the hole 205a90fd19b8 closes.
  plant "$SL/A/AFkm.v" "$D/plantG/A/AFkm.v" 611 '262144' '0x410d4'
  plant "$SL/A/AE30.v" "$D/plantB/A/AE30.v" 1395 '0x200000' '0x2030c0'
  local p f l x
  for p in G:A/AFkm.v:611:0x410d4 B:A/AE30.v:1395:0x2030c0; do
    IFS=: read -r p f l x <<< "$p"
    run addr205a/plant$p-205a pacs "$PAC205A" "$D/plant$p" plant$p-205a "$D/cache"
    plant_row plant$p-205a NON-ADDRESS-CHANGED "$f" "$l" "$x" && tail -n 1 "$D/plant$p-205a.out" | grep -qx 'rc=4' \
      && echo "FIRED addr205a/plant$p-205a ($f:$l -> $x: NON-ADDRESS-CHANGED)" | tee -a "$OUT/verdicts.txt" \
      || echo "VOID addr205a/plant$p-205a" | tee -a "$OUT/verdicts.txt"
    run addr205a/plant$p-0d24 pacs "$PAC0D24" "$D/plant$p" plant$p-0d24 "$D/cache0d24"
    plant_row plant$p-0d24 SAME-SYMBOL "$f" "$l" "$x" \
      && echo "PASS addr205a/plant$p-0d24 ($f:$l -> $x reads SAME-SYMBOL on 0d24592683b6: the hole)" | tee -a "$OUT/verdicts.txt" \
      || echo "FAIL addr205a/plant$p-0d24" | tee -a "$OUT/verdicts.txt"
  done
}

[ $# -ge 1 ] || { sed -n '2,42p' "$0"; exit 2; }
for g in "$@"; do
  case $g in
    all) gate_twin; gate_addr; gate_donordec; gate_codeptr; gate_ifchk; gate_cells; gate_addr3; gate_rc; gate_counts
         gate_addr0d24; gate_addr205a;;
    twin|addr|donordec|codeptr|ifchk|cells|addr3|rc|counts|addr0d24|addr205a) "gate_$g";;
    *) echo "run.sh: unknown gate $g" >&2; exit 2;;
  esac
done
