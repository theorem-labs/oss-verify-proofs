#!/bin/bash
# run_gates.sh -- reac-repacer/fuzz_uci image B (asan-ubsan) start-up data set: every gate, each with its control
# FIRST. OSSV-249 T1 "B". rule 24: proves no function (start-up facts).
# Method of record: the fuzz_decode B gate set (GATES-decB.md + run_gates.sh / run_gates2.sh / gates_dec.py /
# recount_dec.py / yb13/run_gates_yb13.sh / codeptr-c0ce/REPORT.md) and the image-A start-up gate lines (uci-sg/start/*/run_*.sh).
# Tool set of record: commit dbb5a97ad14's corrected start-up set, extracted at
# $FT and run as $FRT = `bash $FT/frozen-run.sh $FT/startup-set-2026-10-30.tsv TOOL` (absolute
# bundle path): codeptr 12348302dfd2, pins 4778073f01be, keyset f050b43e480e, ifchk f5cde600cc18 - byte-equal to the rows
# of commit 8cd71d3a4bb's earlier start-up set ($BUN), on which the first G1/G2 run was made
# (logs/run1-8cd71d3a4bb/). NEVER the withdrawn bundle 894122e7fa24;
# nothing here runs codeptr c0ce606ed1fa.
#
#   bash run_gates.sh [G0 G1 ... G12]      default: all, in order. G0 (snapshot + inputs) runs first whenever any gate
#                                           runs, unless NOSNAP=1. Logs: logs/G<n>*.log; summary on stdout.
# Reads WK/gen, WK/raw, the images and the donor lib; writes only logs/ (here) and $UCIB_GATEWORK. Every machine path
# comes from the lane env file (env.example.sh names each variable); none is written here.
set -uo pipefail
: "${UCIB_UB:?source the lane env file first (env.example.sh names every variable)}"
G=$W/sub/gates; T=$G/tools; L=$G/logs; X=${UCIB_GATEWORK:?}
export UCIB_GATEWORK
export PYTHONDONTWRITEBYTECODE=1
FRT="bash $FT/frozen-run.sh $FT/startup-set-2026-10-30.tsv"   # the set of record (absolute bundle path)
NS=OssFuzzTheorems.Proofs.reac_repacer.fuzz_uci
ALL19="YB01 YB03 YB05 YB12 YB13 YB1h YB1k YB1l YB1m YB1v YCej YD1k YD1y YD2i YD2j YE23 YE37 YE3i YF0m"
UNM=$WK/nm/uciB.nm.txt                       # nm of the unstripped twin (fuzz_uci B's names)
CBN=$X/in/cgifB.nm                           # cgif B recovered nm, '#' lines removed (G0)
A9AF0M=$X/in/a9.AF0m.v   # image A's AF0m for pins --pair, read in G0 from the merged core commit below
ACORE=f47e2a8927b9   # the uci B core head, which holds image A's core e0773c4bc14f and this layer 89a444c41f23
mkdir -p "$L" "$X"
rc() { echo "RESULT $1 rc=$2"; }
present() { for n in $ALL19; do [ -f "$X/in/gen/$n.v" ] && printf '%s ' "$n"; done; }

G0() {  # snapshot of the 19 files + their raw twins; cgif inputs; sha256 of every input and tool
  rm -rf "$X/in"; mkdir -p "$X/in/gen" "$X/in/raw" "$X/in/cgif/A"
  git -C "${UCIB_OVPI:?}" show "$ACORE:proofs/reac-repacer/fuzz_uci/lib/A/AF0m.v" > "$A9AF0M" || echo "G0: cannot read $ACORE lib/A/AF0m.v"
  for n in $ALL19; do
    [ -f "$WK/gen/$n.v" ] && cp "$WK/gen/$n.v" "$X/in/gen/" || echo "G0: MISSING $WK/gen/$n.v"
    [ -f "$WK/raw/$n.v" ] && cp "$WK/raw/$n.v" "$X/in/raw/"
    cp "$DLIBC/$n.v" "$X/in/cgif/"; cp "$DLIBC/A/A${n:1}.v" "$X/in/cgif/A/"
  done
  cp "$WK/gen/YCej.universe.json" "$X/in/gen/" 2>/dev/null
  cp "$DLIBC/YF0l.v" "$DLIBC/YB1w.v" "$X/in/cgif/"; cp "$DLIBC/A/AF0l.v" "$DLIBC/A/AF0m.v" "$DLIBC/A/AB01.v" "$X/in/cgif/A/"
  grep -v '^#' "$S/syms/cgif_file_fuzzer.asan-ubsan.nm" > "$CBN"
  {
    echo "# G0 snapshot $(date -u +%FT%TZ): the 19 files (WK/gen), their donor-namespace twins (WK/raw), images, names"
    (cd "$X/in/gen" && sha256sum *.v *.json)
    (cd "$X/in/raw" && sha256sum *.v | sed 's/  /  raw\//')
    sha256sum "$UB" "$UBs" "$CB" "$CA" "$UA" "$UAs" "$UNM" "$S/syms/cgif_file_fuzzer.asan-ubsan.nm" "$CBN" \
      "$UCIB_LT/cgifB.recovered.nm" "$UCIB_OBJDUMP" "$UCIB_PCB/stage-out/B/YD1g.v" \
      "$BUN" "$S/frozen-run.sh" "$FT/startup-set-2026-10-30.tsv" "$FT/frozen-run.sh" "$A9AF0M"
    echo "# donor lib: git archive 25e3d17bdb50 of proofs/cgif/cgif_file_fuzzer/lib (DLIBC)"
    (cd "$X/in/cgif" && sha256sum *.v A/*.v)
  } > "$L/SHA256.inputs.txt"
  (cd "$T" && find . -type f ! -name '*.pyc' | sort | xargs sha256sum) > "$L/SHA256.tools.txt"
  sha256sum "$G"/run_gates.sh "$G"/codeptr-decl.sh "$G"/pac_table.py >> "$L/SHA256.tools.txt"
  # the two gen_ad1k versions lowbeg.py imports (G10): 814c81b8966e (8cd71d3a4bb, YD1k's generator) and 43a0cf0abc67 (dbb5)
  local b
  for b in 8cd7:"$BUN":"$S/frozen" dbb5:"$FT/startup-set-2026-10-30.tsv":"$FT/frozen"; do
    local tag=${b%%:*} rest=${b#*:}; local bun=${rest%%:*} fz=${rest#*:}
    rm -rf "$X/bundle-$tag"; mkdir -p "$X/bundle-$tag"
    while IFS=$'\t ' read -r name sha; do case "$name" in ''|'#'*) continue;; esac
      mkdir -p "$X/bundle-$tag/$(dirname "$name")"; cp "$fz/$(basename "$name").frozen-$sha" "$X/bundle-$tag/$name"; done < "$bun"
    ln -sfn "$(dirname "$fz")/pautrlen" "$X/bundle-$tag/pautrlen"
  done
  echo "G0 snapshot: $(ls "$X/in/gen"/*.v | wc -l) of 19 files present: $(present)"
  echo "G0 cgif B nm: $(sha256sum "$CBN" | cut -c1-12) ('#'-stripped $S/syms/cgif_file_fuzzer.asan-ubsan.nm $(sha256sum "$S/syms/cgif_file_fuzzer.asan-ubsan.nm" | cut -c1-12)); \$UCIB_LT/cgifB.recovered.nm $(sha256sum "$UCIB_LT/cgifB.recovered.nm" | cut -c1-12)"
}

G1() {  # kimg_overlap FROZEN acfd7418176d (of record) on every file; 5db341e3cd62 on YB01 / YB03
  local K=$T/kimg_overlap-acfd7418176d.py K5=$T/kimg_overlap-5db341e3cd62.py a=() c=()
  echo "=== G1 CONTROL: kimg_overlap acfd7418176d on cgif's released lib/YB01.v / lib/YB03.v at 25e3d17bdb50, cgif B image ==="
  python3 "$K" "$DON" 25e3d17bdb50 proofs/cgif/cgif_file_fuzzer/lib/YB01.v "$CB" \
    25e3d17bdb50 proofs/cgif/cgif_file_fuzzer/lib/YB03.v "$CB" > "$L/G1.kimg.acfd.control.log" 2>&1
  rc "G1 kimg acfd CONTROL cgif YB01/YB03" $?; cat "$L/G1.kimg.acfd.control.log"
  for n in $(present); do c+=(FILE "$X/in/cgif/$n.v" "$CB"); a+=(FILE "$X/in/gen/$n.v" "$UB"); done
  echo "=== G1 CONTROL (per file): the same tool on cgif's released counterpart of every file, cgif B image ==="
  python3 "$K" "$DON" "${c[@]}" > "$L/G1.kimg.acfd.control-all.log" 2>&1
  rc "G1 kimg acfd CONTROL cgif counterparts" $?; sed "s#$X/in/##" "$L/G1.kimg.acfd.control-all.log"
  echo "=== G1 kimg_overlap acfd7418176d on the fuzz_uci B files, fuzz_uci B pin ==="
  python3 "$K" "$DON" "${a[@]}" > "$L/G1.kimg.acfd.uciB.log" 2>&1
  rc "G1 kimg acfd uciB" $?; sed "s#$X/in/##" "$L/G1.kimg.acfd.uciB.log"
  echo "=== G1b kimg_overlap 5db341e3cd62 (decode B's version): CONTROL cgif YB01/YB03, then fuzz_uci B YB01/YB03 ==="
  python3 "$K5" "$DON" 25e3d17bdb50 proofs/cgif/cgif_file_fuzzer/lib/YB01.v "$CB" \
    25e3d17bdb50 proofs/cgif/cgif_file_fuzzer/lib/YB03.v "$CB" > "$L/G1.kimg.5db3.control.log" 2>&1
  rc "G1b kimg 5db3 CONTROL" $?; cat "$L/G1.kimg.5db3.control.log"
  python3 "$K5" "$DON" FILE "$X/in/gen/YB01.v" "$UB" FILE "$X/in/gen/YB03.v" "$UB" > "$L/G1.kimg.5db3.uciB.log" 2>&1
  rc "G1b kimg 5db3 uciB" $?; sed "s#$X/in/##" "$L/G1.kimg.5db3.uciB.log"
}

# --- codeptr declarations: each value NOT stale, keyed by role and symbol / section + offset in BOTH images.
#     Filled from pass 1 (logs/G2c.codeptr.pass1.log); the evidence for each is in GATES-TABLE.md section G2.
. "$G/codeptr-decl.sh"

G2() {  # codeptr 12348302dfd2 (start-up set of commit dbb5a97ad14), the full check: --stale-image + --stale-names + --stale-file
  echo "=== G2a CONTROL: codeptr-controls.sh known answers (tools/frozen/codeptr-controls.dbb5.sh = the known-answer script 25c012a65b96 with the dbb5 runner), donor worktree $DON ==="
  bash "$T/frozen/codeptr-controls.dbb5.sh" "$FT/startup-set-2026-10-30.tsv" "$DON" > "$L/G2a.codeptr-controls.log" 2>&1
  rc "G2a codeptr-controls" $?; tail -3 "$L/G2a.codeptr-controls.log" | cut -c1-400
  local base=(--image "$UB" --names "$UNM" --stale-image "$CB" --stale-names "$CBN")
  echo "=== G2b POSITIVE CONTROL: cgif's UNRELOCATED YD1k / YD2i / YD2j against fuzz_uci B's image (must find, rc 1) ==="
  rm -rf "$X/ctl/cp"; mkdir -p "$X/ctl/cp"; local sf=() f
  for f in YD1k YD2i YD2j; do cp "$DLIBC/$f.v" "$X/ctl/cp/$f.v"; sf+=(--stale-file "$X/ctl/cp/$f.v=$DLIBC/$f.v"); done
  $FRT codeptr.py "${base[@]}" "${sf[@]}" "$X/ctl/cp/YD1k.v" "$X/ctl/cp/YD2i.v" "$X/ctl/cp/YD2j.v" > "$L/G2b.codeptr.posctl.log" 2>&1
  local r=$?; rc "G2b codeptr POSITIVE control (tool rc must be 1)" $r
  grep -v '^frozen-run' "$L/G2b.codeptr.posctl.log" | grep -E 'FINDINGS|UNMEASURED|^codeptr' | cut -c1-260
  sf=(); local files=()
  for f in $(present); do sf+=(--stale-file "$X/in/gen/$f.v=$DLIBC/$f.v"); files+=("$X/in/gen/$f.v"); done
  echo "=== G2c PASS 1: every file, each paired with cgif's donor file of the same name, no declaration ==="
  $FRT codeptr.py "${base[@]}" "${sf[@]}" "${files[@]}" > "$L/G2c.codeptr.pass1.log" 2>&1
  rc "G2c codeptr pass 1" $?; grep -v '^frozen-run' "$L/G2c.codeptr.pass1.log" | grep -E 'FINDINGS|UNMEASURED|NOT read|^codeptr' | cut -c1-400
  echo "=== G2e the evidence of every declaration, by command on BOTH images (tools/decl_evidence.py) ==="
  python3 "$T/decl_evidence.py" "$UB" "$WK/nm/uciB.nmS.txt" "$CB" "$CBN" "$X/in/gen" "$X/in/cgif" > "$L/G2e.decl_evidence.log" 2>&1
  rc "G2e declaration evidence" $?; grep -E '^==|FAIL|^decl_evidence' "$L/G2e.decl_evidence.log" | cut -c1-300
  echo "=== G2d PASS 2: the same + ${#DECL[@]} declaration arguments (codeptr-decl.sh) ==="
  $FRT codeptr.py "${base[@]}" "${sf[@]}" "${DECL[@]}" "${files[@]}" > "$L/G2d.codeptr.pass2.log" 2>&1
  rc "G2d codeptr pass 2" $?; grep -v '^frozen-run' "$L/G2d.codeptr.pass2.log" | grep -E 'FINDINGS|UNMEASURED|NOT read|NOT an address|declared|^codeptr' | cut -c1-400
}

G3() {  # port_addr_check FROZEN 16f8a030c869 (+ scan_literals ae01d69b2ee4, the sibling decode B ran with)
  rm -rf "$X/pac"; mkdir -p "$X/pac/cgifA" "$X/pac/cgifB" "$X/pac/cache"
  cp -r "${UCIB_PACCACHE:?}/." "$X/pac/cache/"
  local inc=() n
  for n in $(present); do cp "$X/in/cgif/A/A${n:1}.v" "$X/pac/cgifA/$n.v"; cp "$X/in/cgif/$n.v" "$X/pac/cgifB/$n.v"; inc+=(--include "$n.v"); done
  local P="python3 $T/pac/port_addr_check.py --git $DON --donors-from "${UCIB_DONORBIN:?}" --cache $X/pac/cache --paired-only --summary"
  echo "=== G3 CONTROL: cgif's own released A set (renamed to its Y twins) -> its B set, the same files ==="
  $P --src "$X/pac/cgifA" --src-image "B=$CA" --dst "$X/pac/cgifB" --dst-image "B=$CB" --out "$L/G3.pac.cgifAB.tsv" "${inc[@]}" > "$L/G3.pac.cgifAB.log" 2>&1
  rc "G3 port_addr_check CONTROL cgif A->B" $?; grep -v '^#' "$L/G3.pac.cgifAB.log" | tail -40
  echo "=== G3 port_addr_check: cgif's released B set (source) -> the fuzz_uci B files (port) ==="
  $P --src "$X/pac/cgifB" --src-image "B=$CB" --dst "$X/in/gen" --dst-image "B=$UB:$UBs" --out "$L/G3.pac.uciB.tsv" "${inc[@]}" > "$L/G3.pac.uciB.log" 2>&1
  rc "G3 port_addr_check cgif B -> uci B" $?; grep -v '^#' "$L/G3.pac.uciB.log" | tail -40
  python3 "$G/pac_table.py" "$L/G3.pac.cgifAB.tsv" "$L/G3.pac.uciB.tsv" > "$L/G3.pac.table.md" 2>&1
  rc "G3 pac_table" $?; cat "$L/G3.pac.table.md"
  echo "  16f8a030c869 has no GENERATOR-FILL class (added in 0767e70e074a); rows with that verdict: control $(awk -F'\t' '$1=="GENERATOR-FILL"' "$L/G3.pac.cgifAB.tsv" | wc -l), uci B $(awk -F'\t' '$1=="GENERATOR-FILL"' "$L/G3.pac.uciB.tsv" | wc -l)"
  # cb0e067e3bae: the installed version of record (frozen copy + versions/cb0e067e3bae/ with its
  # helpers, copied to tools/pac-cb0e and run from there). Rule of record: triage EVERY GENERATOR-FILL row (pac_fill.py).
  local P2="python3 $T/pac-cb0e/port_addr_check.py --git $DON --donors-from "${UCIB_DONORBIN:?}" --cache $X/pac/cache --paired-only --summary"
  echo "=== G3b CONTROL: port_addr_check cb0e067e3bae, cgif's own released A set -> its B set ==="
  $P2 --src "$X/pac/cgifA" --src-image "B=$CA" --dst "$X/pac/cgifB" --dst-image "B=$CB" --out "$L/G3b.pac-cb0e.cgifAB.tsv" "${inc[@]}" > "$L/G3b.pac-cb0e.cgifAB.log" 2>&1
  rc "G3b port_addr_check cb0e CONTROL cgif A->B" $?; grep -v '^#' "$L/G3b.pac-cb0e.cgifAB.log" | grep -v '^ ' | grep -v '^INPUTS' | tail -30
  echo "=== G3b port_addr_check cb0e067e3bae: cgif's released B set -> the fuzz_uci B files ==="
  $P2 --src "$X/pac/cgifB" --src-image "B=$CB" --dst "$X/in/gen" --dst-image "B=$UB:$UBs" --out "$L/G3b.pac-cb0e.uciB.tsv" "${inc[@]}" > "$L/G3b.pac-cb0e.uciB.log" 2>&1
  rc "G3b port_addr_check cb0e cgif B -> uci B" $?; grep -v '^#' "$L/G3b.pac-cb0e.uciB.log" | grep -v '^ ' | grep -v '^INPUTS' | tail -30
  python3 "$G/pac_table.py" "$L/G3b.pac-cb0e.cgifAB.tsv" "$L/G3b.pac-cb0e.uciB.tsv" > "$L/G3b.pac-cb0e.table.md" 2>&1
  rc "G3b pac_table (cb0e)" $?; cat "$L/G3b.pac-cb0e.table.md"
  echo "=== G3c GENERATOR-FILL triage (tools/pac_fill.py): every row a measured reason; CONTROL cgif A -> B first ==="
  python3 "$T/pac_fill.py" "$L/G3b.pac-cb0e.cgifAB.tsv" "$X/pac/cgifB/YF0m.v" "$X/pac/cgifA/YF0m.v" "$CB" "$CBN" "$CA" "$S/syms/cgif_file_fuzzer.asan.nm" > "$L/G3c.fill.cgifAB.log" 2>&1
  rc "G3c fill triage CONTROL cgif A->B" $?; cut -c1-400 "$L/G3c.fill.cgifAB.log"
  python3 "$T/pac_fill.py" "$L/G3b.pac-cb0e.uciB.tsv" "$X/in/gen/YF0m.v" "$X/in/cgif/YF0m.v" "$UB" "$WK/nm/uciB.nmS.txt" "$CB" "$CBN" > "$L/G3c.fill.uciB.log" 2>&1
  rc "G3c fill triage uci B" $?; cut -c1-400 "$L/G3c.fill.uciB.log"
}

G3e() {  # port_addr_check e165063a0081, the version of record (versions/e165063a0081, FLAG-CLASSES 575d398c6022):
         # --fail-on-flags, --paired-only, --assign '*.v=B' (the 19 files are ONE build, image B, checked against image B,
         # so e165's symbol-named-definition rule reads the image each file describes; fix (3) of record). Then: the row
         # join with cb0e067e3bae on the SAME final bytes (pac_moved.py), the GENERATOR-FILL triage (pac_fill.py), and the
         # independent .symtab check of every symbol-named definition (symname_check.py), each control first.
  rm -rf "$T/pac-e165"; cp -r "${UCIB_PACE165:?}" "$T/pac-e165"; chmod -R u+w "$T/pac-e165"
  echo "G3e port_addr_check.py $(sha256sum "$T/pac-e165/port_addr_check.py" | cut -c1-12), scan_literals.py $(sha256sum "$T/pac-e165/scan_literals.py" | cut -c1-12)"
  local inc=() n; for n in $(present); do inc+=(--include "$n.v"); done
  local FL="--git $DON --donors-from ${UCIB_DONORBIN:?} --cache $X/pac/cache --paired-only --summary --fail-on-flags --assign *.v=B"
  echo "=== G3e CONTROL: e165063a0081, cgif's own released A set -> its B set ==="
  python3 "$T/pac-e165/port_addr_check.py" $FL --src "$X/pac/cgifA" --src-image "B=$CA" --dst "$X/pac/cgifB" --dst-image "B=$CB" --out "$L/G3e.pac-e165.cgifAB.tsv" "${inc[@]}" > "$L/G3e.pac-e165.cgifAB.log" 2>&1
  rc "G3e port_addr_check e165 CONTROL cgif A->B (4 = findings, as cb0e)" $?; grep -E '^FLAGGED|^FLAG-CLASSES|^GENERATOR-FILL|^UNMEASURED' "$L/G3e.pac-e165.cgifAB.log"
  echo "=== G3e e165063a0081: cgif's released B set -> the fuzz_uci B files ==="
  python3 "$T/pac-e165/port_addr_check.py" $FL --src "$X/pac/cgifB" --src-image "B=$CB" --dst "$X/in/gen" --dst-image "B=$UB:$UBs" --out "$L/G3e.pac-e165.uciB.tsv" "${inc[@]}" > "$L/G3e.pac-e165.uciB.log" 2>&1
  rc "G3e port_addr_check e165 cgif B -> uci B (4 = findings)" $?; grep -E '^FLAGGED|^FLAG-CLASSES|^GENERATOR-FILL|^UNMEASURED' "$L/G3e.pac-e165.uciB.log"
  echo "=== G3e cb0e067e3bae on the SAME final bytes with the same flags, for the row join ==="
  python3 "$T/pac-cb0e/port_addr_check.py" $FL --src "$X/pac/cgifB" --src-image "B=$CB" --dst "$X/in/gen" --dst-image "B=$UB:$UBs" --out "$L/G3e.pac-cb0e.final.uciB.tsv" "${inc[@]}" > "$L/G3e.pac-cb0e.final.uciB.log" 2>&1
  rc "G3e port_addr_check cb0e same inputs (4 = findings)" $?; grep -E '^FLAGGED|^FLAG-CLASSES|^GENERATOR-FILL' "$L/G3e.pac-cb0e.final.uciB.log"
  {
    echo "TRIAGE port_addr_check e165063a0081 vs cb0e067e3bae on the final 19 files (pac_moved.py: rows keyed by file, line, sentence, index, values)"
    python3 "$T/pac_moved.py" "$L/G3e.pac-cb0e.final.uciB.tsv" "$L/G3e.pac-e165.uciB.tsv"
    echo "TRIAGE YH03 rows in this run: $(awk -F'\t' '$4 ~ /YH03/ || $6 ~ /YH03/' "$L/G3e.pac-e165.uciB.tsv" | wc -l) (YH03.v is not one of the 19 files)"
    echo "TRIAGE GENERATOR-FILL rows of e165, each with a measured reason (pac_fill.py; CONTROL first on cgif A->B):"
    python3 "$T/pac_fill.py" "$L/G3e.pac-e165.cgifAB.tsv" "$X/pac/cgifB/YF0m.v" "$X/pac/cgifA/YF0m.v" "$CB" "$CBN" "$CA" "$S/syms/cgif_file_fuzzer.asan.nm" > "$L/G3e.fill.cgifAB.log" 2>&1
    echo "TRIAGE pac_fill CONTROL cgif A->B rc=$? (1 = it refuses the 236 YCej lines outside its YF0m rules: fails closed)"; tail -1 "$L/G3e.fill.cgifAB.log"
    python3 "$T/pac_fill.py" "$L/G3e.pac-e165.uciB.tsv" "$X/in/gen/YF0m.v" "$X/in/cgif/YF0m.v" "$UB" "$WK/nm/uciB.nmS.txt" "$CB" "$CBN" > "$L/G3e.fill.uciB.log" 2>&1
    echo "TRIAGE pac_fill uci B rc=$?"; cat "$L/G3e.fill.uciB.log"
    echo "TRIAGE independent .symtab check of every symbol-named definition (symname_check.py; CONTROL first: 1 right + 2 planted wrong):"
    printf '(* control *)\nDefinition tfib_A_main : Z := 0x7ee48.\nDefinition tfib_A_sysconf : Z := 0x7ee48.\nDefinition src0_D_stderr : Z := 0x9b6d8.\n' > "$X/symname_ctl.v"
    python3 "$T/symname_check.py" "$UBs" "$X/symname_ctl.v"; echo "TRIAGE symname CONTROL rc=$? (1 = the two planted rows caught)"
    python3 "$T/symname_check.py" "$UBs" "$X/in/gen"/*.v; echo "TRIAGE symname uci B rc=$?"
  } > "$L/G3e.triage.uciB.log" 2>&1
  rc "G3e triage" $?; cat "$L/G3e.triage.uciB.log" | cut -c1-400
}

G3g() {  # port_addr_check efa19b81e92b, the version of record since 10:17Z (versions/efa19b81e92b, FLAG-CLASSES
         # 575d398c6022, unchanged): it fixes e165's mixed-build regression -- the named-symbol rule is read against
         # the build the FILE describes, and a src0_D_ cell whose only candidate of that name is a FUNCTION reads as
         # OK-BY-LOAD or UNMEASURED-NAME, never as a flag. Same inputs, same flags and the same control-first order as
         # G3e, so the two runs join row by row (pac_moved.py e165 -> efa1); then the GENERATOR-FILL triage (pac_fill.py)
         # and the independent .symtab check (symname_check.py), each control first.
  rm -rf "$T/pac-efa1"; cp -r "${UCIB_PACEFA1:?}" "$T/pac-efa1"; chmod -R u+w "$T/pac-efa1"
  echo "G3g port_addr_check.py $(sha256sum "$T/pac-efa1/port_addr_check.py" | cut -c1-12), scan_literals.py $(sha256sum "$T/pac-efa1/scan_literals.py" | cut -c1-12)"
  local inc=() n; for n in $(present); do inc+=(--include "$n.v"); done
  local FL="--git $DON --donors-from ${UCIB_DONORBIN:?} --cache $X/pac/cache --paired-only --summary --fail-on-flags --assign *.v=B"
  echo "=== G3g CONTROL: efa19b81e92b, cgif's own released A set -> its B set ==="
  python3 "$T/pac-efa1/port_addr_check.py" $FL --src "$X/pac/cgifA" --src-image "B=$CA" --dst "$X/pac/cgifB" --dst-image "B=$CB" --out "$L/G3g.pac-efa1.cgifAB.tsv" "${inc[@]}" > "$L/G3g.pac-efa1.cgifAB.log" 2>&1
  rc "G3g port_addr_check efa1 CONTROL cgif A->B (4 = findings, as e165)" $?; grep -E '^FLAGGED|^FLAG-CLASSES|^GENERATOR-FILL|^UNMEASURED|^OK-BY-LOAD' "$L/G3g.pac-efa1.cgifAB.log"
  echo "=== G3g efa19b81e92b: cgif's released B set -> the fuzz_uci B files ==="
  python3 "$T/pac-efa1/port_addr_check.py" $FL --src "$X/pac/cgifB" --src-image "B=$CB" --dst "$X/in/gen" --dst-image "B=$UB:$UBs" --out "$L/G3g.pac-efa1.uciB.tsv" "${inc[@]}" > "$L/G3g.pac-efa1.uciB.log" 2>&1
  rc "G3g port_addr_check efa1 cgif B -> uci B (4 = findings)" $?; grep -E '^FLAGGED|^FLAG-CLASSES|^GENERATOR-FILL|^UNMEASURED|^OK-BY-LOAD' "$L/G3g.pac-efa1.uciB.log"
  {
    echo "TRIAGE port_addr_check e165063a0081 -> efa19b81e92b on the final 19 files (pac_moved.py: rows keyed by file, line, sentence, index, values)"
    python3 "$T/pac_moved.py" "$L/G3e.pac-e165.uciB.tsv" "$L/G3g.pac-efa1.uciB.tsv"
    echo "TRIAGE CONTROL cgif A -> B, e165 -> efa1 (the same join on the control):"
    python3 "$T/pac_moved.py" "$L/G3e.pac-e165.cgifAB.tsv" "$L/G3g.pac-efa1.cgifAB.tsv"
    echo "TRIAGE GENERATOR-FILL rows of efa1, each with a measured reason (pac_fill.py; CONTROL first on cgif A->B):"
    python3 "$T/pac_fill.py" "$L/G3g.pac-efa1.cgifAB.tsv" "$X/pac/cgifB/YF0m.v" "$X/pac/cgifA/YF0m.v" "$CB" "$CBN" "$CA" "$S/syms/cgif_file_fuzzer.asan.nm" > "$L/G3g.fill.cgifAB.log" 2>&1
    echo "TRIAGE pac_fill CONTROL cgif A->B rc=$? (1 = it refuses the 236 YCej lines outside its YF0m rules: fails closed)"; tail -1 "$L/G3g.fill.cgifAB.log"
    python3 "$T/pac_fill.py" "$L/G3g.pac-efa1.uciB.tsv" "$X/in/gen/YF0m.v" "$X/in/cgif/YF0m.v" "$UB" "$WK/nm/uciB.nmS.txt" "$CB" "$CBN" > "$L/G3g.fill.uciB.log" 2>&1
    echo "TRIAGE pac_fill uci B rc=$?"; cat "$L/G3g.fill.uciB.log"
    echo "TRIAGE independent .symtab check of every symbol-named definition (symname_check.py; CONTROL first: 1 right + 2 planted wrong):"
    printf '(* control *)\nDefinition tfib_A_main : Z := 0x7ee48.\nDefinition tfib_A_sysconf : Z := 0x7ee48.\nDefinition src0_D_stderr : Z := 0x9b6d8.\n' > "$X/symname_ctl.v"
    python3 "$T/symname_check.py" "$UBs" "$X/symname_ctl.v"; echo "TRIAGE symname CONTROL rc=$? (1 = the two planted rows caught)"
    python3 "$T/symname_check.py" "$UBs" "$X/in/gen"/*.v; echo "TRIAGE symname uci B rc=$?"
  } > "$L/G3g.triage.uciB.log" 2>&1
  rc "G3g triage" $?; cat "$L/G3g.triage.uciB.log" | cut -c1-400
}

G4() {  # the by-role code-address check classify.py 8daec37298e7 + unit uciB (config only)
  rm -rf "$X/classify"; mkdir -p "$X/classify"
  echo "=== G4 CONTROL FIRST: planted copy (plant_uciB.py), .text end + 4 = 0x95b94 in CODE cells must be flagged, in a DATA cell not ==="
  python3 "$T/classify/plant_uciB.py" "$X/in/gen" "$X/classify/planted" > "$L/G4.plant.log" 2>&1; rc "G4 plant" $?; cat "$L/G4.plant.log"
  (cd "$X/classify" && python3 "$T/classify/classify.py" --unit uciB --files "$X/classify/planted" --out "$X/classify/out" --tag .planted) > "$L/G4.classify.planted.log" 2>&1
  rc "G4 classify PLANTED (must be rc 1)" $?; cat "$L/G4.classify.planted.log"
  python3 - "$L/G4.plant.log" "$L/G4.classify.planted.log" <<'EOF'; rc "G4 planted control verdict" $?
import re, sys
pl = [re.match(r'planted (\S+) (\S+):(\d+)', l).groups() for l in open(sys.argv[1]) if l.startswith('planted ')]
fl = {(m.group(1), int(m.group(2))) for m in re.finditer(r'FINDING (\S+):(\d+) ', open(sys.argv[2]).read())}
ok = True
for tag, f, ln in pl:
    hit = (f, int(ln)) in fl
    want = tag.endswith('CODE')
    print('  %-8s %s:%s flagged=%s want=%s %s' % (tag, f, ln, hit, want, 'ok' if hit == want else 'WRONG'))
    ok &= hit == want
extra = fl - {(f, int(ln)) for _, f, ln in pl}
print('  findings not at a plant: %d %s' % (len(extra), sorted(extra)))
print('  PLANTED CONTROL: %s' % ('PASS' if ok and not extra else 'FAIL'))
sys.exit(0 if ok and not extra else 1)
EOF
  echo "=== G4 classify.py on the fuzz_uci B files ==="
  (cd "$X/classify" && python3 "$T/classify/classify.py" --unit uciB --out "$X/classify/out") > "$L/G4.classify.uciB.log" 2>&1
  rc "G4 classify uciB" $?; cat "$L/G4.classify.uciB.log"
  cp "$X/classify/out/uciB.tsv" "$X/classify/out/uciB.summary.tsv" "$L/" 2>/dev/null; mv "$L/uciB.tsv" "$L/G4.classify.uciB.tsv"; mv "$L/uciB.summary.tsv" "$L/G4.classify.uciB.summary.tsv"
  echo "=== G4 coverage: files classify.py reads (its own regex ^[AY](F0m|B\\w\\w)\\.v\$) and the literals its lemma reader skips ==="
  python3 - "$X/in/gen" "$L/G4.classify.uciB.tsv" "$UB" <<'EOF' > "$L/G4.coverage.log" 2>&1; rc "G4 coverage report" $?; cat "$L/G4.coverage.log"
import collections, os, re, sys
from elftools.elf.elffile import ELFFile
gd, tsv, img = sys.argv[1:4]
e = ELFFile(open(img, 'rb'))
tx = e.get_section_by_name('.text'); tlo, thi = tx['sh_addr'], tx['sh_addr'] + tx['sh_size']
per = collections.Counter(l.split('\t')[0] for l in open(tsv).read().split('\n')[1:] if l)
allf = sorted(f for f in os.listdir(gd) if f.endswith('.v'))
inside = [f for f in allf if re.match(r'^[AY](F0m|B\w\w)\.v$', f)]
print('  classify.py reads %d of %d files: %s' % (len(inside), len(allf), ', '.join('%s %d' % (f[:-2], per.get(f, 0)) for f in inside)))
print('  outside its scope (by design: AF0m / AB* only): %s' % ' '.join(f[:-2] for f in allf if f not in inside))
# the lemma reader (classify_lemmas) matches (?<![\w.])(0x..|\d+)(?![\w.]): a literal right before a sentence-final '.'
# is not read. List every such literal of the files it reads with that reader, and where its value lies.
for f in inside:
    if f[1:4] in ('F0m', 'B01', 'B03', 'B05', 'B12'):
        continue
    for i, l in enumerate(open(os.path.join(gd, f)).read().split('\n'), 1):
        if l.lstrip().startswith('(*') or l.startswith('From') or l.startswith('Require'):
            continue
        for m in re.finditer(r'(?<![\w.])(0x[0-9a-fA-F]+|\d+)\.(?!\w)', l):
            v = int(m.group(1), 0)
            print('  NOT READ by the lemma reader: %s:%d %s (%s) %s' % (f, i, m.group(1), 'inside .text [%#x, %#x)' % (tlo, thi) if tlo <= v < thi else 'not in .text', l.strip()[:90]))
EOF
}

G5() {  # recount: decode's recount_dec.py with fuzz_uci B's IMG table (control row cgifB first)
  echo "=== G5 recount_uci.py (= recount_dec.py ce9e514496ac, IMG table + paths only) ==="
  python3 "$T/recount_uci.py" > "$L/G5.recount.log" 2>&1; rc "G5 recount" $?; cat "$L/G5.recount.log"
}

G6() {  # keyed-table scan
  echo "=== G6 keyed-table scan (twin symbols; cgif AF0l / YF0l control first; 19 files) ==="
  python3 "$T/keyed_scan_uci.py" "$UBs" "$X/in/cgif" $(for n in $(present); do printf '%s ' "$X/in/gen/$n.v"; done) > "$L/G6.keyed.log" 2>&1
  rc "G6 keyed scan" $?; sed "s#$X/in/##" "$L/G6.keyed.log" | cut -c1-400
}

G7() {  # pins.py 4778073f01be stamp (on copies) + emitcheck; keyset f050b43e480e check
  rm -rf "$X/stamp"; mkdir -p "$X/stamp"; local n r
  echo "=== G7a pins.py check (the pin) ==="
  $FRT pins.py check "$UB" --twin "$UBs" > "$L/G7a.pins.check.log" 2>&1; rc "G7a pins check" $?; grep -v '^frozen-run' "$L/G7a.pins.check.log"
  echo "=== G7b pins.py stamp per file (a9's form; on a COPY in $X/stamp, then the copy is compared with the file) ==="
  for n in $(present); do
    cp "$X/in/gen/$n.v" "$X/stamp/$n.v"
    $FRT pins.py stamp "$X/stamp/$n.v" "$UB" --twin "$UBs" --ns "$NS" > "$L/G7b.stamp.$n.log" 2>&1; r=$?
    d=$(python3 - "$X/in/gen/$n.v" "$X/stamp/$n.v" <<'EOF'
import sys
a, b = (open(p).read().split('\n') for p in sys.argv[1:3])
fa = [(i + 1, l) for i, l in enumerate(a) if l.startswith('(* Read from: ')]
fb = [(i + 1, l) for i, l in enumerate(b) if l.startswith('(* Read from: ')]
rest = [l for l in a if not l.startswith('(* Read from: ')] == [l for l in b if not l.startswith('(* Read from: ')]
s = 'file Read-from line: %s; stamp writes it at line %s' % ('line %d' % fa[0][0] if fa else 'ABSENT', fb[0][0] if fb else '-')
if fa and fb:
    import re
    ha, hb = (re.findall(r'[0-9a-f]{64}', x[0][1]) for x in (fa, fb))
    s += ', text %s' % ('EQUAL' if fa[0][1] == fb[0][1] else 'DIFFERENT (%s)' % (
        'the same pin + twin sha256 %s / %s, other wording' % (hb[0][:12], hb[1][:12]) if ha == hb else 'sha256 DIFFER: file %s, pin %s' % (ha, hb)))
s += '; every other line %s' % ('EQUAL' if rest else 'DIFFERENT')
print(s + ('; copy BYTE-EQUAL' if a == b else ''))
EOF
)
    rc "G7b stamp $n ($d)" $r; grep -v '^frozen-run' "$L/G7b.stamp.$n.log" | cut -c1-300
  done
  echo "=== G7c YF0m stamp with the realset pair: --pair a9's image-A AF0m (out/AF0m.v) --pair-syms the A twin, donor cgif A/B ==="
  cp "$X/in/gen/YF0m.v" "$X/stamp/YF0m.pair.v"
  $FRT pins.py stamp "$X/stamp/YF0m.pair.v" "$UB" --twin "$UBs" --ns "$NS" --pair "$A9AF0M" --pair-syms "$UAs" \
    --donor-a "$X/in/cgif/A/AF0m.v" --donor-a-syms "$S/syms/cgif_file_fuzzer.asan.nm" \
    --donor-b "$X/in/cgif/YF0m.v" --donor-b-syms "$S/syms/cgif_file_fuzzer.asan-ubsan.nm" > "$L/G7c.stamp.YF0m.pair.log" 2>&1; r=$?
  python3 - "$X/in/gen/YF0m.v" "$X/stamp/YF0m.pair.v" <<'EOF' > "$X/stamp/YF0m.pair.cmp"
import sys
a, b = (open(p).read().split('\n') for p in sys.argv[1:3])
print('stamped copy %s; the same multiset of lines: %s (only line order in the header moves)' % ('BYTE-EQUAL' if a == b else 'DIFFERS', sorted(a) == sorted(b)))
EOF
  d=$(cat "$X/stamp/YF0m.pair.cmp")
  rc "G7c stamp YF0m --pair ($d)" $r; grep -v '^frozen-run' "$L/G7c.stamp.YF0m.pair.log" | cut -c1-300
  echo "=== G7d pins.py emitcheck --ns $NS on all files (a9's form) ==="
  $FRT pins.py emitcheck --ns "$NS" $(for n in $(present); do printf '%s ' "$X/in/gen/$n.v"; done) > "$L/G7d.emitcheck.log" 2>&1
  rc "G7d emitcheck" $?; grep -v '^frozen-run' "$L/G7d.emitcheck.log" | sed "s#$X/in/##"
  echo "=== G7e keyset.py check: CONTROL cgif's released YB12 / YF0m / YD2j / YB1k on cgif B (--record-names YB1w), one run per file, then fuzz_uci B ==="
  local c
  for c in YB12 YF0m YD2j YB1k; do
    $FRT keyset.py check --image "$CB" --record-names "$X/in/cgif/YB1w.v" "$X/in/cgif/$c.v" > "$L/G7e.keyset.control.$c.log" 2>&1
    rc "G7e keyset CONTROL cgif released $c" $?; grep -v '^frozen-run' "$L/G7e.keyset.control.$c.log" | sed "s#$X/in/##" | cut -c1-300
  done
  echo "=== G7e CONTROL: cgif's YB12 as atable 2d236e51ad70 re-emits it on cgif B (WK/ctl/YB12.cgif.v, the generator's control output: 13 stops_more) ==="
  $FRT keyset.py check --image "$CB" --record-names "$X/in/cgif/YB1w.v" "$WK/ctl/YB12.cgif.v" > "$L/G7e.keyset.control.YB12regen.log" 2>&1
  rc "G7e keyset CONTROL cgif YB12 (atable re-emitted)" $?; grep -v '^frozen-run' "$L/G7e.keyset.control.YB12regen.log" | cut -c1-300
  $FRT keyset.py check --image "$UB" --twin "$UBs" "$X/in/gen/YB12.v" "$X/in/gen/YF0m.v" "$X/in/gen/YD2j.v" "$X/in/gen/YB1k.v" > "$L/G7e.keyset.uciB.log" 2>&1
  rc "G7e keyset uciB" $?; grep -v '^frozen-run' "$L/G7e.keyset.uciB.log" | sed "s#$X/in/##" | cut -c1-300
}

G8() {  # ifchk f5cde600cc18 (start-up set of commit dbb5a97ad14)
  local IF="$FRT ifchk.py" r
  echo "=== G8 CONTROL: cgif's released YF0m x YB01 on the cgif B image, --nholes 50 ==="
  $IF --owned "$X/in/cgif/YF0m.v" --states "$X/in/cgif/YB01.v" --image "$CB" --nholes 50 > "$L/G8.ifchk.control.log" 2>&1
  rc "G8 ifchk CONTROL cgif B" $?; grep -v '^frozen-run' "$L/G8.ifchk.control.log" | sed "s#$X/in/##"
  echo "=== G8 REFUSAL controls: no states (an empty states file), and --nholes 49 (must refuse, rc 2) ==="
  : > "$X/ctl/empty.YB01.v"
  $IF --owned "$X/in/raw/YF0m.v" --states "$X/ctl/empty.YB01.v" --image "$UB" --nholes 50 --ad1g "$UCIB_PCB/stage-out/B/YD1g.v" > "$L/G8.ifchk.nostates.log" 2>&1
  rc "G8 ifchk no-states (want 2)" $?; grep -v '^frozen-run' "$L/G8.ifchk.nostates.log" | tail -3
  $IF --owned "$X/in/raw/YF0m.v" --states "$X/in/raw/YB01.v" --image "$UB" --nholes 49 --ad1g "$UCIB_PCB/stage-out/B/YD1g.v" > "$L/G8.ifchk.nholes49.log" 2>&1
  rc "G8 ifchk --nholes 49 (want 2)" $?; grep -v '^frozen-run' "$L/G8.ifchk.nholes49.log" | tail -3
  echo "=== G8 PLANTED control: one Tfib_const_abs cell of a copy of raw YF0m changed (common_flags_dont_use+0 value 0x1 -> 0x2), must be caught ==="
  python3 - "$X/in/raw/YF0m.v" "$X/ctl/YF0m.ifplant.v" <<'EOF'; rc "G8 plant" $?
import sys
t = open(sys.argv[1]).read()
old, new = 'z8 (ANum 0x130c28) 0x1 ', 'z8 (ANum 0x130c28) 0x2 '
assert t.count(old) == 1, t.count(old)
open(sys.argv[2], 'w').write(t.replace(old, new))
print('planted: %r -> %r' % (old, new))
EOF
  $IF --owned "$X/ctl/YF0m.ifplant.v" --states "$X/in/raw/YB01.v" --image "$UB" --nholes 50 --ad1g "$UCIB_PCB/stage-out/B/YD1g.v" > "$L/G8.ifchk.planted.log" 2>&1
  rc "G8 ifchk PLANTED (want 1)" $?; grep -v '^frozen-run' "$L/G8.ifchk.planted.log" | tail -6 | cut -c1-300
  echo "=== G8 ifchk on fuzz_uci B: --owned WK/raw/YF0m.v --states WK/raw/YB01.v --image UB --nholes 50 --ad1g pcB YD1g ==="
  $IF --owned "$X/in/raw/YF0m.v" --states "$X/in/raw/YB01.v" --image "$UB" --nholes 50 --ad1g "$UCIB_PCB/stage-out/B/YD1g.v" > "$L/G8.ifchk.uciB.log" 2>&1
  rc "G8 ifchk uciB" $?; grep -v '^frozen-run' "$L/G8.ifchk.uciB.log" | sed "s#$X/in/##"
}

G9() {  # ownedcheck / shadowcheck (the released checkers)
  local d
  echo "=== G9 self-test of the latest releases (selftest-d27dfffb.sh, cgif A AF0m on cgif A) ==="
  sh "$T/selftest-d27dfffb.sh" "$T/shadowcheck-542898b2" "$T/ownedcheck-4161c861" "$X/in/cgif/A/AF0m.v" "$CA" > "$L/G9.selftest.log" 2>&1
  rc "G9 selftest 542898b2/4161c861" $?; cat "$L/G9.selftest.log"
  for d in ownedcheck-352fb92f ownedcheck-4161c861; do
    echo "=== G9 $d --elf: CONTROL cgif's released YF0m on cgif B, then fuzz_uci B YF0m on the twin ==="
    (cd "$T/$d" && python3 ownedcheck.py "$X/in/cgif/YF0m.v" --elf "$CB") > "$L/G9.$d.control.log" 2>&1; rc "G9 $d CONTROL" $?; cat "$L/G9.$d.control.log"
    (cd "$T/$d" && python3 ownedcheck.py "$X/in/gen/YF0m.v" --elf "$UBs") > "$L/G9.$d.uciB.log" 2>&1; rc "G9 $d uciB" $?; cat "$L/G9.$d.uciB.log"
  done
  for d in shadowcheck-e04173f5 shadowcheck-6dccc6f9 shadowcheck-542898b2; do
    echo "=== G9 $d: CONTROL cgif YF0m on cgif B with IMG_TOP=0x5fb000, then fuzz_uci B with IMG_TOP=0x5f4000 ==="
    (cd "$T/$d" && IMG_TOP=0x5fb000 python3 shadowcheck.py "$CB" "$X/in/cgif/YF0m.v") > "$L/G9.$d.control.log" 2>&1; rc "G9 $d CONTROL" $?; cat "$L/G9.$d.control.log"
    (cd "$T/$d" && IMG_TOP=0x5f4000 python3 shadowcheck.py "$UB" "$X/in/gen/YF0m.v") > "$L/G9.$d.uciB.log" 2>&1; rc "G9 $d uciB" $?; cat "$L/G9.$d.uciB.log"
  done
}

G10() {  # gen_ad1k hull floor (lowbeg.py 8413f30bc6da) and YD1k's stated bound
  local tg
  for tg in 8cd7 dbb5; do
    echo "=== G10 lowbeg.py with gen_ad1k of bundle $tg ($( [ $tg = 8cd7 ] && echo '814c81b8966e, YD1k'"'"'s generator' || echo 43a0cf0abc67)): CONTROL cgif B first, then fuzz_uci B ==="
    python3 "$T/lowbeg.py" "$DON" "$X/bundle-$tg" "$CB" "$UB" > "$L/G10.lowbeg.$tg.log" 2>&1; rc "G10 lowbeg ($tg)" $?; cat "$L/G10.lowbeg.$tg.log"
    echo "    gen_ad1k.py imported: $(sha256sum "$X/bundle-$tg/gen_ad1k.py" | cut -c1-12)"
  done
  cp "$L/G10.lowbeg.8cd7.log" "$L/G10.lowbeg.log"
  python3 - "$L/G10.lowbeg.log" "$X/in/cgif/YD1k.v" "$X/in/gen/YD1k.v" "$CB" "$UB" <<'EOF'; rc "G10 YD1k hull text = lowbeg hull (cgif control + uci)" $?
import re, sys
log, fc, fu, ic, iu = sys.argv[1:]
hb = {m.group(1): int(m.group(2), 16) for m in re.finditer(r'^(\S+) sha256=\S+ descriptors=\d+ lowest_beg=\S+ mod64=\d+ hull_bound=(0x[0-9a-f]+)', open(log).read(), re.M)}
ok = True
for lab, f, img in (('cgif B (control)', fc, ic), ('fuzz_uci B', fu, iu)):
    t = open(f).read()
    bs = sorted(set(re.findall(r'p \+ n <= (0x[0-9a-f]+)', t)))
    lines = [i + 1 for i, l in enumerate(t.split('\n')) if re.search(r'p \+ n <= 0x', l)]
    good = bs == ['%#x' % hb[img]]
    ok &= good
    print('  %-17s lowbeg hull_bound %#x; YD1k `p + n <= ...` bounds %s at lines %s -> %s' % (lab, hb[img], bs, lines, 'EQUAL' if good else 'DIFFERENT'))
sys.exit(0 if ok else 1)
EOF
}

G11() {  # exit-certificate cross-gates
  rm -rf "$X/exitdrv" "$X/exitdrv-work"; mkdir -p "$X/exitdrv" "$X/exitdrv-work/out"
  echo "G11 gen_exitB.py $(sha256sum "$W/sub/exitdrv/gen_exitB.py" | cut -c1-12), its inputs from \$UCIB_EXITDRV, out/ written to \$UCIB_GATEWORK/exitdrv-work"
  echo "=== G11a gen_exitB.py --af0m WK/raw/YF0m.v (its own controls C1.. run first inside; rodata_chk / cellr / shbyte_chk / DRVW_not_owned) ==="
  (cd "$X/exitdrv" && UCIB_EXITWORK="$X/exitdrv-work" python3 "$W/sub/exitdrv/gen_exitB.py" --af0m "$X/in/raw/YF0m.v") > "$L/G11a.exitB.af0m.log" 2>&1
  rc "G11a gen_exitB --af0m" $?; grep -E 'af0m|PASS|FAIL|C9b|E5|E6' "$L/G11a.exitB.af0m.log" | cut -c1-500
  local n; for n in YE23 YD1y YE37; do
    [ -f "$X/exitdrv-work/out/$n.v" ] || { echo "  $n.v not regenerated"; continue; }
    cmp -s "$X/exitdrv-work/out/$n.v" "$UCIB_EXITWORK/out/$n.v" && echo "  re-generated $n.v BYTE-EQUAL to the exit-driver run's own output (\$UCIB_EXITWORK/out/$n.v)" || echo "  re-generated $n.v DIFFERS from \$UCIB_EXITWORK/out/$n.v"
    python3 - "$X/exitdrv-work/out/$n.v" "$X/in/gen/$n.v" <<'EOF'
import re, sys
# the module-path rewrite (nsB.py) changes only the `From .. Require ..` sentences and the record name TfibSyms -> UciSyms
strip = lambda t: [l for l in re.sub(r'From \S+ Require(?: Import| Export)?[^.]*\.', '', t).split('\n') if l.strip()]
a = strip(open(sys.argv[1]).read().replace('TfibSyms', 'UciSyms'))
b = strip(open(sys.argv[2]).read())
print('  %s: with every `From .. Require ..` sentence removed and TfibSyms -> UciSyms (the module-path / record rewrite), the re-generated (donor-namespace) text and WK/gen are %s (%d / %d non-blank lines)' % (sys.argv[2].split('/')[-1], 'EQUAL' if a == b else 'DIFFERENT', len(a), len(b)))
EOF
  done
  echo "=== G11b a9's run_ae37.sh gate: XW2 of YE23 = YE37's cellr cells + x2_shw windows. CONTROL cgif's released YE23/YE37 first ==="
  for pair in "cgif:$X/in/cgif" "uciB:$X/in/gen"; do
    python3 - "${pair#*:}/YE37.v" "${pair#*:}/YE23.v" "${pair%%:*}" <<'EOF'; rc "G11b XW2 ${pair%%:*}" $?
import re, sys
t, x = open(sys.argv[1]).read(), open(sys.argv[2]).read()
m = re.search(r'Definition XW2 \(a : Z\) : Prop := (.*?)\.\n', x, re.S)
xw2 = sorted((int(a, 16), int(b, 16)) for a, b in re.findall(r'\((0x[0-9a-f]+) <= a < (0x[0-9a-f]+)\)', m.group(1)))
cell = [(int(a, 16), int(a, 16) + int(w)) for a, w in re.findall(r'cellr (0x[0-9a-f]+) (\d+) \(SLit \d+\) true', t)]
shw = [(int(a, 16), int(a, 16) + int(n)) for a, n in re.findall(r'\((0x[0-9a-f]+), ?(\d+)\)', re.search(r'Definition x2_shw[^\n]*', t).group(0))]
mine = sorted(cell + shw)
print(sys.argv[3], 'XW2 (YE23.v)          ', [('%#x' % a, '%#x' % b) for a, b in xw2])
print(sys.argv[3], 'YE37 cellr + x2_shw   ', [('%#x' % a, '%#x' % b) for a, b in mine])
print(sys.argv[3], 'EQUAL' if xw2 == mine else 'DIFFERENT')
sys.exit(0 if xw2 == mine else 1)
EOF
  done
}

G12_body() {  # cgif-B byte-equal controls the generators already ran: collect their result lines (no re-run)
  echo "=== G12 control result lines of the generator runs (file:line), not re-run ==="
  local f
  for f in logs/ab1hk.control.log logs/boxb1.control.B.log logs/yb13.gen.log logs/run_restB.gen2.log logs/af0m/run_af0mB.gen2.log \
           logs/boxb1.yb1m.log logs/cert.B.log; do
    [ -f "$W/$f" ] || { echo "  MISSING $f"; continue; }
    grep -n -i -E 'EQUAL|control|PASS|FAIL|caught|COk|differ' "$W/$f" | sed "s#^#  $f:#" | cut -c1-300
  done
  for f in $(ls "$W/tools/af0mB/ctl" 2>/dev/null); do echo "  tools/af0mB/ctl/$f $(sha256sum "$W/tools/af0mB/ctl/$f" | cut -c1-12)"; done
}
G12() { G12_body > "$L/G12.collected.log" 2>&1; cat "$L/G12.collected.log"; }

GATES=("$@"); [ ${#GATES[@]} -eq 0 ] && GATES=(G1 G2 G3 G3e G4 G5 G6 G7 G8 G9 G10 G11 G12)
[ "${NOSNAP:-0}" = 1 ] || G0 2>&1 | tee "$L/G0.log"
for g in "${GATES[@]}"; do [ "$g" = G0 ] && continue; echo "######## $g $(date -u +%TZ)"; $g 2>&1 | tee "$L/$g.out"; done
