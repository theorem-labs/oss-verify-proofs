#!/bin/bash
# run-gates.sh <gatedir>: every gate of this row over the five committed files lib/B/Rt/{MemmoveDef,MemmoveIm,MemmoveK,
# MemmovePaths,Memmove}.v, each control beside its run; raw outputs to <gatedir> (records-mm.py turns them into
# ../records/). The method is fuzz_uci's image-B class-1 stack_malloc record (stackmalloc1-B/gates/run-gates.sh) with the
# unit, image, donor, file names, tool versions and plants changed. The bytecmp gate (GATES.md section 0) is the
# relocation's, not re-run here; the cb build is the row owner's.
# Environment (each tool and image named by sha; nothing here depends on a host path the tree names):
#   HUB        git dir holding recipes 5098883da0b (fuzz_pcap's released lib/B/Rt/Memmove*.v, the donor)
#   WIRE_BIN   fuzz_wire.asan-ubsan (sha256 af4534831a45) and fuzz_wire.asan-ubsan.unstripped (51eb4bef2425), as
#              ../../memmove-reloc/run.sh reads them
#   PCAP_PIN   fuzz_pcap.asan-ubsan, the donor's pin (9e66f771f22a)
#   PCAP_TWIN  fuzz_pcap.asan-ubsan, the donor's unstripped twin (c969d83cdd59), as run.sh reads it
#   CKDIR      the directory of port_addr_check.py sha256 efa19b81e92b; DONORS its --donors-from tree
#   SET        the start-up set of record at tool-registry commit 5aa27b4282c: its directory under tools/startup-set/ whose bundle
#              startup-set-*.tsv is sha256 453349f98b04 (frozen-run.sh, codeptr 12348302dfd2, keyset 38b229c6ad08,
#              atable 6a35bb77e745)
#   GS         global_settings.py 439f8e3bd463 (v10, the registered global_settings release 2)
set -uo pipefail
GD=${1:?usage: run-gates.sh <gatedir>}
H=$(cd "$(dirname "$0")" && pwd); LIB=$(cd "$H/../../../../lib" && pwd)
: "${HUB:?}" "${WIRE_BIN:?}" "${PCAP_PIN:?}" "${PCAP_TWIN:?}" "${CKDIR:?}" "${DONORS:?}" "${SET:?}" "${GS:?}"
WB=$WIRE_BIN/fuzz_wire.asan-ubsan; WT=$WIRE_BIN/fuzz_wire.asan-ubsan.unstripped
PB=$PCAP_PIN/fuzz_pcap.asan-ubsan; PT=$PCAP_TWIN/fuzz_pcap.asan-ubsan
CK=$CKDIR/port_addr_check.py
REF=5098883da0b; SRCD=proofs/libreac/fuzz_pcap/lib/B/Rt
N5="MemmoveDef MemmoveIm MemmoveK MemmovePaths Memmove"
F5=$(for n in $N5; do printf 'B/Rt/%s.v ' "$n"; done)
sha() { sha256sum "$1" | cut -c1-12; }
BUNDLE=$(for b in "$SET"/startup-set-*.tsv; do [ "$(sha "$b")" = 453349f98b04 ] && echo "$b"; done)
[ -n "$BUNDLE" ] || { echo "run-gates: no start-up bundle of sha256 453349f98b04 in $SET" >&2; exit 2; }
for x in "$WB af4534831a45" "$WT 51eb4bef2425" "$PB 9e66f771f22a" "$PT c969d83cdd59" "$CK efa19b81e92b" \
         "$SET/frozen/codeptr.py.frozen-12348302dfd2 12348302dfd2" "$BUNDLE 453349f98b04" \
         "$GS 439f8e3bd463"; do
  set -- $x; [ "$(sha "$1")" = "$2" ] || { echo "run-gates: $1 is not sha256 $2" >&2; exit 2; }
done
mkdir -p "$GD"; FIN=$GD/final; DON=$GD/don; DONREL=$GD/donrel
rm -rf "$FIN" "$DON" "$DONREL" "$GD"/plant-*
mkdir -p "$FIN/B/Rt" "$DON/B/Rt" "$DONREL"
# FIN: the committed files. DON: the donor's released files with their module paths renamed (libreac.fuzz_pcap ->
# reac_repacer.fuzz_wire, the only change), the text the relocation started from. DONREL: the released files as released.
for n in $N5; do
  cp "$LIB/B/Rt/$n.v" "$FIN/B/Rt/$n.v"
  git -C "$HUB" show "$REF:$SRCD/$n.v" | python3 -c 'import sys; sys.stdout.write(sys.stdin.read().replace("libreac.fuzz_pcap", "reac_repacer.fuzz_wire"))' > "$DON/B/Rt/$n.v" || exit 2
done
git -C "$HUB" archive "$REF" $(for n in $N5; do echo "$SRCD/$n.v"; done) | tar -x -C "$DONREL" || exit 2
git -C "$HUB" show "$REF:proofs/libreac/fuzz_pcap/lib/Reusable/YE2y.v" > "$GD/pcap-YE2y.v" || exit 2
# plant <name> <file> <old> <new>: a copy of the five files with one value planted (exactly one occurrence)
plant() { local d=$GD/plant-$1; cp -r "$FIN" "$d"; python3 - "$d/$2" "$3" "$4" <<'EOF' || exit 9
import sys; p, o, n = sys.argv[1:]; t = open(p).read(); assert t.count(o) == 1, (p, o); open(p, 'w').write(t.replace(o, n))
EOF
}
# the donor's own __asan_memmove entry (fuzz_pcap B 0x51c40) left in place of fuzz_wire's 0x510b0 (flag gate, codeptr,
# by-value check)
plant entry B/Rt/MemmoveK.v 'Definition MM_ENTRY : Z := 0x510b0.' 'Definition MM_ENTRY : Z := 0x51c40.'
# a wrong function: fuzz_wire's LLVMFuzzerTestOneInput (0x7fbf8) in place of internal_memmove (0x63078) (flag gate)
plant real B/Rt/MemmoveK.v 'Definition MM_REAL : Z := 0x63078.' 'Definition MM_REAL : Z := 0x7fbf8.'
# Memmove.v's Local Zify flag made global
plant v10 B/Rt/Memmove.v 'Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).' \
  'Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).'

echo "== measurements the triage reasons cite (both images)"
python3 "$H/measure-mm.py" "$FIN" "$LIB" "$GD/pcap-YE2y.v" > "$GD/measure.out" 2>&1; echo "rc=$?" >> "$GD/measure.out"

echo "== 1 flag gate: port_addr_check efa19b81e92b --fail-on-flags (+ 2 planted pointers)"
# pac-B.sh's flags (core-B/gates/pac-B.sh) with this row's images, keyed B (the build letter of asan-ubsan: efa19b81e92b
# runs keyed by any other name are VOID for the named-symbol rule)
pac() { local src=$1 dst=$2 out=$3; mkdir -p "$out.cache"
  python3 "$CK" --src "$src" --dst "$dst" --src-image "B=$PB:$PT" --dst-image "B=$WB:$WT" --donors-from "$DONORS" \
    --paired-only --out "$out.tsv" --summary --cache "$out.cache" --fail-on-flags > "$out.log" 2>&1
  echo "checker <file> rc=$? (sha256 $(sha "$CK"))" >> "$out.log"; python3 "$CK" --list-flag-classes >> "$out.log" 2>&1; }
pac "$DON" "$FIN" "$GD/pac-rec"
pac "$DON" "$GD/plant-entry" "$GD/pac-plant-entry"
pac "$DON" "$GD/plant-real" "$GD/pac-plant-real"
WHY=$H/../../memmove-reloc/asan-resolve-B.why.txt
for t in rec plant-entry plant-real; do
  python3 "$H/triage-mm.py" "$GD/pac-$t.tsv" "$GD/pac-$t.triage.tsv" "$WHY" > "$GD/pac-$t.triage.out"; echo "rc=$?" >> "$GD/pac-$t.triage.out"; done

echo "== 2a codeptr 12348302dfd2 (base, declared, donor baseline, planted MM_ENTRY with and without the declarations)"
fr() { bash "$SET/frozen-run.sh" "$BUNDLE" "$@"; }
NA=(); if [ -f "$H/codeptr-notaddr-mm.tsv" ]; then
  while IFS=$'\t' read -r v why; do case "$v" in ''|'#'*) continue;; esac; NA+=(--not-address "$v=$why"); done < "$H/codeptr-notaddr-mm.tsv"; fi
# every occurrence a declaration covers (a numeral of the declared value, hex or decimal, in the five files)
python3 - "$FIN" "$H/codeptr-notaddr-mm.tsv" $F5 > "$GD/codeptr-occurrences.tsv" <<'EOF'
import re, sys
d, decl, fs = sys.argv[1], sys.argv[2], sys.argv[3:]
vals = [int(l.split('\t')[0], 0) for l in open(decl) if l.strip() and not l.startswith('#')]
print('value\tfile\tline\ttoken\tsource')
for v in vals:
    for f in fs:
        for i, l in enumerate(open(f'{d}/{f}'), 1):
            for m in re.finditer(r'(?<![\w])(0x[0-9a-fA-F]+|\d+)(?![\w])', l):
                if int(m.group(1), 16 if m.group(1).startswith('0x') else 10) == v:
                    print(f'0x{v:x}\t{f}\t{i}\t{m.group(1)}\t{l.strip()[:140]}')
EOF
sf() { local d=$1 a=(); for f in $F5; do a+=(--stale-file "$d/$f=$DON/$f"); done; echo "${a[@]}"; }
cp1() { local d=$1; shift; fr codeptr.py --image "$WB" --names "$WT" --stale-image "$PB" --stale-names "$PT" $(sf "$d") "$@" $(for f in $F5; do echo "$d/$f"; done); }
cp1 "$FIN" > "$GD/codeptr-base.out" 2>&1; echo "rc=$?" >> "$GD/codeptr-base.out"
cp1 "$FIN" "${NA[@]}" > "$GD/codeptr-declared.out" 2>&1; echo "rc=$?" >> "$GD/codeptr-declared.out"
fr codeptr.py --image "$PB" --names "$PT" $(for f in $F5; do echo "$DON/$f"; done) > "$GD/codeptr-donor.out" 2>&1; echo "rc=$?" >> "$GD/codeptr-donor.out"
cp1 "$GD/plant-entry" > "$GD/codeptr-plant.out" 2>&1; echo "rc=$?" >> "$GD/codeptr-plant.out"
cp1 "$GD/plant-entry" "${NA[@]}" > "$GD/codeptr-plant-declared.out" 2>&1; echo "rc=$?" >> "$GD/codeptr-plant-declared.out"

echo "== 2b atable: N/A (no atable field, no YB12, no keyed table); keyset check over the five files as the evidence"
fr keyset.py check --image "$WB" --twin "$WT" $(for f in $F5; do echo "$FIN/$f"; done) > "$GD/keyset-check.out" 2>&1; echo "rc=$?" >> "$GD/keyset-check.out"
python3 - "$FIN" $F5 > "$GD/atable-scan.out" <<'EOF'
import re, sys
d, fs = sys.argv[1], sys.argv[2:]
for f in fs:
    t = open(f'{d}/{f}').read()
    hits = sorted(set(re.findall(r'\b(YB12|atable\w*|AB12|stops_more|pc_stack_malloc|pc_asan_\w+|Tfib_\w+_shadow|IMG_REGIONS)\b', t)))
    print(f'{f}: atable / keyed-table names: {len(hits)} {hits}')
EOF

echo "== 2c the by-value check (record and a planted donor value)"
python3 "$H/decval-mm.py" --lib "$FIN" --don "$DON" --core-lib "$LIB" --out "$GD/decval.tsv" --review "$GD/decval-review.tsv" > "$GD/decval.out" 2>&1; echo "rc=$?" >> "$GD/decval.out"
python3 "$H/decval-mm.py" --lib "$GD/plant-entry" --don "$DON" --core-lib "$LIB" > "$GD/decval-control.out" 2>&1; echo "rc=$?" >> "$GD/decval-control.out"

echo "== 3 v10 (global_settings 439f8e3bd463): the files, fuzz_pcap's released counterparts, and a planted global flag"
(cd "$GD" && python3 "$GS" "$FIN" $F5 > v10-wireB.out 2>&1; echo "rc=$?" >> v10-wireB.out)
(cd "$GD" && python3 "$GS" "$DONREL" $(for n in $N5; do echo "$SRCD/$n.v"; done) > v10-pcap-counterparts.out 2>&1; echo "rc=$?" >> v10-pcap-counterparts.out)
(cd "$GD" && python3 "$GS" "$GD/plant-v10" $F5 > v10-plant.out 2>&1; echo "rc=$?" >> v10-plant.out)
echo "run-gates: done ($GD)"
