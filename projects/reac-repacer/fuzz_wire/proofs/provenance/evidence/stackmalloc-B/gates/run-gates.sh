#!/bin/bash
# run-gates.sh <workdir>: the gates of reac-repacer/fuzz_wire's image-B __asan_stack_malloc_0 / _1 files, in order, each
# with its planted control; writes ../records/ (host paths replaced by role names; inputs named by sha256).
# Environment (each input named by sha256):
#   P, R    the pinned image trees (run.sh)          DON   the normalised donor lib (run.sh)
#   LIB     the unit lib with the five files          RUN   run.sh's work directory of record (stage/, stage-out/, gate-raw.tsv)
#   KIT     a directory holding exactly the nine files of cmpkit 86da41d3ef68 and its SHA256SUMS
#   CK      port_addr_check.py 45b78aaa48c3 (its version directory beside it); DONORS: the --donors-from tree
#   SM, SMC size_moves.py 7edcb4804346, size_moves_classify.py 810be4eaa791;   SWAPS ab1w_swaps.py 3f885801a1f5
set -uo pipefail
WORK=${1:?usage: run-gates.sh <workdir>}
HERE=$(cd "$(dirname "$0")" && pwd); REC=$HERE/../records
: "${P:?}" "${R:?}" "${DON:?}" "${LIB:?}" "${RUN:?}" "${KIT:?}" "${CK:?}" "${DONORS:?}" "${SM:?}" "${SMC:?}" "${SWAPS:?}"
for x in "SM 7edcb4804346" "SMC 810be4eaa791" "SWAPS 3f885801a1f5" "CK 45b78aaa48c3"; do
  set -- $x; [ "$(sha256sum "${!1}" | cut -c1-12)" = "$2" ] || { echo "run-gates: $1 is not $2" >&2; exit 2; }
done
export PYTHONDONTWRITEBYTECODE=1 P R LIB
rm -rf "$WORK"; mkdir -p "$WORK/out" "$REC"
FILES="B/Rt/StackMalloc0.v B/Rt/StackMalloc0Tbl.v B/Rt/YF0r.v B/Rt/YF0s.v Reusable/YF0v.v"
GTW=$P/unstripped/fuzz_grant/fuzz_grant.asan-ubsan; WTW=$R/result/unstripped/fuzz_wire/fuzz_wire.asan-ubsan
log() { echo "$*" | tee -a "$WORK/out/gates.txt"; }

# 1. body compare (kit, twins, functions, decoded ranges, plant)
python3 "$HERE/bodycmp-smB.py" "$KIT" "$LIB/B/Rt/YF0r.v" "$DON/Rt/YF0r.v" "$WORK/out" > "$WORK/out/bodycmp.txt" 2>&1
log "bodycmp rc=$? $(head -1 "$WORK/out/bodycmp.txt")"

# 2. the numeral table, and its plant (TP of StackMalloc0Tbl.v moved by 8: the TLS rule must give WRONG)
python3 "$HERE/numerals-smB.py" "$LIB" "$DON" "$WORK/out/bodycmp-functions.out" "$WORK/out/numerals-smB.tsv" > "$WORK/out/numerals.txt" 2>&1
log "numerals rc=$? $(head -1 "$WORK/out/numerals.txt")"
PL=$WORK/plantlib; mkdir -p "$PL/B/Rt" "$PL/Reusable"
for f in $FILES B/YF0m.v Reusable/YG00.v Reusable/YG0f.v; do cp "$LIB/$f" "$PL/$f"; done
sed -i 's/^Definition TP : Z := 0x5d3790\./Definition TP : Z := 0x5d3798./' "$PL/B/Rt/StackMalloc0Tbl.v"
python3 "$HERE/numerals-smB.py" "$PL" "$DON" "$WORK/out/bodycmp-functions.out" "$WORK/out/numerals-plant.tsv" > "$WORK/out/numerals-plant.txt" 2>&1
log "numerals plant (TP 0x5d3790 -> 0x5d3798 in B/Rt/StackMalloc0Tbl.v) rc=$? $(head -1 "$WORK/out/numerals-plant.txt"); WRONG rows: $(awk -F'\t' '$8=="WRONG"{print $1":"$2" "$5}' "$WORK/out/numerals-plant.tsv" | tr '\n' ' ')"

# 3. size check
python3 "$SM" "$WORK/out/size-moves.tsv" "$LIB" "smB=$RUN" > "$WORK/out/size-moves.out" 2>&1
log "size_moves rc=$? $(tail -1 "$WORK/out/size-moves.out")"
python3 "$SMC" "$WORK/out/size-moves.tsv" "$LIB" "$WTW" "$WORK/out/size-moves-classified.tsv" "smB=$RUN/gate-raw.tsv=$RUN/stage-out=$GTW" > "$WORK/out/size-moves-classify.out" 2>&1
log "size_moves_classify rc=$? $(tail -1 "$WORK/out/size-moves-classify.out")"

# 4. port_addr_check on donor -> ported pairs, the triage of every row that is not a pass, and the plant (FS_ENTRY of
#    StackMalloc0Tbl.v put back to the donor's __asan_stack_malloc_0 0x3cf4c: must flag and stay unexplained)
FIN=$WORK/final; mkdir -p "$FIN/B/Rt" "$FIN/Reusable"; for f in $FILES; do cp "$LIB/$f" "$FIN/$f"; done
CK=$CK DONORS=$DONORS bash "$HERE/pac-smB.sh" "$RUN/stage" "$FIN" "$WORK/out/flag"; rc=$?
log "port_addr_check rc=$rc $(grep -E '^FLAGGED|^UNMEASURED [0-9]' "$WORK/out/flag.log" | tr '\n' ' ')"
PATCH=$HERE/../B-smB.patch python3 "$HERE/triage-smB.py" "$WORK/out/flag.tsv" "$WORK/out/flag-triage.tsv" > "$WORK/out/triage.txt" 2>&1
log "triage rc=$? $(cat "$WORK/out/triage.txt")"
FPL=$WORK/finalplant; cp -r "$FIN" "$FPL"
sed -i 's/^Definition FS_ENTRY : Z := 0x3c524\./Definition FS_ENTRY : Z := 0x3cf4c./' "$FPL/B/Rt/StackMalloc0Tbl.v"
CK=$CK DONORS=$DONORS bash "$HERE/pac-smB.sh" "$RUN/stage" "$FPL" "$WORK/out/flag-plant"; rc=$?
log "port_addr_check plant (FS_ENTRY 0x3c524 -> 0x3cf4c) rc=$rc $(grep -E '^FLAGGED' "$WORK/out/flag-plant.log")"
KLIB=$LIB LIB=$FPL PATCH=$HERE/../B-smB.patch python3 "$HERE/triage-smB.py" "$WORK/out/flag-plant.tsv" "$WORK/out/flag-plant-triage.tsv" > "$WORK/out/triage-plant.txt" 2>&1
log "triage plant rc=$? $(cat "$WORK/out/triage-plant.txt")"

# 5. crossed pairs: the cells of the five files, and of the unit's image-B cell record lib/B/YB1w.v
for f in $FILES B/YB1w.v; do
  python3 "$SWAPS" "$LIB/$f" "$WTW" "$LIB" "$WORK/out/ab1w-swaps-$(basename "$f" .v).tsv" > "$WORK/out/ab1w-$(basename "$f" .v).txt" 2>&1
  log "ab1w_swaps $f rc=$? $(tail -1 "$WORK/out/ab1w-$(basename "$f" .v).txt")"
done

# 6. records, host paths replaced by role names
python3 - "$WORK/out" "$REC" <<'EOF'
import glob, os, re, shutil, sys
src, dst = sys.argv[1:3]
E = os.environ
subs = [(E['RUN'] + '/stage-out', '<run>/stage-out'), (E['RUN'] + '/stage', '<run>/stage'), (E['RUN'], '<run>'),
        (os.path.dirname(src) + '/finalplant', '<planted ported tree>'),
        (os.path.dirname(src) + '/final', '<ported tree>'), (src, '<out>'),
        (E['P'] + '/unstripped/fuzz_grant/fuzz_grant.asan-ubsan', 'fuzz_grant.asan-ubsan.unstripped(5a5ee7c02b4e)'),
        (E['P'] + '/bin/fuzz_grant/fuzz_grant.asan-ubsan', 'fuzz_grant.asan-ubsan(fde52226dc48)'),
        (E['R'] + '/result/unstripped/fuzz_wire/fuzz_wire.asan-ubsan', 'fuzz_wire.asan-ubsan.unstripped(51eb4bef2425)'),
        (E['R'] + '/result/bin/fuzz_wire/fuzz_wire.asan-ubsan', 'fuzz_wire.asan-ubsan(af4534831a45)'),
        (E['LIB'], '<lib>'), (E['DON'], '<donor lib>'), (E['DONORS'], '<donors-from tree>'), (E['CK'], 'port_addr_check.py(45b78aaa48c3)'),
        (E['KIT'], '<cmpkit 86da41d3ef68>')]
for p in sorted(glob.glob(os.path.join(src, '*'))):
    if os.path.isdir(p):
        continue
    t = open(p, errors='replace').read()
    for a, b in subs:
        t = t.replace(a, b)
    # lane names in tool-printed text (port_addr_check's notes cite the lane that reported a rule)
    t = re.sub(r'\b[hrcg]-[a-z]+(?:-[a-z0-9]+)+\b', '<lane>', t)
    # a document name the checker prints whose hyphenated form reads as a lane name
    t = re.sub(r'port[-]addr[-]check[.]md', "the checker's notes", t)
    assert not re.search(r'/(home|mnt)/\w', t), p
    open(os.path.join(dst, os.path.basename(p)), 'w').write(t)
EOF
echo "run-gates: records written to $(cd "$REC" && pwd)"
