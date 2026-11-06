#!/bin/bash
# Planted controls of the alreloc cross-check (alreloc-xcheck.sh), libdiginet/fuzz_transport image-A core: known-wrong
# values written into a COPY of stage-out, which the decisions must report as `port_core WRONG`, each at its own
# position, and nothing else new. Kind: measurement; it proves no function. Method of libdiginet/fuzz_decode's record
# (alreloc-xcheck-control.sh, sha256 c9f8b7410e16; internal record); only names and paths changed.
#
#   alreloc-xcheck-control.sh WORK LIB OUT
#
# WORK, LIB and OUT as for alreloc-xcheck.sh, which must have run first (it leaves OUT/out/positions.tsv,
# OUT/alreloc-crosscheck-rows.tsv and alreloc's reports in OUT). Writes OUT/control/ (stage-out copy, plants.tsv, out/,
# alreloc-crosscheck-rows.tsv, verdict.txt). Environment: as alreloc-xcheck.sh (the same defaults).
#
# The plants (each picked from OUT/out/positions.tsv, the first position in file order that fits):
#   got-offset    a .got cell both tools moved to its content twin: written as the cell at the same .got OFFSET
#                 when that cell holds other content, else as the next cell (+8)
#   model-const   a model constant both tools keep or port_core kept (KRange (EVar V_HW) 0x112D 0x20112D): written as
#                 alreloc's rule-`symbol` value (theDepot + offset), else + 0x1000
#   address       an address both tools moved alike (symbol + offset): written + 8
#   donor-value   a relocated address written back to the donor's value (A/AE3m.v STDOUT_BUFA, stdout's buffer)
#   decimal-address  a decimal address both tools moved alike: written + 4
# Added for fuzz_transport, one per decision group this unit added to alreloc_decide.py:
#   rodata-const  a .rodata constant port_core moved with the merged 8-byte constants, written back at the donor's
#                 address (fuzz_transport.asan holds other bytes there)
#   region-split  an IMG_B_eq count (A/AD2f.v) that the unit's split of R_A5a changes, written back as the donor's
#   czone         the CZONE bound written back as the donor's 0x80050000 (below the target's constant shadow bytes)
#
# SWEEP="N SEED" (added for fuzz_transport): instead of the plants above, alreloc_sweep.py writes value + 8 at N
# positions picked at random (seeded) among the positions the base run decided right with an image value; the copy and
# the verdict go to OUT/sweep/ (the same verdict rules).
set -eu
U="usage: alreloc-xcheck-control.sh WORK LIB OUT"
RUN=${1:?$U}
LIB=${2:?$U}
OUT=${3:?$U}
GRANT_ELF=${GRANT_ELF:-${PG:?set PG to the fuzz_grant image tree}/bin/fuzz_grant/fuzz_grant.asan}
GRANT_SYMS=${GRANT_SYMS:-$PG/unstripped/fuzz_grant/fuzz_grant.asan}
TRANSPORT_ELF=${TRANSPORT_ELF:-${TIMG:?set TIMG to the fuzz_transport image dir}/stripped/fuzz_transport.asan}
TRANSPORT_SYMS=${TRANSPORT_SYMS:-$TIMG/unstripped/fuzz_transport.asan}
export PYTHONDONTWRITEBYTECODE=1
HERE=$(cd "$(dirname "$0")" && pwd)
RUN=$(cd "$RUN" && pwd)
LIB=$(cd "$LIB" && pwd)
OUT=$(cd "$OUT" && pwd)
[ -f "$OUT/out/positions.tsv" ] && [ -f "$OUT/alreloc-crosscheck-rows.tsv" ] || {
  echo "alreloc-xcheck-control: run alreloc-xcheck.sh WORK LIB OUT first" >&2; exit 2; }
SWEEP=${SWEEP:-}
if [ -n "$SWEEP" ]; then C=$OUT/sweep; else C=$OUT/control; fi
rm -rf "$C"
mkdir -p "$C"
cp -a "$RUN/stage-out" "$C/stage-out"
if [ -n "$SWEEP" ]; then
  read -r SN SS <<< "$SWEEP"
  python3 "$HERE/alreloc_sweep.py" --rows "$OUT/alreloc-crosscheck-rows.tsv" --stage-out "$C/stage-out" \
    --n "$SN" --seed "$SS" --plants "$C/plants.tsv"
else
  python3 "$HERE/alreloc_plant.py" --positions "$OUT/out/positions.tsv" --stage-out "$C/stage-out" \
    --target-elf "$TRANSPORT_ELF" --target-syms "$TRANSPORT_SYMS" --grant-elf "$GRANT_ELF" --grant-syms "$GRANT_SYMS" \
    --plants "$C/plants.tsv"
fi
set +e
bash "$HERE/alreloc-xcheck.sh" "$RUN" "$LIB" "$OUT" "$C/stage-out" "$C" > "$C/run.log" 2>&1
rc=$?
python3 - "$OUT/alreloc-crosscheck-rows.tsv" "$C/alreloc-crosscheck-rows.tsv" "$C/plants.tsv" "$rc" > "$C/verdict.txt" <<'EOF'
import sys
base, ctl, plants, rc = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4])
key = lambda p: (p[0].split('/lib/', 1)[-1], p[2], p[3])   # lib-relative file, stage-out line, token index
def rows(path):
    out = {}
    for l in open(path).read().split('\n')[1:]:
        if l:
            p = l.split('\t')
            out[key(p)] = p
    return out
b, c = rows(base), rows(ctl)
pl = [l.split('\t') for l in open(plants).read().split('\n')[1:] if l]
caught = 0
for p in pl:
    k = (p[1], p[2], p[3])
    r = c.get(k)
    ok = r is not None and r[12].startswith('port_core WRONG')
    caught += ok
    print('%s %s %s:%s tok %s: %s -> %s: %s' % ('CAUGHT' if ok else 'MISSED', p[0], p[1], p[2], p[3], p[4], p[5],
                                                 r[12] if r else 'no row'))
pk = {(p[1], p[2], p[3]) for p in pl}
new = [k for k, r in c.items() if k not in pk and r[12] != (b.get(k) or [''] * 13)[12]]
for k in new:
    print('CHANGED (not planted) %s:%s tok %s: %s -> %s' % (k[0], k[1], k[2], (b.get(k) or ['-'] * 13)[12], c[k][12]))
print('controls: %d planted, %d caught, %d other rows changed; decide status %d (1 = WRONG rows reported)' % (
    len(pl), caught, len(new), rc))
sys.exit(0 if caught == len(pl) and not new and rc == 1 else 1)
EOF
vr=$?
cat "$C/verdict.txt"
exit $vr
