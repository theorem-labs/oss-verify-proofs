#!/bin/bash
# roundconst-A.sh WORK LIB OUT: item 6 of the TCA value lane, roundconst-gate v2 32b39f3b34e9 (the tool
# registry's tools/roundconst-gate/32b39f3b34e9/, writer's SHA256SUMS checked; registry 'roundconst-gate 32b39f3b34e9 RECORDED') on
# the relocated core. port_addr_check is NOT run (the lane brief: its next version is not out). Two inputs:
#   R1  WORK/gate-raw.tsv: the FULL TSV of the symbol gate port_core ran inside the run (port_addr_check 309d2e5f7e01,
#       vendored in port_core d9e0589898fd; the gate's own verdicts select the rows), gzip'd; default selection and --moved
#   R2  the lane's own report (rclane.py: every aligned numeral of a code line, stage/ against stage-out/) in the same
#       columns, with --all-verdicts (the gate's README, 'Input': a tree relocated by another tool)
# Keys: A = fuzz_grant.asan c2c7559b29bd : twin 57c26f993615 (donor), A = fuzz_transport.asan e89be137db17 : twin
# 86efc3a80314 (target). Control (the README's rule: a plant is a kept DONOR value whose target quantity differs):
#   PR1 tfib_at_rw_len written back as the donor's 0x55c000 (a span >= 0x100)
#   PR2 the first moved row below 0x100 whose donor value roundconst calls MISMATCH when kept (a named quantity below 0x100)
#   R2 on the planted rows must give exactly two MISMATCH rows more than R2, at those two rows.
# Env: RC (default: values/tools/roundconst-gate/32b39f3b34e9), P, PG. Output: OUT/roundconst.txt.
set -uo pipefail
[ $# -eq 3 ] || { echo "usage: roundconst-A.sh WORK LIB OUT" >&2; exit 2; }
mkdir -p "$3" || exit 2
WORK=$(readlink -f "$1") LIB=$(readlink -f "$2") OUT=$(readlink -f "$3")
HERE=$(dirname "$(readlink -f "$0")")
RC=${RC:-$HERE/tools/roundconst-gate/32b39f3b34e9}
P=${P:?set P to the fuzz_transport image tree (result/bin/, unstripped/)}
PG=${PG:?set PG to the fuzz_grant image tree}
GB=$PG/bin/fuzz_grant/fuzz_grant.asan; GT=$PG/unstripped/fuzz_grant/fuzz_grant.asan
FB=$P/result/bin/fuzz_transport/fuzz_transport.asan; FT=$P/unstripped/fuzz_transport/fuzz_transport.asan
PINS=""
for x in "$GB:c2c7559b29bd" "$GT:57c26f993615" "$FB:e89be137db17" "$FT:86efc3a80314" "$RC/roundconst.py:32b39f3b34e9"; do
  f=${x%:*} want=${x##*:} got=$(sha256sum < "$f" | cut -c1-12)
  [ "$got" = "$want" ] || { echo "roundconst-A: $f is $got, not the pinned $want" >&2; exit 2; }
  PINS="$PINS $(basename "$f") $got;"
done
SUMS=$(cd "$RC" && sha256sum -c --quiet SHA256SUMS 2>&1) || { echo "roundconst-A: $RC SHA256SUMS do not check: $SUMS" >&2; exit 2; }
DS="A=$GB:$GT" TS="A=$FB:$FT"
rc() { local o=$1; shift; PYTHONDONTWRITEBYTECODE=1 python3 "$RC/roundconst.py" "$@" > "$o.out" 2>&1; echo "rc=$?" >> "$o.out"; }
# R1
if [ -f "$WORK/gate-raw.tsv" ]; then
  gzip -c "$WORK/gate-raw.tsv" > "$OUT/gate-raw.full.tsv.gz"
  GSHA=$(sha256sum < "$WORK/gate-raw.tsv" | cut -c1-12)
  rc "$OUT/r1" "$OUT/gate-raw.full.tsv.gz" "$DS" "$TS" "$OUT/r1"
  rc "$OUT/r1-moved" "$OUT/gate-raw.full.tsv.gz" "$DS" "$TS" "$OUT/r1-moved" --moved
else
  GSHA="(no gate-raw.tsv in WORK)"
fi
# R2 and the control
PYTHONDONTWRITEBYTECODE=1 python3 "$HERE/rclane.py" "$WORK" "$OUT/lane.full.tsv.gz" --low-moved "$OUT/low-moved.full.tsv.gz" \
  --probe "$OUT/probe.full.tsv.gz" > "$OUT/rclane.out" 2>&1
rc "$OUT/r2" "$OUT/lane.full.tsv.gz" "$DS" "$TS" "$OUT/r2" --all-verdicts
rc "$OUT/low" "$OUT/low-moved.full.tsv.gz" "$DS" "$TS" "$OUT/low" --all-verdicts
PR2=$(awk -F'\t' 'NR > 1 && $1 == "MISMATCH" {print $4 ":" $7; exit}' "$OUT/low.tsv")
if [ -z "$PR2" ]; then
  # no core position holds a donor quantity below 0x100 the port moved and the gate flags when kept: a synthetic row (one per
  # value 2..255, src = dst) shows which NAMED donor quantity below 0x100 of this image pair the gate flags; the first is PR2
  rc "$OUT/probe" "$OUT/probe.full.tsv.gz" "$DS" "$TS" "$OUT/probe" --all-verdicts
  PR2=$(awk -F'\t' 'NR > 1 && $1 == "MISMATCH" {print $4 ":" $7; exit}' "$OUT/probe.tsv")
fi
PYTHONDONTWRITEBYTECODE=1 python3 "$HERE/rclane.py" "$WORK" "$OUT/lane.full.tsv.gz" --plant "$OUT/plant.full.tsv.gz" --pr2 "$PR2" >> "$OUT/rclane.out" 2>&1
rc "$OUT/plant" "$OUT/plant.full.tsv.gz" "$DS" "$TS" "$OUT/plant" --all-verdicts
python3 - "$OUT" "$PINS" "$GSHA" "$PR2" > "$OUT/roundconst.txt" <<'PY'
import os, sys
out, pins, gsha, pr2 = sys.argv[1:]
rd = lambda f: open(os.path.join(out, f)).read().splitlines() if os.path.exists(os.path.join(out, f)) else []
st = lambda f: [l.split("\t") for l in rd(f)[1:]]
print("# pins:%s; R1 input WORK/gate-raw.tsv sha256 %s" % (pins, gsha))
for n in ("r1", "r1-moved", "r2", "low", "probe", "plant"):
    print("# %s" % n)
    print("\n".join(l for l in rd(n + ".out") if l.startswith("#") or l.startswith("rc=")))
for n in ("r1", "r1-moved", "r2"):
    for r in st(n + ".tsv"):
        if r[0] != "SAME":
            print("NON-SAME\t%s\t%s" % (n, "\t".join(r[:2] + r[3:6] + r[8:12])))
base = {tuple(r[3:5] + [r[6], r[8]]) for r in st("r2.tsv") if r[0] != "SAME"}
new = [r for r in st("plant.tsv") if r[0] != "SAME" and tuple(r[3:5] + [r[6], r[8]]) not in base]
rl = [l for l in rd("rclane.out") if l.startswith("rclane: plants")]
print("# control")
print(rl[0] if rl else "rclane: no plant line")
for r in new:
    print("  new\t" + "\t".join(r[:1] + r[3:6] + r[8:12]))
ok = len(new) == 2 and all(r[0] == "MISMATCH" for r in new) and any(r[3].startswith("A/AB1w.v") for r in new) and any(r[3] + ":" + r[6] == pr2 for r in new)
print("control: planted PR1 (tfib_at_rw_len 0x55c000) and PR2 (%s): %d new non-SAME rows, %s: %s" % (
    pr2 or "none found", len(new), ", ".join(r[0] for r in new), "PASS" if ok else "FAIL"))
PY
cat "$OUT/roundconst.txt"
