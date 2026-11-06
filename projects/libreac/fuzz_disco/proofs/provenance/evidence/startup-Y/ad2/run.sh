#!/usr/bin/env bash
# startup-Y/ad2: re-derive lib/Reusable/YD2i.v, YD2j.v and YD1k.v of libreac/fuzz_disco from the collector's pass-2
# printed results (../collector/dumps/), the twin's text extracts (twin/), the released donor templates, the unit's
# own YB12.v / YB1h.v / YF0m.v / YImgTop.v and the two image B pins. Steps 1-4b and the stamp of the start-up
# generator's run (gen_ad2 / gen_ad1k on fuzz_disco's own image), then byte comparisons.
#   TREE    a checkout of the series base (the repository root)
#   IMG_B   the image B pin, fuzz_disco.asan-ubsan (index/binaries.tsv row libreac fuzz_disco asan-ubsan)
#   CGIF_B  the donor's image B pin, cgif_file_fuzzer.asan-ubsan (index/binaries.tsv row cgif cgif_file_fuzzer asan-ubsan)
#   OUT     where to write (default: ./out)
#   TWIN_B  optional: an unstripped twin of IMG_B; when given, the twin extracts are made again from it and compared
#           with twin/ (their bodies; the whole files when TWIN_B2 is given too)
#   TWIN_B2 optional, with TWIN_B: the second twin the extract header names. The extracts of record are made with
#           TWIN_B = the twin of sha256 65947ff283f5 (the one the run of record read) and TWIN_B2 = ead714913acd.
set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1
HERE="$(cd "$(dirname "$0")" && pwd)"
: "${TREE:?set TREE}" "${IMG_B:?set IMG_B}" "${CGIF_B:?set CGIF_B}"
OUT="${OUT:-./out}"; mkdir -p "$OUT"; OUT="$(cd "$OUT" && pwd -P)"
IMG_B="$(readlink -f "$IMG_B")"; CGIF_B="$(readlink -f "$CGIF_B")"
T="$HERE/tools"; NM="$HERE/twin/disco_ub.nm"; TWIN="$HERE/twin/disco_ub.symtab"; REC="$HERE/records"
D="$TREE/proofs/cgif/cgif_file_fuzzer/lib"            # the donor templates (released)
SHIP="$TREE/proofs/libreac/fuzz_disco/lib/Reusable"   # the unit's files; YB12 / YB1h / YF0m cite YImgTop.v beside them
export OSSV_BINARIES_TSV="$TREE/index/binaries.tsv"
NS1=OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib=OssFuzzTheorems.Proofs.libreac.fuzz_disco.lib.Reusable
NS2=OssFuzzTheorems.cgif.cgif_file_fuzzer.images=OssFuzzTheorems.libreac.fuzz_disco.images
MOD='the start-up data of this file is generated from fuzz_disco'"'"'s own asan-ubsan image and its own collected hand-off states.'

# 0. optional: the twin extracts again, from the twin
if [ -n "${TWIN_B:-}" ]; then
  mkdir -p "$OUT/twin"
  python3 "$HERE/twin/mknm.py" "$TWIN_B" "$IMG_B" "$OUT/twin/disco_ub.nm" "$OUT/twin/disco_ub.symtab" ${TWIN_B2:+--same "$TWIN_B2"}
  for f in disco_ub.nm disco_ub.symtab; do
    if [ -n "${TWIN_B2:-}" ]; then cmp "$OUT/twin/$f" "$HERE/twin/$f"
    else cmp <(grep -v '^#' "$OUT/twin/$f") <(grep -v '^#' "$HERE/twin/$f"); fi
  done
fi

# The pass-2 extract ships in two line-cut parts; joined, they are the extract hsform.py reads.
cat "$HERE/../collector/dumps/pass2.dump."?? > "$OUT/pass2.dump"
# The records name the files they read: run in OUT, with the two images under their own file names.
cd "$OUT"
[ "$IMG_B" = "$OUT/fuzz_disco.asan-ubsan" ] || ln -sfn "$IMG_B" fuzz_disco.asan-ubsan
[ "$CGIF_B" = "$OUT/cgif_file_fuzzer.asan-ubsan" ] || ln -sfn "$CGIF_B" cgif_file_fuzzer.asan-ubsan
IMG=fuzz_disco.asan-ubsan; CG=cgif_file_fuzzer.asan-ubsan

# 1. the hand-off states of fuzz_disco's own pass-2 run (pin, KImg, mcs, arrival-at-main and descriptor-poison gates).
#    No --pass: the extract holds only pass 2's printed results (the log's one Pass2.v compile).
python3 "$T/hsform.py" hs pass2.dump YB01.v --header "$D/YB01.v" --nholes 50 \
  --image "$IMG" --twin "$TWIN" --names "$NM" --ns "$NS1" --modified "$MOD"
# 2. YD2i + YD2j
python3 "$T/gen_ad2.py" --side B \
  --states YB01.v --atable "$SHIP/YB12.v" --tsegs "$SHIP/YB1h.v" --owned "$SHIP/YF0m.v" \
  --image "$IMG" --twin "$TWIN" \
  --tmpl-ad2i "$D/YD2i.v" --tmpl-ad2j "$D/YD2j.v" --tmpl-image "$CG" \
  --ns "$NS1" --ns "$NS2" --modified "$MOD" \
  --out-ad2i YD2i.v --out-ad2j YD2j.v --report B.report --gate-table B.gate.md
# 3. YD1k: its chunk literals restated from the GENERATED YD2j
python3 "$T/gen_ad1k.py" --tmpl-ad1k "$D/YD1k.v" --tmpl-ad2j "$D/YD2j.v" --tmpl-owned "$D/YF0m.v" --tmpl-image "$CG" \
  --ad2j YD2j.v --owned "$SHIP/YF0m.v" --image "$IMG" --twin "$TWIN" \
  --ns "$NS1" --modified "$MOD" \
  --out YD1k.v --sites YD1k.sites.md --label YD1k.v
# 4. map check 4 on the output (0 failures required), cgif's released pair as the control
python3 "$T/check4.py" --ad2j YD2j.v --ad1k YD1k.v --image "$IMG" \
  --donor-ad2j "$D/YD2j.v" --donor-image "$CG" --label "fuzz_disco YD2j (generated)" > check4.md
# 4b. lia must see through YImgTop.IMG_TOP / IMG_LO in files that Require YImgTop (none of these three does)
python3 "$T/zifyhook.py" YD2i.v YD2j.v YD1k.v
# 5. the pinned-original stamp (the generator's step-5 address-provenance call is not part of this re-run)
for f in YB01 YD2i YD2j YD1k; do python3 "$T/pins.py" stamp "$f.v" "$IMG" --twin "$TWIN"; done

# 6. byte comparisons
cmp YD2j.v "$SHIP/YD2j.v"; cmp YD1k.v "$SHIP/YD1k.v"
# the shipped YD2i.v is this output plus a hand edit with no numeral: one Modified line (after line 5), a comment and
# `Hypothesis H1_8` (after line 507), and H1_8 as the sixth mkW argument of W1 (line 768). The edit's own text names
# a source branch, so the diff is pinned here by its sha256, not shipped.
diff YD2i.v "$SHIP/YD2i.v" > YD2i.hand.diff || [ $? -eq 1 ]
grep -E '^[0-9]' YD2i.hand.diff
[ "$(sha256sum < YD2i.hand.diff | cut -c1-64)" = cbf8f7bab739f4c6a104d3ba8dfd98c2b8cd46905326c621d6c2083f580fb98e ]
# the states gen_ad2 read are the shipped YB01.v's: the same file below the header comments, the same per-hole record
body() { awk 'f || !/^\(\*/ { f = 1; print }' "$1"; }
cmp <(body YB01.v) <(body "$SHIP/YB01.v"); cmp YB01.v.json "$HERE/../collector/YB01.v.json"
for f in B.gate.md B.report YD1k.sites.md check4.md; do cmp "$f" "$REC/$f"; done
echo "ad2: YD2j.v and YD1k.v reproduced byte for byte; YD2i.v = output + the pinned hand edit; records equal"
