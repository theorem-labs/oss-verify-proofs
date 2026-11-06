#!/usr/bin/env bash
# run.sh TWIN_DIR PIN_DIR YH03_TOOL_DIR OUTDIR
#
# Re-runs every script of this slice and compares each output with the shipped file (cmp). Exit 0 only if all match.
#   TWIN_DIR       directory holding the unstripped twins fuzz_disco.plain and fuzz_disco.ubsan (host binaries, not shipped)
#   PIN_DIR        directory holding the pinned images fuzz_disco.plain and fuzz_disco.ubsan (harness.yaml's pins)
#   YH03_TOOL_DIR  directory holding the address-table tools v6.4 of record: yh03check.py (sha256 fb3bfbc1eea8...) and
#                  yh03regen.py (sha256 1254e5c96a44...); cited, not copied (MANIFEST)
#   OUTDIR         an empty scratch directory outside the repository
# The repository root and the unit directory are found from this script's own location. Needs python3 and capstone.
# Steps 1, 2 and 4 to 8 read files that were removed from the shipped tree on 2026-11-04 (internal record; in git history); restore them from there to run those steps.
set -euo pipefail
[ $# -eq 4 ] || { sed -n '2,11p' "$0"; exit 2; }
TWIN=$(cd "$1" && pwd); PIN=$(cd "$2" && pwd); TOOL=$(cd "$3" && pwd); OUT=$4
mkdir -p "$OUT"; OUT=$(cd "$OUT" && pwd)
SLICE=$(cd "$(dirname "$0")" && pwd)
UNIT=$(cd "$SLICE/../../.." && pwd)
ROOT=$(cd "$UNIT/../../.." && pwd)
REL=proofs/libreac/fuzz_disco
[ "$ROOT/$REL" = "$UNIT" ] || { echo "run.sh: not inside $REL"; exit 2; }

want() { [ "$(sha256sum "$1" | cut -c1-12)" = "$2" ] || { echo "run.sh: $1 is not sha256 $2..."; exit 2; }; }
want "$TOOL/yh03check.py" fb3bfbc1eea8
want "$TOOL/yh03regen.py" 1254e5c96a44

fail=0
same() { if cmp -s "$1" "$2"; then echo "OK    $2"; else echo "DIFF  $2"; fail=1; fi; }

# 1. table + old file + the fix's comment line -> the shipped address table, byte for byte
for s in "plain lib/Reusable" "ubsan lib/U/Reusable"; do
  set -- $s
  python3 "$SLICE/scripts/apply_table.py" "$SLICE/inputs/old-$1.v.txt" "$SLICE/tables/yh03-fix-table-$1.tsv" \
    "$SLICE/inputs/header-$1.txt" 4 > "$OUT/YH03-$1.v"
  same "$OUT/YH03-$1.v" "$UNIT/$2/YH03.v"
done

# 2. the deleted cells have no use in the fixed tree
python3 "$SLICE/scripts/delete_users.py" "$UNIT" \
  "$SLICE/tables/yh03-fix-table-plain.tsv" "$SLICE/tables/yh03-fix-table-ubsan.tsv" > "$OUT/delete-users.txt" || true
same "$OUT/delete-users.txt" "$SLICE/gates/delete-users.txt"

# 3. twin vs pin (every PT_LOAD: header and bytes), 4. NOSYM cells by bytes and readers
for b in plain ubsan; do
  python3 "$SLICE/scripts/elf_reader.py" loads "$PIN/fuzz_disco.$b" "$TWIN/fuzz_disco.$b" > "$OUT/twin-pin-$b.txt"
  same "$OUT/twin-pin-$b.txt" "$SLICE/gates/twin-pin-$b.txt"
done
python3 "$SLICE/scripts/nosym_check.py" "$TWIN/fuzz_disco.plain" "$UNIT/lib/Reusable/YH03.v" > "$OUT/nosym-plain.txt"
same "$OUT/nosym-plain.txt" "$SLICE/gates/nosym-plain.txt"
python3 "$SLICE/scripts/nosym_check.py" "$TWIN/fuzz_disco.ubsan" "$UNIT/lib/U/Reusable/YH03.v" > "$OUT/nosym-ubsan.txt"
same "$OUT/nosym-ubsan.txt" "$SLICE/gates/nosym-ubsan.txt"

# 5. the checker v6.4, --pinned, on both fixed files, run with relative paths only (its output names no host path)
W="$OUT/work"; rm -rf "$W"; mkdir -p "$W"
ln -s "$ROOT/proofs" "$W/proofs"; ln -s "$ROOT/projects" "$W/projects"; ln -s "$TWIN" "$W/twin"; ln -s "$PIN" "$W/pin"
for s in "plain lib/Reusable" "ubsan lib/U/Reusable"; do
  set -- $s
  (cd "$W" && python3 "$TOOL/yh03check.py" --pinned "pin/fuzz_disco.$1" --pins projects/libreac/fuzz_disco/harness.yaml \
     "twin/fuzz_disco.$1" "$REL/$2/YH03.v") > "$OUT/yh03check-$1.out" 2>&1 || true
  awk '/^# self-test: [0-9]+ known answers OK/{s=1} /^# rows checked: [0-9]+; rows not OK: 0$/{r=1} END{exit !(s&&r)}' \
    "$OUT/yh03check-$1.out" || { echo "FAIL  yh03check-$1.out: no self-test OK line or rows not OK"; fail=1; }
  same "$OUT/yh03check-$1.out" "$SLICE/gates/yh03check-$1.out"
done
rm -rf "$W"

# 6. the re-derivation tool v6.4 on SCRATCH copies of the OLD files (--pinned, --elf = the unit-identity-checked twin,
#    --proofs = the fixed unit tree for readers; it refuses to write, see its output), then the cell-by-cell comparison
#    of its report with the fixed files: every cell it does not judge or judges otherwise, with the covering decision.
W="$OUT/regen"; rm -rf "$W"; mkdir -p "$W/$REL/lib/Reusable" "$W/$REL/lib/U/Reusable"
ln -s "$ROOT/projects" "$W/projects"; ln -s "$TWIN" "$W/twin"; ln -s "$PIN" "$W/pin"; ln -s "$UNIT" "$W/unit"
for s in "plain lib/Reusable" "ubsan lib/U/Reusable"; do
  set -- $s
  cp "$SLICE/inputs/old-$1.v.txt" "$W/$REL/$2/YH03.v"
  (cd "$W" && python3 "$TOOL/yh03regen.py" /dev/null "$REL/$2/YH03.v" --syms-elf "twin/fuzz_disco.$1" \
     --pinned "pin/fuzz_disco.$1" --pins projects/libreac/fuzz_disco/harness.yaml --elf "twin/fuzz_disco.$1" \
     --proofs unit --report "$OUT/regen-old-$1.tsv") > "$OUT/regen-old-$1.out" 2>&1 || true
  awk '/^# self-test: [0-9]+ known answers OK/{s=1} END{exit !s}' "$OUT/regen-old-$1.out" \
    || { echo "FAIL  regen-old-$1.out: no self-test OK line"; fail=1; }
  same "$OUT/regen-old-$1.out" "$SLICE/gates/regen-old-$1.out"
  same "$OUT/regen-old-$1.tsv" "$SLICE/gates/regen-old-$1.tsv"
  python3 "$SLICE/scripts/regen_compare.py" "$1" "$OUT/regen-old-$1.tsv" "$UNIT/$2/YH03.v" \
    "$SLICE/tables/yh03-fix-table-$1.tsv" > "$OUT/regen-decisions-$1.tsv" \
    || { echo "FAIL  regen-decisions-$1.tsv: the tool proposes another value for a FIXED or KEPT cell"; fail=1; }
  same "$OUT/regen-decisions-$1.tsv" "$SLICE/tables/regen-decisions-$1.tsv"
done
rm -rf "$W"

# 7. the re-derivation tool v6.4 on the FIXED files themselves (no --write: nothing changes), --proofs the unit tree:
#    every cell must be judged without a FIX, an ABSENT / OMITTED or a REFUSED row.
W="$OUT/fixed"; rm -rf "$W"; mkdir -p "$W"
ln -s "$ROOT/proofs" "$W/proofs"; ln -s "$ROOT/projects" "$W/projects"; ln -s "$TWIN" "$W/twin"; ln -s "$PIN" "$W/pin"
for s in "plain lib/Reusable" "ubsan lib/U/Reusable"; do
  set -- $s
  (cd "$W" && python3 "$TOOL/yh03regen.py" /dev/null "$REL/$2/YH03.v" --syms-elf "twin/fuzz_disco.$1" \
     --pinned "pin/fuzz_disco.$1" --pins projects/libreac/fuzz_disco/harness.yaml --elf "twin/fuzz_disco.$1" \
     --proofs "$REL" --report "$OUT/regen-fixed-$1.tsv") > "$OUT/regen-fixed-$1.out" 2>&1 \
     || { echo "FAIL  regen-fixed-$1.out: the tool does not accept the fixed file"; fail=1; }
  awk -F'\t' '$3 ~ /^(FIX|ABSENT|OMITTED|REFUSED|UNCHECKED)$/{b=1} END{exit b}' "$OUT/regen-fixed-$1.tsv" \
    || { echo "FAIL  regen-fixed-$1.tsv: a FIX / ABSENT / OMITTED / REFUSED / UNCHECKED row"; fail=1; }
  same "$OUT/regen-fixed-$1.out" "$SLICE/gates/regen-fixed-$1.out"
  same "$OUT/regen-fixed-$1.tsv" "$SLICE/gates/regen-fixed-$1.tsv"
done
rm -rf "$W"

# 8. every D cell the tool leaves unjudged (NOSYM in the fixed-file report) read against the PINNED image: TRUE / FALSE
#    by what its name says, with its readers outside the two YH03.v files.
for s in "plain lib/Reusable" "ubsan lib/U/Reusable"; do
  set -- $s
  python3 "$SLICE/scripts/nosym_read.py" "$PIN/fuzz_disco.$1" "$TWIN/fuzz_disco.$1" "$UNIT/$2/YH03.v" \
    "$SLICE/gates/regen-fixed-$1.tsv" "$UNIT" > "$OUT/nosym-read-$1.tsv" \
    || { echo "FAIL  nosym-read-$1.tsv: a FALSE cell"; fail=1; }
  same "$OUT/nosym-read-$1.tsv" "$SLICE/gates/nosym-read-$1.tsv"
done
exit $fail
