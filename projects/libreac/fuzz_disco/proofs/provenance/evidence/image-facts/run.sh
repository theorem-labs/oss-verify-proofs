#!/usr/bin/env bash
# run.sh -- re-runs every script of this directory from this directory's files and compares each output with the
# shipped table, gate record or proof file byte for byte (cmp). Prints one line per output; exits 1 if any differs.
# usage: run.sh PIN_A PIN_B TWIN_A TWIN_B UNIT OUT
#   PIN_A, PIN_B: the pinned images fuzz_disco.asan and fuzz_disco.asan-ubsan; TWIN_A, TWIN_B: their unstripped twins;
#   UNIT: the unit's proof directory (proofs/libreac/fuzz_disco of a checkout); OUT: a new scratch directory.
set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1
if [ $# -ne 6 ]; then sed -n '2,6p' "$0"; exit 2; fi
PA=$1; PB=$2; TA=$3; TB=$4; U=$5; O=$6
H=$(cd "$(dirname "$0")" && pwd)
X=$H/extract; LA=$H/listing-A; LY=$H/listing-Y; CK=$H/checklisting
mkdir -p "$O"
bad=0
same() {
  if cmp -s "$1" "$2"; then echo "same      $3"; else echo "DIFFERENT $3"; bad=$((bad + 1)); fi
}
fact() { awk -v k="$2" '$1 == k { $1 = ""; sub(/^ /, ""); print }' "$1"; }

# 1. Text extracts of the twins (symbol tables) and of the pins (sections, segments, RELRO, GOT slots).
python3 "$X/symbol_table.py" "$TA" "$PA" "$O/symbols-asan.txt"
python3 "$X/symbol_table.py" "$TB" "$PB" "$O/symbols-asan-ubsan.txt"
same "$O/symbols-asan.txt" "$X/symbols-asan.txt" extract/symbols-asan.txt
same "$O/symbols-asan-ubsan.txt" "$X/symbols-asan-ubsan.txt" extract/symbols-asan-ubsan.txt
SHADOW=__asan_shadow_memory_dynamic_address; UAR=__asan_option_detect_stack_use_after_return
CA1=$(python3 "$X/symbol_facts.py" "$O/symbols-asan.txt" addr $SHADOW)
CA2=$(python3 "$X/symbol_facts.py" "$O/symbols-asan.txt" addr $UAR)
CB1=$(python3 "$X/symbol_facts.py" "$O/symbols-asan-ubsan.txt" addr $SHADOW)
CB2=$(python3 "$X/symbol_facts.py" "$O/symbols-asan-ubsan.txt" addr $UAR)
python3 "$X/image_facts.py" "$PA" "$O/facts-asan.txt" --got-of "$CA1" --got-of "$CA2"
python3 "$X/image_facts.py" "$PB" "$O/facts-asan-ubsan.txt" --got-of "$CB1" --got-of "$CB2"
same "$O/facts-asan.txt" "$X/facts-asan.txt" extract/facts-asan.txt
same "$O/facts-asan-ubsan.txt" "$X/facts-asan-ubsan.txt" extract/facts-asan-ubsan.txt

# 2. The read-only-after-relocation bounds written in the proofs equal the pins' section headers.
{ python3 "$X/relro_check.py" "$O/facts-asan.txt" "$U/lib/A/Prog/DiscoImg.v" \
    'disco_relro_lo : Z := (0x[0-9a-f]+)' 'disco_relro_hi : Z := (0x[0-9a-f]+)' || true
  python3 "$X/relro_check.py" "$O/facts-asan-ubsan.txt" "$U/lib/Reusable/YCbj.v" \
    'pa_relro_lo := (0x[0-9a-f]+)' 'pa_relro_hi := (0x[0-9a-f]+)' || true; } > "$O/relro.out"
same "$O/relro.out" "$X/relro.out" extract/relro.out

# 3. Image A (asan): the listing, then its three proof files. Objects 66 and 67 are the two cells the walks read
#    through a GOT word (shadow base, use-after-return flag).
RA=$(python3 "$X/symbol_facts.py" "$O/symbols-asan.txt" range LLVMFuzzerTestOneInput reac_ports_parse)
python3 "$LA/mklisting.py" "$PA" "$O/symbols-asan.txt" $RA --prefix disco --out "$O/genA" \
  --call "$(cat "$LA/call-list.txt")" > /dev/null
same "$O/genA/listing.json" "$LA/gen/listing.json" listing-A/gen/listing.json
python3 "$LA/emit_disco.py" "$O/genA" --dst "$O/A" --extra-obj "66=$CA1,67=$CA2" > /dev/null
for f in DiscoSyms DiscoList DiscoAddr; do same "$O/A/$f.v" "$U/lib/A/Prog/$f.v" "lib/A/Prog/$f.v"; done

# 4. Image B (asan-ubsan): the listing, the object numbers the earlier unit's frame files use (objects 0 and 1 are
#    the two GOT slots, 12 and 13 the two cells), then its proof files. RELRO, the PT_LOAD count and the end of .text
#    come from the pin's facts; the C library start (sysconf) and oft_exit_guard from the symbol table extract.
RB=$(python3 "$X/symbol_facts.py" "$O/symbols-asan-ubsan.txt" range LLVMFuzzerTestOneInput reac_ports_parse)
GB1=$(fact "$O/facts-asan-ubsan.txt" got | awk -v c="$CB1" '$2 == c { print $1 }')
GB2=$(fact "$O/facts-asan-ubsan.txt" got | awk -v c="$CB2" '$2 == c { print $1 }')
python3 "$LA/mklisting.py" "$PB" "$O/symbols-asan-ubsan.txt" $RB --prefix discob --out "$O/genY0" \
  --call "$(cat "$LY/call-b.txt")" > /dev/null
python3 "$LY/repin.py" "$O/genY0" "$O/genY" "0=$GB1,1=$GB2,12=$CB1,13=$CB2" > /dev/null
same "$O/genY/listing.json" "$LY/gen/listing.json" listing-Y/gen/listing.json
mkdir -p "$O/Y"
MUSL=$(python3 "$X/symbol_facts.py" "$O/symbols-asan-ubsan.txt" addr sysconf)
GUARD=$(python3 "$X/symbol_facts.py" "$O/symbols-asan-ubsan.txt" addr oft_exit_guard)
TEXT_END=$(fact "$O/facts-asan-ubsan.txt" section | awk '$1 == ".text" { print $4 }')
python3 "$LY/gen_y.py" "$O/genY" "$O/Y" $(fact "$O/facts-asan-ubsan.txt" relro) $(fact "$O/facts-asan-ubsan.txt" nseg) \
  "$MUSL" "$TEXT_END" "$GUARD" > /dev/null
for f in YI0w YI0z YI12 YCef YC8i YB1v; do same "$O/Y/$f.v" "$U/lib/Reusable/$f.v" "lib/Reusable/$f.v"; done

# 5. Gates. The listing range reads one label-minus-base jump table: 9 int32 entries at 0x212b8 (the same address in
#    both images, whose .rodata start and size are equal).
python3 "$CK/checklisting.py" --prog "$U/lib/A/Prog" --elf "$PA" --nm "$O/symbols-asan.txt" --name Disco \
  --prefix disco --jtable 0x212b8,9,rel32 > "$O/checklisting.A.out" || true
same "$O/checklisting.A.out" "$LA/checklisting.A.out" listing-A/checklisting.A.out
python3 "$LA/straightline.py" "$PA" "$O/symbols-asan.txt" $RA --json "$O/straightline.S3a.json" > /dev/null || true
same "$O/straightline.S3a.json" "$LA/straightline.S3a.json" listing-A/straightline.S3a.json
python3 "$LY/pichk.py" "$O/genA" "$PA" > "$O/pichk.A.out" || true
same "$O/pichk.A.out" "$LA/pichk.A.out" listing-A/pichk.A.out
python3 "$CK/emit_rocq.py" "$O/genY" --dst "$O/emitY" --lib OssFuzzTheorems.Proofs.libreac.fuzz_disco.lib \
  --name DiscoB --prefix discob --target fuzz_disco > /dev/null
python3 "$CK/checklisting.py" --prog "$O/emitY" --elf "$PB" --nm "$O/symbols-asan-ubsan.txt" --name DiscoB \
  --prefix discob --jtable 0x212b8,9,rel32 > "$O/checklisting.Y.out" || true
same "$O/checklisting.Y.out" "$LY/checklisting.Y.out" listing-Y/checklisting.Y.out
python3 "$LY/pichk.py" "$O/genY" "$PB" > "$O/pichk.Y.out" || true
same "$O/pichk.Y.out" "$LY/pichk.Y.out" listing-Y/pichk.Y.out
python3 "$LY/heldcheck.py" "$PB" "$O/symbols-asan-ubsan.txt" $RB --table 0x212b8:9:0x212b8 > "$O/heldcheck.b.out" || true
same "$O/heldcheck.b.out" "$LY/heldcheck.b.out" listing-Y/heldcheck.b.out

echo "different: $bad"
[ "$bad" -eq 0 ]
