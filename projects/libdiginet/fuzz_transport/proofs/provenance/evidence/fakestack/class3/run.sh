#!/bin/sh
# One command for this unit's fake-stack class-3 relocation, generalized from ../class5/run.sh (the class-5 method of
# record). Image B (asan-ubsan) only: image A calls no __asan_stack_malloc_3. On whatever image
# projects/libdiginet/fuzz_transport/harness.yaml pins: a re-pin is a re-run.
#   run.sh WT HUB AGENTS TARGET_DIR ALRELOC [--write]
#     WT          this unit's worktree (its harness.yaml names the pin; relocated files are written there)
#     HUB         the git hub holding the donor refs (origin/ossv/recipes history)
#     AGENTS      the root of the pipeline directories (agents/): each donor's <pipeline>/<project>/bin/<unit>/ and
#                 <pipeline>/<project>/unstripped/<unit>/ (donor() names the pipeline whose file is the donor ref's pin)
#     TARGET_DIR  a directory with bin/fuzz_transport/fuzz_transport.asan-ubsan (or result/bin/...) and unstripped/...
#     ALRELOC     alreloc.py of record (a5c53bb2bed4), run from its own directory (it reads align/keep-numerals.txt)
#     --write     write the relocated files (default: alreloc --dry, which writes nothing); RECORD_B names the core's
#                 symbol record of image B (it replaces the donor's record name), required with --write
# Rule 24 first: every released image-B class-3 walk (DONORS: the git-grep lookup of RULE24-LOOKUP.txt) is compared with
# the target image by class3cmp.py, its pin checked against the donor ref's harness.yaml and its twin proved; the donor
# chosen from that compare (SRC, BYTECMP-port2.md says why) then gets: its controls (the donor against itself must PASS
# and move nothing; one planted word in a copy of the target's __asan_stack_malloc_3 must FAIL); alreloc with its resolve
# lines; and checkrep.py, which checks every row of alreloc's report against the two ELFs (it refuses a `gap` row and
# lists every value moved by its offset inside a symbol for a reader to confirm). With --write, a last step per written
# file puts back the donor's leading comment block byte for byte (inherited header and notice lines are not relocated),
# renames the donor's record to RECORD_B outside it, and adds one notice line.
# Outputs under OUT (default WT's provenance/evidence/class3/out).
set -eu
WT=$1 HUB=$2 AGENTS=$3 TD=$4 AL=$5 MODE=${6:---dry}
DONORS="plugin-hostd/fuzz_command libreac/fuzz_boxreg libreac/fuzz_identity libreac/fuzz_disco omx-clap-core/fuzz_state
omx-clap-core/fuzz_preset"
SRC=plugin-hostd/fuzz_command
donor() { # unit -> ref, pipeline, lib directory of its asan-ubsan image, its symbol record, the files a relocation writes
  case $1 in
    plugin-hostd/fuzz_command) echo 781f46bc05cd pau-pipeline B CmdBSyms B/Rt/RtSM3T.v B/Rt/RtSM3.v ;;
    libreac/fuzz_boxreg) echo ee71d1fd3fcf pau-pipeline B BoxregSyms B/Rt/StackMalloc3Tbl.v B/Rt/StackMalloc3.v ;;
    libreac/fuzz_identity) echo cffeac4df63e pau-pipeline B TfibSyms B/Rt/StackMalloc3Tbl.v B/Rt/StackMalloc3.v ;;
    libreac/fuzz_disco) echo b5cf457a8820 pau-pipeline Y TfibSyms Y/Rt/StackMalloc3Tbl.v Y/Rt/StackMalloc3.v ;;
    omx-clap-core/fuzz_state) echo d0e2eea9a341 pau-pipeline B TfibSyms B/FCimg.v B/FCm3r.v B/FCm3s.v ;;
    omx-clap-core/fuzz_preset) echo 4cda83dac850 pau-preset-102 AU TfibSyms AU/FCimgB.v AU/FCm3r.v AU/FCm3s.v ;;
  esac
}
here=$(cd "$(dirname "$0")" && pwd)
OUT=${OUT:-$here/out}
mkdir -p "$OUT"
b=asan-ubsan
pin() { # harness.yaml text, build -> sha256
  printf '%s\n' "$1" | awk -v b="  $2:" '$0 == b {f = 1; next} f && /sha256:/ {print $2; exit}'
}
find1() { # dir, unit, build -> pinned file under bin/ or result/bin/
  for d in "$1/result/bin/$2" "$1/bin/$2"; do [ -f "$d/$2.$3" ] && { echo "$d/$2.$3"; return; }; done
  echo "run.sh: no $2.$3 under $1" >&2; exit 1
}
# HARNESS (optional): a harness.yaml naming the target pin to check against instead of WT's
th=$(cat "${HARNESS:-$WT/projects/libdiginet/fuzz_transport/harness.yaml}")
rc=0
kit=$(cd "${KIT:?KIT: the cmpkit 86da41d3ef68 directory (inputs/cmpkit-86da41d3ef68/ of the internal record)}" && pwd); KIT=$kit; export KIT
(cd "$kit" && sha256sum -c --quiet SHA256SUMS) || { echo "run.sh: the comparison kit copy does not match its SHA256SUMS" >&2; exit 1; }
[ "$(sha256sum < "$kit/SHA256SUMS" | cut -c1-12)" = 86da41d3ef68 ] || { echo "run.sh: kit id is not 86da41d3ef68" >&2; exit 1; }
tp=$(find1 "$TD" fuzz_transport $b); tu="$TD/unstripped/fuzz_transport/fuzz_transport.$b"
[ "$(sha256sum < "$tp" | cut -c1-64)" = "$(pin "$th" $b)" ] || { echo "run.sh: $tp is not WT's $b pin" >&2; exit 1; }
echo "== image B ($b): target pin $(pin "$th" $b | cut -c1-12)"
# rule 24: compare every donor first
for u in $DONORS; do
  set -- $(donor $u); ref=$1; P="$AGENTS/$2/${u%/*}"
  n=${u#*/}; dp=$(find1 "$P" $n $b); du="$P/unstripped/$n/$n.$b"
  dh=$(git -C "$HUB" show "$ref:projects/$u/harness.yaml")
  [ "$(sha256sum < "$dp" | cut -c1-64)" = "$(pin "$dh" $b)" ] || { echo "run.sh: $dp is not $u's $b pin at $ref" >&2; exit 1; }
  # each pinned image and its unstripped twin: same PT_LOAD layout, no differing byte outside the ELF header and build-id
  python3 "$kit/drvcmp.py" twins "$dp" "$du" "$tp" "$tu" > "$OUT/twins-$n.txt" 2>&1 || { echo "twins $n: drvcmp failed" >&2; rc=1; }
  if grep -q 'PT_LOAD layout equal: False\|): \[[^]]' "$OUT/twins-$n.txt"; then echo "twins $n: NOT proved (see twins-$n.txt)" >&2; rc=1
  else echo "twins $n: proved ($(grep -c 'layout equal: True' "$OUT/twins-$n.txt") pairs)"; fi
  if python3 "$here/class3cmp.py" --hub "$HUB" --ref $ref --src $u --donor "$dp" "$du" --target "$tp" "$tu" \
       --out "$OUT/cmp-$n" > "$OUT/cmp-$n.log"; then v=PASS; else v=FAIL; fi
  echo "rule 24 compare $u at $ref (pin $(pin "$dh" $b | cut -c1-12)): $v; $(grep '^closeness' "$OUT/cmp-$n.log")"
done
# the chosen donor
set -- $(donor $SRC); REF=$1 P="$AGENTS/$2/${SRC%/*}" SUB=$3 REC=$4; shift 4; files="$*"
n=${SRC#*/}; dp=$(find1 "$P" $n $b); du="$P/unstripped/$n/$n.$b"
echo "== chosen donor $SRC at $REF"
python3 "$here/class3cmp.py" --hub "$HUB" --ref $REF --src $SRC --donor "$dp" "$du" --target "$tp" "$tu" --out "$OUT" || rc=1
# control 1: the donor against itself passes and moves no value
python3 "$here/class3cmp.py" --hub "$HUB" --ref $REF --src $SRC --donor "$dp" "$du" --target "$dp" "$du" \
  --out "$OUT/ctl-self" > "$OUT/ctl-self-B.log" || { echo "control self B: FAILED to pass" >&2; rc=1; }
if grep -q '^PASS' "$OUT/ctl-self-B.log" && grep -q 'resolve lines: 0 move a value' "$OUT/ctl-self-B.log"; then
  echo "control self B: PASS, 0 values moved"
else echo "control self B: NOT clean (see ctl-self-B.log)" >&2; rc=1; fi
# control 2: one planted word (an or for the first and of __asan_stack_malloc_3) must be caught
python3 - "$tp" "$tu" "$OUT/plant-B" <<'EOF'
import sys, os
from elftools.elf.elffile import ELFFile
src, twin, out = sys.argv[1:]
os.makedirs(out, exist_ok=True)
e = ELFFile(open(twin, 'rb'))
s = [x for x in e.get_section_by_name('.symtab').iter_symbols() if x.name == '__asan_stack_malloc_3'][0]
for path in (src, twin):
    f = ELFFile(open(path, 'rb'))
    off = next(g['p_offset'] + s['st_value'] - g['p_vaddr'] for g in f.iter_segments()
               if g['p_type'] == 'PT_LOAD' and g['p_vaddr'] <= s['st_value'] < g['p_vaddr'] + g['p_filesz'])
    data = bytearray(open(path, 'rb').read())
    for k in range(0, s['st_size'], 4):
        w = int.from_bytes(data[off + k:off + k + 4], 'little')
        if w & 0xfe00707f == 0x7033:  # and -> or
            data[off + k:off + k + 4] = (w & ~0x7000 | 0x6000).to_bytes(4, 'little')
            print('planted: __asan_stack_malloc_3 + 0x%x: 0x%08x -> 0x%08x' % (k, w, w & ~0x7000 | 0x6000))
            break
    open(os.path.join(out, os.path.basename(path) + ('.twin' if path == twin else '')), 'wb').write(data)
EOF
if python3 "$here/class3cmp.py" --hub "$HUB" --ref $REF --src $SRC --donor "$dp" "$du" \
     --target "$OUT/plant-B/$(basename "$tp")" "$OUT/plant-B/$(basename "$tu").twin" --out "$OUT/ctl-plant" \
     > "$OUT/ctl-plant-B.log"; then echo "control plant B: NOT caught" >&2; rc=1
else echo "control plant B: caught ($(grep -c '^FAIL' "$OUT/ctl-plant-B.log") FAIL lines)"; fi
rm -rf "$OUT/plant-B"
# the relocation (dry unless --write); the core's record name is the unit's start-up layer's (RECORD_B)
rec=${RECORD_B:-}
if [ "$MODE" = --write ] && [ -z "$rec" ]; then echo "run.sh: --write needs RECORD_B (the core's record name)" >&2; exit 1; fi
set -- --src $SRC --ref $REF --unit libdiginet/fuzz_transport --build $b --wt "$WT" \
  --pinned-elf "$tp" --unit-elf "$tu" --resolve "$OUT/resolve-B.txt" --report "$OUT/report"
[ "$MODE" = --write ] || set -- "$@" --dry
(cd "$(dirname "$AL")" && python3 "$(basename "$AL")" "$@" $files) > "$OUT/alreloc-B.out" 2>&1 ||
  { echo "alreloc B: rc != 0 (see alreloc-B.out)"; rc=1; }
tail -n 3 "$OUT/alreloc-B.out"
# every report row checked against the two ELFs, independently of alreloc's rules (checkrep.py)
python3 "$here/checkrep.py" "$OUT/report/libdiginet/fuzz_transport" $SUB "$du" "$tu" > "$OUT/checkrep-B.txt" ||
  { echo "checkrep B: WRONG rows (see checkrep-B.txt)"; rc=1; }
grep 'MOVED\|PASS\|WRONG' "$OUT/checkrep-B.txt" || true
[ "$MODE" = --write ] || exit $rc
for f in $files; do
  git -C "$HUB" show "$REF:proofs/$SRC/lib/$f" > "$OUT/donor.v"
  python3 - "$OUT/donor.v" "$WT/proofs/libdiginet/fuzz_transport/lib/$f" "$REC" "$rec" $b <<'EOF'
import re, sys
donor, path, old, rec, build = sys.argv[1:]
d = open(donor).read().split('\n'); t = open(path).read().split('\n')
hd = next(k for k, l in enumerate(d) if l.startswith(('From ', 'Require ')))
ht = next(k for k, l in enumerate(t) if l.startswith(('From ', 'Require ')))
body = [re.sub(r'\b%s\b' % old, rec, l) for l in t[ht:]]
note = ('(* Modified by Theorem Labs, 2026-10: relocated to libdiginet/fuzz_transport\'s %s image by this unit\'s '
        'provenance/evidence/class3/run.sh (alreloc with the resolve lines of class3cmp.py); %s becomes %s. *)'
        % (build, old, rec))
open(path, 'w').write('\n'.join(d[:hd] + [note] + body))
print('%s: header %d lines restored from the donor, %d %s renamed, notice added'
      % (path.split('/lib/')[1], hd, sum(len(re.findall(r'\b%s\b' % old, l)) for l in t[ht:]), old))
EOF
done
exit $rc
