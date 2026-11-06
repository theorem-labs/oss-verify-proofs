#!/bin/sh
# One command for this unit's fake-stack class-5 relocation from plugin-hostd/fuzz_command (origin/ossv/recipes REF),
# on whatever images projects/libdiginet/fuzz_transport/harness.yaml pins: a re-pin is a re-run.
#   run.sh WT HUB DONOR_DIR TARGET_DIR ALRELOC [--write]
#     WT          this unit's worktree (its harness.yaml names the pins; relocated files are written there)
#     HUB         the git hub holding REF
#     DONOR_DIR   a directory with bin/fuzz_command/fuzz_command.<build> and unstripped/fuzz_command/fuzz_command.<build>
#     TARGET_DIR  the same for fuzz_transport (result/bin/... or bin/..., and unstripped/...)
#     ALRELOC     alreloc.py of record (a5c53bb2bed4), run from its own directory (it reads align/keep-numerals.txt)
#     --write     write the relocated files (default: alreloc --dry, which writes nothing); RECORD_A / RECORD_B name the
#                 core's symbol record of each image (the donor's CmdBSyms), required with --write
# For each image (A = asan, B = asan-ubsan): pins checked against harness.yaml (donor's at REF); class5cmp.py pairs and
# compares every walked range and writes the resolve lines; its controls (the donor against itself must PASS and move
# nothing; one planted word in a copy of the target's __asan_stack_malloc_5 must FAIL); then alreloc with those resolve
# lines, and checkrep.py checks every row of alreloc's report against the two ELFs (it refuses a `gap` row and lists
# every value moved by its offset inside a symbol for a reader to confirm). With --write, a last step per written file
# puts back the donor's leading comment block byte for byte (inherited
# header and notice lines are not relocated), renames CmdBSyms to the record outside it, and adds one notice line.
# Outputs under OUT (default WT's provenance/evidence/class5/out). IMAGES (default "A B") selects the images run; unset,
# the run is the two-image run of record.
set -eu
WT=$1 HUB=$2 DD=$3 TD=$4 AL=$5 MODE=${6:---dry}
REF=781f46bc05cd
here=$(cd "$(dirname "$0")" && pwd)
OUT=${OUT:-$here/out}
mkdir -p "$OUT"
pin() { # harness.yaml text, build -> sha256
  printf '%s\n' "$1" | awk -v b="  $2:" '$0 == b {f = 1; next} f && /sha256:/ {print $2; exit}'
}
find1() { # dir, unit, build -> pinned file under bin/ or result/bin/
  for d in "$1/result/bin/$2" "$1/bin/$2"; do [ -f "$d/$2.$3" ] && { echo "$d/$2.$3"; return; }; done
  echo "run.sh: no $2.$3 under $1" >&2; exit 1
}
# HARNESS (optional): a harness.yaml naming the target pins to check against instead of WT's (a re-pin measured before
# the unit's own harness.yaml moves; the record names the file and its sha256)
th=$(cat "${HARNESS:-$WT/projects/libdiginet/fuzz_transport/harness.yaml}")
dh=$(git -C "$HUB" show "$REF:projects/plugin-hostd/fuzz_command/harness.yaml")
rc=0
kit=$(cd "${KIT:?KIT: the cmpkit 86da41d3ef68 directory (inputs/cmpkit-86da41d3ef68/ of the internal record)}" && pwd); KIT=$kit; export KIT
(cd "$kit" && sha256sum -c --quiet SHA256SUMS) || { echo "run.sh: the comparison kit copy does not match its SHA256SUMS" >&2; exit 1; }
[ "$(sha256sum < "$kit/SHA256SUMS" | cut -c1-12)" = 86da41d3ef68 ] || { echo "run.sh: kit id is not 86da41d3ef68" >&2; exit 1; }
for I in ${IMAGES:-A B}; do
  b=asan; [ $I = B ] && b=asan-ubsan
  dp=$(find1 "$DD" fuzz_command $b); tp=$(find1 "$TD" fuzz_transport $b)
  du="$DD/unstripped/fuzz_command/fuzz_command.$b"; tu="$TD/unstripped/fuzz_transport/fuzz_transport.$b"
  [ "$(sha256sum < "$dp" | cut -c1-64)" = "$(pin "$dh" $b)" ] || { echo "run.sh: $dp is not REF's $b pin" >&2; exit 1; }
  [ "$(sha256sum < "$tp" | cut -c1-64)" = "$(pin "$th" $b)" ] || { echo "run.sh: $tp is not WT's $b pin" >&2; exit 1; }
  echo "== image $I ($b): donor pin $(pin "$dh" $b | cut -c1-12), target pin $(pin "$th" $b | cut -c1-12)"
  # each pinned image and its unstripped twin: same PT_LOAD layout, no differing byte outside the ELF header and build-id
  python3 "$kit/drvcmp.py" twins "$dp" "$du" "$tp" "$tu" > "$OUT/twins-$I.txt" 2>&1 || { echo "twins $I: drvcmp failed" >&2; rc=1; }
  if grep -q 'PT_LOAD layout equal: False\|): \[[^]]' "$OUT/twins-$I.txt"; then echo "twins $I: NOT proved (see twins-$I.txt)" >&2; rc=1
  else echo "twins $I: proved ($(grep -c 'layout equal: True' "$OUT/twins-$I.txt") pairs)"; fi
  python3 "$here/class5cmp.py" --hub "$HUB" --ref $REF --img $I --donor "$dp" "$du" --target "$tp" "$tu" --out "$OUT" || rc=1
  # control 1: the donor against itself passes and moves no value
  python3 "$here/class5cmp.py" --hub "$HUB" --ref $REF --img $I --donor "$dp" "$du" --target "$dp" "$du" \
    --out "$OUT/ctl-self" > "$OUT/ctl-self-$I.log" || { echo "control self $I: FAILED to pass" >&2; rc=1; }
  if grep -q '^PASS' "$OUT/ctl-self-$I.log" && grep -q 'resolve lines: 0 move a value' "$OUT/ctl-self-$I.log"; then
    echo "control self $I: PASS, 0 values moved"
  else echo "control self $I: NOT clean (see ctl-self-$I.log)" >&2; rc=1; fi
  # control 2: one planted word (an or for the first and of __asan_stack_malloc_5) must be caught
  python3 - "$tp" "$tu" "$OUT/plant-$I" <<'EOF'
import sys, os
from elftools.elf.elffile import ELFFile
src, twin, out = sys.argv[1:]
os.makedirs(out, exist_ok=True)
e = ELFFile(open(twin, 'rb'))
s = [x for x in e.get_section_by_name('.symtab').iter_symbols() if x.name == '__asan_stack_malloc_5'][0]
for path in (src, twin):
    f = ELFFile(open(path, 'rb'))
    off = next(g['p_offset'] + s['st_value'] - g['p_vaddr'] for g in f.iter_segments()
               if g['p_type'] == 'PT_LOAD' and g['p_vaddr'] <= s['st_value'] < g['p_vaddr'] + g['p_filesz'])
    data = bytearray(open(path, 'rb').read())
    for k in range(0, s['st_size'], 4):
        w = int.from_bytes(data[off + k:off + k + 4], 'little')
        if w & 0x707f == 0x7033:  # and -> or
            data[off + k:off + k + 4] = (w & ~0x7000 | 0x6000).to_bytes(4, 'little'); break
    open(os.path.join(out, os.path.basename(path) + ('.twin' if path == twin else '')), 'wb').write(data)
EOF
  if python3 "$here/class5cmp.py" --hub "$HUB" --ref $REF --img $I --donor "$dp" "$du" \
       --target "$OUT/plant-$I/$(basename "$tp")" "$OUT/plant-$I/$(basename "$tu").twin" --out "$OUT/ctl-plant" \
       > "$OUT/ctl-plant-$I.log"; then echo "control plant $I: NOT caught" >&2; rc=1
  else echo "control plant $I: caught ($(grep -c '^FAIL' "$OUT/ctl-plant-$I.log") FAIL lines)"; fi
  rm -rf "$OUT/plant-$I"
  # the relocation (dry unless --write); the core's record name is the unit's start-up layer's (RECORD_A / RECORD_B)
  rec=$( [ $I = A ] && echo "${RECORD_A:-}" || echo "${RECORD_B:-}" )
  if [ "$MODE" = --write ] && [ -z "$rec" ]; then echo "run.sh: --write needs RECORD_$I (the core's record name)" >&2; exit 1; fi
  files="$I/Rt/RtSM5T.v $I/Rt/RtSM5.v $I/Rt/RtSF5.v $I/Rt/RtSMxA.v $I/Rt/RtStack.v"
  set -- --src plugin-hostd/fuzz_command --ref $REF --unit libdiginet/fuzz_transport --build $b --wt "$WT" \
    --pinned-elf "$tp" --unit-elf "$tu" --resolve "$OUT/resolve-$I.txt" --report "$OUT/report"
  [ "$MODE" = --write ] || set -- "$@" --dry
  (cd "$(dirname "$AL")" && python3 "$(basename "$AL")" "$@" $files) > "$OUT/alreloc-$I.out" 2>&1 ||
    { echo "alreloc $I: rc != 0 (see alreloc-$I.out)"; rc=1; }
  tail -n 3 "$OUT/alreloc-$I.out"
  # every report row checked against the two ELFs, independently of alreloc's rules (checkrep.py)
  python3 "$here/checkrep.py" "$OUT/report/libdiginet/fuzz_transport" $I "$du" "$tu" > "$OUT/checkrep-$I.txt" ||
    { echo "checkrep $I: WRONG rows (see checkrep-$I.txt)"; rc=1; }
  grep 'MOVED\|PASS\|WRONG' "$OUT/checkrep-$I.txt" || true
  [ "$MODE" = --write ] || continue
  for f in $files; do
    git -C "$HUB" show "$REF:proofs/plugin-hostd/fuzz_command/lib/$f" > "$OUT/donor.v"
    python3 - "$OUT/donor.v" "$WT/proofs/libdiginet/fuzz_transport/lib/$f" "$rec" $b <<'EOF'
import re, sys
donor, path, rec, build = sys.argv[1:]
d = open(donor).read().split('\n'); t = open(path).read().split('\n')
hd = next(k for k, l in enumerate(d) if l.startswith(('From ', 'Require ')))
ht = next(k for k, l in enumerate(t) if l.startswith(('From ', 'Require ')))
body = [re.sub(r'\bCmdBSyms\b', rec, l) for l in t[ht:]]
note = ('(* Modified by Theorem Labs, 2026-10: relocated to libdiginet/fuzz_transport\'s %s image by this unit\'s '
        'provenance/evidence/class5/run.sh (alreloc with the resolve lines of class5cmp.py); CmdBSyms becomes %s. *)'
        % (build, rec))
open(path, 'w').write('\n'.join(d[:hd] + [note] + body))
print('%s: header %d lines restored from the donor, %d CmdBSyms renamed, notice added'
      % (path.split('/lib/')[1], hd, sum(len(re.findall(r'\bCmdBSyms\b', l)) for l in t[ht:])))
EOF
  done
done
exit $rc
