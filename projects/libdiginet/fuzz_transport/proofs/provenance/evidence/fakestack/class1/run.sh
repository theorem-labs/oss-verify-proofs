#!/bin/sh
# One command for this unit's fake-stack class-N relocation (class5/run.sh made class- and donor-generic), on whatever
# images projects/libdiginet/fuzz_transport/harness.yaml pins: a re-pin is a re-run.
#   run.sh WT HUB DONOR_DIR TARGET_DIR ALRELOC [--write]
#     WT          this unit's worktree (its harness.yaml names the pins; relocated files are written there)
#     HUB         the git hub holding the donor REF
#     DONOR_DIR   a directory with bin/<u>/<u>.<build> and unstripped/<u>/<u>.<build> of the donor unit <u>
#     TARGET_DIR  the same for fuzz_transport (result/bin/... or bin/..., and unstripped/...)
#     ALRELOC     alreloc.py of record (a5c53bb2bed4), run from its own directory (it reads align/keep-numerals.txt)
#     --write     write the relocated files (default: alreloc --dry, which writes nothing); RECORD_A / RECORD_B name the
#                 core's symbol record of each image (the donor's $SYMREC), required with --write
# The class is the directory of the calling run.sh (CLSDIR, default this one): CLSDIR/donor.conf names the donor (SRC at
# REF), per image the code tables (TABLES_<I>, FILE:VAR) and the files relocated (FILES_<I>), the image-free files the
# relocated ones Require (COPY, checked here to hold no image-range numeral), and the donor's record name SYMREC;
# CLSDIR/model.txt lists the model constants (kept). For each image (A = asan, B = asan-ubsan): pins checked against
# harness.yaml (the donor's at REF); clscmp.py pairs and compares every walked range and writes the resolve lines; its
# controls (the donor against itself must PASS and move nothing; one planted word in a copy of the target's
# __asan_stack_malloc_<CLS> must FAIL); then alreloc with those resolve lines, and checkrep.py checks every row of
# alreloc's report against the two ELFs (it refuses a `gap` row and lists every value moved by its offset inside a symbol
# for a reader to confirm). With --write, a last step per written file puts back the donor's leading comment block byte
# for byte (inherited header and notice lines are not relocated), renames $SYMREC to the record outside it, and adds one
# notice line. Outputs under OUT (default CLSDIR/out-port2). IMAGES (default "A B") selects the images run; unset, the
# run is the two-image run of record.
set -eu
WT=$1 HUB=$2 DD=$3 TD=$4 AL=$5 MODE=${6:---dry}
here=$(cd "$(dirname "$0")" && pwd)
CLSDIR=${CLSDIR:-$here}
. "$CLSDIR/donor.conf"
OUT=${OUT:-$CLSDIR/out-port2}
mkdir -p "$OUT"
u=${SRC#*/}
pin() { # harness.yaml text, build -> sha256
  printf '%s\n' "$1" | awk -v b="  $2:" '$0 == b {f = 1; next} f && /sha256:/ {print $2; exit}'
}
find1() { # dir, unit, build -> pinned file under bin/ or result/bin/
  for d in "$1/result/bin/$2" "$1/bin/$2"; do [ -f "$d/$2.$3" ] && { echo "$d/$2.$3"; return; }; done
  echo "run.sh: no $2.$3 under $1" >&2; exit 1
}
# HARNESS (optional): a harness.yaml naming the target pins to check against instead of WT's
th=$(cat "${HARNESS:-$WT/projects/libdiginet/fuzz_transport/harness.yaml}")
dh=$(git -C "$HUB" show "$REF:projects/$SRC/harness.yaml")
rc=0
kit=$(cd "${KIT:?KIT: the cmpkit 86da41d3ef68 directory (inputs/cmpkit-86da41d3ef68/ of the internal record)}" && pwd); KIT=$kit; export KIT
(cd "$kit" && sha256sum -c --quiet SHA256SUMS) || { echo "run.sh: the comparison kit copy does not match its SHA256SUMS" >&2; exit 1; }
[ "$(sha256sum < "$kit/SHA256SUMS" | cut -c1-12)" = 86da41d3ef68 ] || { echo "run.sh: kit id is not 86da41d3ef68" >&2; exit 1; }
echo "== class $CLS, donor $SRC at $REF"
# the image-free files the relocated ones Require: no numeral of the image range (>= 0x10000, hex or decimal)
for f in ${COPY:-}; do
  n=$(git -C "$HUB" show "$REF:proofs/$SRC/lib/$f" | grep -oE '\b(0x[0-9a-fA-F]+|[0-9]+)\b' |
      while read -r t; do case $t in 0x*) v=$((t));; *) v=$t;; esac; [ "$v" -ge 65536 ] && echo "$t"; done | wc -l)
  if [ "$n" -eq 0 ]; then echo "copy $f: image-free (0 numerals >= 0x10000)"; else echo "copy $f: $n numerals >= 0x10000" >&2; rc=1; fi
done
for I in ${IMAGES:-A B}; do
  b=asan; [ $I = B ] && b=asan-ubsan
  eval "tables=\$TABLES_$I files=\$FILES_$I"
  dp=$(find1 "$DD" "$u" $b); tp=$(find1 "$TD" fuzz_transport $b)
  du="$DD/unstripped/$u/$u.$b"; tu="$TD/unstripped/fuzz_transport/fuzz_transport.$b"
  [ "$(sha256sum < "$dp" | cut -c1-64)" = "$(pin "$dh" $b)" ] || { echo "run.sh: $dp is not REF's $b pin" >&2; exit 1; }
  [ "$(sha256sum < "$tp" | cut -c1-64)" = "$(pin "$th" $b)" ] || { echo "run.sh: $tp is not WT's $b pin" >&2; exit 1; }
  echo "== image $I ($b): donor pin $(pin "$dh" $b | cut -c1-12), target pin $(pin "$th" $b | cut -c1-12)"
  # each pinned image and its unstripped twin: same PT_LOAD layout, no differing byte outside the ELF header and build-id
  python3 "$kit/drvcmp.py" twins "$dp" "$du" "$tp" "$tu" > "$OUT/twins-$I.txt" 2>&1 || { echo "twins $I: drvcmp failed" >&2; rc=1; }
  if grep -q 'PT_LOAD layout equal: False\|): \[[^]]' "$OUT/twins-$I.txt"; then echo "twins $I: NOT proved (see twins-$I.txt)" >&2; rc=1
  else echo "twins $I: proved ($(grep -c 'layout equal: True' "$OUT/twins-$I.txt") pairs)"; fi
  ccmp() { # donor pinned, donor twin, target pinned, target twin, out dir
    python3 "$here/clscmp.py" --hub "$HUB" --ref "$REF" --src "$SRC" --cls "$CLS" --img $I --tables $tables \
      --reloc $files --model "$CLSDIR/model.txt" --donor "$1" "$2" --target "$3" "$4" --out "$5"
  }
  ccmp "$dp" "$du" "$tp" "$tu" "$OUT" || rc=1
  # control 1: the donor against itself passes and moves no value
  ccmp "$dp" "$du" "$dp" "$du" "$OUT/ctl-self" > "$OUT/ctl-self-$I.log" || { echo "control self $I: FAILED to pass" >&2; rc=1; }
  if grep -q '^PASS' "$OUT/ctl-self-$I.log" && grep -q 'resolve lines: 0 move a value' "$OUT/ctl-self-$I.log"; then
    echo "control self $I: PASS, 0 values moved"
  else echo "control self $I: NOT clean (see ctl-self-$I.log)" >&2; rc=1; fi
  # control 2: one planted word (an or for the first and of __asan_stack_malloc_<CLS>) must be caught
  python3 - "$tp" "$tu" "$OUT/plant-$I" "__asan_stack_malloc_$CLS" > "$OUT/plant-$I.txt" <<'EOF'
import sys, os
from elftools.elf.elffile import ELFFile
src, twin, out, body = sys.argv[1:]
os.makedirs(out, exist_ok=True)
e = ELFFile(open(twin, 'rb'))
s = [x for x in e.get_section_by_name('.symtab').iter_symbols() if x.name == body][0]
for path in (src, twin):
    f = ELFFile(open(path, 'rb'))
    off = next(g['p_offset'] + s['st_value'] - g['p_vaddr'] for g in f.iter_segments()
               if g['p_type'] == 'PT_LOAD' and g['p_vaddr'] <= s['st_value'] < g['p_vaddr'] + g['p_filesz'])
    data = bytearray(open(path, 'rb').read())
    for k in range(0, s['st_size'], 4):
        w = int.from_bytes(data[off + k:off + k + 4], 'little')
        if w & 0xfe00707f == 0x7033:  # and -> or
            data[off + k:off + k + 4] = (w & ~0x7000 | 0x6000).to_bytes(4, 'little')
            print('%s: planted or for the and at %s + 0x%x (word 0x%08x -> 0x%08x)' % (os.path.basename(path), body, k, w,
                  w & ~0x7000 | 0x6000))
            break
    open(os.path.join(out, os.path.basename(path) + ('.twin' if path == twin else '')), 'wb').write(data)
EOF
  if ccmp "$dp" "$du" "$OUT/plant-$I/$(basename "$tp")" "$OUT/plant-$I/$(basename "$tu").twin" "$OUT/ctl-plant" \
       > "$OUT/ctl-plant-$I.log"
  then echo "control plant $I: NOT caught" >&2; rc=1
  else echo "control plant $I: caught ($(grep -c '^FAIL' "$OUT/ctl-plant-$I.log") FAIL lines; $(head -n 1 "$OUT/plant-$I.txt"))"; fi
  rm -rf "$OUT/plant-$I"
  # the relocation (dry unless --write); the core's record name is the unit's start-up layer's (RECORD_A / RECORD_B)
  rec=$( [ $I = A ] && echo "${RECORD_A:-}" || echo "${RECORD_B:-}" )
  if [ "$MODE" = --write ] && [ -z "$rec" ]; then echo "run.sh: --write needs RECORD_$I (the core's record name)" >&2; exit 1; fi
  set -- --src "$SRC" --ref "$REF" --unit libdiginet/fuzz_transport --build $b --wt "$WT" \
    --pinned-elf "$tp" --unit-elf "$tu" --resolve "$OUT/resolve-$I.txt" --report "$OUT/report"
  [ "$MODE" = --write ] || set -- "$@" --dry
  (cd "$(dirname "$AL")" && python3 "$(basename "$AL")" "$@" $files) > "$OUT/alreloc-$I.out" 2>&1 ||
    { echo "alreloc $I: rc != 0 (see alreloc-$I.out)"; rc=1; }
  tail -n 2 "$OUT/alreloc-$I.out"
  # every report row checked against the two ELFs, independently of alreloc's rules (checkrep.py)
  python3 "$here/checkrep.py" "$OUT/report/libdiginet/fuzz_transport" $I "$du" "$tu" > "$OUT/checkrep-$I.txt" ||
    { echo "checkrep $I: WRONG rows (see checkrep-$I.txt)"; rc=1; }
  grep 'MOVED\|PASS\|WRONG' "$OUT/checkrep-$I.txt" || true
  [ "$MODE" = --write ] || continue
  for f in $files; do
    git -C "$HUB" show "$REF:proofs/$SRC/lib/$f" > "$OUT/donor.v"
    python3 - "$OUT/donor.v" "$WT/proofs/libdiginet/fuzz_transport/lib/$f" "$rec" $b "$SYMREC" "$CLS" <<'EOF'
import re, sys
donor, path, rec, build, old, cls = sys.argv[1:]
d = open(donor).read().split('\n'); t = open(path).read().split('\n')
hd = next(k for k, l in enumerate(d) if l.startswith(('From ', 'Require ')))
ht = next(k for k, l in enumerate(t) if l.startswith(('From ', 'Require ')))
body = [re.sub(r'\b%s\b' % old, rec, l) for l in t[ht:]]
note = ('(* Modified by Theorem Labs, 2026-10: relocated to libdiginet/fuzz_transport\'s %s image by this unit\'s '
        'provenance/evidence/class%s/run.sh (alreloc with the resolve lines of clscmp.py); %s becomes %s. *)'
        % (build, cls, old, rec))
open(path, 'w').write('\n'.join(d[:hd] + [note] + body))
print('%s: header %d lines restored from the donor, %d %s renamed, notice added'
      % (path.split('/lib/')[1], hd, sum(len(re.findall(r'\b%s\b' % old, l)) for l in t[ht:]), old))
EOF
  done
done
# the image-free files: copied with the donor's module paths made this unit's, and one notice line
if [ "$MODE" = --write ]; then
  for f in ${COPY:-}; do
    git -C "$HUB" show "$REF:proofs/$SRC/lib/$f" > "$OUT/donor.v"
    mkdir -p "$(dirname "$WT/proofs/libdiginet/fuzz_transport/lib/$f")"
    python3 - "$OUT/donor.v" "$WT/proofs/libdiginet/fuzz_transport/lib/$f" "$SRC" "$CLS" <<'EOF'
import re, sys
donor, path, src, cls = sys.argv[1:]
d = open(donor).read().split('\n')
hd = next(k for k, l in enumerate(d) if l.startswith(('From ', 'Require ')))
old = 'OssFuzzTheorems.Proofs.%s.lib' % src.replace('-', '_').replace('/', '.')
body = [l.replace(old, 'OssFuzzTheorems.Proofs.libdiginet.fuzz_transport.lib') for l in d[hd:]]
note = ('(* Modified by Theorem Labs, 2026-10: copied from %s for libdiginet/fuzz_transport by this unit\'s '
        'provenance/evidence/class%s/run.sh (image-free: module paths only). *)' % (src, cls))
open(path, 'w').write('\n'.join(d[:hd] + [note] + body))
print('%s: copied, %d module paths renamed' % (path.split('/lib/')[1], sum(l.count(old) for l in d[hd:])))
EOF
  done
fi
exit $rc
