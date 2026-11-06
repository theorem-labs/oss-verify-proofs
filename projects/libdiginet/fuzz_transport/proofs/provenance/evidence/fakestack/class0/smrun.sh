#!/bin/sh
# One command for a fake-stack class relocation onto fuzz_transport, on whatever images
# projects/libdiginet/fuzz_transport/harness.yaml pins: a re-pin is a re-run. It is class5/run.sh with the donor, the
# class, the code tables and the relocated files read from a configuration file (class0/class0.conf, class4/class4.conf).
#   smrun.sh WT HUB DONOR_DIR TARGET_DIR ALRELOC CONF [--write]
#     WT          this unit's worktree (its harness.yaml names the pins; relocated files are written there)
#     HUB         the git hub holding REF
#     DONOR_DIR   a directory with bin/<H>/<H>.<build> (or result/bin/...) and unstripped/<H>/<H>.<build> of the donor
#     TARGET_DIR  the same for fuzz_transport
#     ALRELOC     alreloc.py of record (a5c53bb2bed4), run from its own directory (it reads align/keep-numerals.txt)
#     CONF        a sh file setting CLS, SRC (the donor P/H), REF, IMAGES (A and / or B), TABLES_<I> (FILE[:VAR] of the
#                 code tables), FILES_<I> (the relocated files), KEEPALL_<I>, MODEL (a file beside CONF, or empty) and
#                 DREC (the donor's symbol-record name, renamed to RECORD_<I> by --write)
#     --write     write the relocated files (default: alreloc --dry, which writes nothing); RECORD_A / RECORD_B name the
#                 core's symbol record of each image, required with --write
# For each image (A = asan, B = asan-ubsan): pins checked against harness.yaml (the donor's at REF); twins proved;
# smcmp.py pairs and compares every walked range and writes the resolve lines; its controls (the donor against itself must
# PASS and move nothing; one planted word in a copy of the target's __asan_stack_malloc_<CLS> must FAIL); then alreloc
# with those resolve lines, and checkrep.py checks every row of alreloc's report against the two ELFs (it refuses a `gap`
# row and lists every value moved by its offset inside a symbol for a reader to confirm). With --write, a last step per
# written file puts back the donor's leading comment block byte for byte (inherited header and notice lines are not
# relocated), renames DREC to the record outside it, and adds one notice line.
# Outputs under OUT: the environment's OUT if set (e.g. a scratch directory for a --write test), else CONF's OUT, else
# out; a relative OUT is taken from the directory of CONF.
set -eu
WT=$1 HUB=$2 DD=$3 TD=$4 AL=$5 CONF=$6 MODE=${7:---dry}
here=$(cd "$(dirname "$0")" && pwd)
cdir=$(cd "$(dirname "$CONF")" && pwd)
envout=${OUT:-}
CLS= SRC= REF= IMAGES= TABLES_A= TABLES_B= FILES_A= FILES_B= KEEPALL_A= KEEPALL_B= MODEL= DREC= OUT=
. "$cdir/$(basename "$CONF")"
OUT=${envout:-${OUT:-out}}
case $OUT in /*) ;; *) OUT=$cdir/$OUT ;; esac
mkdir -p "$OUT"
H=${SRC#*/}
pin() { # harness.yaml text, build -> sha256
  printf '%s\n' "$1" | awk -v b="  $2:" '$0 == b {f = 1; next} f && /sha256:/ {print $2; exit}'
}
find1() { # dir, unit, build -> pinned file under bin/ or result/bin/
  for d in "$1/result/bin/$2" "$1/bin/$2"; do [ -f "$d/$2.$3" ] && { echo "$d/$2.$3"; return; }; done
  echo "smrun.sh: no $2.$3 under $1" >&2; exit 1
}
# HARNESS (optional): a harness.yaml naming the target pins to check against instead of WT's
th=$(cat "${HARNESS:-$WT/projects/libdiginet/fuzz_transport/harness.yaml}")
dh=$(git -C "$HUB" show "$REF:projects/$SRC/harness.yaml")
model=; [ -n "$MODEL" ] && model="--model $cdir/$MODEL"
rc=0
kit=$(cd "${KIT:?KIT: the cmpkit 86da41d3ef68 directory (inputs/cmpkit-86da41d3ef68/ of the internal record)}" && pwd); KIT=$kit; export KIT
(cd "$kit" && sha256sum -c --quiet SHA256SUMS) || { echo "smrun.sh: the comparison kit copy does not match its SHA256SUMS" >&2; exit 1; }
[ "$(sha256sum < "$kit/SHA256SUMS" | cut -c1-12)" = 86da41d3ef68 ] || { echo "smrun.sh: kit id is not 86da41d3ef68" >&2; exit 1; }
for I in $IMAGES; do
  b=asan; [ $I = B ] && b=asan-ubsan
  eval "tables=\$TABLES_$I files=\$FILES_$I keepall=\$KEEPALL_$I"
  dp=$(find1 "$DD" $H $b); tp=$(find1 "$TD" fuzz_transport $b)
  du="$DD/unstripped/$H/$H.$b"; tu="$TD/unstripped/fuzz_transport/fuzz_transport.$b"
  [ "$(sha256sum < "$dp" | cut -c1-64)" = "$(pin "$dh" $b)" ] || { echo "smrun.sh: $dp is not REF's $b pin" >&2; exit 1; }
  [ "$(sha256sum < "$tp" | cut -c1-64)" = "$(pin "$th" $b)" ] || { echo "smrun.sh: $tp is not WT's $b pin" >&2; exit 1; }
  echo "== class $CLS image $I ($b): donor $SRC at $REF pin $(pin "$dh" $b | cut -c1-12), target pin $(pin "$th" $b | cut -c1-12)"
  # each pinned image and its unstripped twin: same PT_LOAD layout, no differing byte outside the ELF header and build-id
  python3 "$kit/drvcmp.py" twins "$dp" "$du" "$tp" "$tu" > "$OUT/twins-$I.txt" 2>&1 || { echo "twins $I: drvcmp failed" >&2; rc=1; }
  if grep -q 'PT_LOAD layout equal: False\|): \[[^]]' "$OUT/twins-$I.txt"; then echo "twins $I: NOT proved (see twins-$I.txt)" >&2; rc=1
  else echo "twins $I: proved ($(grep -c 'layout equal: True' "$OUT/twins-$I.txt") pairs)"; fi
  smc() { # target pinned, target twin, out dir
    python3 "$here/smcmp.py" --hub "$HUB" --ref $REF --src $SRC --img $I --cls $CLS --donor "$dp" "$du" --target "$1" "$2" \
      --out "$3" --tables $tables --reloc $files --keep-all $keepall $model
  }
  smc "$tp" "$tu" "$OUT" || rc=1
  # control 1: the donor against itself passes and moves no value
  smc "$dp" "$du" "$OUT/ctl-self" > "$OUT/ctl-self-$I.log" || { echo "control self $I: FAILED to pass" >&2; rc=1; }
  if grep -q '^PASS' "$OUT/ctl-self-$I.log" && grep -q 'resolve lines: 0 move a value' "$OUT/ctl-self-$I.log"; then
    echo "control self $I: PASS, 0 values moved"
  else echo "control self $I: NOT clean (see ctl-self-$I.log)" >&2; rc=1; fi
  # control 2: one planted word (an or for the first and of __asan_stack_malloc_<CLS>) must be caught; the two planted
  # copies are written beside the target images (PLANT_DIR, default TARGET_DIR/plant-<I>), never in the worktree
  pd=${PLANT_DIR:-$TD}/plant-$I
  python3 - "$tp" "$tu" "$pd" "__asan_stack_malloc_$CLS" <<'EOF'
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
            print('planted: %s + 0x%x: 0x%08x -> 0x%08x' % (body, k, w, w & ~0x7000 | 0x6000), file=sys.stderr)
            break
    else:
        sys.exit('no `and` in %s' % body)
    open(os.path.join(out, os.path.basename(path) + ('.twin' if path == twin else '')), 'wb').write(data)
EOF
  if smc "$pd/$(basename "$tp")" "$pd/$(basename "$tu").twin" "$OUT/ctl-plant" > "$OUT/ctl-plant-$I.log"
  then echo "control plant $I: NOT caught" >&2; rc=1
  else echo "control plant $I: caught ($(grep -c '^FAIL' "$OUT/ctl-plant-$I.log") FAIL lines)"; fi
  rm -f "$pd/$(basename "$tp")" "$pd/$(basename "$tu").twin" && rmdir "$pd"
  # the relocation (dry unless --write); the core's record name is the unit's start-up layer's (RECORD_A / RECORD_B)
  rec=$( [ $I = A ] && echo "${RECORD_A:-}" || echo "${RECORD_B:-}" )
  if [ "$MODE" = --write ] && [ -z "$rec" ]; then echo "smrun.sh: --write needs RECORD_$I (the core's record name)" >&2; exit 1; fi
  set -- --src $SRC --ref $REF --unit libdiginet/fuzz_transport --build $b --wt "$WT" \
    --pinned-elf "$tp" --unit-elf "$tu" --resolve "$OUT/resolve-$I.txt" --report "$OUT/report"
  [ "$MODE" = --write ] || set -- "$@" --dry
  (cd "$(dirname "$AL")" && python3 "$(basename "$AL")" "$@" $files) > "$OUT/alreloc-$I.out" 2>&1 ||
    { echo "alreloc $I: rc != 0 (see alreloc-$I.out)"; rc=1; }
  grep '^  [A-Z]' "$OUT/alreloc-$I.out" || true
  tail -n 2 "$OUT/alreloc-$I.out"
  # every report row checked against the two ELFs, independently of alreloc's rules (checkrep.py)
  python3 "$here/checkrep.py" "$OUT/report/libdiginet/fuzz_transport" $I "$du" "$tu" > "$OUT/checkrep-$I.txt" ||
    { echo "checkrep $I: WRONG rows (see checkrep-$I.txt)"; rc=1; }
  grep 'MOVED\|PASS\|WRONG' "$OUT/checkrep-$I.txt" || true
  [ "$MODE" = --write ] || continue
  for f in $files; do
    git -C "$HUB" show "$REF:proofs/$SRC/lib/$f" > "$OUT/donor.v"
    python3 - "$OUT/donor.v" "$WT/proofs/libdiginet/fuzz_transport/lib/$f" "$DREC" "$rec" $b "$CLS" <<'EOF'
import re, sys
donor, path, drec, rec, build, cls = sys.argv[1:]
d = open(donor).read().split('\n'); t = open(path).read().split('\n')
hd = next(k for k, l in enumerate(d) if l.startswith(('From ', 'Require ')))
ht = next(k for k, l in enumerate(t) if l.startswith(('From ', 'Require ')))
body = [re.sub(r'\b%s\b' % drec, rec, l) for l in t[ht:]]
note = ('(* Modified by Theorem Labs, 2026-10: relocated to libdiginet/fuzz_transport\'s %s image by this unit\'s '
        'provenance/evidence/class%s run (alreloc with the resolve lines of smcmp.py); %s becomes %s. *)'
        % (build, cls, drec, rec))
open(path, 'w').write('\n'.join(d[:hd] + [note] + body))
print('%s: header %d lines restored from the donor, %d %s renamed, notice added'
      % (path.split('/lib/')[1], hd, sum(len(re.findall(r'\b%s\b' % drec, l)) for l in t[ht:]), drec))
EOF
  done
done
exit $rc
