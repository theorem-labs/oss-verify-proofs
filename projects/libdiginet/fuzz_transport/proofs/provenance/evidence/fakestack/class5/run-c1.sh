#!/bin/sh
# Relocate plugin-hostd/fuzz_command's lib/<I>/Rt/RtSM1T.v (origin/ossv/recipes 781f46bc05cd) to fuzz_transport's
# image I by the class5 directory's method (class5cmp.py -> class1cmp.py for RtSM1T's fs_ranges; controls self +
# planted word in __asan_stack_malloc_1; alreloc a5c53bb2bed4 with the resolve lines; checkrep on every row; header
# restored from the donor, CmdBSyms -> RECORD, one notice line). One image: IMAGES (default A, the run of record of
# image A) is A (asan) or B (asan-ubsan).
#   run-c1.sh WT HUB DONOR_DIR TARGET_DIR ALRELOC [--write]      env: KIT (cmpkit 86da41d3ef68), OUT, RECORD, IMAGES
set -eu
WT=$1 HUB=$2 DD=$3 TD=$4 AL=$5 MODE=${6:---dry}
REF=781f46bc05cd I=${IMAGES:-A}
case $I in A) b=asan ;; B) b=asan-ubsan ;; *) echo "run-c1.sh: IMAGES is one image, A or B" >&2; exit 1 ;; esac
here=$(cd "$(dirname "$0")" && pwd)
: "${OUT:?}"
mkdir -p "$OUT"
kit=$(cd "${KIT:?KIT: the cmpkit 86da41d3ef68 directory (inputs/cmpkit-86da41d3ef68/ of the internal record)}" && pwd); KIT=$kit; export KIT
(cd "$kit" && sha256sum -c --quiet SHA256SUMS) || { echo "kit copy does not match its SHA256SUMS" >&2; exit 1; }
[ "$(sha256sum < "$kit/SHA256SUMS" | cut -c1-12)" = 86da41d3ef68 ] || { echo "kit id is not 86da41d3ef68" >&2; exit 1; }
rc=0
dp="$DD/bin/fuzz_command/fuzz_command.$b"; du="$DD/unstripped/fuzz_command/fuzz_command.$b"
tp="$TD/bin/fuzz_transport/fuzz_transport.$b"; tu="$TD/unstripped/fuzz_transport/fuzz_transport.$b"
python3 "$here/class1cmp.py" --hub "$HUB" --ref $REF --img $I --donor "$dp" "$du" --target "$tp" "$tu" --out "$OUT" || rc=1
python3 "$here/class1cmp.py" --hub "$HUB" --ref $REF --img $I --donor "$dp" "$du" --target "$dp" "$du" \
  --out "$OUT/ctl-self" > "$OUT/ctl-self-$I.log" || { echo "control self: FAILED to pass" >&2; rc=1; }
if grep -q '^PASS' "$OUT/ctl-self-$I.log" && grep -q 'resolve lines: 0 move a value' "$OUT/ctl-self-$I.log"; then
  echo "control self $I: PASS, 0 values moved"; else echo "control self $I: NOT clean" >&2; rc=1; fi
python3 - "$tp" "$tu" "$OUT/plant-$I" <<'EOF'
import sys, os
from elftools.elf.elffile import ELFFile
src, twin, out = sys.argv[1:]
os.makedirs(out, exist_ok=True)
e = ELFFile(open(twin, 'rb'))
s = [x for x in e.get_section_by_name('.symtab').iter_symbols() if x.name == '__asan_stack_malloc_1'][0]
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
if python3 "$here/class1cmp.py" --hub "$HUB" --ref $REF --img $I --donor "$dp" "$du" \
     --target "$OUT/plant-$I/$(basename "$tp")" "$OUT/plant-$I/$(basename "$tu").twin" --out "$OUT/ctl-plant" \
     > "$OUT/ctl-plant-$I.log"; then echo "control plant $I: NOT caught" >&2; rc=1
else echo "control plant $I: caught ($(grep -c '^FAIL' "$OUT/ctl-plant-$I.log") FAIL lines)"; fi
rm -rf "$OUT/plant-$I"
files="$I/Rt/RtSM1T.v"
set -- --src plugin-hostd/fuzz_command --ref $REF --unit libdiginet/fuzz_transport --build $b --wt "$WT" \
  --pinned-elf "$tp" --unit-elf "$tu" --resolve "$OUT/resolve-$I.txt" --report "$OUT/report"
[ "$MODE" = --write ] || set -- "$@" --dry
(cd "$(dirname "$AL")" && python3 "$(basename "$AL")" "$@" $files) > "$OUT/alreloc-$I.out" 2>&1 ||
  { echo "alreloc $I: rc != 0 (see alreloc-$I.out)"; rc=1; }
tail -n 3 "$OUT/alreloc-$I.out"
python3 "$here/checkrep.py" "$OUT/report/libdiginet/fuzz_transport" $I "$du" "$tu" > "$OUT/checkrep-$I.txt" ||
  { echo "checkrep $I: WRONG rows (see checkrep-$I.txt)"; rc=1; }
grep 'MOVED\|PASS\|WRONG' "$OUT/checkrep-$I.txt" || true
[ "$MODE" = --write ] || exit $rc
: "${RECORD:?}"
for f in $files; do
  git -C "$HUB" show "$REF:proofs/plugin-hostd/fuzz_command/lib/$f" > "$OUT/donor.v"
  python3 - "$OUT/donor.v" "$WT/proofs/libdiginet/fuzz_transport/lib/$f" "$RECORD" $b "$OUT/absent-$I.txt" <<'EOF'
import re, sys
donor, path, rec, build, absf = sys.argv[1:]
d = open(donor).read().split('\n'); t = open(path).read().split('\n')
hd = next(k for k, l in enumerate(d) if l.startswith(('From ', 'Require ')))
ht = next(k for k, l in enumerate(t) if l.startswith(('From ', 'Require ')))
body = '\n'.join(re.sub(r'\bCmdBSyms\b', rec, l) for l in t[ht:])
absent = [l.split('\t') for l in open(absf).read().split('\n') if l]
m = re.search(r'Definition fs_ranges : list \(Z \* nat\) :=.*?\]\.', body, re.S)
fr = m.group(0)
for _, s, n, name in absent:
    fr, k = re.subn(r'\(%s, %s%%nat\);\s*' % (s, n), '', fr)
    assert k == 1, (s, n)
body = body[:m.start()] + fr + body[m.end():]
for _, s, n, name in absent:
    assert not re.search(r'\b%s\b' % s, body), s
names = ', '.join('%s (%s)' % (name, s) for _, s, n, name in absent)
note = ('(* Modified by Theorem Labs, 2026-10: relocated to libdiginet/fuzz_transport\'s %s image by the class-5 '
        'method (alreloc with resolve lines from the paired instructions of RtSM1T.v\'s code ranges); CmdBSyms becomes %s; '
        'fs_ranges drops %s, which this image does not link. *)' % (build, rec, names))
open(path, 'w').write('\n'.join(d[:hd] + [note]) + '\n' + body)
print('%s: header %d lines restored from the donor, %d CmdBSyms renamed, notice added; fs_ranges drops %s'
      % (path.split('/lib/')[1], hd, sum(len(re.findall(r'\bCmdBSyms\b', l)) for l in t[ht:]), names))
EOF
done
exit $rc
