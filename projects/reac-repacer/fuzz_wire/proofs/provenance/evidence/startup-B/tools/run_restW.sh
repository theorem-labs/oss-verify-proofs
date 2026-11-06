#!/bin/bash
# run_restW.sh -- reac-repacer/fuzz_wire image B (asan-ubsan): YB12, YD2i + YD2j, YD1k, YE3i (lib/B), the twin of the
# fuzz_uci image-B run's tools/run_restB.sh, after tools/af0mB/run_af0mB.sh (work/raw/YF0m.v). rule 24: proves no function
# (kind: start-up facts). Tools: the start-up set of record, the start-up tool set at commit dbb5a97ad14 ($FT:
# atable 42e18a7eef50, gen_ad2 979c52cd71c6, gen_ad1k 43a0cf0abc67) and ae3i 3cf49addef7e (not in the set; run through
# frozen-run.sh with the one-line bundle bundle/ae3i-3cf49addef7e.tsv). Every generator writes the donor's module paths;
# tools/nsW.py rewrites them to the lib/B layout afterwards (and gates the Require set against fuzz_grant B's twin).
# fuzz_wire registers 0 ASan globals: each generator's n = 0 line is kept in its log and echoed here.
set -uo pipefail
. "$W/env.sh"   # W is exported by env.sh; this brings scrub and every path variable
FA="bash $S/frozen-run.sh $W/bundle/ae3i-3cf49addef7e.tsv"
C=$DLIBC; R=$WK/raw; G=$WK/gen; L=$W/logs/rest; CT=$WK/ctl
CORE=$LT/pcB/stage-out
mkdir -p $L $CT
FAILED=
rc() { echo "$1 rc=$2"; [ "$2" = 0 ] || FAILED="$FAILED [$1]"; }
cd $LT

echo "=== YB12: atable CONTROL on cgif B (cgif's YB1w names): the diff must be exactly the two derived fields ==="
$FR3 atable.py $CB $C/YB1w.v --side B --prefix $NS_D --donor-image $CB --donor-atable $C/YB12.v --cells $C/YF0m.v \
  > $CT/YB12.cgif.v 2> >(scrub > $CT/YB12.cgif.log); rc "atable control cgif B" $?
diff <(grep -v '^(\*' $C/YB12.v) $CT/YB12.cgif.v > $CT/YB12.cgif.diff
python3 - $CT/YB12.cgif.diff <<'EOF'; rc "control diff = stops_more + 13th self-loop, TFIB_TEXT_N 111037 -> ceil(.text/4)" $?
import sys
d = [l for l in open(sys.argv[1]).read().splitlines() if l[:1] in '<>']
print('control diff lines:'); print('\n'.join('  ' + x for x in d))
ok = len(d) == 4 and d[0].startswith('< stops_more') and d[1].startswith('> stops_more') and d[1].count(';') == d[0].count(';') + 1 \
     and d[2] == '< Definition TFIB_TEXT_N : nat := 111037.' and d[3].startswith('> Definition TFIB_TEXT_N : nat := ')
sys.exit(0 if ok else 1)
EOF
echo "=== YB12 on fuzz_wire B (--cells = work/raw/YF0m.v) ==="
$FR3 atable.py $UB $UBs --side B --prefix $NS_D --donor-image $CB --donor-atable $C/YB12.v --cells $R/YF0m.v \
  --header $W/tools/hdr.YB12.txt > $R/YB12.v 2> >(scrub > $L/atable.wireB.log); rc "atable fuzz_wire B" $?
sleep 1; grep -v '^frozen-run' $L/atable.wireB.log
cmp $R/YB12.v $W/tools/af0mB/YB12.prov.v; rc "same text as the provisional YB12 af0m's --ab12 read" $?
python3 - $R/YB12.v <<'EOF'; rc "TFIB_TEXT_LO 0x2ff5c / TFIB_TEXT_N 105697 (.text 0x2ff5c + 0x67384, ceil / 4)" $?
import re, sys
t = open(sys.argv[1]).read()
lo = re.search(r'TFIB_TEXT_LO : Z := (0x[0-9a-f]+)\.', t).group(1); n = re.search(r'TFIB_TEXT_N : nat := (\d+)\.', t).group(1)
print('TFIB_TEXT_LO', lo, 'TFIB_TEXT_N', n); sys.exit(0 if (int(lo, 16), int(n)) == (0x2ff5c, (0x67384 + 3) // 4) else 1)
EOF
# planted control: one changed field of the emitted record must be caught by the regeneration compare
sed 's/x_memset := 0x91fac/x_memset := 0x91fb0/' $R/YB12.v > $CT/YB12.planted.v
$FR3 atable.py $UB $UBs --side B --prefix $NS_D --donor-image $CB --donor-atable $C/YB12.v --cells $R/YF0m.v \
  --header $W/tools/hdr.YB12.txt > $CT/YB12.regen.v 2>/dev/null
diff $CT/YB12.regen.v $CT/YB12.planted.v > $CT/YB12.planted.diff; n=$(grep -c '^[<>]' $CT/YB12.planted.diff)
cmp -s $CT/YB12.regen.v $R/YB12.v && [ "$n" = 2 ]; rc "atable planted control (regen == file; planted x_memset +4 caught: $n diff lines)" $?

echo "=== YD2i / YD2j: gen_ad2 CONTROL on cgif B (byte-equal to cgif's released YD2i / YD2j) ==="
$FR3 gen_ad2.py --side B --states $C/YB01.v --atable $C/YB12.v --tsegs $C/YB1h.v --owned $C/YF0m.v --image $CB \
  --tmpl-ad2i $C/YD2i.v --tmpl-ad2j $C/YD2j.v --tmpl-image $CB --out-ad2i $CT/YD2i.cgif.v --out-ad2j $CT/YD2j.cgif.v \
  --report $CT/ad2.cgif.report --gate-table $CT/ad2.cgif.gates.md 2>&1 | scrub > $CT/ad2.cgif.log; rc "gen_ad2 control cgif B" ${PIPESTATUS[0]}
cmp $CT/YD2i.cgif.v $C/YD2i.v; rc "control YD2i BYTE-EQUAL" $?
cmp $CT/YD2j.cgif.v $C/YD2j.v; rc "control YD2j BYTE-EQUAL" $?
echo "=== YD2i / YD2j on fuzz_wire B ==="
MOD="generated for reac-repacer/fuzz_wire image B by gen_ad2.py (sha256 979c52cd71c6, the start-up tool set at commit dbb5a97ad14) from fuzz_wire.asan-ubsan, its atable (lib/B/YB12.v), its TSEGS window (lib/B/YB1h.v), its owned statics (lib/B/YF0m.v) and the 50 hand-off states of lib/B/YB01.v; the image registers 0 ASan globals (no asan_globals section); proofs/cgif/cgif_file_fuzzer/lib/YD2i.v and YD2j.v at commit 25e3d17bdb50 give the text only"
$FR3 gen_ad2.py --side B --states $R/YB01.v --atable $R/YB12.v --tsegs $R/YB1h.v --owned $R/YF0m.v --image $UB --twin $UBs \
  --tmpl-ad2i $C/YD2i.v --tmpl-ad2j $C/YD2j.v --tmpl-image $CB --world-core $CORE/Reusable/YA0n.v --argh0 $CORE/B/YA02.v \
  --out-ad2i $R/YD2i.v --out-ad2j $R/YD2j.v --modified "$MOD" --report $L/ad2.wireB.report --gate-table $L/ad2.wireB.gates.md \
  2>&1 | scrub > $L/gen_ad2.wireB.log; rc "gen_ad2 fuzz_wire B (PRECHECK, GATE, TWIN, keyset)" ${PIPESTATUS[0]}
grep -v '^frozen-run' $L/gen_ad2.wireB.log
python3 - $R/YD2j.v <<'EOF'; rc "canary chunk at the .got word 0x99500 = 627968 and CVal 8 (SOff 41 0) present" $?
import re, sys
t = open(sys.argv[1]).read()
print('kept .got canary chunk `mkChunk 627968 (CImg 8)`:', len(re.findall(r'mkChunk 627968 \(CImg 8\)', t)),
      '; canary value chunks CVal 8 (SOff 41 0):', len(re.findall(r'CVal 8 \(SOff 41 0\)', t)))
sys.exit(0 if re.search(r'mkChunk 627968 \(CImg 8\)', t) and re.search(r'CVal 8 \(SOff 41 0\)', t) else 1)
EOF

echo "=== YD1k: gen_ad1k CONTROL on cgif B (byte-equal to cgif's released YD1k) ==="
$FR3 gen_ad1k.py --tmpl-ad1k $C/YD1k.v --tmpl-ad2j $C/YD2j.v --tmpl-owned $C/YF0m.v --tmpl-image $CB \
  --ad2j $C/YD2j.v --owned $C/YF0m.v --image $CB --out $CT/YD1k.cgif.v --sites $CT/ad1k.cgif.sites.md --label 'YD1k.v' \
  2>&1 | scrub > $CT/ad1k.cgif.log; rc "gen_ad1k control cgif B" ${PIPESTATUS[0]}
cmp $CT/YD1k.cgif.v $C/YD1k.v; rc "control YD1k BYTE-EQUAL" $?
echo "=== YD1k on fuzz_wire B ==="
MOD="generated for reac-repacer/fuzz_wire image B (asan-ubsan) by gen_ad1k.py (sha256 43a0cf0abc67, the start-up tool set at commit dbb5a97ad14) from fuzz_wire.asan-ubsan, the regions of its generated lib/B/YD2j.v and the owned statics of its generated lib/B/YF0m.v; the image registers 0 ASan globals, so the rodata hull bound is the end of YF0m's first Tfib_zero_shadow range (the image top) floored to 64 bytes; proofs/cgif/cgif_file_fuzzer/lib/YD1k.v at commit 25e3d17bdb50 gives the text only"
$FR3 gen_ad1k.py --tmpl-ad1k $C/YD1k.v --tmpl-ad2j $C/YD2j.v --tmpl-owned $C/YF0m.v --tmpl-image $CB \
  --ad2j $R/YD2j.v --owned $R/YF0m.v --image $UB --twin $UBs --modified "$MOD" \
  --out $R/YD1k.v --sites $L/ad1k.wireB.sites.md --label 'YD1k.v' 2>&1 | scrub > $L/gen_ad1k.wireB.log; rc "gen_ad1k fuzz_wire B" ${PIPESTATUS[0]}
grep -v '^frozen-run' $L/gen_ad1k.wireB.log
python3 - $UB $R/YD1k.v $L/gen_ad1k.wireB.log <<'EOF'; rc "hull bound = the MEASURED image top of the pin (page-up of the last PT_LOAD end)" $?
import re, sys
from elftools.elf.elffile import ELFFile
loads = [s for s in ELFFile(open(sys.argv[1], 'rb')).iter_segments() if s['p_type'] == 'PT_LOAD']
top = (max(s['p_vaddr'] + s['p_memsz'] for s in loads) + 0xfff) & ~0xfff
m = re.search(r'hull bound (0x[0-9a-f]+)', open(sys.argv[3]).read())
t = open(sys.argv[2]).read()
lem = re.findall(r'Lemma (rodata_hull_zero|rodata_shadow_facts) :[^\n]*?p \+ n <= ([^ ]+) ->', t)
print('measured image top (pin, page-up of the last PT_LOAD end): %#x; gen_ad1k hull bound: %s; YD1k lemmas state: %s' % (top, m.group(1) if m else None, lem))
sys.exit(0 if m and int(m.group(1), 16) == top and lem and all(b in (hex(top), 'YImgTop.IMG_TOP') for _, b in lem) else 1)
EOF

echo "=== YE3i: ae3i CONTROL on cgif B (--img-ro-hi 0x2f1ac; cgif's 15 chunks byte for byte) ==="
$FA ae3i.py --tmpl $C/YE3i.v --owned $C/YF0m.v --image $CB --img-ro-hi 0x2f1ac --out $CT/YE3i.cgif.v 2>&1 | scrub > $CT/ae3i.cgif.log
rc "ae3i control cgif B" ${PIPESTATUS[0]}; cmp $CT/YE3i.cgif.v $C/YE3i.v; rc "control BYTE-EQUAL to cgif's YE3i.v" $?
echo "=== YE3i on fuzz_wire B ==="
MOD="IMG_RO_LO / IMG_RO_HI / img_ro_chunks generated for reac-repacer/fuzz_wire's asan-ubsan image by ae3i.py (sha256 3cf49addef7e): the chunks are [IMG_RO_LO, IMG_RO_HI) minus lib/B/YF0m.v's Tfib_owned_static (the rule reproduces cgif's own 15 chunks byte for byte), and IMG_RO_HI is THIS image's read-only PT_LOAD end - the donor's 0x2f1ac is a free choice, not a derivable boundary, so relocating it is unsound"
$FA ae3i.py --tmpl $C/YE3i.v --owned $R/YF0m.v --image $UB --modified "$MOD" --out $R/YE3i.v 2>&1 | scrub > $L/ae3i.wireB.log
rc "ae3i fuzz_wire B" ${PIPESTATUS[0]}; grep -v '^frozen-run' $L/ae3i.wireB.log
python3 - $R/YE3i.v $R/YF0m.v $UB <<'EOF'; rc "chunk gate (inside the RO segment, ordered, disjoint, = region minus owned)" $?
import re, sys
from elftools.elf.elffile import ELFFile
t, af, img = open(sys.argv[1]).read(), open(sys.argv[2]).read(), sys.argv[3]
lo = int(re.search(r'IMG_RO_LO : Z := (0x[0-9a-f]+)', t).group(1), 16); hi = int(re.search(r'IMG_RO_HI : Z := (0x[0-9a-f]+)', t).group(1), 16)
cs = [(int(a, 16), hi if b == 'IMG_RO_HI' else int(b, 16)) for a, b in re.findall(r'mkChunk (0x[0-9a-f]+) \(CImg \((IMG_RO_HI|0x[0-9a-f]+) - 0x[0-9a-f]+\)\)', t)]
seg = [(s['p_vaddr'], s['p_vaddr'] + s['p_filesz']) for s in ELFFile(open(img, 'rb')).iter_segments() if s['p_type'] == 'PT_LOAD'][0]
i = af.index('Definition Tfib_owned_static'); own = sorted((int(a, 16), int(eval(l))) for a, l in re.findall(r'\((0x[0-9a-f]+), ([^)]+)\)', af[i:af.index('].', i)]))
want, cur = [], lo
for a, n in own:
    if a + n <= cur or a >= hi: continue
    if a > cur: want.append((cur, min(a, hi)))
    cur = max(cur, a + n)
if cur < hi: want.append((cur, hi))
ok = cs == want and (lo, hi) == seg and all(lo <= a < b <= hi for a, b in cs) and all(cs[k][1] <= cs[k + 1][0] for k in range(len(cs) - 1))
print('IMG_RO [%#x, %#x) = RO PT_LOAD file range [%#x, %#x); %d chunks; recomputed region minus owned: %s' % (lo, hi, seg[0], seg[1], len(cs), 'EQUAL' if cs == want else 'DIFFERENT'))
sys.exit(0 if ok else 1)
EOF

echo "=== module paths: nsW (port_core rename_text, grant B's lib/B layout, placement rule) ==="
for f in YB12 YD2i YD2j YD1k YE3i YF0m; do python3 $W/tools/nsW.py $R/$f.v $G/$f.v --grant-twin $f 2>&1 | scrub; rc "nsW $f" ${PIPESTATUS[0]}; done
sha256sum $R/YB12.v $R/YD2i.v $R/YD2j.v $R/YD1k.v $R/YE3i.v $R/YF0m.v $G/YB12.v $G/YD2i.v $G/YD2j.v $G/YD1k.v $G/YE3i.v $G/YF0m.v | scrub
[ -z "$FAILED" ] || { echo "FAILED:$FAILED"; exit 1; }
echo "all rest-of-set generation gates pass"
