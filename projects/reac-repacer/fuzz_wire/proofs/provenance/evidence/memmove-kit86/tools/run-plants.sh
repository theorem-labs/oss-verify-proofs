#!/bin/sh
# Run the whole comparison and settlement on each planted image pair (out/plants), so the record shows that the
# settlement refuses both plants. usage: run-plants.sh
cd "$(dirname "$0")" || exit 1
export PYTHONDONTWRITEBYTECODE=1
O=out/plants
for op in add xor; do
  X=$O/plant-$op-X.elf; YT=$O/plant-$op-Ytwin.elf; YP=$O/plant-$op-Ypin.elf
  python3 kit/closure_strict3.py $X $YT __asan_memmove > $O/closure-$op.txt 2> $O/closure-$op.err
  python3 kit/paircl.py $X $YP __asan_memmove 0x51bf0 $YT --full --targets-out $O/paircl-targets-$op.tsv \
      > $O/paircl-$op.txt 2> $O/paircl-$op.err
  python3 - "$op" <<'EOF'
import re, sys
op = sys.argv[1]
names = []
for ln in open('out/plants/closure-%s.txt' % op).read().splitlines()[1:]:
    m = re.match(r'^   (\S+) @0x[0-9a-f]+: ', ln)
    if m: names.append(m.group(1))
for ln in open('out/plants/paircl-targets-%s.tsv' % op).read().splitlines()[1:]:
    n = ln.split('\t')[0]
    if n not in names: names.append(n)
open('out/plants/jtnames-%s.txt' % op, 'w').write(','.join(names) + '\n')
EOF
  python3 kit/jtcheck.py $X $YT "$(cat $O/jtnames-$op.txt)" > $O/jtcheck-$op.txt 2> $O/jtcheck-$op.err
  python3 tools/settle3.py kit $X $YP $YT $O/closure-$op.txt $O/paircl-$op.txt $O/paircl-targets-$op.tsv \
      $O/jtcheck-$op.txt tools/luiclass.tsv $O/settle-$op > $O/settle-$op-summary.txt 2>&1
  echo "== plant $op"; cat $O/settle-$op-summary.txt
  grep -F '_ZN6__asan9Allocator22FindHeapChunkByAddressEm' $O/settle-$op-targets.tsv | head -4
done
