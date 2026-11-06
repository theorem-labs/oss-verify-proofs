#!/bin/bash
# root-controls.sh <outdir>: the two controls of the root compare (GATES.md section 0) with the comparator fncmp.py
# (sha256 f8b778b1103a), each of which must say DIFFERENT:
#   plant   a copy of fuzz_wire.asan-ubsan with ONE bit flipped inside __asan_memmove: the word at 0x510f0
#           (__asan_memmove + 0x40, `addi s4, s0, -0x800` = 0x80040a13) made 0x80140a13 (`addi s4, s0, -0x7ff`),
#           against fuzz_pcap.asan-ubsan's __asan_memmove 0x51c40, 880 B; the copy is deleted after
#   memcpy  fuzz_wire.asan-ubsan's __asan_memmove 0x510b0 against its own __asan_memcpy 0x50c14, 880 B
# Environment: WIRE_BIN, PCAP_PIN (as run-gates.sh), FNCMP (fncmp.py).
set -uo pipefail
OUT=${1:?usage: root-controls.sh <outdir>}
: "${WIRE_BIN:?}" "${PCAP_PIN:?}" "${FNCMP:?}"
WB=$WIRE_BIN/fuzz_wire.asan-ubsan; PB=$PCAP_PIN/fuzz_pcap.asan-ubsan
sha() { sha256sum "$1" | cut -c1-12; }
for x in "$WB af4534831a45" "$PB 9e66f771f22a" "$FNCMP f8b778b1103a"; do
  set -- $x; [ "$(sha "$1")" = "$2" ] || { echo "root-controls: $1 is not sha256 $2" >&2; exit 2; }
done
mkdir -p "$OUT"; T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
cp "$WB" "$T/plant"
python3 - "$T/plant" <<'EOF' || exit 2
import sys
from elftools.elf.elffile import ELFFile
p, va = sys.argv[1], 0x510f0
with open(p, 'rb') as f:
    seg = next(s for s in ELFFile(f).iter_segments() if s['p_type'] == 'PT_LOAD' and s['p_vaddr'] <= va < s['p_vaddr'] + s['p_filesz'])
    off = seg['p_offset'] + va - seg['p_vaddr']
b = bytearray(open(p, 'rb').read())
w = int.from_bytes(b[off:off + 4], 'little')
assert w == 0x80040a13, hex(w)
b[off:off + 4] = (w ^ (1 << 20)).to_bytes(4, 'little')
open(p, 'wb').write(b)
print(f'plant: word at 0x{va:x} (file offset 0x{off:x}) 0x{w:08x} -> 0x{w ^ (1 << 20):08x}')
EOF
{ python3 - "$WB" "$T/plant" <<'EOF'
import sys
a, b = open(sys.argv[1], 'rb').read(), open(sys.argv[2], 'rb').read()
d = [i for i in range(len(a)) if a[i] != b[i]]
print(f'# planted copy: {len(a)} bytes, {len(d)} byte differs from fuzz_wire.asan-ubsan af4534831a45 (offset {", ".join(hex(i) for i in d)}; '
      f'bits {sum(bin(a[i] ^ b[i]).count("1") for i in d)})')
EOF
  echo "# fncmp.py f8b778b1103a: planted copy (sha256 $(sha "$T/plant")) 0x510b0 vs fuzz_pcap.asan-ubsan 9e66f771f22a 0x51c40, 880 B"
  python3 "$FNCMP" "$T/plant" 0x510b0 "$PB" 0x51c40 880; echo "rc=$?"; } > "$OUT/root-control-plant.out" 2>&1
{ echo "# fncmp.py f8b778b1103a: fuzz_wire.asan-ubsan af4534831a45 __asan_memmove 0x510b0 vs its __asan_memcpy 0x50c14, 880 B"
  python3 "$FNCMP" "$WB" 0x510b0 "$WB" 0x50c14 880; echo "rc=$?"; } > "$OUT/root-control-memcpy.out" 2>&1
echo "root-controls: $(grep -h VERDICT "$OUT"/root-control-*.out | tr '\n' ' ')"
