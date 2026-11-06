#!/usr/bin/env python3
"""extract_twin_syms.py IMAGE TWIN OUT -- the symbol extract that atable.py reads in place of an unstripped twin.

atable.py reads two facts from the twin of the image: its STT_FUNC symbols (name -> start, size), and that the twin's
PT_LOAD file bytes equal the image's. This script makes that check here and writes, for each symbol name that
atable.py's CODE_SPEC and STOP_SPEC look up (in that order, each name once), one tab-separated line
`<name> 0x<start> <size>`, as atable.py's own ELF reader gives it. It refuses when a name is not a symbol of the twin.

Header lines (`#`) name the twin's sha256, the image's (pin's) sha256, and the two PT_LOAD checks it made:
  - PT_LOAD 2..4 of twin and pin: same vaddr, file size, memory size and flags, and byte-equal file bytes;
  - all PT_LOAD file bytes, with the ELF header and the GNU build-id note masked (atable.py's own twin check): equal.
It refuses when either check fails. atable.py checks that the image it is given has the pin sha256 named here.

Python 3 stdlib only; atable.py must be in the same directory.
"""
import hashlib
import sys

from atable import CODE_SPEC, STOP_SPEC, Elf


def check_loads(twin, pin):
    if len(twin.loads) < 4 or len(pin.loads) < 4:
        raise ValueError(f'expected at least 4 PT_LOAD segments (twin {len(twin.loads)}, pin {len(pin.loads)})')
    for i in range(1, 4):
        (tv, to, tf, tm, tp), (pv, po, pf, pm, pp) = twin.loads[i], pin.loads[i]
        if (tv, tf, tm, tp) != (pv, pf, pm, pp):
            raise ValueError(f'PT_LOAD {i + 1}: twin and pin differ in vaddr, file size, memory size or flags')
        if twin.b[to:to + tf] != pin.b[po:po + pf]:
            raise ValueError(f'PT_LOAD {i + 1}: twin and pin file bytes differ')
    if twin.load_bytes() != pin.load_bytes():
        raise ValueError('PT_LOAD file bytes of twin and pin differ (ELF header and build-id note masked)')


def main():
    image, twin_path, out = sys.argv[1:4]
    pin, twin = Elf(image), Elf(twin_path)
    check_loads(twin, pin)
    names = []
    for spec in [s[1] for s in CODE_SPEC] + [s[0] for s in STOP_SPEC]:
        if spec not in names:
            names.append(spec)
    missing = [n for n in names if n not in twin.symbols]
    if missing:
        raise KeyError(f'not an STT_FUNC symbol of the twin: {missing}')
    lines = [
        '# atable.py symbol extract: STT_FUNC symbols (name, start, size) of an unstripped twin, the names atable.py '
        'looks up',
        f'# twin sha256 {hashlib.sha256(twin.b).hexdigest()}',
        f'# pin sha256 {hashlib.sha256(pin.b).hexdigest()}',
        '# PT_LOAD 2..4 of twin and pin: byte-equal (same vaddr, file size, memory size, flags and file bytes)',
        '# all PT_LOAD file bytes of twin and pin, ELF header and build-id note masked: equal',
    ]
    lines += [f'{n}\t{twin.symbols[n][0]:#x}\t{twin.symbols[n][1]}' for n in names]
    with open(out, 'w') as f:
        f.write('\n'.join(lines) + '\n')


main()
