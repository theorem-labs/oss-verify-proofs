#!/usr/bin/env python3
"""S2b: regenerate lib/Reusable/YF0m.v reproducibly.

  yf0m_regen.py --image PIN --symbols SYMBOLS.tsv --binaries index/binaries.tsv --imgtop YImgTop.v
                --stage STAGE_YF0m.v --base BASE.v --values PASS2_VALUES.tsv --out OUT.v

Runs af0m.py (the one generator) on fuzz_disco's asan-ubsan image and the collector's pass-2 hand-off states, then
applies the three deterministic edits that the generator does not know about, each with the reason:

  EXTRA (given to af0m.py as --add ADDR/W, which reads each value from every collected state; the owned rows go into
  the generator's INPUT first, so af0m.py's own owned-coverage gate keeps the cells):
    z8 (ANum 0x10350) 0xf5f5f5f5f5f5f5f5   the class-6 stack-free fill pattern, read through am_const by the release
                                           walk; owned range (0x10350, 8).
    z8 (ANum 0xa25b0) 0x9a160              REAL(strlen): the GOT-like cell __interceptor_strlen loads.
    z8 (ANum 0x103b8) 0xafffff00000fffff   the mask __asan_unregister_globals loads (insn 0x407ac), also YE2k's FF_mask icell;
                                           owned range (0x103b8, 8).
  DROP:
    z4 (ANum 0x21408) 0x22732522 and owned (0x21408, 4)   inside the registered global .str.7 (0x21400, 13), so owning
                                           it contradicts YRo's tfib_ro_unowned; no walk uses the cell.

Every value is checked against the image before it is written, and the generator's output is not edited after it
runs: all three edits are made to its input. Re-running this with the same inputs reproduces the
committed file byte for byte.

This is a new version of yf0m_regen.py 9a83fd295f33 with the same edits and the same output. Every input is an
argument: the pinned image (--image), the shared symbol extract of its unstripped twin (--symbols, read through
symbols.nm_lines: the names file the earlier version read, byte for byte), the pin table (--binaries), YImgTop.v
(--imgtop), the relocated stage YF0m.v (--stage) and the collector's pass-2 states as the per-value table that
extract_pass2.py writes (--values; the earlier version gave af0m.py the 6 MB log). af0m.py and the modules it runs
(pins.py, tr0.py, dphash.py, symbols.py, trace-image/) are read from this script's directory. The image words are read
from the image's PT_LOADs here (the earlier version read them through elfdis.load, a tool outside its directory, with
the same rule). The unstripped twin itself is not passed to af0m.py: it only fed a provenance line this run does not write.
"""
import argparse
import hashlib
import os
import re
import struct
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import symbols  # noqa: E402

# The generator is pinned: a changed af0m.py changes the output (a later version places the regenerated descriptor words
# where the base's sat, which moves every later Tfib_const_abs index). Refuse to run on another version. af0m.py here is
# the new version of af0m.py 2ac2dbe25a9a (reads --values / --symbols / --binaries; same rules, same output).
AF0M = os.path.join(HERE, 'af0m.py')
AF0M_SHA = 'd8c26ca9e704'
# The --base used for the committed file: yf0m_base.v (an earlier generated YF0m, which fixes the row order that
# consumers index); its sha256 prefix:
BASE_SHA = '058c1113c079'   # reads decimal-valued rows, keeps the base's spelling
EXTRA = [(8, 0x10350, 0xf5f5f5f5f5f5f5f5, (0x10350, 8)), (8, 0xa25b0, 0x9a160, None),
         (8, 0x103b8, 0xafffff00000fffff, (0x103b8, 8)),
         # disco's sysconf jump-table entry 3 (table at 0x21c1c), the twin of cgif's dropped z4 0x21408 cell; YFio's
         # BCELLS read it through tfib_const_lookup (YFii's R_scj, YFk1)
         (4, 0x21c28, 0x6dc9c, (0x21c28, 4)),
         # the GOT cell of REAL(vsnprintf), _ZN14__interception14real_vsnprintfE -> vsnprintf 0x99478 (RELRO, not owned,
         # like its neighbour real_vfprintf 0xa2610); G9's FMsnprintfGvsni0 vsni_rodata_chk reads it
         (8, 0xa2618, 0x99478, None)]
# Base rows that kept cgif's DATA address (the remap moved neither the value nor the address): position-aware, found
# by comparing the base with cgif's own YF0m (an address unchanged from the donor, inside cgif's data / bss). Each
# target is the same disco object at the same offset, checked against fuzz_disco.asan-ubsan's symbols; af0m.py then
# reads the value from the collected states. The asan flags first, the rest from the same scan.
ADDR_FIX = {0xa3a80: 0xa6c80, 0xa3aa8: 0xa6ca8, 0xa3ab8: 0xa6cb8, 0xa3ac8: 0xa6cc8, 0xa3ad8: 0xa6cd8,  # asan_flags +8 .. +0x60
            0x137d70: 0x13af70,   # __sanitizer::MFHooks + 0x30
            0xa5ac0: 0xa8cc0,     # interceptor_metadata_map + 0
            0xa5ae0: 0xa8ce0}     # __asan::tsd_key_inited + 0
# Cells appended after a landing: moved to the end of Tfib_const_abs (index-stable).
APPEND_LAST = [0xa2618]
DROP_CELL = r'\s*z4 \(ANum 0x21408\)\s+0x22732522\s*;'
DROP_OWNED = r'\s*\(0x21408,\s*4\);'


def ial_offsets(stage):
    """The internal allocator's interior: TFIB_IAL_W and TFIB_IAL_HI are fixed offsets from TFIB_IAL_LO inside
    internal_alloc_placeholder, taken from cgif's own YF0m (W - LO, HI - LO) as the relocated stage file keeps them;
    af0m.py only checks that they lie inside a symbol, so relocated values passed it (disco's code at 0x5ea90 writes the
    page size at LO + 0x40dc0 = 0xeb440). The donor's offsets are applied to disco's LO here."""
    d = open(stage).read()
    g = lambda n: int(re.search(r'Definition %s : Z := (0x[0-9a-fA-F]+)' % n, d).group(1), 16)
    return g('TFIB_IAL_W') - g('TFIB_IAL_LO'), g('TFIB_IAL_HI') - g('TFIB_IAL_LO')


def image_word(img, a, n):
    """the n-byte little-endian word at a, from the file bytes of the first PT_LOAD whose file part holds it whole"""
    f = open(img, 'rb').read()
    phoff = struct.unpack_from('<Q', f, 0x20)[0]
    phent, phnum = struct.unpack_from('<H', f, 0x36)[0], struct.unpack_from('<H', f, 0x38)[0]
    for i in range(phnum):
        o = phoff + i * phent
        if struct.unpack_from('<I', f, o)[0] != 1:   # PT_LOAD
            continue
        off, v, fs = (struct.unpack_from('<Q', f, o + 0x08)[0], struct.unpack_from('<Q', f, o + 0x10)[0],
                      struct.unpack_from('<Q', f, o + 0x20)[0])
        if v <= a and a + n <= v + fs:
            return int.from_bytes(f[off + (a - v):off + (a - v) + n], 'little')
    return None


def ro_ranges(img):
    """The image's read-only ranges: PT_LOADs without PF_W, and PT_GNU_RELRO (read-only once main runs)."""
    f = open(img, 'rb').read()
    phoff = struct.unpack_from('<Q', f, 0x20)[0]
    phent, phnum = struct.unpack_from('<H', f, 0x36)[0], struct.unpack_from('<H', f, 0x38)[0]
    out = []
    for i in range(phnum):
        o = phoff + i * phent
        typ, fl = struct.unpack_from('<II', f, o)
        va, msz = struct.unpack_from('<Q', f, o + 0x10)[0], struct.unpack_from('<Q', f, o + 0x28)[0]
        if (typ == 1 and not fl & 2) or typ == 0x6474e552:
            out.append((va, va + msz))
    return out


def ro_pins(inp, img, desc):
    """Every OWNED byte inside a read-only segment is a const cell holding its image byte. Returns the
    --add specs for the owned read-only bytes the input does not pin yet: an aligned 8-byte word when the whole word
    is owned, read-only and unpinned, else single bytes. The values are read by af0m.py from the states (KImg)."""
    t = open(inp).read()
    i, j = t.find('Definition Tfib_owned_static'), t.find('Definition TFIB_TR0')
    owned = []
    for m in re.finditer(r'\((0x[0-9a-fA-F]+|\d+),\s*([^)]+)\)', t[i:j]):
        s = m.group(2).strip()
        if re.fullmatch(r'[0-9a-fA-FxX\s+\-*/()]+', s):
            owned.append((int(m.group(1), 0), eval(s)))
    ci, cj = t.find('Definition Tfib_const_abs'), t.find('Definition Tfib_const_shadow')
    pinned = set()
    for w, a in re.findall(r'z(\d)\s*\(ANum\s+(0x[0-9a-fA-F]+|\d+)\)', t[ci:cj]):
        pinned.update(range(int(a, 0), int(a, 0) + int(w)))
    pinned.update(x for w, a, _, _ in EXTRA for x in range(a, a + w))
    # af0m.py itself emits every word of the asan_globals descriptor array (49 x 64 bytes at __start_asan_globals), so
    # those bytes are never --add'ed (0xa5d98 was once stated twice).
    pinned.update(range(desc[0], desc[1]))
    ro = ro_ranges(img)
    need = sorted({x for a, n in owned for x in range(a, a + n)
                   if any(lo <= x < hi for lo, hi in ro) and x not in pinned})
    needs, specs, k = set(need), [], 0
    while k < len(need):
        x = need[k]
        if x % 8 == 0 and all(x + d in needs for d in range(8)):
            specs.append('%#x/8' % x); k += 8
        else:
            specs.append('%#x/1' % x); k += 1
    return specs, len(need)


def prepare_input(base, path, img, stage, ial):
    """The generator's INPUT: the base with the owned rows of the EXTRA cells added and the DROP cell removed, so that
    af0m.py's own gates (xowned coverage, cellcheck of every --add value against all states) see the final layout."""
    t = open(base).read()
    i, j = t.find('Definition Tfib_owned_static'), t.find('Definition TFIB_TR0')
    blk = t[i:j]
    for w, addr, val, owned in EXTRA:
        if val is None:
            continue                     # runtime value: af0m.py reads it from every state and requires agreement
        got = image_word(img, addr, w)
        if got != val:
            sys.exit('yf0m_regen: %#x holds %s, not %#x' % (addr, hex(got) if got is not None else 'nothing', val))
        if owned and '(%#x, %d)' % owned not in blk:
            assert '(0x10338, 8);' in blk, 'owned anchor (0x10338, 8) missing from the base'
            blk = blk.replace('(0x10338, 8);', '(0x10338, 8); (%#x, %d);' % owned, 1)
    blk, n2 = re.subn(DROP_OWNED, '', blk, count=1)
    t = t[:i] + blk + t[j:]
    t, n1 = re.subn(DROP_CELL, '', t, count=1)
    ci, cj = t.find('Definition Tfib_const_abs'), t.find('Definition Tfib_const_shadow')
    # Position-aware: only the base rows that CAME FROM the donor are moved, i.e. the first DONOR_N rows of
    # Tfib_const_abs (the base keeps the donor's order there; later rows were added from disco's own states). A later
    # row at the same address is disco's own cell (0xa5ac0 / 0xa5ae0 in the stride-8 run at 0xa5a78) and stays; moving
    # it made duplicate cells (z8 0xa8ce0 over the 1-byte tsd_key_inited).
    d = open(stage).read()
    DONOR_N = len(re.findall(r'z\d\s*\(ANum\s', d[d.find('Definition Tfib_const_abs'):d.find('Definition Tfib_const_shadow')]))
    nfix, seen = [0], [0]
    def fix(m):
        k = seen[0]
        seen[0] += 1
        a = int(m.group(2), 0)
        if a in ADDR_FIX and k < DONOR_N:
            nfix[0] += 1
            return m.group(1) + '%#x' % ADDR_FIX[a]
        return m.group(0)
    blk = re.sub(r'(z\d\s*\(ANum\s+)(0x[0-9a-fA-F]+|\d+)(?=\))', fix, t[ci:cj])
    # The base states 0x10448 / 0x10458 / 0x10558 twice (same width, same value). The LATER copy is dropped (no proof
    # cites a Tfib_const_abs index above 72; the copies sit at 118 / 123 / 125).
    seen_rows, ndup = set(), [0]
    def dedup(m):
        key = (m.group(1), int(m.group(2), 0), int(m.group(3), 0))
        if key in seen_rows:
            ndup[0] += 1
            return ''
        seen_rows.add(key)
        return m.group(0)
    blk = re.sub(r'\s*z(\d)\s*\(ANum\s+(0x[0-9a-fA-F]+|\d+)\)\s+(0x[0-9a-fA-F]+|\d+)\s*;', dedup, blk)
    t = t[:ci] + blk + t[cj:]
    print('yf0m_regen: %d base rows moved from a cgif data address to its disco object; %d duplicate rows dropped'
          % (nfix[0], ndup[0]))
    lo = int(re.search(r'Definition TFIB_IAL_LO : Z := (0x[0-9a-fA-F]+)', t).group(1), 16)
    for name, off in (('TFIB_IAL_W', ial[0]), ('TFIB_IAL_HI', ial[1])):
        t = re.sub(r'(Definition %s : Z := )0x[0-9a-fA-F]+' % name, lambda m: m.group(1) + '%#x' % (lo + off), t, count=1)
    print('yf0m_regen: TFIB_IAL_W = LO + %#x = %#x, TFIB_IAL_HI = LO + %#x = %#x' % (ial[0], lo + ial[0], ial[1], lo + ial[1]))
    open(path, 'w').write(t)
    return n1, n2


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--image', required=True, help='the pinned image fuzz_disco.asan-ubsan')
    ap.add_argument('--symbols', required=True, help="the symbol extract of the image's unstripped twin (TSV)")
    ap.add_argument('--binaries', required=True, help='index/binaries.tsv: the pin table af0m.py checks --image against')
    ap.add_argument('--imgtop', required=True, help='lib/Reusable/YImgTop.v (its IMG_TOP)')
    ap.add_argument('--stage', required=True, help='the relocated stage YF0m.v (donor row count, allocator offsets)')
    ap.add_argument('--base', required=True)
    ap.add_argument('--values', required=True, help="extract_pass2.py's table of the collector's pass-2 states")
    ap.add_argument('--out', required=True)
    a = ap.parse_args()
    have = hashlib.sha256(open(AF0M, 'rb').read()).hexdigest()[:12]
    if have != AF0M_SHA:
        sys.exit('yf0m_regen: af0m.py is %s, pinned %s: re-check the output order before re-pinning' % (have, AF0M_SHA))
    if hashlib.sha256(open(a.base, 'rb').read()).hexdigest()[:12] != BASE_SHA:
        print('yf0m_regen: NOTE --base is not the pinned base %s; row order may differ' % BASE_SHA)
    nmv = {l.split()[-1]: int(l.split()[0], 16) for l in symbols.nm_lines(a.symbols) if l.split()}
    desc = (nmv['__start_asan_globals'], nmv['__stop_asan_globals'])   # the 49 descriptors, 64 bytes each
    inp = a.out + '.input.v'
    n1, n2 = prepare_input(a.base, inp, a.image, a.stage, ial_offsets(a.stage))
    adds = []
    for w, addr, _, _ in EXTRA:
        adds += ['--add', '%#x/%d' % (addr, w)]
    ro_specs, ro_n = ro_pins(inp, a.image, desc)
    for s in ro_specs:
        adds += ['--add', s]
    print('yf0m_regen: %d owned read-only bytes not yet pinned -> %d --add cells' % (ro_n, len(ro_specs)))
    r = subprocess.run([sys.executable, AF0M, '--base', inp, '--values', a.values, '--image', a.image,
                        '--binaries', a.binaries, '--symbols', a.symbols, '--out', a.out] + adds,
                       capture_output=True, text=True)
    sys.stdout.write(r.stdout)
    if r.returncode:
        sys.exit(r.stderr.strip() or 'af0m.py failed')
    out = open(a.out).read()
    missing = [hex(addr) for w, addr, _, _ in EXTRA if 'ANum %#x)' % addr not in out]
    if missing:
        sys.exit('yf0m_regen: af0m.py dropped --add cells %s' % missing)
    # The ONE post-step, a citation not a value change (the image-top decision, as A's AF0m): a Tfib_zero_shadow range
    # that ends at the image top cites YImgTop.IMG_TOP instead of the numeral. The numeral is checked to equal YImgTop's
    # value first.
    top = int(re.search(r'Definition IMG_TOP : Z := (0x[0-9a-fA-F]+)', open(a.imgtop).read()).group(1), 16)
    zi = out.find('Definition Tfib_zero_shadow')
    zj = out.find('].', zi)
    blk, nz = re.subn(r'\((0x[0-9a-f]+), %#x - \1\)' % top, lambda m: '(%s, YImgTop.IMG_TOP - %s)' % (m.group(1), m.group(1)),
                      out[zi:zj])
    if nz != 1:
        sys.exit('yf0m_regen: expected exactly one zero range ending at the image top %#x, found %d' % (top, nz))
    out = out[:zi] + blk + out[zj:]
    # Second post-step, an ORDER change only: a cell added after the committed file landed moves to the END of
    # Tfib_const_abs, so no earlier index moves (af0m.py --reads does the same on fuzz_identity).
    ai = out.find('Definition Tfib_const_abs')
    aj = out.find('].', ai)
    rows = out[ai:aj].split('\n')
    head = [r for r in rows if not re.match(r'^z\d \(ANum ', r)]
    cells = [r for r in rows if re.match(r'^z\d \(ANum ', r)]
    assert rows[:2] == head[:2] and len(head) == 2, head   # 'Definition ... :=' and '['
    for adr in APPEND_LAST:
        hit = [r for r in cells if re.match(r'^z\d \(ANum %#x\) ' % adr, r)]
        if len(hit) != 1:
            sys.exit('yf0m_regen: APPEND_LAST cell %#x found %d times' % (adr, len(hit)))
        cells.remove(hit[0])
        cells.append(hit[0])
        last = cells[-2] if cells[-1] is hit[0] else cells[-1]
    # only the two rows whose role changes are re-spelled: the old last row gains the separator, the moved row ends
    # the list; every other row keeps its exact text
    old_last = [r for r in rows if re.match(r'^z\d \(ANum ', r)][-1]
    i_old = cells.index(old_last)
    cells[i_old] = old_last.rstrip() + '  ;'
    for k in range(len(cells) - len(APPEND_LAST), len(cells) - 1):
        cells[k] = re.sub(r'\s*;?\s*$', '', cells[k]) + '  ;'
    cells[-1] = re.sub(r'\s*;?\s*$', '', cells[-1]) + '    '
    body = '\n'.join(cells)
    out = out[:ai] + head[0] + '\n' + head[1] + '\n' + body + out[aj:]
    open(a.out, 'w').write(out)
    print('yf0m_regen: input = base + %d owned rows, 0x21408 cell dropped (%d) and its owned row (%d); af0m.py '
          'output written unedited except the last zero range citing YImgTop.IMG_TOP (= %#x)'
          % (sum(1 for e in EXTRA if e[3]), n1, n2, top))


main()
