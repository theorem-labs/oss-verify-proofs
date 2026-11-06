#!/usr/bin/env python3
"""measure-mm.py LIB CORELIB PCAP_AE2Y: the measurements the triage reasons of GATES.md cite, each read out of BOTH images
(fuzz_wire.asan 2f8f8697cd4f / twin d2f662a22962, the target; fuzz_pcap.asan b7a91d9b1fb0 / twin 36da3052c383, the
donor; environment WIRE_BIN, PCAP_PIN, PCAP_TWIN as run-gates.sh). LIB holds the five checked files (A/Rt/<name>.v),
CORELIB is the unit's lib (lib/A/AE2y.v), PCAP_AE2Y is fuzz_pcap's released lib/A/AE2y.v.
  1. MemmoveIm.v's 22 words W_mm<off> against the stripped image's word at __sanitizer_internal_memmove + off
     (the instruction words codeptr reads as numbers, and the words decval lists without a fetch pair);
  2. the two ld words kept by asan-resolve-A.txt (538627 = 0x83803, 571523 = 0x8b883) at __asan_memmove + 0x84 / +0xd0
     and + 0x88 / + 0xd4;
  3. the return address of asan-resolve-A.txt (345460 -> 343188): __asan_region_is_poisoned + 0x174 and the call word
     before it (equal in both images);
  4. MemmoveK.v's bound 0x200000 against the largest row end lo + len of each unit's icpt_rodata;
  5. MemmoveK.v's three `clookup tbl_icpt` words (__asan_memmove + 0x0 / + 0xe0 / + 0x36c) against both images.
Exit 1 on any mismatch."""
import os
import re
import sys

from elftools.elf.elffile import ELFFile


class Img:
    def __init__(self, name, stripped, twin):
        self.name = name
        with open(twin, 'rb') as f:
            e = ELFFile(f)
            self.syms = {s.name: s['st_value'] for s in e.get_section_by_name('.symtab').iter_symbols() if s.name}
        with open(stripped, 'rb') as f:
            e = ELFFile(f)
            self.loads = [(s['p_vaddr'], s['p_memsz'], s.data()) for s in e.iter_segments() if s['p_type'] == 'PT_LOAD']

    def word(self, a):
        for v, m, d in self.loads:
            if v <= a < v + m:
                return int.from_bytes(d[a - v:a - v + 4], 'little')
        return None


lib, corelib, pcap_ye2y = sys.argv[1:4]
W = Img('fuzz_wire.asan', os.environ['WIRE_BIN'] + '/fuzz_wire.asan', os.environ['WIRE_BIN'] + '/fuzz_wire.asan.unstripped')
P = Img('fuzz_pcap.asan', os.environ['PCAP_PIN'] + '/fuzz_pcap.asan', os.environ['PCAP_TWIN'] + '/fuzz_pcap.asan')
bad = 0


def say(ok, msg):
    global bad
    bad += 0 if ok else 1
    print(('OK   ' if ok else 'BAD  ') + msg)


print('# 1. MemmoveIm.v W_mm<off> = the word at __sanitizer_internal_memmove + off (wire 0x%x, pcap 0x%x)' % (
    W.syms['__sanitizer_internal_memmove'], P.syms['__sanitizer_internal_memmove']))
t = open(f'{lib}/A/Rt/MemmoveIm.v').read()
ws = re.findall(r'^Definition W_mm([0-9a-f]{2}) : bv 32 := (0x[0-9a-f]{8})\.$', t, re.M)
say(len(ws) == 22, f'{len(ws)} words W_mm00 .. W_mm54 in MemmoveIm.v')
for off, v in ws:
    o, v = int(off, 16), int(v, 16)
    gw, gp = W.word(W.syms['__sanitizer_internal_memmove'] + o), P.word(P.syms['__sanitizer_internal_memmove'] + o)
    say(gw == v and gp == v, f'W_mm{off} = 0x{v:08x}: wire 0x{gw:08x} at 0x{W.syms["__sanitizer_internal_memmove"] + o:x}, '
        f'pcap 0x{gp:08x} at 0x{P.syms["__sanitizer_internal_memmove"] + o:x}' +
        ('  (in [0x10000, image top): a number codeptr / decval read)' if 0x10000 <= v < 0x5f4ff0 else ''))
print('# 2. the kept ld words at __asan_memmove + off (wire 0x%x, pcap 0x%x)' % (W.syms['__asan_memmove'], P.syms['__asan_memmove']))
for dec, offs in ((538627, (0x84, 0xd0)), (571523, (0x88, 0xd4))):
    for o in offs:
        gw, gp = W.word(W.syms['__asan_memmove'] + o), P.word(P.syms['__asan_memmove'] + o)
        say(gw == dec and gp == dec, f'{dec} = 0x{dec:x}: wire 0x{gw:x} at __asan_memmove+0x{o:x}, pcap 0x{gp:x} at __asan_memmove+0x{o:x}')
print('# 3. the return address 345460 -> 343188')
for img, val in ((P, 345460), (W, 343188)):
    a = img.syms['__asan_region_is_poisoned'] + 0x174
    say(a == val, f'{img.name}: __asan_region_is_poisoned 0x{img.syms["__asan_region_is_poisoned"]:x} + 0x174 = 0x{a:x} = {a} '
        f'(the file\'s {val}); word before it 0x{img.word(a - 4):08x}')
cw, cp = W.word(W.syms['__asan_region_is_poisoned'] + 0x170), P.word(P.syms['__asan_region_is_poisoned'] + 0x170)
say(cw == cp, f'the call word at +0x170 is the same in both images: wire 0x{cw:08x}, pcap 0x{cp:08x}')
print('# 4. MemmoveK.v bound 0x200000 vs the row ends of icpt_rodata')
k = open(f'{lib}/A/Rt/MemmoveK.v').read()
say(k.count('<= 0x200000)') == 1, 'MemmoveK.v states `fst (fst e) + snd (fst e) <= 0x200000` once (Hrange of entD_ro)')
for name, path in (('fuzz_wire lib/A/AE2y.v', f'{corelib}/A/AE2y.v'), ("fuzz_pcap's released lib/A/AE2y.v", pcap_ye2y)):
    s = open(path).read()
    i = s.index('Definition icpt_rodata')
    rows = re.findall(r'\((0x[0-9a-f]+), (\d+), \[', s[i:s.index('].', i)])
    ends = [int(lo, 16) + int(n) for lo, n in rows]
    say(max(ends) <= 0x200000, f'{name}: {len(rows)} rows, largest lo + len = 0x{max(ends):x} <= 0x200000')
print('# 5. MemmoveK.v clookup tbl_icpt words (the three instruction words the flag gate reads INSN-SAME)')
for off, word in ((0x0, 0x81010113), (0xe0, 0x6e9110ef), (0x36c, 0xd75ff06f)):
    a = W.syms['__asan_memmove'] + off
    say(f'clookup tbl_icpt 0x{a:x} = Some 0x{word:08x}' in k, f'MemmoveK.v states clookup tbl_icpt 0x{a:x} = Some 0x{word:08x}')
    gw, gp = W.word(a), P.word(P.syms['__asan_memmove'] + off)
    say(gw == word and gp == word, f'0x{word:08x} at __asan_memmove+0x{off:x}: wire 0x{gw:08x} at 0x{a:x}, pcap 0x{gp:08x} at '
        f'0x{P.syms["__asan_memmove"] + off:x}')
print(f'measure-mm: {bad} mismatches')
sys.exit(1 if bad else 0)
