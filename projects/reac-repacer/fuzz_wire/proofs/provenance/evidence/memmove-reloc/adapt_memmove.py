#!/usr/bin/env python3
"""Adapt libreac/fuzz_pcap's released ASan memmove files (lib/{A,B}/Rt/Memmove{Def,Im,K,Paths,}.v, commit
5098883da0b), AFTER alreloc (frozen a5c53bb2bed4ad03) has moved their numerals to fuzz_wire, to fuzz_wire's module layout.
alreloc maps addresses and the unit namespace only; this script makes the changes it does not, each counted:
  1. body comments that name the donor's build (`of libreac/fuzz_pcap's v1.9.0 <build> build`) name fuzz_wire's, because
     the numerals beside them are fuzz_wire's now;
  2. image B only: fuzz_pcap keeps its image-B kernel files YB1v / YE2y / YE34 / YF0l / YF0m / YF0x under lib/Reusable,
     fuzz_wire keeps them under lib/B: the Require moves to lib.B;
  3. fuzz_pcap's image end `PcapImgEnd.pcap_img_end` is a Definition equal to YImgTop.IMG_TOP (lib/Reusable/PcapImgEnd.v:11);
     fuzz_wire states its image end only as TFIB_IMG_END := IMG_TOP, a parsing-only Notation (lib/B/YImgTop.v,
     lib/Reusable/YImgTop.v), which `unfold` cannot name: the two names leave the `unfold` lists (unfolding TFIB_IMG_END
     gives the number), and their Require goes;
  4. fuzz_pcap's symbol record PcapSyms (lib/Reusable/YF0m.v:436, lib/A/AF0m.v:437) is fuzz_wire's WireSyms
     (lib/B/YF0m.v:272, lib/A/AF0m.v:349);
  5. header: the inherited lines (Copyright, SPDX, the donor's Written-by / Modified-by lines) stay byte for byte, names
     included (the unit's comment scrub runs later on the whole unit tree); one line `Modified by Theorem Labs, 2026-10:
     ...` is added under them, naming the changes made to that file.
The runs read the core's code table tbl_icpt (lib/<IMG>/YE34.v / AE34.v icpt_ranges), which must list __asan_memmove's
range, as fuzz_pcap's does (0x51c40, 220 words); that row belongs to the core, not to these files.
usage: adapt_memmove.py A|B LIBDIR      (LIBDIR = projects/reac-repacer/fuzz_wire/proofs/lib). Exit 1 on any count mismatch."""
import re, sys

img, lib = sys.argv[1], sys.argv[2]
assert img in ('A', 'B')
BUILD = {'A': 'asan', 'B': 'asan-ubsan'}[img]
ENTRY = {'A': '0x51310', 'B': '0x510b0'}[img]
FILES = ['MemmoveDef', 'MemmoveIm', 'MemmoveK', 'MemmovePaths', 'Memmove']
NS = 'OssFuzzTheorems.Proofs.reac_repacer.fuzz_wire.lib'
fail = []


def sub(text, pat, rep, want, what, f, flags=0):
    new, n = re.subn(pat, rep, text, flags=flags)
    if want is not None and n != want:
        fail.append(f'{f}: {what}: {n} replacements, expected {want}')
    return new, n


for name in FILES:
    f = f'{lib}/{img}/Rt/{name}.v'
    t = open(f).read()
    did = ['addresses and numbers moved by symbol to its ' + BUILD + ' image', 'module paths changed']
    # the inherited header: every leading comment line up to the first non-comment line stays byte for byte
    m = re.match(r'((?:\(\*.*?\*\)\n)+)', t, re.S)
    head_end = len(m.group(1)) if m else 0
    lic = re.match(r'(\(\* Copyright[^\n]*\*\)\n\(\* SPDX[^\n]*\*\)\n(?:\(\* (?:Written|Modified) by Theorem Labs.*?\*\)\n)*)', t, re.S)
    if not lic:
        fail.append(f'{f}: no inherited licence block')
        continue
    lic_end = len(lic.group(1))
    head, rest = t[:lic_end], t[lic_end:]
    # 1. body comments naming the donor's build
    rest, n1 = sub(rest, r"of libreac/fuzz_pcap's v1\.9\.0 " + re.escape(BUILD) + " build",
                   "of reac-repacer/fuzz_wire's " + BUILD + " build", None, 'body build name', f)
    if n1:
        did.append('its comments name that build')
    # 2. image-B kernel files: lib.Reusable -> lib.B
    if img == 'B':
        want = 0 if name in ('MemmoveDef', 'MemmoveIm') else 1
        rest, n2 = sub(rest, re.escape(f'From {NS}.Reusable Require Import YB1v YE34 YF0l YF0m YF0x YE2y.'),
                       f'From {NS}.B Require Import YB1v YE34 YF0l YF0m YF0x YE2y.', want, 'B kernel Require', f)
        if n2:
            did.append('the image-B kernel files Required from lib/B')
    # 3. image end
    rest, n3 = sub(rest, r", PcapImgEnd\.pcap_img_end, YImgTop\.IMG_TOP(?= in \*)", '', None, 'unfold list', f)
    rest, _ = sub(rest, re.escape(f'From {NS}.Reusable Require PcapImgEnd YImgTop.') + r'\n', '',
                  1 if n3 else 0, 'PcapImgEnd Require', f)
    if n3:
        did.append('the image end read from TFIB_IMG_END (PcapImgEnd dropped)')
    if re.search(r'PcapImgEnd|pcap_img_end', rest):
        fail.append(f'{f}: PcapImgEnd / pcap_img_end still present')
    # 4. symbol record
    rest, n4 = sub(rest, r'\bPcapSyms\b', 'WireSyms', None, 'PcapSyms', f)
    if n4:
        did.append('the symbol record PcapSyms renamed WireSyms')
    note = "(* Modified by Theorem Labs, 2026-10: relocated to reac-repacer/fuzz_wire's " + BUILD + ' build: ' + '; '.join(did) + '. *)\n'
    open(f, 'w').write(head + note + rest)
    print(f'{f}: ' + '; '.join(did))

if fail:
    print('\n'.join(fail))
    sys.exit(1)
print('adapt_memmove: OK')
