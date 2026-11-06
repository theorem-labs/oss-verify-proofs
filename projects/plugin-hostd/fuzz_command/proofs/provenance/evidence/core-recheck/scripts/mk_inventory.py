#!/usr/bin/env python3
"""Inventory of plugin-hostd/fuzz_command's relocated core: which files came from which port_core run (or other tool),
with which inputs, and the route of the re-check.

Usage: mk_inventory.py OURS_LIB MERGED_LIB DONOR_LIB RUN_A1_STAGE_OUT RUN_A2_STAGE_OUT RUN1_STAGE_OUT RUN1_KEPT OUT.tsv
  OURS_LIB / MERGED_LIB: proofs/plugin-hostd/fuzz_command/lib at the checked commit and at the merged tree;
  DONOR_LIB: proofs/cgif/cgif_file_fuzzer/lib at c8557374ad2e;
  RUN_*_STAGE_OUT: the stage-out/ directories of the untagged runs (A1: 377 A/ files; A2: 14 A/ files; run 1: its
  Reusable/ part); RUN1_KEPT: run 1's kept.txt (non-A files the target already held).
Prints the counts per set and route."""
import hashlib, os, re, sys
from collections import Counter

ours, merged, donor, a1, a2, r1, r1kept, out = sys.argv[1:9]
MOD = re.compile(r'\(\* Modified by Theorem Labs, \d{4}-\d{2}: (.*?)\*\)', re.S)


def sha(p):
    return hashlib.sha256(open(p, 'rb').read()).hexdigest() if os.path.isfile(p) else '-'


def header(p):
    text = open(p, encoding='utf-8', errors='replace').read(6000)
    mods = [re.sub(r'\s+', ' ', m).strip() for m in MOD.findall(text)]
    mods = [m for m in mods if not m.startswith('ported to rc.2') and not m.startswith('ported to the binaries')]
    if re.match(r'\(\* Machine-generated', text):
        mods = ['machine-generated: ' + (mods[0] if mods else '')]
    return mods


kept = set(os.path.basename(l.split()[0]) for l in open(r1kept) if l.strip())
GEN_A = {'AB01.v', 'AB03.v', 'AF0m.v', 'AD2j.v', 'AE3i.v', 'ACej.v', 'AB1w.v'}
rows = []
for sub, pat in (('A', r'^A.*\.v$'), ('B', r'^Y.*\.v$'), ('A/Rt', r'.*\.v$'), ('B/Rt', r'.*\.v$'), ('Reusable', r'.*\.v$')):
    d = os.path.join(ours, sub)
    for f in sorted(os.listdir(d)):
        p = os.path.join(d, f)
        if not (os.path.isfile(p) and re.match(pat, f)):
            continue
        mods = header(p)
        h = ' | '.join(mods)[:300].replace('\t', ' ')
        s_ours, s_merged = sha(p), sha(os.path.join(merged, sub, f))
        old = '-'
        if sub == 'A':
            twin = f
            if os.path.isfile(os.path.join(a1, 'A', f)):
                st, old = 'A1 core run (port_core blob bebe64d6f526)', sha(os.path.join(a1, 'A', f))
            elif os.path.isfile(os.path.join(a2, 'A', f)):
                st, old = 'A2 runtime run (port_core blob bebe64d6f526)', sha(os.path.join(a2, 'A', f))
            else:
                st = 'not a port_core output (written for this unit)'
            if f in GEN_A:
                st += '; regenerated from image A by the unit generator'
            route = 'value gate RA (check of record) + d9e0 --dry diff' if 'run' in st else 'value gate RA where paired'
        elif sub == 'B':
            st = 'B relay of the A twin (a2b / relay, not port_core)' if any('this harness' in m for m in mods) else (
                'B start-up set (collector / generator for image B)' if f.startswith('YB') else 'B file (see header)')
            if 'Y' + f[1:] in ():
                pass
            if f.replace('Y', 'A', 1) in GEN_A:
                st += '; regenerated from image B by the unit generator'
            route = 'value gate RB (check of record) + relay view RAB'
        elif sub in ('A/Rt', 'B/Rt'):
            joined = ' '.join(mods)
            if re.search(r'(copied|made|adapted) from proofs/', joined) and re.search(r'moved|entry moved|addresses', joined):
                st = 'runtime relocation from a donor file (header names it)'
                route = 'value gate on the donor pairing (Rt runs)'
            elif 'this harness' in joined:
                st = 'B twin of a lib/A/Rt file (reloc_rt.py over a2b)'
                route = 'value gate on the donor pairing (Rt runs) / relay'
            else:
                st = 'runtime proof written for this unit'
                route = 'not a port_core output'
        else:
            dn = os.path.isfile(os.path.join(donor, f))
            if os.path.isfile(os.path.join(r1, 'Reusable', f)):
                same = sha(os.path.join(r1, 'Reusable', f)) == s_ours
                st = 'run 1 non-A copy (untagged port_core, version not identifiable)' + ('' if same else '; edited after')
                old = sha(os.path.join(r1, 'Reusable', f))
            elif f in kept:
                st = 'kept by run 1 (copied earlier from the donor model files)'
            elif dn:
                st = 'donor model file copied (not by the runs above)'
            else:
                st = 'no donor file of that name (written for this unit or from another donor)'
            route = 'value gate RU' if dn else 'not a cgif port_core output'
        rows.append((sub, f, st, route, s_ours[:12], s_merged[:12], old[:12], h))

with open(out, 'w') as fh:
    fh.write('dir\tfile\tset\troute\tsha256_checked\tsha256_merged\tsha256_run_stage_out\theader_provenance\n')
    for r in rows:
        fh.write('\t'.join(r) + '\n')
c = Counter((r[0], r[2]) for r in rows)
for k in sorted(c):
    print(*k, c[k], sep='\t')
