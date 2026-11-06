#!/usr/bin/env python3
"""records-B.py OUTDIR GATEDIR WORK: write the gate records of this slice from the raw outputs of pac-B.sh, codeptr-B.sh,
triage-B.py, decval-B.py and global_settings.py (all under GATEDIR), host-path free: every absolute path is replaced by
a role name (<work> for WORK, <file> for any other absolute path), nothing else is changed. Output files:
  flag-gate.txt          the FLAGGED / FLAG-CLASSES lines of the record run and of the two planted controls
  flag-triage.tsv        one line per flagged or GENERATOR-FILL row with its reason (triage-B.py)
  codeptr.txt            codeptr's per-file lines with findings and the closing line, per run (donor / plant / declared /
                         plant-declared)
  byvalue.txt            decval-B.py's summary of the record run and of the planted control
  byvalue-rows.tsv       decval-B.py's per-numeral table of the record run
  settings-count.txt     global_settings 439f8e3bd463 SUMMARY of this core and of fuzz_grant's released counterparts"""
import os, re, shutil, sys

out, g, work = sys.argv[1:4]
os.makedirs(out, exist_ok=True)


def neutral(s):
    s = s.replace(work, '<work>')
    return re.sub(r'(?<![\w.<])/(?:[\w.+-]+/)+[\w.+-]+', '<file>', s)


def lines(p):
    return open(p, errors='replace').read().splitlines()


def keep(p, pred):
    return [neutral(l) for l in lines(p) if pred(l)]


with open(f'{out}/flag-gate.txt', 'w') as fh:
    for tag, p in (('record run', 'efa1-rec5.log'),
                   ('control: YF0l.v pc_wrap_memcpy planted as 0x86980 (abort)', 'cb0e-plant2/efa1-out.log'),
                   ('control: YF0l.v pc_wrap_memcpy planted as 0x50674 (pc_asan_memcpy, a value of the same sentence)',
                    'cb0e-plant2/efa1-dup.log'),
                   ('control: the same file unplanted', 'cb0e-plant2/efa1-clean.log')):
        fh.write(f'# {tag}\n')
        fh.write('\n'.join(keep(f'{g}/{p}', lambda l: l.startswith(('FLAGGED', 'FLAG-CLASSES', 'checker')))) + '\n')
shutil.copy(f'{g}/efa1-rec5.triage.tsv', f'{out}/flag-triage.tsv')
with open(f'{out}/codeptr.txt', 'w') as fh:
    for run in ('donor', 'plant', 'declared', 'plant-declared'):
        fh.write(f'# {run}\n')
        fh.write('\n'.join(keep(f'{g}/codeptr-rec4/{run}.out',
                                lambda l: re.search(r'[1-9]\d* FINDINGS', l) or l.startswith(('codeptr: UNMEASURED', 'rc=')))) + '\n')
with open(f'{out}/byvalue.txt', 'w') as fh:
    for tag, p in (('record run', 'decval-B.out'), ('control: YB1w.v tfib_at_x_memset put back to fuzz_grant B memset 0x96c94', 'decval-ctrl.out')):
        fh.write(f'# {tag}\n' + '\n'.join(neutral(l) for l in lines(f'{g}/{p}')) + '\n')
shutil.copy(f'{g}/decval-B.tsv', f'{out}/byvalue-rows.tsv')
with open(f'{out}/settings-count.txt', 'w') as fh:
    for tag, p in (('this core (370 lib/B files) + lib/Reusable/YA09.v and YA0e.v', 'v10-uciB.out'),
                   ("fuzz_grant's released counterparts of the 370 (recipes 4f87de75d67)", 'v10-grantB-counterparts.out')):
        fh.write(f'# {tag}\n' + '\n'.join(keep(f'{g}/{p}', lambda l: l.startswith(('SUMMARY', 'TOOL')))) + '\n')
for f in sorted(os.listdir(out)):
    t = open(f'{out}/{f}').read()
    n = len(re.findall('|'.join('/%s/' % d for d in ('home', 'mnt', 'tmp', 'data', 'srv')) + r'|ts\.net', t))
    print(f'{f}: {len(t.splitlines())} lines, host-path matches {n}')
