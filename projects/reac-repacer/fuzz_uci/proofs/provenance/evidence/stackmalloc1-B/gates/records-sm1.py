#!/usr/bin/env python3
"""records-sm1.py OUTDIR GATEDIR WORK BUILD_LOG PA_LOG BUILD_CONTROL_LOG: write this slice's gate records from the raw
outputs of run-gates.sh (GATEDIR) and three cb logs (the build of record, the Print Assumptions scratch build, the
planted build control), host-path free: GATEDIR -> <gates>, WORK -> <work>, a build VM's name -> <vm>, any other
absolute path -> <file>; nothing
else is changed. Output files (OUTDIR):
  bytecmp-bodies.out, bytecmp-control-1.out, bytecmp-control-2.out   bytecmp.py's output, unplanted and the two plants
  flag-gate.txt          FLAGGED / FLAG-CLASSES / checker lines of the record run and the planted run, triage summaries
  flag-triage.tsv        triage-sm1.py's per-row reasons of the record run
  codeptr.txt            codeptr's per-file lines and rc, per run (base, declared, donor, plant, plant-declared)
  atable-replacement.txt keyset classes (uci B, grant B), keyset check, the range-table check and its two plants
  byvalue.txt            the by-value check's summary: record (with the declaration), undeclared, planted control
  byvalue-rows.tsv, byvalue-review.tsv   its per-numeral table and review rows of the record run
  settings-count.txt     v10 (global_settings 439f8e3bd463) reported rows and SUMMARY: the files, the donor's released
                         counterparts, the planted control
  yh03check.txt          yh03check ca63d81d7725 on the files (N/A) and its two known-answer controls
  build.txt              cb build of record: mode, pins, the .vo lines of the three files, rc; the planted control's failure
  print-assumptions.txt  Check + Print Assumptions of stack_malloc1_contract (the uncommitted scratch file's output)"""
import os, re, shutil, sys

out, g, work, blog, palog, ctllog = sys.argv[1:7]
os.makedirs(out, exist_ok=True)


def neutral(s):
    s = s.replace(g, '<gates>').replace(work, '<work>')
    s = re.sub(r'\b(?:ossv-)?open-u\d+\b', '<vm>', s)
    return re.sub(r'(?<![\w.<])/(?:[\w.+-]+/)+[\w.+-]+', '<file>', s)


def lines(p):
    return open(p, errors='replace').read().splitlines()


def keep(p, pred):
    return [neutral(l) for l in lines(p) if pred(l)]


def section(fh, tag, ls):
    fh.write(f'# {tag}\n' + '\n'.join(ls) + '\n')


for src, dst in (('bytecmp.out', 'bytecmp-bodies.out'), ('bytecmp-plant1.out', 'bytecmp-control-1.out'),
                 ('bytecmp-plant2.out', 'bytecmp-control-2.out')):
    open(f'{out}/{dst}', 'w').write('\n'.join(neutral(l) for l in lines(f'{g}/{src}')) + '\n')
with open(f'{out}/flag-gate.txt', 'w') as fh:
    for tag, p in (('record run (donor = stage/, ported = the committed files)', 'e165-rec'),
                   ('control: YF0r.v FS_LOOP planted as the donor\'s 0x3d154', 'e165-plant')):
        section(fh, tag, keep(f'{g}/{p}.log', lambda l: l.startswith(('FLAGGED', 'FLAG-CLASSES', 'checker'))) +
                [neutral(l) for l in lines(f'{g}/{p}.triage.out')])
shutil.copy(f'{g}/e165-rec.triage.tsv', f'{out}/flag-triage.tsv')
with open(f'{out}/codeptr.txt', 'w') as fh:
    for run, tag in (('base', 'the files on fuzz_uci.asan-ubsan, stale against fuzz_grant.asan-ubsan (each file\'s donor text)'),
                     ('declared', 'the same with the --not-address declarations of codeptr-notaddr-sm1.tsv'),
                     ('donor', 'control: the donor text on its own image (the tool\'s baseline)'),
                     ('plant', 'control: YF0r.v FS_ENTRY planted as the donor\'s 0x3d0c0'),
                     ('plant-declared', 'control: the same plant under the declarations')):
        section(fh, f'{run}: {tag}', keep(f'{g}/codeptr-{run}.out',
                                         lambda l: re.match(r'Y\w+\.v\s', l) or l.startswith(('codeptr:', 'rc='))))
with open(f'{out}/atable-replacement.txt', 'w') as fh:
    fh.write('# atable: N/A for these files. atable.py 42e18a7eef50 only emits the YB12 atable record; YF0r / YF0s / YF0v\n'
             '# state no atable field and Require no YB12. In its place: keyset (f050b43e480e) and the keyed range-table\n'
             '# check of fs_ranges (rangetab-sm1.py).\n')
    for tag, p in (('keyset classes, fuzz_uci.asan-ubsan', 'keyset-classes-uciB.out'),
                   ('keyset classes, fuzz_grant.asan-ubsan (control: the donor image)', 'keyset-classes-grantB.out'),
                   ('keyset check over the three files', 'keyset-check-uciB.out'),
                   ('observation, not this slice: keyset check over the image-B core\'s lib/B/YF0l.v', 'keyset-check-YF0l.out')):
        section(fh, tag, keep(f'{g}/{p}', lambda l: not l.startswith('frozen-run')))
    for tag, p in (('range-table check of fs_ranges, the committed YF0r.v', 'rangetab-rec.out'),
                   ('control: row (0x60904, 2) planted as (0x60908, 2)', 'rangetab-plant-offset.out'),
                   ('control: row (0x68358, 140) planted as (0x68358, 141)', 'rangetab-plant-count.out')):
        section(fh, tag, [neutral(l) for l in lines(f'{g}/{p}')])
with open(f'{out}/byvalue.txt', 'w') as fh:
    for tag, p in (('record run (--declare FS_FROFF 0x109000)', 'decval.out'), ('the same without the declaration', 'decval-undeclared.out'),
                   ('control: YF0r.v FS_ENTRY planted as the donor\'s 0x3d0c0', 'decval-control.out')):
        section(fh, tag, [neutral(l) for l in lines(f'{g}/{p}')])
shutil.copy(f'{g}/decval.tsv', f'{out}/byvalue-rows.tsv')
shutil.copy(f'{g}/decval-review.tsv', f'{out}/byvalue-review.tsv')
with open(f'{out}/settings-count.txt', 'w') as fh:
    for tag, p in (('the three files', 'v10-uciB.out'), ("fuzz_grant's released counterparts (recipes 4f87de75d67)", 'v10-grant-counterparts.out'),
                   ('control: YF0s.v\'s #[local] Zify flag made global', 'v10-plant.out')):
        section(fh, tag, keep(f'{g}/{p}', lambda l: l.startswith(('SUMMARY', 'TOOL', 'read ', '   :', 'rc='))))
with open(f'{out}/yh03check.txt', 'w') as fh:
    for tag, p in (('the three files: no src0_ row, so nothing to check (N/A)', 'yh03check.out'),
                   ('control: a src0_ row at __asan_stack_malloc_1 (right)', 'yh03check-control-ok.out'),
                   ('control: the same row with A off by 4 (planted)', 'yh03check-control-bad.out')):
        section(fh, tag, [neutral(l) for l in lines(f'{g}/{p}')])
VO = ('lib/Reusable/YF0v.vo', 'lib/B/Rt/YF0r.vo', 'lib/B/Rt/YF0s.vo')
with open(f'{out}/build.txt', 'w') as fh:
    section(fh, 'cb build of the three .vo (the build of record)', keep(blog, lambda l: l.startswith(('cb-cache:', 'cb: pin', 'cb: target', 'rc=')) or
                                                                         (any(v in l for v in VO) and '(real' in l)))
    section(fh, 'control: YF0r.v cell (0x9e960, ...) planted as (0x9e968, ...), the same build (reverted after)',
            keep(ctllog, lambda l: l.startswith(('cb-cache:', 'cb: target', 'rc=', 'File ', 'Error', 'Unable')) or '(real' in l and 'YF0r' in l))
t = open(palog).read()
i, j = t.find('stack_malloc1_contract\n'), t.find('ZPaSm1.vo (real')
pa = t[i:t.rfind('\n', 0, j)]
open(f'{out}/print-assumptions.txt', 'w').write(
    '# Check + Print Assumptions YF0s.stack_malloc1_contract, from an uncommitted scratch file lib/B/Rt/ZPaSm1.v built by cb\n'
    '# (CB_COMPILE) and deleted; every axiom is in toolchain/allowed-axioms.txt\n' + neutral(pa) + '\n')
for f in sorted(os.listdir(out)):
    s = open(f'{out}/{f}').read()
    n = len(re.findall(r'/(?:home|mnt|tmp|data|srv)/|ts\.net', s))
    print(f'{f}: {len(s.splitlines())} lines, host-path matches {n}')
