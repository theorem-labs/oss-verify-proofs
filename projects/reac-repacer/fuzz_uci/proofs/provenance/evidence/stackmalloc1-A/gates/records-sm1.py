#!/usr/bin/env python3
"""records-sm1.py OUTDIR GATEDIR WORK BUILD_LOG BUILD_CONTROL_LOG PA_LOG PA_SRC FIT_LOG FIT_SRC: write this slice's gate
records from the raw outputs of run-gates.sh (GATEDIR) and four cb logs (the build of record, the planted build control,
the Print Assumptions scratch build and the consumer-fit scratch build) with the two scratch files' sources,
host-path free: GATEDIR -> <gates>, WORK -> <work>, a build VM's name -> <vm>, any other absolute path -> <file>;
nothing else is changed. The image-B record's records-sm1.py with image B -> image A, the flag gate's two checkers and
planted pointers, the bytecmp controls 3 to 6 and the consumer-fit record. A scratch build's LOG and SRC given as `-`
leave its record (print-assumptions.txt, consumer-fit.txt) as it is: a re-run of the gates alone does not rebuild the
scratch files. Output files (OUTDIR):
  bytecmp-bodies.out, bytecmp-bodies-b-tool.out, bytecmp-control-1.out .. -6.out   bytecmp.py's output, the same with
                         --no-addi0 (the image-B tool), and the six plants
  sites-target.out, sites-donor.out   sites.py on the two twins
  flag-gate.txt          FLAGGED / FLAG-CLASSES / checker lines of the record run and the two planted runs, for
                         port_addr_check efa19b81e92b (of record) and e165063a0081, with the triage summaries
  flag-triage.tsv        triage-sm1.py's per-row reasons of the efa19b81e92b record run
  codeptr.txt            codeptr's per-file lines and rc, per run (base, declared, donor, plant, plant-declared)
  atable-replacement.txt keyset classes (uci A, grant A), keyset check, the range-table check and its two plants
  byvalue.txt            the by-value check's summary: record (with the declaration), undeclared, planted control
  byvalue-rows.tsv, byvalue-review.tsv   its per-numeral table and review rows of the record run
  settings-count.txt     v10 (global_settings 439f8e3bd463) reported rows and SUMMARY: the files, the donor's released
                         counterparts, the planted control
  yh03check.txt          yh03check ca63d81d7725 on the files (N/A) and its two known-answer controls
  build.txt              cb build of record: mode, pins, the .vo lines of the three files, rc; the planted control's failure
  print-assumptions.txt  the scratch file and its Check + Print Assumptions of stack_malloc1_contract
  consumer-fit.txt       the scratch file stating the consumer's hypothesis type under its bindings, closed by exact"""
import os, re, shutil, sys

out, g, work, blog, ctllog, palog, pasrc, fitlog, fitsrc = sys.argv[1:10]
os.makedirs(out, exist_ok=True)


def neutral(s):
    s = s.replace(g, '<gates>').replace(work, '<work>')
    s = re.sub(r'\b(?:ossv-)?(?:open-u\d+|decbox-a\d+-v\d+)\b', '<vm>', s)
    return re.sub(r'(?<![\w.<])/(?:[\w.+-]+/)+[\w.+-]+', '<file>', s)


def lines(p):
    return open(p, errors='replace').read().splitlines()


def keep(p, pred):
    return [neutral(l) for l in lines(p) if pred(l)]


def section(fh, tag, ls):
    fh.write(f'# {tag}\n' + '\n'.join(ls) + '\n')


for src, dst in [('bytecmp.out', 'bytecmp-bodies.out'), ('bytecmp-b-tool.out', 'bytecmp-bodies-b-tool.out')] + \
        [(f'bytecmp-plant{k}.out', f'bytecmp-control-{k}.out') for k in range(1, 7)] + \
        [('sites-target.out', 'sites-target.out'), ('sites-donor.out', 'sites-donor.out')]:
    open(f'{out}/{dst}', 'w').write('\n'.join(neutral(l) for l in lines(f'{g}/{src}')) + '\n')
with open(f'{out}/flag-gate.txt', 'w') as fh:
    for ck, role in (('efa19b81e92b', 'of record'), ('e165063a0081', 'the checker it replaces, beside it')):
        for t, tag in (('rec', 'record run (donor = stage/, ported = the committed files)'),
                       ('loop', 'control, a code pointer: AF0r.v FS_LOOP planted as the donor\'s 0x3cfac'),
                       ('tsd', 'control, a data pointer: AF0r.v TSD planted as the donor\'s 0x5f8e78')):
            section(fh, f'{ck} ({role}): {tag}',
                    keep(f'{g}/{ck}-{t}.log', lambda l: l.startswith(('FLAGGED', 'FLAG-CLASSES', 'checker'))) +
                    [neutral(l) for l in lines(f'{g}/{ck}-{t}.triage.out')])
shutil.copy(f'{g}/efa19b81e92b-rec.triage.tsv', f'{out}/flag-triage.tsv')
with open(f'{out}/codeptr.txt', 'w') as fh:
    for run, tag in (('base', 'the files on fuzz_uci.asan, stale against fuzz_grant.asan (each file\'s donor text)'),
                     ('declared', 'the same with the --not-address declarations of codeptr-notaddr-sm1.tsv'),
                     ('donor', 'control: the donor text on its own image (the tool\'s baseline)'),
                     ('plant', 'control: AF0r.v FS_ENTRY planted as the donor\'s 0x3cf18'),
                     ('plant-declared', 'control: the same plant under the declarations')):
        section(fh, f'{run}: {tag}', keep(f'{g}/codeptr-{run}.out',
                                         lambda l: re.match(r'[AY]\w+\.v\s', l) or l.startswith(('codeptr:', 'rc='))))
with open(f'{out}/atable-replacement.txt', 'w') as fh:
    fh.write('# atable: N/A for these files. atable.py 42e18a7eef50 only emits the start-up layer\'s atable record; AF0r /\n'
             '# AF0s / YF0v state no atable field. In its place: keyset (f050b43e480e) and the keyed range-table check of\n'
             '# fs_ranges (rangetab-sm1.py).\n')
    for tag, p in (('keyset classes, fuzz_uci.asan', 'keyset-classes-uciA.out'),
                   ('keyset classes, fuzz_grant.asan (control: the donor image)', 'keyset-classes-grantA.out'),
                   ('keyset check over the three files', 'keyset-check-uciA.out')):
        section(fh, tag, keep(f'{g}/{p}', lambda l: not l.startswith('frozen-run')))
    for tag, p in (('range-table check of fs_ranges, the committed AF0r.v', 'rangetab-rec.out'),
                   ('control: row (0x60904, 2) planted as (0x60908, 2)', 'rangetab-plant-offset.out'),
                   ('control: row (0x68358, 140) planted as (0x68358, 141)', 'rangetab-plant-count.out')):
        section(fh, tag, [neutral(l) for l in lines(f'{g}/{p}')])
with open(f'{out}/byvalue.txt', 'w') as fh:
    for tag, p in (('record run (--declare FS_FROFF 0x109000)', 'decval.out'), ('the same without the declaration', 'decval-undeclared.out'),
                   ('control: AF0r.v FS_ENTRY planted as the donor\'s 0x3cf18', 'decval-control.out')):
        section(fh, tag, [neutral(l) for l in lines(f'{g}/{p}')])
shutil.copy(f'{g}/decval.tsv', f'{out}/byvalue-rows.tsv')
shutil.copy(f'{g}/decval-review.tsv', f'{out}/byvalue-review.tsv')
with open(f'{out}/settings-count.txt', 'w') as fh:
    for tag, p in (('the three files', 'v10-uciA.out'), ("fuzz_grant's released counterparts (recipes 4f87de75d67)", 'v10-grant-counterparts.out'),
                   ('control: a second global Zify flag line planted in AF0s.v', 'v10-plant.out')):
        section(fh, tag, keep(f'{g}/{p}', lambda l: l.startswith(('SUMMARY', 'TOOL', 'read ', '   :', 'rc='))))
with open(f'{out}/yh03check.txt', 'w') as fh:
    for tag, p in (('the three files: no src0_ row, so nothing to check (N/A)', 'yh03check.out'),
                   ('control: a src0_ row at __asan_stack_malloc_1 (right)', 'yh03check-control-ok.out'),
                   ('control: the same row with A off by 4 (planted)', 'yh03check-control-bad.out')):
        section(fh, tag, [neutral(l) for l in lines(f'{g}/{p}')])
VO = ('lib/Reusable/YF0v.vo', 'lib/A/Rt/AF0r.vo', 'lib/A/Rt/AF0s.vo')
with open(f'{out}/build.txt', 'w') as fh:
    section(fh, 'cb build of the three .vo (the build of record; CB_COMPILE: each target compiled, the cache not consulted)',
            keep(blog, lambda l: l.startswith(('cb-cache:', 'cb: pin', 'cb: target', 'cb-dune: phase', 'rc=')) or
                 (any(v in l for v in VO) and '(real' in l)))
    section(fh, 'control: AF0r.v cell (0x9e860, ...) planted as (0x9e868, ...), the same build (reverted after)',
            keep(ctllog, lambda l: l.startswith(('cb-cache:', 'cb: target', 'rc=', 'File ', 'Error', 'Unable')) or '(real' in l and 'AF0r' in l))


def scratch(logp, srcp, name):
    t = open(logp).read()
    i = t.find(name + '.{glob,vo}\n')
    body = t[i + len(name + '.{glob,vo}\n'):]
    keepl = [l for l in body.splitlines()
             if not l.startswith(('        rocq ', 'File ', 'Warning', '"Abbreviation"', '[notation', 'proofs/')) or name in l]
    keepl = [l for l in keepl if not (l.startswith('proofs/') and name not in l)]
    return open(srcp).read(), '\n'.join(neutral(l) for l in keepl)


if palog != '-':
    src, body = scratch(palog, pasrc, 'ScratchSm1A')
    open(f'{out}/print-assumptions.txt', 'w').write(
        '# Check + Print Assumptions of stack_malloc1_contract, and the consumer\'s hypothesis type closed by exact (an\n'
        '# uncommitted scratch file lib/A/ScratchSm1A.v, built by `CB_COMPILE=<it> cb build` on this branch and deleted;\n'
        '# 14 axioms, every one in toolchain/allowed-axioms.txt)\n## the scratch file\n' + src +
        '## its compile output (the build log\'s lines after it)\n' + body + '\n')
if fitlog != '-':
    src, body = scratch(fitlog, fitsrc, 'ZSm1Fit')
    open(f'{out}/consumer-fit.txt', 'w').write(
        '# The consumer\'s hypothesis closed by exact, on a scratch merge (never pushed) of the consumer\'s commit 9ee6811b6c95\n'
        '# (lib/A/UciClose.v:143 H_RT_STACK_MALLOC1, bindings segs := ucisegs0, B := AD2l.UciB) with this branch at 8d60aff2fa87:\n'
        '# the merge had no conflict; the scratch file lib/A/ZSm1Fit.v below states the hypothesis\'s type verbatim under\n'
        '# UciClose.v\'s two bindings and closes it by exact of stack_malloc1_contract. Built by `CB_COMPILE=<it> cb build`.\n'
        '## the scratch file\n' + src + '## its compile output (the build log\'s lines after it)\n' + body + '\n')
for f in sorted(os.listdir(out)):
    s = open(f'{out}/{f}').read()
    n = len(re.findall(r'/(?:home|mnt|tmp|data|srv)/|ts\.net', s))
    print(f'{f}: {len(s.splitlines())} lines, host-path matches {n}')
