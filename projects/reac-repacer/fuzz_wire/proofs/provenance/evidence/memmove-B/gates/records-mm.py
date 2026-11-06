#!/usr/bin/env python3
"""records-mm.py OUTDIR GATEDIR: write this row's gate records from the raw outputs of run-gates.sh (GATEDIR), host-path
free: GATEDIR -> <gates>, any other absolute path -> <file>; nothing else is changed (records-sm1.py's rule). Files:
  measure.out             measure-mm.py: the values the triage reasons cite, read out of both images
  flag-gate.txt           port_addr_check efa19b81e92b: inputs, per-verdict counts, FLAG-CLASSES / FLAGGED / checker lines
                          of the record run and the two planted runs, and triage-mm.py's summaries
  flag-triage.tsv         triage-mm.py's rows of the record run (flagged rows: none; the 60 expected-class rows)
  codeptr.txt             codeptr's per-file lines and rc, per run (base, declared, donor, plant, plant-declared)
  codeptr-occurrences.tsv every occurrence of each --not-address declaration in the five files
  atable.txt              atable N/A: the name scan of the five files and keyset check over them
  byvalue.txt             the by-value check: record run and planted control
  byvalue-rows.tsv, byvalue-review.tsv   its per-numeral rows and review rows of the record run
  settings-count.txt      v10 (global_settings 439f8e3bd463): reported rows and SUMMARY of the five files, of fuzz_pcap's
                          released counterparts, and of the planted control"""
import os
import re
import sys

out, g = sys.argv[1:3]
g = os.path.realpath(g)
os.makedirs(out, exist_ok=True)


def neutral(s):
    s = s.replace(g, '<gates>')
    return re.sub(r'(?<![\w.<])/(?:[\w.+-]+/)+[\w.+-]+', '<file>', s)


def lines(p):
    return open(p, errors='replace').read().splitlines()


def keep(p, pred):
    return [neutral(l) for l in lines(p) if pred(l)]


def section(fh, tag, ls):
    fh.write(f'# {tag}\n' + '\n'.join(ls) + '\n')


def copy(src, dst):
    open(f'{out}/{dst}', 'w').write('\n'.join(neutral(l) for l in lines(f'{g}/{src}')) + '\n')


copy('measure.out', 'measure.out')
VERDICT = re.compile(r'^[A-Z][A-Z-]+\t\d+')
with open(f'{out}/flag-gate.txt', 'w') as fh:
    for tag, p in (('record run (donor = fuzz_pcap released text with module paths renamed, ported = the committed files)', 'pac-rec'),
                   ("control: MemmoveK.v MM_ENTRY planted as the donor's __asan_memmove 0x51c40", 'pac-plant-entry'),
                   ("control: MemmoveK.v MM_REAL planted as fuzz_wire's LLVMFuzzerTestOneInput 0x7fbf8 (a wrong function)", 'pac-plant-real')):
        section(fh, tag, keep(f'{g}/{p}.log', lambda l: l.startswith(('  image ', '  count ', '  control ', '  DECLARED', '# files',
                                                                        'FLAGGED', 'FLAG-CLASSES', 'checker')) or VERDICT.match(l)) +
                [neutral(l) for l in lines(f'{g}/{p}.triage.out')])
copy('pac-rec.triage.tsv', 'flag-triage.tsv')
with open(f'{out}/codeptr.txt', 'w') as fh:
    for run, tag in (('base', 'the five files on fuzz_wire.asan-ubsan, stale against fuzz_pcap.asan-ubsan (each file\'s donor text)'),
                     ('declared', 'the same with the --not-address declarations of gates/codeptr-notaddr-mm.tsv'),
                     ('donor', 'control: the donor text on its own image (the tool\'s baseline)'),
                     ('plant', 'control: MemmoveK.v MM_ENTRY planted as the donor\'s 0x51c40'),
                     ('plant-declared', 'control: the same plant under the declarations')):
        section(fh, f'{run}: {tag}', keep(f'{g}/codeptr-{run}.out',
                                         lambda l: re.match(r'Memmove\w*\.v\s', l) or l.startswith(('codeptr:', 'rc=', 'frozen-run:   codeptr'))))
copy('codeptr-occurrences.tsv', 'codeptr-occurrences.tsv')
with open(f'{out}/atable.txt', 'w') as fh:
    fh.write('# atable: N/A for these files. atable.py 6a35bb77e745 only emits the per-image atable file (YB12.v for asan-ubsan,\n'
             '# the `atable` record of YK09); the five files state no atable field, Require no YB12 and carry no keyed table\n'
             '# (the name scan and keyset 38b229c6ad08 below).\n')
    section(fh, 'name scan of the five files (YB12, atable*, AB12, stops_more, pc_stack_malloc, pc_asan_*, Tfib_*_shadow, IMG_REGIONS)',
            [neutral(l) for l in lines(f'{g}/atable-scan.out')])
    section(fh, 'keyset check over the five files (start-up set bundle 453349f98b04)',
            keep(f'{g}/keyset-check.out', lambda l: not l.startswith('frozen-run') or l.startswith('frozen-run:   keyset')))
with open(f'{out}/byvalue.txt', 'w') as fh:
    for tag, p in (('record run', 'decval.out'), ("control: MemmoveK.v MM_ENTRY planted as the donor's 0x51c40", 'decval-control.out')):
        section(fh, tag, [neutral(l) for l in lines(f'{g}/{p}')])
copy('decval.tsv', 'byvalue-rows.tsv')
copy('decval-review.tsv', 'byvalue-review.tsv')
with open(f'{out}/settings-count.txt', 'w') as fh:
    for tag, p in (('the five files', 'v10-wireB.out'), ("fuzz_pcap's released counterparts (recipes 5098883da0b)", 'v10-pcap-counterparts.out'),
                   ("control: Memmove.v's Local Zify flag made global", 'v10-plant.out')):
        section(fh, tag, keep(f'{g}/{p}', lambda l: l.startswith(('SUMMARY', 'TOOL', 'read ', '   :', 'rc='))))
for f in sorted(os.listdir(out)):
    s = open(f'{out}/{f}').read()
    n = len(re.findall(r'/(?:home|mnt|tmp|data|srv)/|ts\.net', s))
    print(f'{f}: {len(s.splitlines())} lines, host-path matches {n}')
