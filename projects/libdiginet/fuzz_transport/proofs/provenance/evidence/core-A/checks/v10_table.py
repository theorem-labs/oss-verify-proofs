#!/usr/bin/env python3
"""v10_table.py RUN GS LIB DONWT OUT [FILES] -- global_settings v10 (439f8e3bd463) over the files this core relocation adds,
and over their released donor files; write the row table (OUT) and print both SUMMARY lines.

  RUN      the relocation run dir (run.sh's WORK): the files this core adds are its stage-out/A/*.v and
           stage-out/Reusable/*.v (run.sh: A/ files always, a non-A file only when LIB lacks it; a non-A file LIB
           holds with other bytes is printed as `kept by LIB` and not read)
  GS       global_settings.py (sha256 439f8e3bd463..., beside its SHA256SUMS and control files)
  LIB      the unit's lib (proofs/libdiginet/fuzz_transport/lib, the lib the run used): its Reusable/YImgTop.v (taken by
           path) is added
  DONWT    a tree holding fuzz_grant's released lib at 25e3d17bdb50 (proofs/libreac/fuzz_grant/lib, NOT normalised)
  OUT      the row table
  FILES    (optional) the list of the files read, one lib-relative path a line

The files read are copied to a scratch tree as proofs/libdiginet/fuzz_transport/lib/<file> (the path they take in the
unit). Every row of a target file is paired with the identical setting (same class, level and text) of its donor file,
in order; the donor of lib/A/X.v is fuzz_grant's lib/A/X.v, of lib/Reusable/X.v fuzz_grant's lib/Reusable/X.v. A row
with no identical donor row is printed as UNPAIRED (exit 1); a KERNEL row (global_settings exit 5) is a row too, and
no donor file has one. The donor rows left with no target row are printed as DONOR-ONLY, by file and setting.
rule: proves no function (kind: measurement)."""
import collections
import filecmp
import os
import re
import shutil
import subprocess
import sys
import tempfile

RUN, GS, LIB, DONWT, OUT = sys.argv[1:6]
FILES = sys.argv[6] if len(sys.argv) > 6 else None
TL = 'proofs/libdiginet/fuzz_transport/lib/'
DL = 'proofs/libreac/fuzz_grant/lib/'
SO = os.path.join(RUN, 'stage-out')
files, kept = [], []
for top in ('A', 'Reusable'):
    for d, _, fs in os.walk(os.path.join(SO, top)):
        for n in fs:
            if not n.endswith('.v'):
                continue
            rel = os.path.relpath(os.path.join(d, n), SO)
            mine = os.path.join(LIB, rel)
            if top != 'A' and os.path.exists(mine) and not filecmp.cmp(mine, os.path.join(SO, rel), shallow=False):
                kept.append(rel)
                continue
            files.append(rel)
files.sort()
staged = len(files)
files.append('Reusable/YImgTop.v')
if FILES:
    open(FILES, 'w').write(''.join(f + '\n' for f in files))
ROW = re.compile(r'^   :(\d+) (?:(\w+) (\w+)|(KERNEL)): (.*)$')


def run(root, rels):
    r = subprocess.run([sys.executable, GS, root] + rels, capture_output=True, text=True)
    rows, cur, summary = collections.defaultdict(list), None, None
    for line in r.stdout.splitlines():
        m = re.match(r'^read (\S+): ', line)
        if m:
            cur = m.group(1)
            continue
        m = ROW.match(line)
        if m and cur:
            cls, lvl = (m.group(2), m.group(3)) if m.group(2) else ('KERNEL', 'KERNEL')
            rows[cur].append((int(m.group(1)), cls, lvl, m.group(5)))
        if line.startswith('SUMMARY:'):
            summary = line
    return r.returncode, summary, rows


with tempfile.TemporaryDirectory() as tmp:
    for f in files:
        src = os.path.join(LIB if f == 'Reusable/YImgTop.v' else SO, f)
        dst = os.path.join(tmp, TL, f)
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        shutil.copyfile(src, dst)
    trc, tsum, trows = run(tmp, [TL + f for f in files])
drc, dsum, drows = run(DONWT, [DL + f for f in files])
unpaired, donor_only = 0, collections.Counter()
with open(OUT, 'w') as fh:
    fh.write(f'# v10 global_settings 439f8e3bd463 on the files this core adds (the {staged} files of the run\'s stage-out\n'
             '# A/ and Reusable/, and Reusable/YImgTop.v taken by path), each row with the identical setting of its\n'
             '# released donor file (fuzz_grant at 25e3d17bdb50).\n')
    fh.write(f'# target: {tsum} (rc {trc})\n# donor:  {dsum} (rc {drc})\n')
    fh.write('file\tline\tclass\tlevel\tdonor_released_file@25e3d17bdb50\tdonor_line\tsetting\n')
    for f in files:
        pool = list(drows.get(DL + f, []))
        for ln, cls, lvl, txt in trows.get(TL + f, []):
            k = next((i for i, d in enumerate(pool) if d[1:] == (cls, lvl, txt)), None)
            if k is None:
                unpaired += 1
                fh.write(f'{f}\t{ln}\t{cls}\t{lvl}\tUNPAIRED\t-\t{txt}\n')
                print(f'UNPAIRED {f}:{ln} {cls} {lvl}: {txt}')
                continue
            d = pool.pop(k)
            fh.write(f'{f}\t{ln}\t{cls}\t{lvl}\t{DL}{f}\t{d[0]}\t{txt}\n')
        for _, cls, lvl, txt in pool:
            donor_only[(f, cls, lvl, txt)] += 1
for f in kept:
    print(f'kept by LIB (not added, not read): {f}')
for (f, cls, lvl, txt), n in sorted(donor_only.items()):
    print(f'DONOR-ONLY {f}: {n} x {cls} {lvl}: {txt}')
print('files read:', len(files), f'(stage-out {staged} + Reusable/YImgTop.v); kept by LIB:', len(kept))
print('target:', tsum, 'rc', trc)
print('donor: ', dsum, 'rc', drc)
print('unpaired target rows:', unpaired)
print('donor rows with no target row:', sum(donor_only.values()))
sys.exit(1 if unpaired or trc or drc else 0)
