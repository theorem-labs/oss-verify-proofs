#!/usr/bin/env python3
"""Planted controls for checks.py: each control copies the d9e0589898fd work directory, plants one defect, and
requires checks.py to FAIL the named check (and only report a planted defect, never miss it).

Usage: controls.py --work D9E0_WORK [checks.py arguments other than --work / --out-dir] --scratch DIR

Controls (one per check, plus the classification):
  classify  any byte edit of a staged file                         -> classify row DIFFERS
  1         a donor segment size (seg1.size, 0x6d000) stated         -> check 1 FAIL
  2         the donor GOT[0] cell address (0x9e1a8) stated            -> check 2 FAIL
  3         a numeral with no role (0x5a5a5a5a)                      -> check 3 FAIL
  4         a no-twin row naming a function the target links (memcmp) -> check 4 FAIL
The planted lines are appended after the file's last sentence, outside every comment.
"""
import argparse
import os
import shutil
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
CONTROLS = [
    ('1', 'append', 'YE6t.v', '\nDefinition ctl_seg : Z := 0x6d000.\n', '1 kept image-derived counts'),
    ('2', 'append', 'YE6t.v', '\nDefinition ctl_got : Z := 0x9e1a8.\n', '2 GOT[0]'),
    ('3', 'append', 'YE6t.v', '\nDefinition ctl_bad : Z := 0x5a5a5a5a.\n', '3 shadow offsets and model constants by role'),
    ('4', 'notwin', None, 'Reusable/YE6t.v\t10\t0x41934\tcontrol\t0x41934\tmemcmp\n', "4 'no twin' drops"),
]


def run(args, work, out):
    os.makedirs(out, exist_ok=True)
    cmd = [sys.executable, os.path.join(HERE, 'checks.py'), '--work', work, '--out-dir', out] + args
    p = subprocess.run(cmd, capture_output=True, text=True)
    verdicts = {}
    for line in open(os.path.join(out, 'checks.tsv')):
        if not line.startswith('#'):
            f = line.rstrip('\n').split('\t')
            verdicts[f[0]] = f[-1]
    differs = sum(1 for line in open(os.path.join(out, 'classify.tsv')) if line.rstrip('\n').endswith('\tDIFFERS'))
    return p.returncode, verdicts, differs


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--work', required=True)
    p.add_argument('--scratch', required=True)
    a, rest = p.parse_known_args()
    rc, base, differs = run(rest, a.work, os.path.join(a.scratch, 'base'))
    if rc or differs or any(v != 'PASS' for v in base.values()):
        sys.exit(f'controls.py: the unplanted run does not pass (rc {rc}, differs {differs}, {base})')
    failed = []
    for name, how, f, text, check in CONTROLS:
        w = os.path.join(a.scratch, f'ctl-{name}', 'work')
        shutil.rmtree(os.path.dirname(w), ignore_errors=True)
        shutil.copytree(a.work, w)
        if how == 'append':
            with open(os.path.join(w, 'stage-out', 'Reusable', f), 'a') as fh:
                fh.write(text)
        else:
            nt = os.path.join(w, 'no-twin.tsv')
            head = open(nt).read().split('\n')[0]
            open(nt, 'w').write(head + '\n' + text)
        rc, v, differs = run(rest, w, os.path.join(a.scratch, f'ctl-{name}', 'out'))
        ok = rc == 1 and v.get(check) == 'FAIL' and (how != 'append' or differs == 1)
        print(f'control {name}: {check}: {v.get(check)}, classify DIFFERS {differs}, rc {rc}: {"caught" if ok else "MISSED"}')
        if not ok:
            failed.append(name)
        shutil.rmtree(os.path.dirname(w))
    if failed:
        sys.exit('controls.py: missed ' + ' '.join(failed))
    print(f'controls: {len(CONTROLS)} of {len(CONTROLS)} caught (classification caught every append control)')


if __name__ == '__main__':
    main()
