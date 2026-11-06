#!/usr/bin/env python3
"""Run the comparison kit's exposure scans on the code-identity record, which was first made with the kit 4bbd3a74be89.

  scans.py luiscan  KIT_DIR PAIRS OUT fm=FM_TWIN TAG=TWIN ...
      luiscan.py --all --fns <every function name PAIRS pairs in some image> on the fm twin and each image twin: the
      rule-8 (lui-built absolute value) exposure of every copy of each name. Writes OUT (the kit's output, verbatim).
  scans.py ambiscan KIT_DIR RECORD OUTDIR [MEASURE ...] -- fm=FM_TWIN TAG=TWIN ...
      Writes OUTDIR/lookups.tsv, one line per function lookup the record made, in the kit's `cmp` row form (name, the
      pair fm:TAG, both addresses, how: by address in the tcmp compares of both kits; by name in the jtcheck runs, in the
      lowest-address compare and in the measurement scripts), then runs ambiscan.py fm-twin TAG-twin on the record, the
      measurement tables and lookups.tsv, writing OUTDIR/ambiscan-TAG.tsv (the kit's output, verbatim).
KIT_DIR: the comparison kit 86da41d3ef68 (its SHA256SUMS is checked). The scans run in a scratch directory that holds
the twins under TAG/<file name> and the scanned files under their names relative to this slice (codeid/...), so the
outputs name no path of the machine they ran on.
"""
import csv
import hashlib
import os
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))


def sha(p):
    return hashlib.sha256(open(p, 'rb').read()).hexdigest()


def kit(d):
    for line in open(os.path.join(d, 'SHA256SUMS')).read().split('\n'):
        if line.strip():
            h, n = line.split(None, 1)
            if sha(os.path.join(d, n.lstrip('*'))) != h:
                sys.exit('scans.py: %s does not match the kit SHA256SUMS' % n)
    return sha(os.path.join(d, 'SHA256SUMS'))[:12]


def stage(images, files=()):
    """a scratch directory holding TAG/<twin file name> for every image and each file under its slice-relative name"""
    t = tempfile.mkdtemp(prefix='scans.')
    rel = []
    for tag, p in images:
        os.makedirs(os.path.join(t, tag))
        os.symlink(os.path.abspath(p), os.path.join(t, tag, os.path.basename(p)))
        rel.append((tag, os.path.join(tag, os.path.basename(p))))
    for p, r in files:
        os.makedirs(os.path.dirname(os.path.join(t, r)), exist_ok=True)
        os.symlink(os.path.abspath(p), os.path.join(t, r))
    return t, rel


def run(d, cwd, tool, args):
    r = subprocess.run([sys.executable, os.path.join(os.path.abspath(d), tool)] + args, cwd=cwd, capture_output=True,
                       text=True, env=dict(os.environ, PYTHONDONTWRITEBYTECODE='1'))
    if r.returncode:
        sys.exit('scans.py: %s exit %d: %s' % (tool, r.returncode, r.stderr[-2000:]))
    return r.stdout


def luiscan(d, pairs, out, images):
    kit(d)
    names = []
    for r in csv.DictReader(open(pairs), delimiter='\t'):
        if r['pairing'] != 'absent' and r['fm function'] not in names:
            names.append(r['fm function'])
    t, rel = stage(images)
    try:
        text = run(d, t, 'luiscan.py', ['--all', '--fns', ','.join(names)] + [p for _, p in rel])
    finally:
        shutil.rmtree(t)
    open(out, 'w').write(text)


def ambiscan(d, record, outdir, measures, images):
    kit(d)
    lines = []
    rows = list(csv.DictReader([l for l in open(record).read().split('\n') if l and not l.startswith('#')],
                               delimiter='\t'))
    for r in rows:
        pair, fn = 'fm:' + r['image'], r['fm function']
        if r['old kit (4bbd3a74be89) tcmp']:
            lines.append((fn, pair, r['fm addr'], r['image addr'], 'compared by address (tcmp of both kits)'))
        for col, how in (('old kit (4bbd3a74be89) jtcheck', 'looked up by name (jtcheck 824905e26211)'),
                         ('new kit (86da41d3ef68) jtcheck', 'looked up by name (jtcheck 8b0ea3862423)')):
            if r[col]:
                lines.append((fn, pair, r['fm addr'], r['image addr'], how))
        low = r['lowest-address copies compared by the old kit (what a lookup by name took)']
        if low:
            a, b = low.split(':', 2)[:2]
            lines.append((fn, pair, a.strip(), b.strip(), 'looked up by name (the lowest-address compare, old kit)'))
    for m in measures:
        fn = open(m).readline()[2:].split('+', 1)[0]
        for tag, _ in images[1:]:
            lines.append((fn, 'fm:' + tag, '', '', 'looked up by name (%s)' % os.path.basename(m)))
    out = os.path.join(outdir, 'lookups.tsv')
    with open(out, 'w') as fh:
        fh.write('# one line per function lookup of codeid/codeid-kit.tsv and its measurement tables: name, pair, fm '
                 'address, image address, how the function was found\n')
        fh.write(''.join('\t'.join(x) + '\n' for x in lines))
    scanned = [record] + list(measures) + [out]
    files = [(p, os.path.join('codeid', os.path.basename(p))) for p in scanned]
    t, rel = stage(images, files)
    try:
        for tag, p in rel[1:]:
            text = run(d, t, 'ambiscan.py', [rel[0][1], p] + [r for _, r in files])
            open(os.path.join(outdir, 'ambiscan-%s.tsv' % tag), 'w').write(text)
    finally:
        shutil.rmtree(t)


def main():
    a = sys.argv[1:]
    if a[:1] == ['luiscan'] and len(a) >= 6:
        luiscan(a[1], a[2], a[3], [x.split('=', 1) for x in a[4:]])
    elif a[:1] == ['ambiscan'] and '--' in a:
        k = a.index('--')
        ambiscan(a[1], a[2], a[3], a[4:k], [x.split('=', 1) for x in a[k + 1:]])
    else:
        sys.exit(__doc__)


if __name__ == '__main__':
    main()
