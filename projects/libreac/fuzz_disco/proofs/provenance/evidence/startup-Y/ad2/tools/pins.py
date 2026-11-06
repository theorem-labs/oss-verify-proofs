#!/usr/bin/env python3
"""pins.py -- the pinned-original gate: every emitter reads only the unit's PINNED image, and every generated file says
which image it read.

  pins.py check IMAGE [--twin TWIN] [--index index/binaries.tsv]     # exit 1 unless IMAGE is a pinned original
  pins.py stamp FILE.v IMAGE [--twin TWIN] [--index ...]             # check, then write the provenance line

Why (a measured root cause): 13 of 14 units' start-up facts were generated
from the toolchain-N image (malloc_context_size = 1); every downstream artefact agreed with them, so every
self-consistency check passed. Only the ORIGINAL images caught it. So the sha256 of the ELF a run reads must be the
unit's pinned original, the row of index/binaries.tsv (project, harness, build, file, ..., sha256) that
projects/<project>/<harness>/harness.yaml pins.

The provenance line, put after the file's last leading comment line:
  (* Read from: <file> (<project>/<harness> <build>) sha256 <sha>; unstripped twin sha256 <sha> *)
The twin is the same build with symbols; it is read for names only, so its sha is recorded, not gated. TWIN is the
twin's ELF or its symbol extract (twin/mknm.py), whose first header line names the twin's sha256.
The index is the file OSSV_BINARIES_TSV names (the repository's index/binaries.tsv), or --index.
"""
import argparse, hashlib, os, re, sys

DEFAULT_INDEX = os.environ.get('OSSV_BINARIES_TSV')


def sha256(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for b in iter(lambda: f.read(1 << 20), b''):
            h.update(b)
    return h.hexdigest()


def twin_sha256(twin):
    """the twin's sha256: of the ELF itself, or the one the first header line of its symbol extract names"""
    with open(twin, 'rb') as f:
        if f.read(4) == b'\x7fELF':
            return sha256(twin)
    m = re.match(r'# unstripped twin sha256 ([0-9a-f]{64}) ', open(twin).readline())
    if not m:
        sys.exit('pins: %s is neither an ELF nor a twin symbol extract (no `# unstripped twin sha256` first line)' % twin)
    return m.group(1)


def pinned(image, index=DEFAULT_INDEX):
    """(project, harness, build, file, sha) of the pinned row whose sha256 is the image's; exits 1 when there is none"""
    if not index:
        sys.exit('pins: no index: set OSSV_BINARIES_TSV to the repository\'s index/binaries.tsv, or pass --index')
    s = sha256(image)
    for line in open(index):
        p = line.rstrip('\n').split('\t')
        if len(p) >= 8 and p[7] == s:
            return p[0], p[1], p[2], p[3], s
    sys.exit('pins: REFUSED: %s (sha256 %s) is not a pinned original in %s. Read the unit\'s own published image, '
             'never a rebuild or a toolchain-N copy.' % (image, s, index))


def provenance(image, twin=None, index=DEFAULT_INDEX):
    proj, harness, build, fname, s = pinned(image, index)
    line = '(* Read from: %s (%s/%s %s) sha256 %s' % (fname, proj, harness, build, s)
    if twin:
        line += '; unstripped twin sha256 %s' % twin_sha256(twin)
    return line + ' *)'


def stamp(path, image, twin=None, index=DEFAULT_INDEX):
    line = provenance(image, twin, index)
    lines = open(path).read().split('\n')
    lines = [l for l in lines if not l.startswith('(* Read from: ')]
    last = max([i for i, l in enumerate(lines[:16]) if l.startswith('(*')] or [-1])
    lines.insert(last + 1, line)
    open(path, 'w').write('\n'.join(lines))
    return line


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest='cmd', required=True)
    c = sub.add_parser('check'); c.add_argument('image'); c.add_argument('--twin'); c.add_argument('--index', default=DEFAULT_INDEX)
    s = sub.add_parser('stamp'); s.add_argument('file'); s.add_argument('image'); s.add_argument('--twin')
    s.add_argument('--index', default=DEFAULT_INDEX)
    a = ap.parse_args()
    if a.cmd == 'check':
        print(provenance(a.image, a.twin, a.index))
    else:
        print('%s: %s' % (a.file, stamp(a.file, a.image, a.twin, a.index)))


if __name__ == '__main__':
    main()
