#!/usr/bin/env python3
"""pins.py -- the pinned-original gate: every emitter reads only the unit's PINNED image, and every generated file says
which image it read.

  pins.py check IMAGE --index index/binaries.tsv [--twin UNSTRIPPED]       # exit 1 unless IMAGE is a pinned original
  pins.py stamp FILE.v IMAGE --index index/binaries.tsv [--twin UNSTRIPPED]  # check, then write the provenance line

Why (a measured root cause): 13 of 14 units' start-up facts were once generated
from the toolchain-N image (malloc_context_size = 1); every downstream artefact agreed with them, so every
self-consistency check passed. Only the ORIGINAL images caught it. So the sha256 of the ELF a run reads must be the
unit's pinned original, the row of index/binaries.tsv (project, harness, build, file, ..., sha256) that
projects/<project>/<harness>/harness.yaml pins.

The provenance line, put after the file's last leading comment line:
  (* Read from: <file> (<project>/<harness> <build>) sha256 <sha>; unstripped twin sha256 <sha> *)
The twin is the same build with symbols; it is read for names only, so its sha is recorded, not gated.

A new version of pins.py 88e69cd871f8: the pin table is a required argument (--index; the earlier version fell back to a
file at a fixed path); everything else is unchanged.
"""
import argparse, hashlib, os, re, sys


def sha256(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for b in iter(lambda: f.read(1 << 20), b''):
            h.update(b)
    return h.hexdigest()


EXTRA = [x for x in os.environ.get('OSSV_PIN_TABLES', '').split(':') if x]


def pinned(image, index):
    """(project, harness, build, file, sha) of the pinned row whose sha256 is the image's; exits 1 when there is none.
    Besides index/binaries.tsv, OSSV_PIN_TABLES (colon-separated) names more pin tables for units pinned elsewhere:
    each is a binaries.tsv-format file or a SHA256SUMS file (`sha  path`)."""
    s = sha256(image)
    for line in open(index):
        p = line.rstrip('\n').split('\t')
        if len(p) >= 8 and p[7] == s:
            return p[0], p[1], p[2], p[3], s
    for t in EXTRA:
        for line in open(t):
            p = line.rstrip('\n').split('\t')
            if len(p) >= 8 and p[7] == s:
                return p[0], p[1], p[2], p[3], s
            q = line.split()
            if len(q) == 2 and q[0] == s:
                return 'pin', os.path.basename(t), '-', os.path.basename(q[1].lstrip('*')), s
    sys.exit('pins: REFUSED: %s (sha256 %s) is not a pinned original in %s. Read the unit\'s own published image, '
             'never a rebuild or a toolchain-N copy.' % (image, s, index))


def provenance(image, twin, index):
    proj, harness, build, fname, s = pinned(image, index)
    line = '(* Read from: %s (%s/%s %s) sha256 %s' % (fname, proj, harness, build, s)
    if twin:
        line += '; unstripped twin sha256 %s' % sha256(twin)
    return line + ' *)'


ALLOWED_PREFIXES = ('Stdlib', 'Coq', 'LinuxProcessSemantics', 'OssFuzzTheorems.Core')


def emitcheck(path, ns):
    """REFUSE a generated file that still carries generator plumbing: a `From <module> Require` outside the receiving
    unit's namespace (found on grant's YB05: donor Requires, so nothing in it compiles outside the donor
    tree), or a scratch header. `ns` is the unit's namespace prefix, e.g. OssFuzzTheorems.Proofs.plugin_hostd.fuzz_reply
    (its images namespace OssFuzzTheorems.<project>.<harness>.images is allowed too)."""
    txt = open(path).read()
    bad_hdr = [l for l in txt.split('\n')[:12] if 'SCRATCH' in l or 'never committed' in l]
    unit = ns.replace('OssFuzzTheorems.Proofs.', 'OssFuzzTheorems.')
    bad_req = []
    for m in re.finditer(r'^From (\S+) Require', txt, re.M):
        mod = m.group(1)
        if mod.startswith(ns) or mod.startswith(unit) or any(mod == p or mod.startswith(p + '.') for p in ALLOWED_PREFIXES):
            continue
        bad_req.append(mod)
    if bad_hdr or bad_req:
        sys.exit('pins: REFUSED to stamp %s: %s%s' % (
            path, 'scratch header %r; ' % bad_hdr[:1] if bad_hdr else '',
            'Requires outside %s: %s' % (ns, sorted(set(bad_req))) if bad_req else ''))
    return len(re.findall(r'^From ', txt, re.M))


def stamp(path, image, twin, index, ns=None):
    if ns:
        emitcheck(path, ns)
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
    c = sub.add_parser('check'); c.add_argument('image'); c.add_argument('--twin'); c.add_argument('--index', required=True)
    s = sub.add_parser('stamp'); s.add_argument('file'); s.add_argument('image'); s.add_argument('--twin')
    s.add_argument('--index', required=True)
    s.add_argument('--ns', default=None, help="the receiving unit's namespace prefix: refuse a file with a Require "
                   "outside it or a scratch header")
    e = sub.add_parser('emitcheck'); e.add_argument('files', nargs='+'); e.add_argument('--ns', required=True)
    a = ap.parse_args()
    if a.cmd == 'check':
        print(provenance(a.image, a.twin, a.index))
    elif a.cmd == 'emitcheck':
        for f in a.files:
            print('%s: %d Require lines, all inside %s, no scratch header' % (f, emitcheck(f, a.ns), a.ns))
    else:
        print('%s: %s' % (a.file, stamp(a.file, a.image, a.twin, a.index, a.ns)))


if __name__ == '__main__':
    main()
