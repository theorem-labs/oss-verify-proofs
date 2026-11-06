#!/usr/bin/env python3
"""bpaths.py -- after an image-B --write from a donor that keeps its image-B core under lib/Reusable (libreac/fuzz_ctrl:
YB1v YE34 YF0l YF0m YF0x YE2y), Require those modules from this unit's lib/B, where fuzz_transport's image-B core is.

  bpaths.py WT HUB SRC REF FILE...
    WT    this unit's worktree (FILEs are read and rewritten under proofs/libdiginet/fuzz_transport/lib/)
    HUB   the git hub holding REF
    SRC   the donor P/H (libreac/fuzz_ctrl)
    REF   the donor commit the FILEs were relocated from (layout proofs/<P>/<H>/lib)
    FILE  the written files, lib-relative (B/Rt/StackMalloc0Tbl.v ...)

The donor's image-B core under lib/Reusable is read from the donor, not listed by hand: a module M of the donor's
lib/Reusable at REF whose A twin, A + M[1:], is a file of the donor's lib/A at REF (YB1v <-> A/AB1v.v). A module of the
donor's lib/Reusable with no A twin (YCe5, YG0q, ...) is shared by the donor's two images and stays lib/Reusable.

In each FILE, a `From <unit>.lib.Reusable Require Import <list>.` line whose modules are all core modules becomes the same
line with lib.B; each of those modules must be a file of the unit's lib/B (MISSING: nothing is written, exit 1). A line
that mixes core and shared modules, or a Require list split over lines that names a core module, is refused (exit 1).
The unit's one notice line (`(* Modified by Theorem Labs, 2026-10: relocated to libdiginet/fuzz_transport's ...`) gets one
sentence that says so. Then every module each FILE Requires under the unit's prefix is resolved against the unit's tree
(lib/<dir>/<module>.v); an unresolved one is listed (UNRESOLVED, exit 1).
"""
import os
import re
import subprocess
import sys

NS = 'OssFuzzTheorems.Proofs.libdiginet.fuzz_transport.lib'


def tree(hub, ref, path):
    out = subprocess.run(['git', '-C', hub, 'ls-tree', '--name-only', ref, path + '/'], check=True,
                         capture_output=True, text=True).stdout.split('\n')
    return {os.path.basename(p)[:-2] for p in out if p.endswith('.v')}


def main(wt, hub, src, ref, files):
    lib = os.path.join(wt, 'proofs/libdiginet/fuzz_transport/lib')
    dlib = 'proofs/%s/lib' % src
    dr, da = tree(hub, ref, dlib + '/Reusable'), tree(hub, ref, dlib + '/A')
    core = sorted(m for m in dr if m.startswith('Y') and 'A' + m[1:] in da)
    print('donor %s at %s: %d lib/Reusable modules with an A twin in lib/A (its image-B core under lib/Reusable)'
          % (src, ref, len(core)))
    rc = 0
    for f in files:
        path = os.path.join(lib, f)
        lines = open(path).read().split('\n')
        moved, bad = [], []
        for k, l in enumerate(lines):
            m = re.match(r'From %s\.Reusable Require Import ([\w ]+)\.\s*$' % re.escape(NS), l)
            if not m:
                if re.match(r'From %s\.Reusable Require Import\s*$' % re.escape(NS), l):
                    j = k + 1
                    while j < len(lines) and not lines[j - 1].rstrip().endswith('.'):
                        if set(re.findall(r'\w+', lines[j])) & set(core):
                            bad.append('%s:%d: a Require list over several lines names a core module' % (f, k + 1))
                        j += 1
                continue
            mods = m.group(1).split()
            c = [x for x in mods if x in core]
            if not c:
                continue
            if len(c) != len(mods):
                bad.append('%s:%d: core %s and shared %s on one line' % (f, k + 1, ' '.join(c),
                                                                         ' '.join(x for x in mods if x not in core)))
                continue
            miss = [x for x in c if not os.path.isfile(os.path.join(lib, 'B', x + '.v'))]
            if miss:
                bad.append('%s:%d: MISSING in the unit\'s lib/B: %s' % (f, k + 1, ' '.join(miss)))
                continue
            both = [x for x in c if os.path.isfile(os.path.join(lib, 'Reusable', x + '.v'))]
            lines[k] = l.replace('%s.Reusable Require' % NS, '%s.B Require' % NS, 1)
            moved.append((k + 1, c, both))
        if bad:
            print('\n'.join(bad))
            rc = 1
            continue
        if moved:
            n = [k for k, l in enumerate(lines) if l.startswith('(* Modified by Theorem Labs, 2026-10: relocated to '
                                                                'libdiginet/fuzz_transport\'s')]
            if len(n) != 1 or not lines[n[0]].endswith(' *)'):
                print('%s: %d notice lines of this unit, expected 1' % (f, len(n)))
                rc = 1
                continue
            mods = sorted({x for _, c, _ in moved for x in c})
            lines[n[0]] = lines[n[0]][:-3] + (' The donor\'s image-B core modules %s are Required from this unit\'s '
                                              'lib/B (class0/bpaths.py). *)' % ' '.join(mods))
            open(path, 'w').write('\n'.join(lines))
        for k, c, both in moved:
            print('%s:%d: lib.Reusable -> lib.B for %s%s' % (f, k, ' '.join(c),
                                                           ' (also in the unit\'s lib/Reusable: %s)' % ' '.join(both)
                                                           if both else ''))
        if not moved:
            print('%s: no Require of a core module from lib.Reusable' % f)
        text = re.sub(r'\(\*.*?\*\)', '', '\n'.join(lines), flags=re.S)
        req, unres = 0, []
        for m in re.finditer(r'From\s+%s((?:\.\w+)*)\s+Require\s+(?:(?:Import|Export)\s+)?([\w\s]+?)\.(?=\s|$)'
                             % re.escape(NS), text):
            d = m.group(1).lstrip('.').replace('.', '/')
            for x in m.group(2).split():
                req += 1
                if not os.path.isfile(os.path.join(lib, d, x + '.v')):
                    unres.append('%s/%s' % (d, x))
        print('%s: %d modules Required under the unit\'s prefix, %d resolved%s'
              % (f, req, req - len(unres), '; UNRESOLVED: ' + ' '.join(unres) if unres else ''))
        rc |= 1 if unres else 0
    return rc


if __name__ == '__main__':
    if len(sys.argv) < 6:
        sys.exit(__doc__)
    sys.exit(main(sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4], sys.argv[5:]))
