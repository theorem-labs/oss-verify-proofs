#!/usr/bin/env python3
"""wire_kernel.py GRANT_REL_DIR NEW_DIR UNIT_REUSABLE REF_DIR FILE... -- write fuzz_wire's copies of kernel files from new texts in
fuzz_grant's released form, by the transformation port_core 0e4e065eab9f + the header-rule step applied to the released
originals, and prove that transformation on the originals first.

T(text, F) = the transformation that made this unit's COMMITTED kernel files (port_core's relocation, then the
comments-only undating step of the committed core; nothing committed is reverted): dated `Modified by Theorem Labs,
YYYY-MM: ` notices undated; port_core's provenance line `(* Modified by Theorem Labs: copied from proofs/libreac/fuzz_grant/lib/F (donor image sha256 c2c7559b29bd), with its
module paths changed. *)` inserted after the leading header comment lines; the module text
OssFuzzTheorems.Proofs.libreac.fuzz_grant.lib.Reusable -> OssFuzzTheorems.Proofs.reac_repacer.fuzz_wire.lib.Reusable.
Gate (equality): T(GRANT_REL_DIR/F) must equal REF_DIR/F (the unit's committed file), byte for byte, for every FILE;
else nothing is written. Then UNIT_REUSABLE/F := T(NEW_DIR/F), so the patch set's diff touches no notice line. Prints one line per file."""
import re, sys

DATED = re.compile(r'Modified by Theorem Labs, \d{4}-\d{2}(?:-\d{2})?: ')
PROV = ('(* Modified by Theorem Labs: copied from proofs/libreac/fuzz_grant/lib/%s (donor image sha256 c2c7559b29bd), '
        'with its module paths changed. *)')


def T(text, f):
    lines = DATED.sub('Modified by Theorem Labs: ', text).split('\n')
    n = 0
    while n < len(lines) and lines[n].startswith('(*') and lines[n].rstrip().endswith('*)'):
        n += 1
    lines.insert(n, PROV % f)
    return '\n'.join(lines).replace('OssFuzzTheorems.Proofs.libreac.fuzz_grant.lib.Reusable',
                                    'OssFuzzTheorems.Proofs.reac_repacer.fuzz_wire.lib.Reusable')


def main():
    grel, new, unit, ref = sys.argv[1:5]
    files = sys.argv[5:]
    bad = []
    for f in files:
        if T(open('%s/%s' % (grel, f)).read(), f) != open('%s/%s' % (ref, f)).read():
            bad.append(f)
    if bad:
        sys.exit('wire_kernel: GATE FAILED: T(released) != the committed file for %s; nothing written' % ' '.join(bad))
    print('wire_kernel: gate PASS: T(released grant text) == the unit\'s committed file, byte for byte, for all %d files' % len(files))
    for f in files:
        open('%s/%s' % (unit, f), 'w').write(T(open('%s/%s' % (new, f)).read(), f))
        print('wire_kernel: wrote Reusable/%s' % f)


if __name__ == '__main__':
    main()
