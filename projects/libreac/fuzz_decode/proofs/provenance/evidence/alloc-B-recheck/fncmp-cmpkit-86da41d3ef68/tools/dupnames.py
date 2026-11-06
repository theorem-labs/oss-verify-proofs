#!/usr/bin/env python3
"""dupnames.py -- which of the names this record compared by NAME have more than one symtab entry in either twin.
(1) the 8 functions passed to the kit's compare `cmp` by name (strictcmp3 refuses an FNLIST name several functions carry);
(2) every member of the 8 roots' call closure as the closure script builds it (its own callees() / member() code,
    imported unchanged by exec of its definitions), with the Y counterpart the closure chose (qualified name:
    name{STT_FILE} for a duplicated name).
Counts every .symtab entry of the name (any type) and the sized STT_FUNC entries, in BOTH twins (elftools). For a
duplicated name it prints every copy and, for (1), the copy the kit used (fsym) and the copies the CODE calls (jal / auipc+jalr
targets inside the 8 roots' closure). usage: dupnames.py"""
import collections, os, sys, importlib.util
from elftools.elf.elffile import ELFFile
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common
HERE = common.HERE
X_ELF, Y_ELF = common.CGIF_B_TWIN, common.DECODE_B_TWIN
FNS = [l.strip() for l in open(os.path.join(HERE, 'out', 'FNLIST8.txt')) if l.strip()]


def counts(path):
    allc, fn = collections.Counter(), collections.defaultdict(list)
    for s in ELFFile(open(path, 'rb')).get_section_by_name('.symtab').iter_symbols():
        if not s.name:
            continue
        allc[s.name] += 1
        if s['st_info']['type'] == 'STT_FUNC' and s['st_size'] > 0:
            fn[s.name].append((s['st_value'], s['st_size'], s['st_info']['bind']))
    return allc, fn


def main():
    g = common.closure_globals(FNS)
    X, Y, dc = g['X'], g['Y'], g['dc']
    ax, fx = counts(X_ELF)
    ay, fy = counts(Y_ELF)
    print('# X = %s\n# Y = %s' % (X_ELF, Y_ELF))
    print('== (1) the 8 functions given to %s cmp by name' % common.CMP_PY)
    amb1 = 0
    for f in FNS:
        sx, sy = X.fsym(f), Y.fsym(f)
        line = '%s\tX symtab %d (sized FUNC %d)\tY symtab %d (sized FUNC %d)\tfsym X %#x Y %#x' % (
            f[:90], ax[f], len(fx[f]), ay[f], len(fy[f]), sx[0], sy[0])
        if ax[f] > 1 or ay[f] > 1:
            amb1 += 1
            line += '\tDUPLICATED: X %s | Y %s' % ([hex(v) for v, z, b in fx[f]], [hex(v) for v, z, b in fy[f]])
        print(line)
    print('(1) names with more than one symtab entry in either image: %d' % amb1)
    # (2) the union closure, as the closure script builds it
    seen = set()
    for r in FNS:
        s = X.fsym(r)
        work = [s[0]]; seen.add(s[0])
        while work:
            a = work.pop()
            c, _ = g['callees'](a, g['starts'][a][0][1])
            for t in c:
                if t not in seen:
                    seen.add(t); work.append(t)
    dup = []
    for a in sorted(seen):
        n, z, q = g['member'](a)
        if ax[n] > 1 or ay[n] > 1 or len(fx[n]) > 1 or len(fy[n]) > 1:
            ys, err = g['ycounterpart'](n, q) if q else (None, 'AMBIGUOUS-NAME-in-X')
            dup.append((n, a, q, ys, err))
    print('== (2) closure members: %d; members whose name has more than one symtab entry in either image: %d' % (len(seen), len(dup)))
    for n, a, q, ys, err in dup:
        print('%s\tX %#x\tqualified %s\tY counterpart %s\tX copies %s\tY copies %s' % (
            n[:70], a, q, ('%#x' % ys[0]) if ys else err, [hex(v) for v, z, b in fx[n]], [hex(v) for v, z, b in fy[n]]))


if __name__ == '__main__':
    main()
