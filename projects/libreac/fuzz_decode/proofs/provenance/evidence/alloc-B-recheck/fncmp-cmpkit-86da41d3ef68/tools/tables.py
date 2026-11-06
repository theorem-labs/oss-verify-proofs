#!/usr/bin/env python3
"""tables.py -- independent BY-ADDRESS measurement of the targets settle.py's classifier does not shape-match and the kit's
jtcheck accepted as a table or initializer (its `ACCEPT <fn> table|initializer +<off> [<x>|<y>] <kind> <n>`
lines in out/jtcheck.out). For each: the functions are taken by ADDRESS from out/fulldiff.tsv (the closure's own
pairing), the target pair from the kit's `targets` at that word (must equal jtcheck's [x|y]), then
  rel4-jump N : entry k is a signed 4-byte offset from the table; target_k - function start must be equal on both sides
                for k < N;
  abs8-ptr N  : entry k is an 8-byte pointer; both pointers must name the same thing: the same symbol + offset, or equal
                NUL-terminated strings (both in .rodata), or the same offset inside the function;
  initializer B: the B bytes at the target; 8-byte words are compared as pointers (same symbol + offset or same section +
                offset of an equal-content cell) when they lie in the image, else byte for byte.
usage: tables.py"""
import collections, os, re, sys, importlib.util
TOOLS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, TOOLS)
import common
HERE = common.HERE
sp = importlib.util.spec_from_file_location('settle', os.path.join(TOOLS, 'settle.py'))
st = importlib.util.module_from_spec(sp); sp.loader.exec_module(st)
sc = st.sc
X_ELF, Y_ELF = common.CGIF_B_TWIN, common.DECODE_B_TWIN


def home(I, v):
    best = None
    for a, z, n, t in I.syms:
        if t in ('STT_FUNC', 'STT_OBJECT') and z > 0 and a <= v < a + z and (best is None or z < best[2]):
            best = (n, v - a, z)
    return best


def cstr(I, v):
    b = sc.frd(I, v, 512)
    return b[:b.index(b'\0') + 1] if b and b'\0' in b else None


def same_ptr(C, D, pc, pd, fc, fd, zf):
    if pc == pd and not (0x10000 <= pc < 0x600000):
        return True, 'equal-non-pointer'    # outside both images [0x10000, 0x5fb000): the bytes themselves, equal
    if fc <= pc < fc + zf and fd <= pd < fd + zf:
        return pc - fc == pd - fd, 'in-function +%#x' % (pc - fc)
    hc, hd = home(C, pc), home(D, pd)
    if hc and hd:
        return (hc[0] == hd[0] and hc[1] == hd[1]), '%s+%#x | %s+%#x' % (hc[0][:40], hc[1], hd[0][:40], hd[1])
    sc_, sd_ = cstr(C, pc), cstr(D, pd)
    if sc_ is not None and sd_ is not None:
        return sc_ == sd_, 'C string %r' % (sc_[:30] if sc_ == sd_ else (sc_[:20], sd_[:20]),)
    return False, 'no home %#x | %#x' % (pc, pd)


def main():
    C, D = sc.Img(X_ELF), sc.Img(Y_ELF)
    fx = {}
    for l in list(open(os.path.join(HERE, 'out', 'fulldiff.tsv')))[1:]:
        c = l.rstrip('\n').split('\t')
        fx[c[0]] = (int(c[1], 16), int(c[2], 16))
    acc = []
    for l in open(os.path.join(HERE, 'out', common.JT_OUT)):
        m = re.match(r'\s+ACCEPT (\S+) (table|initializer) \+(0x[0-9a-f]+) \[(0x[0-9a-f]+)\|(0x[0-9a-f]+)\] (?:(\S+) (\d+) entries|(\d+))', l)
        if m:
            acc.append(m.groups())
    out, cnt = [], collections.Counter()
    for fn, what, off, jx, jy, kind, n, nb in acc:
        if fn not in fx:
            continue
        ax, ay = fx[fn]
        zx, zy = C.fsym(fn)[1], D.fsym(fn)[1]
        assert C.fsym(fn)[0] == ax and D.fsym(fn)[0] == ay, fn
        o = int(off, 16)
        _, _, tc, _ = st.target_and_code(C, fn, o, (ax, zx))
        _, _, td, _ = st.target_and_code(D, fn, o, (ay, zy))
        assert (tc, td) == (int(jx, 16), int(jy, 16)), (fn, off, tc, td, jx, jy)
        bad = []
        if what == 'table' and kind == 'rel4-jump':
            for k in range(int(n)):
                ec = int.from_bytes(sc.frd(C, tc + 4 * k, 4), 'little', signed=True)
                ed = int.from_bytes(sc.frd(D, td + 4 * k, 4), 'little', signed=True)
                if tc + ec - ax != td + ed - ay:
                    bad.append(k)
            why = '%s entries, function-relative targets %s' % (n, 'equal' if not bad else 'DIFFER at %s' % bad[:5])
        elif what == 'table' and kind == 'abs8-ptr':
            notes = collections.Counter()
            for k in range(int(n)):
                pc = int.from_bytes(sc.frd(C, tc + 8 * k, 8), 'little')
                pd = int.from_bytes(sc.frd(D, td + 8 * k, 8), 'little')
                ok, why1 = same_ptr(C, D, pc, pd, ax, ay, zx)
                notes[why1.split(' ')[0]] += 1
                if not ok:
                    bad.append((k, why1))
            why = '%s pointers, each naming the same thing (%s)%s' % (n, dict(notes), '' if not bad else ' DIFFER %s' % bad[:3])
        elif what == 'table' and kind == 'rel4-str':
            # jtcheck's reading: entry k is a signed 4-byte offset from the table to a C string. An entry whose targets are
            # equal C strings (through the NUL) is a string; an entry whose target is a C string on NEITHER side is compared
            # as its 4 entry bytes (as jtcheck does); anything else differs.
            strs = []
            for k in range(int(n)):
                ex, ey = sc.frd(C, tc + 4 * k, 4), sc.frd(D, td + 4 * k, 4)
                ec, ed = int.from_bytes(ex, 'little', signed=True), int.from_bytes(ey, 'little', signed=True)
                s1, s2 = sc.cstring(C, tc + ec), sc.cstring(D, td + ed)
                if s1 is not None and s1 == s2:
                    strs.append(repr(s1))
                elif s1 is None and s2 is None and ex == ey:
                    strs.append('value %d (not a string on either side; entry bytes equal)' % ec)
                else:
                    bad.append((k, ec, ed, s1, s2))
            why = '%s entries (jtcheck\'s reading: rel4 offsets to C strings), %s: %s' % (
                n, 'all settled' if not bad else 'DIFFER at %s' % [b[0] for b in bad][:5], ' ; '.join(strs)[:200])
        else:
            B = int(nb)
            bc, bd = sc.frd(C, tc, B), sc.frd(D, td, B)
            if bc is None or bd is None:
                why, bad = 'not file-backed', ['unreadable']
            else:
                words = collections.Counter()
                for k in range(0, B, 8):
                    wc, wd = int.from_bytes(bc[k:k + 8], 'little'), int.from_bytes(bd[k:k + 8], 'little')
                    if wc == wd:
                        words['equal'] += 1; continue
                    ok, why1 = same_ptr(C, D, wc, wd, ax, ay, zx)
                    words['pointer ' + why1] += 1
                    if not ok:
                        bad.append((k, hex(wc), hex(wd), why1))
                why = '%d bytes: %s%s' % (B, dict(words), '' if not bad else ' DIFFER %s' % bad[:3])
        v = 'DIFFERS' if bad else ('TABLE-' + kind.upper() if what == 'table' else 'INITIALIZER')
        cnt[v] += 1
        out.append((fn, off, v, '%#x' % tc, '%#x' % td, why))
    with open(os.path.join(HERE, 'out', 'tables.tsv'), 'w') as f:
        f.write('function\tword\tmeasurement\tX target\tY target\tdetail\n')
        for r in out:
            f.write('\t'.join(r) + '\n')
    print('rows %d: %s' % (len(out), dict(cnt)))
    for r in out:
        print('  %s %s %s %s' % (r[0][:60], r[1], r[2], r[5][:230]))


if __name__ == '__main__':
    main()
