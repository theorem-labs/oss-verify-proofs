#!/usr/bin/env python3
"""Settle every target a kit run leaves unsettled, from the kit's FULL target list (cmpkit 4bbd3a74be89).
closure_strict2 and paircl print only the first two differing targets of a function (closure_strict2.py:88,
paircl.py:67), so this tool re-runs the kit's own one compare, strictcmp2.tcmp, on each reported function pair and
settles every target in its full list.
usage: settle2.py KITDIR X_ELF Y_ELF CLOSURE_OUT PAIRCL_OUT   (X, Y unstripped twins)
Function pairs: closure rows give the X address and the name (Y by its one symbol of that name); paircl rows give X and
Y addresses. Each pair is compared once (strictcmp2.tcmp over the X function's size).
Per differing target (offset, kind):
  data-differs / cstr-differs (a read-only data target):
    TABLE-k*w  the target register is added to an index register and a load of width w reads the sum; the index is
               bounded to k entries by a mask (andi m: m+1), a shift (srli s, 64-bit: 2^(64-s)) or a compare against a
               constant (addi rB, zero, K; bltu rB, rI): the first k*w bytes are equal on both sides;
    CSTR       no such index, and the bytes up to the first NUL are equal on both sides, NUL included (any byte values,
               possibly empty); every CSTR row is for the consumer audit;
    OPEN       neither (jump / pointer / string tables: settled by jtcheck or by hand, outside this tool);
  unmeasured (an auipc result no target consumes, or an I/S-type word on an auipc register):
    WORD-EQUAL the 4 bytes of the word are equal in X and Y (then a by-hand reading says what the word is);
  any other kind: REAL (a difference; report it).
Every target is printed; the last line counts them."""
import sys, os, re, importlib.util, collections

kit, xe, ye, clf, pcf = sys.argv[1:6]
spec = importlib.util.spec_from_file_location('s2', os.path.join(kit, 'strictcmp2.py'))
s2 = importlib.util.module_from_spec(spec); sys.argv = [sys.argv[0]]; spec.loader.exec_module(s2)
I = {'X': s2.Img(xe), 'Y': s2.Img(ye)}
X, Y = I['X'], I['Y']


def fbytes(img, a, n):
    for (v, fz, d) in img.segs:
        if v <= a < v + fz:
            return d[a - v:min(a - v + n, fz)]
    return b''


def sym_at(img, a):
    for v, z, nm, t in img.syms:
        if v == a and t == 'STT_FUNC' and z > 0:
            return nm, z
    return None, None


pairs = collections.OrderedDict()
for l in open(clf):
    m = re.match(r'\s{3}(\S+) @(0x[0-9a-f]+): ', l)
    if m and 'target-differ' in l:
        xa = int(m.group(2), 16); nm, z = sym_at(X, xa)
        ys = Y.fsym(nm)
        if ys: pairs[(xa, ys[0])] = (nm, z, 'closure')
for l in open(pcf):
    p = l.split()
    if l.startswith('   ') and len(p) > 3 and p[1].startswith('0x') and 'target-diff' in l:
        xa, ya = int(p[1], 16), int(p[2], 16); nm, z = sym_at(X, xa)
        if (xa, ya) in pairs:
            pairs[(xa, ya)] = (nm, z, 'closure+paircl')
        else:
            pairs[(xa, ya)] = (nm, z, 'paircl')

W = {0: 1, 1: 2, 2: 4, 3: 8, 4: 1, 5: 2, 6: 4}


def table_reading(w, i):
    """(entries, width) if the target register of word i is added to a bounded index and the sum is loaded"""
    o, x, n = w[i]
    r = (x >> 7) & 31
    for j in range(i + 1, min(i + 10, len(w))):
        oj, y, nj = w[j]
        if nj != 4: continue
        if (y & 0x7f) == 0x33 and ((y >> 12) & 7) == 0 and (y >> 25) == 0 and r in ((y >> 15) & 31, (y >> 20) & 31):
            rs = (y >> 20) & 31 if ((y >> 15) & 31) == r else (y >> 15) & 31
            rd = (y >> 7) & 31
            width = None
            for k in range(j + 1, min(j + 4, len(w))):
                ok_, z, nk = w[k]
                if nk == 4 and (z & 0x7f) == 0x03 and ((z >> 15) & 31) == rd and (z >> 20) == 0:
                    width = W.get((z >> 12) & 7); break
            if width is None: return None
            # the index rs: walk its definitions backwards (slli scales, then the bound)
            reg, scale = rs, 1
            for k in range(j - 1, max(-1, j - 16), -1):
                ok_, z, nk = w[k]
                if nk != 4: continue
                op, f3, rdk, rs1 = z & 0x7f, (z >> 12) & 7, (z >> 7) & 31, (z >> 15) & 31
                if rdk == reg and op == 0x13 and f3 == 1:
                    scale <<= (z >> 20) & 0x3f; reg = rs1; continue
                if rdk == reg and op == 0x13 and f3 == 7:
                    m = s2._g['sx'](z >> 20, 12)
                    return (m + 1, width) if m > 0 else None
                if rdk == reg and op == 0x13 and f3 == 5 and (z >> 26) == 0 and ((z >> 20) & 0x3f) >= 56:
                    return (1 << (64 - ((z >> 20) & 0x3f)), width)
                if op == 0x63 and f3 in (6, 7) and reg in (rs1, (z >> 20) & 31):
                    # bltu rB, reg (skip when reg > K) / bgeu reg, rB: find rB = K
                    rb = rs1 if (z >> 20) & 31 == reg else (z >> 20) & 31
                    for q in range(k - 1, max(-1, k - 8), -1):
                        oq, u, nq = w[q]
                        if nq == 4 and (u & 0x7f) == 0x13 and ((u >> 12) & 7) == 0 and ((u >> 15) & 31) == 0 and ((u >> 7) & 31) == rb:
                            return (s2._g['sx'](u >> 20, 12) + 1, width)
                    return None
                if rdk == reg:
                    return None
            return None
    return None


cnt = collections.Counter(); rows = 0
for (xa, ya), (nm, z, src) in pairs.items():
    v, c, acc, diff = s2.tcmp(I, 'X', xa, 'Y', ya, z)
    bx = fbytes(X, xa, z); by = fbytes(Y, ya, z)
    tx, ty = s2.targets(xa, bx), s2.targets(ya, by)
    wx = s2.bc_words(bx); offi = {o: i for i, (o, x, n) in enumerate(wx)}
    for (off, r1, r2, kind, info) in diff:
        rows += 1; oi = offi.get(int(off, 16))
        if kind in ('data-differs', 'cstr-differs'):
            ax, ay = tx[oi][1], ty[oi][1]
            dx, dy = fbytes(X, ax, 4096), fbytes(Y, ay, 4096)
            L = 0
            while L < min(len(dx), len(dy)) and dx[L] == dy[L]: L += 1
            tr = table_reading(wx, oi)
            if tr:
                k, w_ = tr
                cls = 'TABLE' if L >= k * w_ else 'OPEN'
                why = '%d entries x %d bytes, %d bytes equal of %d' % (k, w_, min(L, k * w_), k * w_)
            else:
                nul = dx[:L].find(b'\0')
                if nul >= 0:
                    cls = 'CSTR'; why = 'equal C string of %d bytes + NUL: %r' % (nul, dx[:nul][:40])
                else:
                    cls = 'OPEN'; why = 'equal prefix %d, no NUL in it; X %s | Y %s' % (L, dx[:16].hex(), dy[:16].hex())
            print('%s\t%s+%s\t%s\tX %#x Y %#x\t%s' % (cls, nm, off, src, ax, ay, why))
        elif kind == 'unmeasured':
            ex, ey = fbytes(X, xa + int(off, 16), 4), fbytes(Y, ya + int(off, 16), 4)
            cls = 'WORD-EQUAL' if ex == ey else 'REAL'
            print('%s\t%s+%s\t%s\t%s\tword X %s Y %s' % (cls, nm, off, src, r1, ex.hex(), ey.hex()))
        else:
            cls = 'REAL'
            print('%s\t%s+%s\t%s\t%s %s %s %s' % (cls, nm, off, src, kind, r1, r2, info))
        cnt[(cls, src)] += 1
tot = collections.Counter()
for (cls, src), n in cnt.items(): tot[cls] += n
print('# settle2: functions %d, targets %d; %s; by run: %s' % (len(pairs), rows, ' '.join('%s %d' % kv for kv in sorted(tot.items())),
      ' '.join('%s/%s %d' % (k[0], k[1], n) for k, n in sorted(cnt.items()))))
