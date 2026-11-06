#!/usr/bin/env python3
"""escape.py -- the second settlement pass. Read-only on X_ELF, Y_ELF and FIELDSCAN_TSV; rewrites SETTLE_TSV in place.

For each target pair settle.py left UNSETTLED whose target is the empty string (1 NUL byte, `00` in both images), the
pair becomes class CSTR-ESCAPE, verdict SETTLED-EQUAL, when every use of the pointer is accounted for by a measurement:
  - ESCAPE: every use of the pointer in the traced function (settle.uses), decoded from the image: each store into an
    object field (`s* rs, off(rb)` at its pc), each stack spill and reload, each return, each call argument. The uses
    must be the same (kind, pc, instruction) in X and Y.
  - DIRECT READERS: settle.string_readers on the pointer (the same rule as the CSTR class): a `const char *` parameter of a
    named callee, a printf-like `%s` vararg (format checked), an lb/lbu inside the string, a pointer compare, a spill and
    its reloads.
  - FIELD READS: for each store into an object field, the whole-image scan of objscan.py (FIELDSCAN_TSV): every load of
    that field anywhere in the image, through every copy of the object and every handler object that holds the field's
    address, each followed to its readers with the same rule. Required: 0 UNRESOLVED rows in X and in Y, and the same
    READ rows (function, pc, instruction) in X and Y. WRITE rows replace the value and read nothing.
  - RETURN: a return of the pointer, for the functions in RETURNS only: the caller path and the caller words that read
    it (musl's strftime family). Every cited word is decoded here in X and in Y and must be exactly as listed.
  - SUPPORT: the equal window at the target in both images (second check only; the readers' NUL stop is the bound).
Any use not accounted for leaves the pair UNSETTLED. A row counts settled-equal only when all its pairs are.
usage: escape.py X_ELF Y_ELF SETTLE_TSV FIELDSCAN_TSV"""
import os, runpy, sys, collections
HERE = os.path.dirname(os.path.abspath(__file__))
_argv = sys.argv[:]
sys.argv = [os.path.join(HERE, 'settle.py'), _argv[1], _argv[2], '']
S = runpy.run_path(os.path.join(HERE, 'settle.py'), run_name='settle_lib')
sys.argv = _argv
dc, X, Y, Fn, dec, RN = S['dc'], S['X'], S['Y'], S['Fn'], S['dec'], S['RN']
fsymq = S['jt']['fsymq']

# the return rows: the caller path, and the words of the callers that read the returned pointer. escape.py decodes
# each listed word in X and in Y and leaves the pair UNSETTLED unless every one is exactly as listed.
STRFTIME_L = [('__strftime_l', '+0x70', 'addi s7,zero,10'), ('__strftime_l', '+0x74', 'addi s10,zero,48'),
              ('__strftime_l', '+0x1c0', 'beq a0,zero -> +0x2e0'), ('__strftime_l', '+0x1cc', 'lbu a0,0(a1)'),
              ('__strftime_l', '+0x1d0', 'addi a2,zero,43'), ('__strftime_l', '+0x1d4', 'beq a0,a2 -> +0x1e0'),
              ('__strftime_l', '+0x1d8', 'addi a2,zero,45'), ('__strftime_l', '+0x1dc', 'bne a0,a2 -> +0x200'),
              ('__strftime_l', '+0x204', 'bne a0,s10 -> +0x220'), ('__strftime_l', '+0x23c', 'lbu a4,0(a3)'),
              ('__strftime_l', '+0x240', 'addi a4,a4,-48'), ('__strftime_l', '+0x24c', 'bltu a4,s7 -> +0x23c')]
STRLEN_LEN = [('__strftime_fmt_1', '+0x514', 'jal ra,__interceptor_trampoline_strlen/__wrap_strlen'),
              ('__strftime_fmt_1', '+0x518', 'addi a1,a0,0'), ('__strftime_fmt_1', '+0x520', 'sd a1,0(s0)')]
READ_L = ('__strftime_l reads it: +0x1c0 beq a0,zero is a null test; +0x1cc lbu a0,0(a1) reads byte 0, the NUL; byte 0 '
          'is not 43 (+0x1d0/+0x1d4), 45 (+0x1d8/+0x1dc -> +0x200) or 48 (+0x204 -> +0x220), so the lbu 1(a1) at '
          '+0x1e4 and +0x208 does not run; the digit loop (+0x23c lbu a4,0(a3); +0x240 addi a4,a4,-48; +0x24c bltu '
          'a4,s7 with s7 = 10) stops at the NUL; the memcpy at +0xa0 copies the length __strftime_fmt_1 returns with '
          'the pointer, ')
RETURNS = {
    '__nl_langinfo_l': ('returned to __strftime_fmt_1 +0x480 (from there a2, the format, of __strftime_l: a direct '
                        'reader above) and +0x508, where +0x514 strlen reads it to the NUL and +0x520 sd a1,0(s0) '
                        'returns that length (0) with it to __strftime_l. ' + READ_L + 'here 0 bytes',
                        STRFTIME_L + STRLEN_LEN),
    '__strftime_fmt_1': ('returned to __strftime_l +0x1bc, its only direct caller, with length 0: +0x528 / +0x544 '
                         'sd zero,0(s0) just before the pointer is made. ' + READ_L + 'here 0 bytes',
                         STRFTIME_L + [('__strftime_fmt_1', '+0x528', 'sd zero,0(s0)'),
                                       ('__strftime_fmt_1', '+0x544', 'sd zero,0(s0)')]),
    '__tm_to_tzname': ('returned to __strftime_fmt_1 +0x438; +0x514 strlen reads it to the NUL and +0x520 sd a1,0(s0) '
                       'returns that length (0) with it to __strftime_l. ' + READ_L + 'here 0 bytes',
                       STRFTIME_L + STRLEN_LEN),
}

def ins(F, j):
    m, rd, r1, r2, im = F.d[j]
    if m in S['STORE']: return '%s %s,%d(%s)' % (m, RN[r2], im, RN[r1])
    if m in S['LOADW']: return '%s %s,%d(%s)' % (m, RN[rd], im, RN[r1])
    if m == 'jalr': return 'jalr %s,%d(%s)' % (RN[rd], im, RN[r1])
    return m

def desc(F, j):
    m, rd, r1, r2, im = F.d[j]
    if m in S['BRANCH']: return '%s %s,%s -> +%#x' % (m, RN[r1], RN[r2], F.w[j][0] + im)
    if m == 'jal': return 'jal %s,%s' % (RN[rd], dc.qres(F.I, F.a + F.w[j][0] + im)[:-4])
    if m == 'addi': return 'addi %s,%s,%d' % (RN[rd], RN[r1], im)
    return ins(F, j)

def check_words(words):
    """[] if every (function, pc, decoded) word is as listed in X and in Y, else the differences"""
    bad = []
    for fnn, pc, want in words:
        for tag, Im in (('X', X), ('Y', Y)):
            F = Fn(Im, *fsymq(Im, fnn)); j = F.idx.get(int(pc[1:], 16))
            got = desc(F, j) if j is not None else None
            if got != want: bad.append('%s %s %s: %s, not %s' % (tag, fnn, pc, got, want))
    return bad

def window(ax, ay):
    bx = dc.frd(X, ax, 65536) or b''; by = dc.frd(Y, ay, 65536) or b''
    n = 0
    while n < min(len(bx), len(by)) and bx[n] == by[n]: n += 1
    return n

scan = collections.defaultdict(lambda: collections.defaultdict(list))   # escape tag -> image -> rows
for l in open(_argv[4]).read().splitlines()[1:]:
    f = l.split('\t'); scan[f[1]][f[0]].append(f)

def data_ptrs():
    """(ok, text): the data words that point into the scanned objects must be the same in X and Y, and none may point
    at a scanned field"""
    dx = sorted(r[6] for r in scan['data']['X']); dy = sorted(r[6] for r in scan['data']['Y'])
    bad = [r for r in scan['data']['X'] + scan['data']['Y'] if r[2] == 'UNRESOLVED']
    if bad or dx != dy:
        return False, 'data words into the scanned objects: %d point at a scanned field; same in X and Y: %s' % (len(bad), dx == dy)
    return True, 'data words into the scanned objects (same in X and Y): %s' % ('; '.join(dx) or 'none')

def field_reads(tag):
    """(ok, text) for one field store, from the whole-image scan"""
    sx, sy = scan[tag]['X'], scan[tag]['Y']
    if not sx or not sy: return False, 'no field scan rows for %s' % tag
    key = lambda r: (r[2], r[3], r[4], r[5])
    ux = [r for r in sx if r[2] == 'UNRESOLVED']; uy = [r for r in sy if r[2] == 'UNRESOLVED']
    rx = sorted({key(r) for r in sx if r[2] == 'READ'}); ry = sorted({key(r) for r in sy if r[2] == 'READ'})
    obj = next(r[6] for r in sx if r[2] == 'ESCAPE')
    nw = len({key(r) for r in sx if r[2] == 'WRITE'})
    if ux or uy or rx != ry:
        return False, '%s: %d unresolved in X, %d in Y, reads equal in X and Y: %s' % (obj, len(ux), len(uy), rx == ry)
    reads = []
    for r in sorted({(r[3], r[4], r[5], r[6]) for r in sx if r[2] == 'READ'}):
        reads.append('%s %s `%s`: %s' % r)
    return True, '%s: %d load site(s) of the field in the image, the same in X and Y, each read as a C string: %s; ' \
                 '%d write site(s) (they replace the value, no read); 0 unresolved' % (obj, len(reads), ' | '.join(reads), nw)

old = open(_argv[3]).read().splitlines()
new = []; replaced = 0; kept = []
for l in old:
    f = l.split('\t')
    if not (f[0] == 'ACCEPT' and f[6] == 'UNSETTLED' and f[9] == '00' and f[10] == '00'):
        new.append(l); continue
    fn, off = f[1], int(f[2], 16)
    FX, FY = Fn(X, *fsymq(X, fn)), Fn(Y, *fsymq(Y, fn))
    i = FX.idx[off]; rd = FX.d[i][1]
    ux, uy = S['uses'](FX, i, rd), S['uses'](FY, FY.idx[off], FY.d[FY.idx[off]][1])
    sig = lambda F, us: sorted((k, F.pc(j), ins(F, j)) for k, j, d in us)
    why = []
    if sig(FX, ux) != sig(FY, uy): why.append('the uses differ between X and Y')
    esc, fields, rets = [], [], []
    for k, j, d in sorted(ux, key=lambda u: u[1]):
        if k == 'store':
            esc.append('store `%s` at %s' % (ins(FX, j), FX.pc(j)))
            ok, txt = field_reads('%s+%s %s' % (fn, f[2], FX.pc(j)))
            fields.append('field store at %s -> %s' % (FX.pc(j), txt))
            if not ok: why.append(txt)
            ok, txt = data_ptrs()
            if not ok: why.append(txt)
        elif k in ('spill', 'reload'): esc.append('%s `%s` at %s' % (k, ins(FX, j), FX.pc(j)))
        elif k == 'ret': esc.append('return `%s` at %s' % (ins(FX, j), FX.pc(j))); rets.append(FX.pc(j))
    ok, ev, unk = S['string_readers'](FX, FY, i, rd, 1)
    for u in unk:
        if ' store ' in u: continue                          # covered by the field scan above
        if ' returned' in u and fn in RETURNS: continue      # covered by RETURNS below
        why.append('direct use not shown to read a C string: ' + u)
    if rets and fn not in RETURNS: why.append('a return with no recorded caller path')
    if rets and fn in RETURNS: why += check_words(RETURNS[fn][1])
    if why:
        kept.append((fn, f[2], why)); new.append(l); continue
    w = window(int(f[4], 16), int(f[5], 16))
    text = ('PRIMARY (measured): the pointer is read only as a C string, so only its first byte, the NUL, is read; '
            'that byte is 00 in X and Y. ESCAPE (decoded, the same in X and Y): %s. DIRECT READERS: %s.%s%s '
            'SUPPORT: the equal window at the target is %d bytes in both images (second check only).' % (
                '; '.join(esc) or '-', '; '.join(ev) or 'none',
                (' FIELD READS (whole-image scan, objscan.py, fieldscan.tsv): ' + ' || '.join(fields) + '; ' + data_ptrs()[1] + '.') if fields else '',
                (' RETURN (each cited word decoded in X and Y by escape.py): ' + RETURNS[fn][0] + '.') if rets else '', w))
    new.append('\t'.join(['ACCEPT', f[1], f[2], f[3], f[4], f[5], 'CSTR-ESCAPE', text,
                          '1 byte to the NUL (reader bound); %d bytes equal window at the target (support)' % w,
                          f[9], f[10], 'SETTLED-EQUAL']))
    replaced += 1
by_fn = {}
for l in new:
    f = l.split('\t')
    if f[0] == 'ACCEPT' and f[1] != 'function': by_fn.setdefault(f[1], []).append(f[-1])
out = []
for l in new:
    f = l.split('\t')
    if f[0] == 'ROW' and f[1] in by_fn:
        vs = by_fn[f[1]]; ok = sum(1 for v in vs if v == 'SETTLED-EQUAL')
        tag = 'ROW SETTLED-EQUAL' if ok == len(vs) and vs else 'ROW NOT SETTLED'
        out.append('\t'.join(['ROW', f[1], f[2], 'settled-equal %d of %d' % (ok, len(vs)), tag]))
    else:
        out.append(l)
open(_argv[3], 'w').write('\n'.join(out) + '\n')
print('escape.py: %d target pairs re-classed CSTR-ESCAPE SETTLED-EQUAL; %d left UNSETTLED%s' % (
    replaced, len(kept), ''.join('\n  %s %s: %s' % (a, b, '; '.join(c)) for a, b, c in kept)))
