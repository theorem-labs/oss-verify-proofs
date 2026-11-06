#!/usr/bin/env python3
"""settle.py -- by-hand settlement of every row the kit's jtcheck left NOT settled (`UNMEASURED` and `DIFF`) over the closure
members the closure script reported (out/jtcheck.out), and the measure() fulldiff.py applies to every non-lui target.
Read-only; nothing here is a kit verdict.

For each (function, word offset), the target in each image is the kit's own `targets` (strictcmp3 -> drvcmp), and the
measurement is chosen by what the code does with the target register (rd of the word), read from the following words of
the same function with capstone:
  DEBRUIJN  rd is added to an index made by `srli _, _, 58` (0..63) and read by one `lbu`: the 64 bytes at both targets
            must be equal.
  RELJUMP   rd is a jump-table base: `bltu B, i` (B from an earlier `addi B, zero, K`), `slli i, i, 2`, `add _, i, rd`,
            `lw e, 0(_)`, `add _, e, rd`, `jr`: entries 0..K; every entry's target minus the function start must be equal
            on both sides.
  CSTR      otherwise, the target is used as an address (passed to a call / returned / stored): it must be a
            NUL-terminated byte string within 4096 bytes on both sides, and the two strings INCLUDING the NUL must be
            equal. Subclasses for the audit: EMPTY (the first byte is the NUL: ""), NONPRINT (a byte before the NUL is not
            printable ASCII, e.g. an ANSI escape), PRINT (all printable: the kit's own C-string rule would accept it, but
            the kit compared the region because ...: listed with the kit's reason if any).
Any other shape, or unequal bytes, is DIFFERS. Writes out/settle.tsv; prints the counts per class and every DIFFERS.
usage: settle.py [JTCHECK_OUT]"""
import sys, os, re, importlib.util, collections
from capstone import Cs, CS_ARCH_RISCV, CS_MODE_RISCV64, CS_MODE_RISCVC
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common
HERE = common.HERE
sc = common.kit_module(common.CMP_PY)
CG = os.environ.get('SETTLE_C', common.CGIF_B_TWIN)
DE = os.environ.get('SETTLE_D', common.DECODE_B_TWIN)
md = Cs(CS_ARCH_RISCV, CS_MODE_RISCV64 | CS_MODE_RISCVC)
md.detail = False
PRINTABLE = set(range(32, 127)) | {9, 10, 13}


def target_and_code(I, fn, off, at=None):
    a, z = at if at is not None else I.fsym(fn)    # at = (address, size): by address, never by name
    b = sc.frd(I, a, z)
    w = sc.bc_words(b)
    t = sc._g['targets'](a, b)
    idx = [i for i, (o, x, k) in enumerate(w) if o == off][0]
    tg = t[idx][1] if idx in t else None
    ins = [(i.address - a, i.mnemonic, i.op_str) for i in md.disasm(b, a)]
    return a, z, tg, ins


def rd_of(ins, off):
    m = [x for x in ins if x[0] == off][0]
    return m[2].split(',')[0].strip(), m


def classify(I, fn, off, at=None):
    a, z, tg, ins = target_and_code(I, fn, off, at)
    rd, word = rd_of(ins, off)
    after = [x for x in ins if off < x[0] <= off + 0x60]
    before = [x for x in ins if off - 0x40 <= x[0] < off]
    ops = ' ; '.join('%s %s' % (m, o) for _, m, o in after[:14])
    # DEBRUIJN: an add with rd, an index from srli 58 before or after, then lbu
    if re.search(r'srli \w+, \w+, 0x3a', ' ; '.join('%s %s' % (m, o) for _, m, o in before + after)) and \
            re.search(r'add \w+, (%s, \w+|\w+, %s) ; lbu' % (rd, rd), ops):
        return 'DEBRUIJN', tg, a, None
    m = re.search(r'bltu (\w+), (\w+), .*? ; slli \w+, \w+, 2 ; add \w+, \w+, %s ; lw \w+, 0\(\w+\) ; add \w+, \w+, %s ; jr' % (rd, rd), ops)
    if m:
        bnd = None
        for _, mn, op in reversed([x for x in ins if x[0] < off + 0x60]):
            mm = re.match(r'%s, zero, (0x[0-9a-f]+|\d+)$' % m.group(1), op)
            if mn in ('addi', 'li') and mm:
                bnd = int(mm.group(1), 0); break
            mm = re.match(r'%s, (0x[0-9a-f]+|-?\d+)$' % m.group(1), op)
            if mn == 'li' and mm:
                bnd = int(mm.group(1), 0); break
        return 'RELJUMP', tg, a, bnd
    # RELSTR: rd + index -> lw e -> rd + e is the RESULT (ret): a table of 4-byte offsets from rd to C strings, its
    # bound from `addi B, zero, K ; bltu B, i` before the word (SignalContext::Describe's signal names)
    if re.search(r'^add \w+, (%s, \w+|\w+, %s) ; lw (\w+), 0\(\w+\) ; add \w+, (%s, \w+|\w+, %s) ; ret' % (rd, rd, rd, rd), ops):
        pre = ' ; '.join('%s %s' % (mn, op) for _, mn, op in before)
        mm = re.search(r'addi (\w+), zero, (0x[0-9a-f]+|\d+) ; bltu \1, ', pre)
        return 'RELSTR', tg, a, int(mm.group(2), 0) if mm else None
    # INDEXED: rd + (index << S) -> one load of 2^S bytes from that sum, the index bounded by `addi B, zero, K ; bltu B, i`
    # (OpenFile's 3-entry open() flag table): exactly (K + 1) * 2^S bytes can be read
    m = re.match(r'add (\w+), (?:%s, (\w+)|(\w+), %s) ; (lw|lwu|ld|lh|lhu|lb|lbu) (\w+), 0\(\1\)' % (rd, rd), ops)
    if m:
        idx = m.group(2) or m.group(3)
        width = {'lw': 4, 'lwu': 4, 'ld': 8, 'lh': 2, 'lhu': 2, 'lb': 1, 'lbu': 1}[m.group(4)]
        win = [x for x in ins if off - 0x40 <= x[0] <= off + 0x60]
        sh = [(o, int(op.split(',')[2], 0)) for o, mn, op in win if mn == 'slli' and op.startswith('%s, %s,' % (idx, idx)) and o < off + 0x60]
        guard = None
        for k in range(len(win) - 1):
            o1, m1, p1 = win[k]; o2, m2, p2 = win[k + 1]
            mm = re.match(r'(\w+), zero, (0x[0-9a-f]+|\d+)$', p1)
            if m1 in ('addi', 'li') and mm and m2 == 'bltu' and p2.startswith('%s, %s,' % (mm.group(1), idx)):
                guard = (o1, o2, int(mm.group(2), 0))
        uses = [x[0] for x in after[:2]]
        if guard and sh and (1 << sh[0][1]) == width:
            return 'INDEXED', tg, a, (guard[2] + 1, width, guard[0], guard[1], sh[0][0], uses[0], uses[1], m.group(4))
        return 'INDEXED-NOGUARD', tg, a, None
    return 'CSTR', tg, a, ops


def measure(C, D, fn, off, atc=None, atd=None):
    kc, tc, ac, xc = classify(C, fn, off, atc)
    kd, td, ad, xd = classify(D, fn, off, atd)
    if kc != kd or tc is None or td is None:
        return 'DIFFERS', 'shape %s vs %s' % (kc, kd), tc, td
    if kc == 'DEBRUIJN':
        bc, bd = sc.frd(C, tc, 64), sc.frd(D, td, 64)
        return ('DEBRUIJN' if bc is not None and bc == bd else 'DIFFERS'), '64 B %s' % (bc.hex()[:16] if bc else None), tc, td
    if kc == 'RELJUMP':
        if xc is None or xc != xd:
            return 'DIFFERS', 'bound %s vs %s' % (xc, xd), tc, td
        oc, od = [], []
        for k in range(xc + 1):
            ec = int.from_bytes(sc.frd(C, tc + 4 * k, 4), 'little', signed=True)
            ed = int.from_bytes(sc.frd(D, td + 4 * k, 4), 'little', signed=True)
            oc.append(tc + ec - ac); od.append(td + ed - ad)
        return ('RELJUMP' if oc == od else 'DIFFERS'), '%d entries, function-relative targets %s' % (
            xc + 1, 'equal' if oc == od else 'differ'), tc, td
    if kc == 'RELSTR':
        if xc is None or xc != xd:
            return 'DIFFERS', 'bound %s vs %s' % (xc, xd), tc, td
        sc_, sd_ = [], []
        for k in range(xc + 1):
            ec = int.from_bytes(sc.frd(C, tc + 4 * k, 4), 'little', signed=True)
            ed = int.from_bytes(sc.frd(D, td + 4 * k, 4), 'little', signed=True)
            bc, bd = sc.frd(C, tc + ec, 256), sc.frd(D, td + ed, 256)
            sc_.append(bc[:bc.find(b'\0') + 1] if bc and b'\0' in bc else None)
            sd_.append(bd[:bd.find(b'\0') + 1] if bd and b'\0' in bd else None)
        ok = sc_ == sd_ and None not in sc_
        return ('RELSTR' if ok else 'DIFFERS'), '%d entries, C strings %s: %s' % (
            xc + 1, 'equal' if ok else 'differ', ' '.join(repr(s) for s in sc_)[:200]), tc, td
    if kc == 'INDEXED-NOGUARD':
        return 'DIFFERS', 'indexed load with no bound found: extent unknown', tc, td
    if kc == 'INDEXED':
        n, w, pg1, pg2, psl, padd, pld, ldm = xc
        if xd is None or xd[:2] != (n, w):
            return 'DIFFERS', 'bound / width %s vs %s' % (xc, xd), tc, td
        bc, bd = sc.frd(C, tc, n * w), sc.frd(D, td, n * w)
        vals = [int.from_bytes(bc[k * w:(k + 1) * w], 'little', signed=True) for k in range(n)] if bc else None
        return ('INDEXED' if bc is not None and bc == bd else 'DIFFERS'), (
            '%d entries of %d bytes = %d bytes read (bound: +%#x `addi B, zero, %d` ; +%#x `bltu B, i`; +%#x `slli i, i, %d`; '
            '+%#x `add` ; +%#x `%s _, 0(_)`): bytes %s both, entries %s' % (
                n, w, n * w, pg1, n - 1, pg2, psl, w.bit_length() - 1, padd, pld, ldm,
                'EQUAL' if bc == bd else 'DIFFER', vals)), tc, td
    bc, bd = sc.frd(C, tc, 4096), sc.frd(D, td, 4096)
    if bc is None or bd is None:
        return 'DIFFERS', 'unreadable', tc, td
    nc, nd = bc.find(b'\0'), bd.find(b'\0')
    if nc < 0 or nd < 0 or bc[:nc + 1] != bd[:nd + 1]:
        return 'DIFFERS', 'strings differ: %r | %r' % (bc[:max(nc, 0) + 1][:40], bd[:max(nd, 0) + 1][:40]), tc, td
    s = bc[:nc + 1]
    sub = 'EMPTY' if nc == 0 else ('NONPRINT' if any(ch not in PRINTABLE for ch in s[:-1]) else 'PRINT')
    return 'CSTR-' + sub, '%r (%d B incl NUL); used as: %s' % (s[:60], nc + 1, xc[:120]), tc, td


def main():
    jt = sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, 'out', common.JT_OUT)
    C, D = sc.Img(CG), sc.Img(DE)
    rows, cur = [], None
    for l in open(jt):
        l = l.rstrip('\n')
        if not l.startswith(' ') and '\t' in l and not l.startswith(('CSTR\t', 'ACCEPT')):
            cur = l.split('\t')[0]
            continue
        m = re.match(r'\s+(UNMEASURED|DIFF) \+(0x[0-9a-f]+) ', l)
        if m:
            rows.append((cur, m.group(1), int(m.group(2), 16)))
    out, cnt = [], collections.Counter()
    for fn, kind, off in rows:
        v, why, tc, td = measure(C, D, fn, off)
        cnt[v] += 1
        out.append((fn, '+%#x' % off, kind, v, hex(tc) if tc else '-', hex(td) if td else '-', why))
    with open(os.path.join(HERE, 'out', 'settle.tsv'), 'w') as f:
        f.write('function\tword\tjtcheck\tsettlement\tcgif target\tdecode target\tmeasurement\n')
        for r in out:
            f.write('\t'.join(r) + '\n')
    print('rows %d: %s' % (len(out), dict(cnt)))
    for r in out:
        if r[3] == 'DIFFERS':
            print('DIFFERS', r[0][:70], r[1], r[6][:200])


if __name__ == '__main__':
    main()
