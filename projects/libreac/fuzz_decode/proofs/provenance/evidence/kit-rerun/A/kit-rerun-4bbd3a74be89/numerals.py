#!/usr/bin/env python3
"""numerals.py -- re-check, on cmpkit 4bbd3a74be89, the per-numeral word claim of ALLOC-PATTERN.md section 8: each of the
417 code numerals of image A's relocated Allocate chain points at donor symbol + offset, and the word at that offset in
the decode copy is identical to the donor's or differs only pc-relatively.

Classification is bytecmp 1480ca2faea0's own per-word rule (its `cmp`, lines 158-177), loaded through the kit's drvcmp
(which sha-checks the bytecmp file), re-applied word by word so that each numeral's own offset can be named; and, for
the words that are compared pc-relative TARGETS, strictcmp2 16982e3ef42b's verdict on that target (the kit's ONE
compare): a target difference at the word is reported as `target-differ`.

usage: numerals.py KIT NUMERALS.TSV PAIRS.TSV C-ELF A-ELF OUT.TSV
"""
import collections, importlib.util, os, sys

KIT, NUM, PAIRS, CELF, AELF, OUT = sys.argv[1:7]
sys.dont_write_bytecode = True
_sp = importlib.util.spec_from_file_location('strictcmp2_kit', os.path.join(KIT, 'strictcmp2.py'))
S = importlib.util.module_from_spec(_sp); _sp.loader.exec_module(S)
UNKNOWN = S._bc['UNKNOWN']
flow_states = S._bc['flow_states']

# the words the old record singled out (ecall / AMO / LR / SC), named there by function and byte offset
SPECIAL = {('_ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb', 0x328): 'lr',
           ('_ZN6__asan9Allocator8AllocateEmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeEb', 0x33c): 'sc',
           ('_ZN11__sanitizer17CombinedAllocatorINS_20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE'
            'ENS_33LargeMmapAllocatorPtrArrayDynamicEE8AllocateEPNS_30SizeClassAllocator64LocalCacheIS6_EEmm', 0x1d8): 'amo',
           ('_ZN11__sanitizer13internal_mmapEPvmiiiy', 0x4): 'ecall'}


def word_classes(b1, b2):
    """bytecmp 1480ca2faea0 cmp's per-word verdict, by byte offset: same / pcrel / real / unmeasured"""
    w1, w2 = S.bc_words(b1), S.bc_words(b2)
    assert len(w1) == len(w2) and all(a[2] == b[2] for a, b in zip(w1, w2)), 'SHAPE'
    st = flow_states(w1); out = {}
    for i, ((o, x, n), (_, y, _)) in enumerate(zip(w1, w2)):
        if x == y:
            out[o] = 'same'; continue
        if n == 4 and (x & 0x7f) == (y & 0x7f):
            op = x & 0x7f; rs1 = (x >> 15) & 31
            mask = 0x01fff07f if op in (0x23, 0x27) else 0x000fffff
            lo12_shape = op in (0x13, 0x03, 0x23, 0x67, 0x07, 0x27) and (x & mask) == (y & mask)
            j = st[i].get(rs1)
            if op in (0x17, 0x6f) and ((x >> 7) & 31) == ((y >> 7) & 31): out[o] = 'pcrel'
            elif lo12_shape and j is not None and j >= 0: out[o] = 'pcrel'
            elif lo12_shape and j == UNKNOWN: out[o] = 'unmeasured'
            else: out[o] = 'real'
        else:
            out[o] = 'real'
    return out, {o: (x, y) for (o, x, _), (_, y, _) in zip(w1, w2)}


I = {'C': S.Img(CELF), 'A': S.Img(AELF)}
fns = [l.split('\t')[0] for l in open(PAIRS).read().splitlines()[1:] if l.strip()]
OPC = {0x03: 'load', 0x23: 'store', 0x07: 'fp-load', 0x27: 'fp-store', 0x6f: 'jal', 0x67: 'jalr',
       0x63: 'branch', 0x17: 'auipc', 0x37: 'lui', 0x13: 'op-imm', 0x1b: 'op-imm32', 0x33: 'op', 0x3b: 'op32',
       0x2f: 'amo', 0x73: 'system', 0x0f: 'fence', 0x53: 'fp-op'}
LOADF3 = {0: 'lb', 1: 'lh', 2: 'lw', 3: 'ld', 4: 'lbu', 5: 'lhu', 6: 'lwu'}
STOREF3 = {0: 'sb', 1: 'sh', 2: 'sw', 3: 'sd'}


def consumer(k, addr):
    """what the image does at addr: the instruction there (the site the proof's pc names), or the object it is in.
    A numeral that is in no executable section and in no object is a non-address use (a size or a mask constant)."""
    sec = I[k].sec(addr)
    w = S.frd(I[k], addr, 4)
    if sec is None: return 'no section (non-address use)'
    if not S.execsec(I[k], addr):
        r = S.qres(I[k], addr)
        return 'data in %s (%s), not an instruction' % (sec, r or 'unnamed')
    if w is None: return 'code in %s, not file-backed' % sec
    x = int.from_bytes(w, 'little')
    if x & 3 != 3: return 'compressed instruction (%04x) in %s' % (x & 0xffff, sec)
    op = x & 0x7f; f3 = (x >> 12) & 7
    nm = OPC.get(op, 'opcode %#x' % op)
    if op == 0x03: nm = LOADF3.get(f3, nm)
    elif op == 0x23: nm = STOREF3.get(f3, nm)
    elif op == 0x2f: nm = {2: 'lr/sc/amo.w', 3: 'lr/sc/amo.d'}.get(f3, 'amo')
    elif op == 0x73: nm = 'ecall/ebreak/csr'
    elif op == 0x13 and f3 == 0: nm = 'addi'
    return '%s (%08x)' % (nm, x)

cls, raw, tdiff = {}, {}, {}
for f in fns:
    s1, s2 = I['C'].fsym(f), I['A'].fsym(f)
    assert s1 and s2 and s1[1] == s2[1], (f, s1, s2)
    b1, b2 = S.frd(I['C'], s1[0], s1[1]), S.frd(I['A'], s2[0], s2[1])
    cls[f], raw[f] = word_classes(b1, b2)
    _v, _c, _t3, diff = S.tcmp(I, 'C', s1[0], 'A', s2[0], s1[1], [])
    tdiff[f] = {int(d[0], 16): d[3] for d in diff}

rows = open(NUM).read().splitlines()
hdr = rows[0].split('\t')
out = [hdr[:5] + ['kit_word_class', 'strictcmp2_target', 'donor_word', 'decode_word', 'same_as_old',
                  'consumes_donor_value', 'consumes_decode_value']]
cnt_old, cnt_new, changed, cons = collections.Counter(), collections.Counter(), [], collections.Counter()
for ln in rows[1:]:
    if not ln.strip(): continue
    c = ln.split('\t')
    fn, off = c[3].rsplit('+', 1); off = int(off, 16)
    k = cls[fn][off]; x, y = raw[fn][off]
    td = tdiff[fn].get(off, '')
    cnt_old[c[4]] += 1; cnt_new[k] += 1
    same = 'yes' if k == c[4] and not td else 'no'
    if same == 'no': changed.append((c[0], fn, hex(off), c[4], k, td))
    cd, ca = consumer('C', int(c[1], 16)), consumer('A', int(c[2], 16))
    cons[ca.split(' (')[0]] += 1
    out.append(c[:5] + [k, td, '%08x' % x, '%08x' % y, same, cd, ca])
open(OUT, 'w').write('\n'.join('\t'.join(r) for r in out) + '\n')

print('# kit', KIT, 'strictcmp2 sha256', S.sha(os.path.join(KIT, 'strictcmp2.py'))[:12],
      'bytecmp sha256', S.sha(os.path.join(KIT, 'bytecmp-1480ca2faea0.py'))[:12])
print('# C', CELF, S.sha(CELF)[:12])
print('# A', AELF, S.sha(AELF)[:12])
print('numerals', len(out) - 1)
print('old classes', dict(cnt_old))
print('kit classes', dict(cnt_new))
print('changed', len(changed), changed[:20])
print('what the decode image does at each numeral (the instruction that consumes it):', dict(cons))
print()
print('SINGLED-OUT WORDS (ecall / AMO / LR / SC) of the old record')
for (fn, off), tag in SPECIAL.items():
    x, y = raw[fn][off]
    print('%-6s %s+%#x: donor %08x decode %08x -> %s%s' %
          (tag, fn[:48], off, x, y, cls[fn][off], ' target-differ ' + tdiff[fn][off] if off in tdiff[fn] else ''))
print()
print('ALL words of the 7 functions, by kit class')
for f in fns:
    c = collections.Counter(cls[f].values())
    print('%-60s %s target-differ %s' % (f[:60], dict(c), tdiff[f] or 0))
