#!/usr/bin/env python3
"""settle5-B.py D_TWIN T_TWIN: settle every target cmpkit 86da41d3ef68's strictcmp3 `tcmp` refuses in the five runtime
functions TCB names (MaybeReleaseToOS, __sanitizer::VSNPrintf, __asan::Decorator::ShadowByte,
__sanitizer::SignalContext::Describe, __strftime_fmt_1), donor libreac fuzz_decode.asan-ubsan vs libdiginet
fuzz_transport.asan-ubsan (re-pinned 41113a03c82f). Each function by (address, size) after a unique-name check.

For each differing target of tcmp's FULL list, the target address on both sides comes from strictcmp3's own `targets`
pass over the function bytes. Settlement (kit verdict and settled verdict side by side):
  rel4 code    base-relative 4-byte signed entries w, base + w inside the function (a switch table): N = the run of such
               entries from the base, equal on both sides; every entry compared as SYMBOL + OFFSET (qres).
  rel4 string  base + w inside .rodata (a string-pointer table, e.g. Describe's signal names): every entry compared as
               its C string up to and including the NUL; N as above.
  cstring      first byte NUL on both sides (an empty string): compared with its NUL.
  bytes(64)    otherwise the 64 bytes from the target (MaybeReleaseToOS's ctz table).
  lui          a lui-built value in a section: printed for the hand dataflow (the kit's dataflow does not follow
               add / sub / shNadd); see the record for each use.
Anything not EQUAL is NOT CERTIFIED. Output TSV: fn, word offset, kind, kit verdict, settled verdict, detail."""
import importlib.util, os, struct, sys
import capstone
HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location('s3', os.path.join(HERE, 'strictcmp3.py'))
s3 = importlib.util.module_from_spec(spec); sys.argv, argv = ['x'], sys.argv; spec.loader.exec_module(s3)
D, T = argv[1:3]
I = {'D': s3.Img(D), 'T': s3.Img(T)}
NAMES = ['_ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE16MaybeReleaseToOSEPNS_12MemoryMapperIS5_EEmb',
         '_ZN11__sanitizer9VSNPrintfEPciPKcPv', '_ZN6__asan9Decorator10ShadowByteEh',
         '_ZNK11__sanitizer13SignalContext8DescribeEv', '__strftime_fmt_1']
MD = capstone.Cs(capstone.CS_ARCH_RISCV, capstone.CS_MODE_RISCV64 | capstone.CS_MODE_RISCVC)


def rel_tbl(Im, a, fn, strings):
    out = []
    while True:
        b = s3.frd(Im, a + 4 * len(out), 4)
        if b is None:
            return out
        x = a + struct.unpack('<i', b)[0]
        if strings:
            if Im.sec(x) != '.rodata':
                return out
            s = s3.frd(Im, x, 256)
            out.append(s[:s.index(b'\0') + 1] if s and b'\0' in s else None)
        else:
            if not fn[0] <= x < fn[1]:
                return out
            out.append(s3.qres(Im, x))


def lui_window(Im, fa, n, off):
    ins = list(MD.disasm(s3.frd(Im, fa, n), fa))
    k = next(i for i, x in enumerate(ins) if x.address - fa == off)
    return ' ; '.join('%+#x %s %s' % (x.address - fa, x.mnemonic, x.op_str) for x in ins[max(0, k - 1):k + 4])

def bytetable(Im, fa, n, off):
    """an indexed byte table formed at fa+off: an `srli r, r, S` just before and an `add` + `lbu` just after (the ctz /
    De Bruijn lookup): N = 1 << (64 - S); None otherwise"""
    ins = list(MD.disasm(s3.frd(Im, fa, n), fa))
    k = next(i for i, x in enumerate(ins) if x.address - fa == off)
    win = ins[max(0, k - 3):k + 4]
    sr = [x for x in win[:4] if x.mnemonic == 'srli']
    if sr and any(x.mnemonic == 'lbu' for x in win[3:]) and any(x.mnemonic == 'add' for x in win[3:]):
        return 1 << (64 - int(sr[-1].op_str.split(',')[-1], 0))
    return None


def consumer(Im, fa, n, off):
    ins = list(MD.disasm(s3.frd(Im, fa, n), fa))
    k = next(i for i, x in enumerate(ins) if x.address - fa == off)
    return ' ; '.join('%+#x %s %s' % (x.address - fa, x.mnemonic, x.op_str) for x in ins[k:k + 4])



print('fn\toffset\tkind\tkit\tsettled\tdetail')
for nm in NAMES:
    c = {k: s3.fcopies(I[k], nm) for k in 'DT'}
    assert all(len({(v, z) for v, z, q in c[k]}) == 1 for k in 'DT'), (nm, c)
    (a1, n1, _), (a2, n2, _) = c['D'][0], c['T'][0]
    assert n1 == n2
    fb = []
    v, cc, t3, diff = s3.tcmp(I, 'D', a1, 'T', a2, n1, fb)
    b1, b2 = s3.frd(I['D'], a1, n1), s3.frd(I['T'], a2, n2)
    tg1, tg2 = s3.targets(a1, b1), s3.targets(a2, b2)
    short = 'MaybeReleaseToOS' if 'MaybeRelease' in nm else nm
    print(f'# {short}: D {a1:#x} T {a2:#x} size {n1}: tcmp verdict {v}, {len(diff)} differing targets')
    for d in diff:
        off, kind = int(d[0], 16), d[3]
        if kind == 'lui-in-section':
            print(f'{short}\t{off:#x}\tlui\tDIFFERENT ({kind})\tHAND\tD: {lui_window(I["D"], a1, n1, off)} | '
                  f'T: {lui_window(I["T"], a2, n2, off)} | kit: {d[4][0]}')
            continue
        x1 = [t for i, (k_, t) in sorted(tg1.items()) if s3.w_off(b1, i) == off][0]
        x2 = [t for i, (k_, t) in sorted(tg2.items()) if s3.w_off(b2, i) == off][0]
        bt1, bt2 = bytetable(I['D'], a1, n1, off), bytetable(I['T'], a2, n2, off)
        if bt1 is not None or bt2 is not None:
            assert bt1 == bt2, (short, off, bt1, bt2)
            q1, q2 = s3.frd(I['D'], x1, bt1), s3.frd(I['T'], x2, bt2)
            print(f'{short}\t{off:#x}\tbyte table\tDIFFERENT ({kind})\t{"EQUAL" if q1 == q2 else "NOT CERTIFIED"}\t'
                  f'indexed lbu after srli {64 - bt1.bit_length() + 1}: N {bt1} at {x1:#x} / {x2:#x}: {q1.hex()} / {q2.hex()}')
            continue
        if s3.frd(I['D'], x1, 1) == s3.frd(I['T'], x2, 1) == b'\x00':
            cons = consumer(I['T'], a2, n2, off)
            print(f'{short}\t{off:#x}\tcstring\tDIFFERENT ({kind})\tEQUAL\tempty string at {x1:#x} / {x2:#x}: '
                  f'b"\\x00" on both; consumer (T): {cons}')
            continue
        done = False
        for strings in (False, True):
            e1 = rel_tbl(I['D'], x1, (a1, a1 + n1), strings)
            e2 = rel_tbl(I['T'], x2, (a2, a2 + n2), strings)
            if len(e1) >= 2:
                ok = e1 == e2
                what = 'rel4 string' if strings else 'rel4 code'
                det = (f'N {len(e1)} / {len(e2)} at {x1:#x} / {x2:#x}; '
                       + (f'entries {e1}' if ok else f'pairs {list(zip(e1, e2))}'))
                print(f'{short}\t{off:#x}\t{what}\tDIFFERENT ({kind})\t{"EQUAL" if ok else "NOT CERTIFIED"}\t{det}')
                done = True
                break
        if not done:
            q1, q2 = s3.frd(I['D'], x1, 64), s3.frd(I['T'], x2, 64)
            print(f'{short}\t{off:#x}\tbytes(64)\tDIFFERENT ({kind})\t{"EQUAL" if q1 == q2 else "NOT CERTIFIED"}\t'
                  f'at {x1:#x} / {x2:#x}: {q1.hex()} / {q2.hex()}')
