#!/usr/bin/env python3
"""bytecmp.py DONOR_TWIN TARGET_TWIN [--plant TPC:HEXWORD]: compare, instruction by instruction, every code body that
lib/B/Rt/YF0r.v / YF0s.v step through (the code table fs_ranges and its callees), donor fuzz_grant.asan-ubsan
(unstripped twin) against target fuzz_uci.asan-ubsan (unstripped twin).

A body is named by its symbol; a local name with several copies (MemToShadow) is taken where the paired call site
lands (`via`). Both bodies are disassembled linearly (capstone RISCV64 | RVC). Two instructions are IDENTICAL when
mnemonic, operands and size agree. A differing pair is SAME when it is pc-relative and both sides resolve to the same
place: jal -> the symbol + offset it lands on; auipc + its partner (addi / ld / lw / lb / lbu / sd ... on the same
register) -> the symbol + offset of the effective address, and for a load from a .got slot the symbol + offset the
slot holds (a slot that holds no symbol value is compared by its bytes, 24 bytes from the slot). Anything else is
DIFFERENT. Exit 0 when every body is equal up to relocation, 1 otherwise.

--plant TPC:HEXWORD overwrites the 4 bytes at target pc TPC with HEXWORD (little-endian instruction word) in memory
only: the control (one planted word must give exactly one DIFFERENT row and exit 1)."""
import bisect, hashlib, sys

import capstone
from elftools.elf.elffile import ELFFile

SHA = {'donor': '5a5ee7c02b4e2a1d1653dc0c256182c9b65c33dde3a7ddc98b9de2afffe7a417',
       'target': '8d07ffcf594874884207465cc34ff9f3b1062f21f6d9b3622e0771fa76490b16'}

# (label, symbol, via): via = None (unique name) or (caller symbol, offset of the jal in the caller)
BODIES = [
    ('__asan_stack_malloc_1 (FS_ENTRY .. FS_RET; fs_ranges)', '__asan_stack_malloc_1', None),
    ('__interceptor_trampoline___tls_get_addr (callee of stack_malloc_1 +0x20)', '__interceptor_trampoline___tls_get_addr', None),
    ('___interceptor___tls_get_addr (fs_ranges)', '___interceptor___tls_get_addr', None),
    ('__asan::TryAsanInitFromRtl (callee of the interceptor +0x18)', '_ZN6__asan18TryAsanInitFromRtlEv', None),
    ('__tls_get_addr (fs_ranges; the interceptor calls it through .got)', '__tls_get_addr', None),
    ('__asan::GetCurrentThread (fs_ranges)', '_ZN6__asan16GetCurrentThreadEv', None),
    ('__asan::AsanTSDGet (fs_ranges, first 6 words)', '_ZN6__asan10AsanTSDGetEv', None),
    ('__pthread_getspecific (fs_ranges)', '__pthread_getspecific', None),
    ('__sanitizer::DTLS_on_tls_get_addr (fs_ranges, first 140 words)', '_ZN11__sanitizer20DTLS_on_tls_get_addrEPvS0_mm', None),
    ('__asan::MemToShadow, the copy stack_malloc_1 +0x144 calls (fs_ranges, first 28 words)', '_ZN6__asanL11MemToShadowEm',
     ('__asan_stack_malloc_1', 0x144)),
    ('__sanitizer::RegisterCommonFlags (fs_ranges: the 2 words at +0x358)', '_ZN11__sanitizer19RegisterCommonFlagsEPNS_10FlagParserEPNS_11CommonFlagsE', None),
    ('__asan::FakeStack::GC (callee of stack_malloc_1 +0x40)', '_ZN6__asan9FakeStack2GCEm', None),
    ('__asan::AsanThread::AsyncSignalSafeLazyInitFakeStack (callee of stack_malloc_1 +0x180)',
     '_ZN6__asan10AsanThread32AsyncSignalSafeLazyInitFakeStackEv', None),
]
PCREL_PARTNER = {'addi', 'ld', 'lw', 'lwu', 'lh', 'lhu', 'lb', 'lbu', 'sd', 'sw', 'sh', 'sb', 'jalr', 'flw', 'fld'}


class Img:
    def __init__(self, path, role):
        raw = open(path, 'rb').read()
        sha = hashlib.sha256(raw).hexdigest()
        if sha != SHA[role]:
            sys.exit(f'{role} {path}: sha256 {sha} is not {SHA[role]}')
        self.sha = sha
        self.f = open(path, 'rb')
        self.e = ELFFile(self.f)
        self.segs = [(p['p_vaddr'], p['p_filesz'], p['p_memsz'], p['p_offset']) for p in self.e.iter_segments()
                     if p['p_type'] == 'PT_LOAD']
        self.secs = [(s.name, s['sh_addr'], s['sh_size']) for s in self.e.iter_sections() if s['sh_addr']]
        syms = []
        for s in self.e.get_section_by_name('.symtab').iter_symbols():
            if s.name and not s.name.startswith('$') and s['st_info']['type'] in ('STT_FUNC', 'STT_OBJECT', 'STT_TLS') \
                    and s['st_size'] > 0:
                syms.append((s['st_value'], s['st_size'], s.name, s['st_info']['type']))
        syms.sort()
        self.syms = syms
        self.starts = [s[0] for s in syms]
        self.byname = {}
        for a, sz, n, ty in syms:
            self.byname.setdefault(n, []).append((a, sz))
        self.plants = {}

    def read(self, a, n):
        """n bytes at virtual address a. Only the part beyond p_filesz is zero-filled: zero-filling the WHOLE range
        when it crosses that bound made a window near the end of .got read as zeros in both images, so two places
        compared equal for the wrong reason (found 12:2xZ)."""
        for v, fs, ms, off in self.segs:
            if v <= a and a + n <= v + ms:
                have = max(0, min(n, v + fs - a))
                b = bytearray(n)
                if have:
                    self.f.seek(off + a - v)
                    b[:have] = self.f.read(have)
                for pa, w in self.plants.items():
                    for k in range(len(w)):
                        if a <= pa + k < a + n:
                            b[pa + k - a] = w[k]
                return bytes(b)
        return None

    def where(self, a):
        """symbol + offset of a sized symbol holding a (the smallest), else section + offset."""
        i = bisect.bisect_right(self.starts, a)
        best = None
        for j in range(max(0, i - 64), i):
            st, sz, n, ty = self.syms[j]
            if st <= a < st + sz and (best is None or sz < best[1]):
                best = (st, sz, n, ty)
        if best:
            return ('sym', best[2], a - best[0])
        for n, ad, sz in self.secs:
            if ad <= a < ad + sz:
                return ('sec', n, None)
        return ('abs', hex(a), None)

    def where_data(self, a):
        """where() for a value read out of a data cell. It ignores a TLS symbol, whose st_value is an offset in the TLS
        block and not an address: without that, the TLS index pair (module id 1, offset) of a .got cell resolved to
        'the TLS object holding address 1' (found 12:2xZ)."""
        i = bisect.bisect_right(self.starts, a)
        best = None
        for j in range(max(0, i - 64), i):
            st, sz, n, ty = self.syms[j]
            if ty != 'STT_TLS' and st <= a < st + sz and (best is None or sz < best[1]):
                best = (st, sz, n, ty)
        return ('sym', best[2], a - best[0]) if best else ('none', None, None)


def cs():
    m = capstone.Cs(capstone.CS_ARCH_RISCV, capstone.CS_MODE_RISCV64 | capstone.CS_MODE_RISCVC)
    m.detail = False
    return m


MD = cs()


def insns(img, a, n):
    return list(MD.disasm(img.read(a, n), a))


def imm_of(op_str):
    return int(op_str.split(',')[-1].strip(), 0)


def reg0(op_str):
    return op_str.split(',')[0].strip()


def body_addr(img, sym, via):
    if via is None:
        c = img.byname[sym]
        if len(c) != 1:
            sys.exit(f'{sym}: {len(c)} copies, give a via')
        return c[0]
    caller, off = via
    (ca, _), = img.byname[caller]
    i = insns(img, ca + off, 4)[0]
    assert i.mnemonic == 'jal', (caller, off, i.mnemonic)
    tgt = ca + off + imm_of(i.op_str)
    for a, sz in img.byname[sym]:
        if a == tgt:
            return a, sz
    sys.exit(f'{sym}: the call at {caller}+{off:#x} lands on {tgt:#x}, no copy of the name there')


def auipc_hi(ins):
    imm = imm_of(ins.op_str) & 0xfffff
    if imm >= 0x80000:
        imm -= 0x100000
    return (ins.address + (imm << 12)) % (1 << 64)


def partner(seq, k, rd):
    """index and effective-address offset of the first instruction after seq[k] that uses rd as its base, before rd is
    written again (the auipc pairs interleave: auipc a0; auipc a1; addi a0, a0, x; addi a2, a1, y)."""
    for j in range(k + 1, min(k + 17, len(seq))):
        ins = seq[j]
        parts = [p.strip() for p in ins.op_str.split(',')]
        if ins.mnemonic == 'addi' and len(parts) == 3 and parts[1] == rd:
            return j, int(parts[2], 0)
        if ins.mnemonic in PCREL_PARTNER and ins.mnemonic != 'addi' and parts and '(' in parts[-1]:
            off, base = parts[-1][:-1].split('(')
            if base == rd:
                return j, int(off or '0', 0)
        if parts and parts[0] == rd and ins.mnemonic not in ('sd', 'sw', 'sh', 'sb') and not ins.mnemonic.startswith('b'):
            return None, None
    return None, None


PTR_SECS = ('.got', '.got.plt', '.data.rel.ro', '.plt.got')


def place_bytes(img, ea, sec):
    """The evidence for a place with no sized symbol.

    A cell of a POINTER section is read as its 8-byte value and RESOLVED to the symbol + offset it names, the way a
    .got cell must be read: a relocated pointer is not byte-equal across two images unless both name the same address.
    When the value resolves to no sized symbol it is reported as the cell's 16 bytes, which is what a TLS index pair
    (module id, offset) is.
    Any other place: its section, the NUL-terminated string at it AND a fixed 64-byte window. The window is what makes
    that fail closed; a NUL cut alone calls two DIFFERENT places equal whenever their strings agree, and for an EMPTY
    string that is one zero byte (the defect class of jtcheck 2e2f9c2126b2 and repin_check 9cbc3553c09e).
    The offset in the section is NOT compared: a relocated place legitimately moves inside its section."""
    if sec in PTR_SECS:
        cell = img.read(ea, 16) or b''
        val = int.from_bytes(cell[:8], 'little')
        w = img.where_data(val)
        return (sec, 'ptr', w) if w[0] == 'sym' else (sec, 'cell', cell.hex())
    b = img.read(ea, 64) or b''
    z = b.find(b'\0')
    return (sec, b[:z + 1].hex() if 0 <= z < 63 else '', b.hex())


def resolve(img, seq, k):
    """the place a pc-relative instruction names, image-independently; (place, partner index or None)."""
    ins = seq[k]
    m = ins.mnemonic
    if m in ('jal', 'j'):
        return ('call' if m == 'jal' else 'jump', img.where(ins.address + imm_of(ins.op_str))), None
    if m == 'auipc':
        rd = reg0(ins.op_str)
        hi = auipc_hi(ins)
        j, off = partner(seq, k, rd)
        if j is None:
            return ('auipc-alone', img.where(hi)), None
        ea = (hi + off) % (1 << 64)
        pm = seq[j].mnemonic
        w = img.where(ea)
        if pm == 'ld' and w[0] == 'sec' and w[1] in ('.got', '.got.plt'):
            slot = int.from_bytes(img.read(ea, 8), 'little')
            ws = img.where(slot)
            if ws[0] == 'sym':
                return ('got', ws), j
            return ('got-bytes', img.read(ea, 24).hex()), j
        if w[0] == 'sym':
            return (pm, w), j
        return (pm, 'bytes') + place_bytes(img, ea, w[1]), j
    return None, None



def fields(ins):
    """The instruction with ONLY its pc-relative immediate masked out. Two pc-relative words, or an auipc partner,
    that agree on their target but differ outside the immediate (a destination or source register, funct3, the
    opcode) are a DIFFERENCE: a planted `addi s1, a0, ..` for `addi s0, a0, ..` was called SAME before this check
    (found by a fresh review). Masks: auipc / jal keep rd + opcode; I-type (addi, loads, jalr, flw / fld) keep
    rs1 + funct3 + rd + opcode; S-type (stores) keep rs2 + rs1 + funct3 + opcode. A 2-byte (RVC) word keeps its
    mnemonic and its operands with every number blanked."""
    if ins.size != 4:
        return ('rvc', ins.mnemonic, _re_num.sub('#', ins.op_str))
    w = int.from_bytes(ins.bytes, 'little')
    op = w & 0x7f
    if op in (0x17, 0x6f):
        return w & 0x00000fff
    if op in (0x13, 0x03, 0x07, 0x67):
        return w & 0x000fffff
    if op in (0x23, 0x27):
        return w & 0x01fff07f
    return w


_re_num = __import__('re').compile(r'-?0x[0-9a-fA-F]+|-?\b\d+\b')

def compare(d, t, label, sym, via):
    da, dsz = body_addr(d, sym, via)
    ta, tsz = body_addr(t, sym, via)
    di, ti = insns(d, da, dsz), insns(t, ta, tsz)
    rows, same, ident, diff = [], 0, 0, 0
    n = min(len(di), len(ti))
    consumed = set()
    for k in range(n):
        a, b = di[k], ti[k]
        if a.address - da != b.address - ta:
            rows.append((hex(a.address), hex(b.address), a.mnemonic, 'offset', 'offset', 'DIFFERENT'))
            diff += 1
            break
        if (a.mnemonic, a.op_str, a.size) == (b.mnemonic, b.op_str, b.size):
            if a.mnemonic not in ('jal', 'j', 'auipc'):
                ident += 1
                continue
            # a pc-relative word with the same text lands on the same place only if the layouts agree: resolve it
            ra, ja = resolve(d, di, k)
            rb, jb = resolve(t, ti, k)
            if ra == rb and ja == jb:
                if ja is not None:
                    consumed.add(ja)
                ident += 1
            else:
                rows.append((hex(a.address), hex(b.address), f'{a.mnemonic} {a.op_str} (same word)', str(ra), str(rb), 'DIFFERENT'))
                diff += 1
            continue
        if k in consumed:
            if fields(a) == fields(b):
                same += 1
            else:
                rows.append((hex(a.address), hex(b.address), f'{a.mnemonic} {a.op_str} / {b.mnemonic} {b.op_str}',
                             'partner of a matched pair', 'fields outside the immediate differ', 'DIFFERENT'))
                diff += 1
            continue
        ra, ja = resolve(d, di, k)
        rb, jb = resolve(t, ti, k)
        if ra is None and rb is None:
            # the partner of an earlier auipc whose own text is identical: resolve the pair from that auipc
            for p in range(k - 1, max(-1, k - 17), -1):
                if di[p].mnemonic == 'auipc' and ti[p].mnemonic == 'auipc':
                    pa, qa = resolve(d, di, p)
                    pb, qb = resolve(t, ti, p)
                    if qa == k and qb == k:
                        ra, ja, rb, jb = pa, None, pb, None
                        break
        if ra is not None and ra == rb and a.mnemonic == b.mnemonic and ja == jb and fields(a) == fields(b):
            if ja is not None:
                consumed.add(ja)
            rows.append((hex(a.address), hex(b.address), a.mnemonic, str(ra), str(rb), 'SAME'))
            same += 1
        else:
            rows.append((hex(a.address), hex(b.address), f'{a.mnemonic} {a.op_str} / {b.mnemonic} {b.op_str}', str(ra), str(rb), 'DIFFERENT'))
            diff += 1
    if len(di) != len(ti) or dsz != tsz:
        diff += 1
        rows.append(('-', '-', f'size {dsz} / {tsz}, insns {len(di)} / {len(ti)}', '', '', 'DIFFERENT'))
    return dict(label=label, sym=sym, da=da, ta=ta, dsz=dsz, tsz=tsz, nd=len(di), nt=len(ti), ident=ident, pcrel=same,
                diff=diff, rows=rows)


def main():
    args = sys.argv[1:]
    plant = pdata = None
    if '--plant' in args:
        k = args.index('--plant')
        plant = args[k + 1]
        del args[k:k + 2]
    if '--plant-data' in args:
        # --plant-data ADDR:HEX overwrites bytes at a DATA address of the target: the control for a pointer place
        k = args.index('--plant-data')
        pdata = args[k + 1]
        del args[k:k + 2]
    d, t = Img(args[0], 'donor'), Img(args[1], 'target')
    if plant:
        pc, w = plant.split(':')
        t.plants[int(pc, 0)] = int(w, 16).to_bytes(4, 'little')
    if pdata:
        ad, hx = pdata.split(':')
        t.plants[int(ad, 0)] = bytes.fromhex(hx)
    res = [compare(d, t, *b) for b in BODIES]
    print(f'donor  sha256 {d.sha}\ntarget sha256 {t.sha}\ntool: pyelftools + capstone {capstone.__version__} (RISCV64 | RVC)')
    print('\n| body | donor | target | bytes | insns | identical | pc-relative, same place | different | verdict |')
    print('|---|---|---|---|---|---|---|---|---|')
    bad = 0
    for r in res:
        v = 'EQUAL UP TO RELOCATION' if r['diff'] == 0 else 'NOT EQUAL'
        bad += r['diff'] != 0
        print(f"| {r['label']} | {r['da']:#x} | {r['ta']:#x} | {r['dsz']} / {r['tsz']} | {r['nd']} / {r['nt']} | {r['ident']} | {r['pcrel']} | {r['diff']} | {v} |")
    for r in res:
        if not r['rows']:
            continue
        print(f"\n{r['label']}:\n\n| donor pc | target pc | insn | donor resolves to | target resolves to | verdict |\n|---|---|---|---|---|---|")
        for row in r['rows']:
            print('| ' + ' | '.join(x.replace('|', '/') for x in row) + ' |')
    print(f'\nbodies {len(res)}, not equal {bad}')
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
