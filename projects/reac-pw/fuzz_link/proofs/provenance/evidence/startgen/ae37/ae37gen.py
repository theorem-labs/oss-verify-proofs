#!/usr/bin/env python3
"""ae37gen.py -- write lib/A/AE23.v and lib/A/AE37.v of reac-pw/fuzz_link image A from their scratch bases.

The bases are libreac/fuzz_pcap's lib/A/AE23.v and lib/A/AE37.v (origin/ossv/recipes 88154566652a) relocated to
link.asan by alreloc 56664a20986e. alreloc left pcap's numerals where it could not map them: the asan_globals
descriptor table (pcap's 4 descriptors at 0x9e100, link's 43 at 0xa62a0), ___asan_globals_registered, the shadow
windows, one .rodata constant-pool address and one end of a musl range whose symbol name has several copies (buf).
This script replaces exactly those numerals and nothing else, reading every value from the image, its unstripped
twin or link's generated lib/A/AF0m.v, and checks every other value of x2_rodata against AF0m.

  ae37gen.py --image link.asan --twin link.asan.unstripped --donor fuzz_pcap.asan(unstripped)
             --af0m lib/A/AF0m.v --ae3h lib/A/AE3h.v --donor-ae3h pcap-AE3h.v
             --base-ae23 bases/AE23.v --base-ae37 bases/AE37.v
             --out-ae23 lib/A/AE23.v --out-ae37 lib/A/AE37.v --table ae37-values.tsv --removed REMOVED-LINES.tsv

What it derives, and from where:
  - the descriptor array: section asan_globals of the image (43 descriptors of 8 little-endian 64-bit words); the
    words the dtor walk reads are those at offsets 0, 8, 16, 32, 40, 48 and 56 of each descriptor (the base's set);
    each is checked equal to the AF0m Tfib_const_abs cell at that address;
  - the (globals_lo, globals_hi) pair cell and ___asan_globals_registered: the two pc-relative ld and the addi in
    asan.module_dtor (twin .symtab) decoded with capstone; the pair's words are read from the image and must be
    __start_asan_globals / __stop_asan_globals; the flag is the twin's OBJECT ___asan_globals_registered;
  - a constant-pool address the base kept as pcap's: the pc-relative loads of the X2 walk (x2_ranges of link's
    AE3h.v and of pcap's AE3h.v) are paired in program order; a base x2_rodata region whose address is a pcap target
    and not a link target is moved to the paired link target;
  - XW2 and x2_shw: for each descriptor [shadow(beg), shadow(beg) + size_with_redzone / 8), and for the array
    [shadow(0xa62a0), shadow(0xa62a0) + 2752 / 8), shadow(a) = 0x7fff8000 + a / 8 (lib/Reusable/YG0f.v SHADOW_OFF);
  - x2_shw_const: the runs of window bytes that are rows of AF0m's Tfib_const_shadow; x2_shw_zero: the runs of window
    bytes in the shadow of a Tfib_zero_shadow row, with the row's 0-based index in Tfib_zero_shadow; every window byte
    must be exactly one of the two;
  - the end of AE23's musl ofl region (base 0x5f4f90, pcap's buf): the twin's ofl_head + its size.
Exit 0 only when every check passes.
"""
import argparse, hashlib, re, struct, sys
from elftools.elf.elffile import ELFFile
from capstone import Cs, CS_ARCH_RISCV, CS_MODE_RISCV64, CS_MODE_RISCVC

PIN = '059dae63e07ca2d80ae9227fa125d40586a02172c96d2b6884f8617ab912061d'
TWIN = '66cd0f159895f119b29a44eb3760cfda78506402a019729057dba69562af9d9f'
DONOR = '36da3052c383096eed46abd71490e47af9600c030bdf511c4e83d48924e24291'
BASE23 = '3443e26d041e0acfdcaf78abeb855eb1067bdb4eab98d64926c28460db76a9cc'
BASE37 = 'ed7826c0d12af0cc63933131ed8fdf23d8319febf8918236e861be30ddf3aa16'
SHADOW_OFF = 0x7fff8000
IMG_LO, IMG_TOP = 0x10000, 0x654000
READ_OFFS = (0, 8, 16, 32, 40, 48, 56)
# pcap's asan_globals numerals that may not stay in either output file
PCAP_LEFT = ['0x9e200', '0x9e100', '0x20d00', '0x20d20', '0x20d40', '0x20d60', '0x5d3f40', '0x5d3f60', '0x5d3f48',
             '0x5d3f68', '0x20d08', '0x103a0', '0x8000bc20', '0x8000bc40', '0x7fffc1a0', '0x7fffc1a1', '0x7fffc1a4',
             '0x7fffc1a8', '0x7fffc1ac', '0x800b27e8', '0x800b27e9', '0x800b27ec', '0x800b27ed', '0x800b27f0',
             '0x5f4f90', '682920', '8608']

bad = []


def need(cond, what):
    if not cond:
        bad.append(what)
        print('FAIL: ' + what)
    return cond


def sha(path):
    return hashlib.sha256(open(path, 'rb').read()).hexdigest()


def shadow(a):
    return SHADOW_OFF + a // 8


class Img:
    def __init__(self, path):
        self.e = ELFFile(open(path, 'rb'))
        self.segs = [(s['p_vaddr'], s['p_memsz'], s.data()) for s in self.e.iter_segments() if s['p_type'] == 'PT_LOAD']

    def read(self, a, n):
        for v, m, d in self.segs:
            if v <= a and a + n <= v + m:
                b = d[a - v:a - v + n]
                return b + b'\0' * (n - len(b))
        raise ValueError('0x%x+%d not in a PT_LOAD' % (a, n))

    def u64(self, a):
        return struct.unpack('<Q', self.read(a, 8))[0]

    def syms(self):
        out = {}
        for s in self.e.get_section_by_name('.symtab').iter_symbols():
            out.setdefault(s.name, []).append((s['st_value'], s['st_size'], s['st_info']['type']))
        return out


def x2_ranges(ae3h_text):
    m = re.search(r'Definition x2_ranges : list \(Z \* nat\) := \[(.*?)\]\.', ae3h_text)
    return [(int(a, 0), int(n)) for a, n in re.findall(r'\((0x[0-9a-f]+), (\d+)%nat\)', m.group(1))]


def pcrel(img, ranges):
    """Program-order list of (function start, pc, mnemonic, target) of auipc-relative ld/lb/lbu/lw/sd/addi."""
    md = Cs(CS_ARCH_RISCV, CS_MODE_RISCV64 | CS_MODE_RISCVC)
    res = []
    for start, count in ranges:
        regs, n = {}, 0
        for ins in md.disasm(img.read(start, count * 4 + 8), start):
            if n >= count:
                break
            n += 1
            ops = ins.op_str.replace(' ', '').split(',')
            if ins.mnemonic == 'auipc':
                imm = int(ops[1], 0)
                imm = imm - (1 << 20) if imm >= (1 << 19) else imm
                regs[ops[0]] = ins.address + (imm << 12)
                continue
            t = None
            if ins.mnemonic == 'addi' and len(ops) == 3 and regs.get(ops[1]) is not None:
                t = regs[ops[1]] + int(ops[2], 0)
            elif '(' in ins.op_str:
                off, base = ops[-1].split('(')
                base = base.rstrip(')')
                if regs.get(base) is not None:
                    t = regs[base] + int(off or '0', 0)
            if t is not None:
                res.append((start, ins.address, ins.mnemonic, t))
            if ops and ops[0] in regs and not (ins.mnemonic[0] == 's' and '(' in ins.op_str):
                regs.pop(ops[0], None)
    return res


def af0m_tables(text):
    s, e = text.index('Definition Tfib_const_abs :'), text.index('Definition Tfib_const_abs_filled')
    absd = {}
    for k, a, v in re.findall(r'\bz([1248]) \(ANum (0x[0-9a-f]+|\d+)\) (0x[0-9a-f]+|\d+)', text[s:e]):
        a, v, w = int(a, 0), int(v, 0), int(k)
        need(absd.get(a, (w, v)) == (w, v), 'AF0m Tfib_const_abs: two different cells at 0x%x' % a)
        absd[a] = (w, v)
    s, e = text.index('Definition Tfib_const_shadow :'), text.index('Definition Tfib_const (ly')
    shd = {}
    for a, v in re.findall(r'\bz1 \(ANum (0x[0-9a-f]+)\) (0x[0-9a-f]+|\d+)', text[s:e]):
        shd[int(a, 0)] = int(v, 0)
    s = text.index('Definition Tfib_zero_shadow :')
    e = text.index('].', s)
    zrows = []
    for x, y in re.findall(r'\(([^,()]+), ([^,()]+)\)', text[s:e]):
        env = {'YImgTop.IMG_LO': IMG_LO, 'YImgTop.IMG_TOP': IMG_TOP}

        def ev(t):
            t = t.strip()
            for k, v in env.items():
                t = t.replace(k, str(v))
            need(re.fullmatch(r'[0-9a-fx+\- ]+', t) is not None, 'AF0m Tfib_zero_shadow: cannot read %r' % t)
            return eval(t)
        zrows.append((ev(x), ev(y)))
    return absd, shd, zrows


def zfmt(z):
    return '0x%x' % z if z else '0'


def wrap(head, items, tail, width=118):
    """head + items joined by '; ' + tail, broken into lines of at most width characters (continuations at column 0)."""
    out, cur = [], head
    for k, it in enumerate(items):
        piece = it + (';' if k + 1 < len(items) else tail)
        if len(cur) + 1 + len(piece) > width and cur != head:
            out.append(cur)
            cur = piece
        else:
            cur = cur + piece if cur == head else cur + ' ' + piece
    return out + [cur]


def main():
    ap = argparse.ArgumentParser()
    for k in ('image', 'twin', 'donor', 'af0m', 'ae3h', 'donor-ae3h', 'base-ae23', 'base-ae37', 'out-ae23', 'out-ae37',
              'table', 'removed'):
        ap.add_argument('--' + k, required=True)
    a = ap.parse_args()
    for p, want in ((a.image, PIN), (a.twin, TWIN), (a.donor, DONOR), (a.base_ae23, BASE23), (a.base_ae37, BASE37)):
        h = sha(p)
        print('%s sha256 %s (%s)' % (p, h, 'PIN' if h == want else 'NOT THE PIN'))
        need(h == want, 'sha256 of ' + p)
    for p in (a.af0m, a.ae3h, a.donor_ae3h):
        print('%s sha256 %s (input)' % (p, sha(p)))
    img, twin, donor = Img(a.image), Img(a.twin), Img(a.donor)
    ts = twin.syms()

    def sym1(name, typ=None):
        r = [x for x in ts.get(name, []) if typ is None or x[2] == typ]
        need(len(r) == 1, 'twin symbol %s: %d copies' % (name, len(r)))
        return r[0]

    # the descriptor array
    sec = img.e.get_section_by_name('asan_globals')
    G, GB = sec['sh_addr'], sec['sh_size']
    need(GB % 64 == 0, 'asan_globals size %d is not a multiple of 64' % GB)
    need(sym1('__start_asan_globals')[0] == G and sym1('__stop_asan_globals')[0] == G + GB, '__start/__stop_asan_globals')
    desc = [struct.unpack('<8Q', img.read(G + 64 * i, 64)) for i in range(GB // 64)]
    print('asan_globals 0x%x, %d bytes, %d descriptors' % (G, GB, len(desc)))
    REG = sym1('___asan_globals_registered', 'STT_OBJECT')
    MU = sym1('_ZN6__asanL14mu_for_globalsE', 'STT_OBJECT')
    DTOR = sym1('asan.module_dtor', 'STT_FUNC')
    # asan.module_dtor: ld a1 <- pair+0, ld a2 <- pair+8, a0 <- &registered
    dt = pcrel(img, [(DTOR[0], DTOR[1] // 4)])
    lds = [x[3] for x in dt if x[2] == 'ld']
    adds = [x[3] for x in dt if x[2] == 'addi']
    need(len(lds) == 2 and lds[1] == lds[0] + 8, 'asan.module_dtor: two ld of one 16-byte cell: %s' % [hex(x) for x in lds])
    need(adds == [REG[0]], 'asan.module_dtor: a0 = ___asan_globals_registered: %s' % [hex(x) for x in adds])
    PAIR = lds[0]
    pair = (img.u64(PAIR), img.u64(PAIR + 8))
    need(pair == (G, G + GB), 'pair cell 0x%x holds (0x%x, 0x%x)' % ((PAIR,) + pair))
    print('pair cell 0x%x = (0x%x, 0x%x); ___asan_globals_registered 0x%x (%d bytes); mu_for_globals 0x%x (%d bytes)'
          % (PAIR, pair[0], pair[1], REG[0], REG[1], MU[0], MU[1]))

    absd, shd, zrows = af0m_tables(open(a.af0m).read())
    print('AF0m: %d Tfib_const_abs cells, %d Tfib_const_shadow rows, %d Tfib_zero_shadow rows'
          % (len(absd), len(shd), len(zrows)))

    def af(addr, w):
        c = absd.get(addr)
        need(c is not None and c[0] == w, 'AF0m has no %d-byte cell at 0x%x (has %r)' % (w, addr, c))
        return c[1] if c else None

    need(af(REG[0], 8) == 1, 'AF0m ___asan_globals_registered = 1')
    for i, d in enumerate(desc):
        for k in range(8):
            need(af(G + 64 * i + 8 * k, 8) == d[k], 'AF0m descriptor word 0x%x' % (G + 64 * i + 8 * k))
    for k in range(2):
        need(af(PAIR + 8 * k, 8) == pair[k], 'AF0m pair word 0x%x' % (PAIR + 8 * k))

    # pc-relative loads of the X2 walk, link and pcap, paired in program order
    lr = pcrel(img, x2_ranges(open(a.ae3h).read()))
    dr = pcrel(donor, x2_ranges(open(a.donor_ae3h).read()))
    need(len(lr) == len(dr) and all(x[2] == y[2] for x, y in zip(lr, dr)), 'X2 walk pc-relative references pair 1:1')
    lt = {x[3] for x in lr}
    dmap = {}
    for x, y in zip(lr, dr):
        need(dmap.setdefault(y[3], x[3]) == x[3], 'pcap target 0x%x pairs with two link targets' % y[3])

    b37 = open(a.base_ae37).read().split('\n')
    b23 = open(a.base_ae23).read().split('\n')
    removed = []

    # ---------------- x2_rodata
    s = b37.index('Definition x2_rodata : list (Z * Z * list (Z * N * Z)) :=')
    e = [i for i, l in enumerate(b37) if l.startswith('Definition ro_chunk')][0]
    rod = ' '.join(b37[s + 1:e])
    regs = []
    for base, size, body in re.findall(r'\((0x[0-9a-f]+), (\d+), \[(.*?)\]\)', rod):
        ch = [(int(o), int(w), int(v, 0)) for o, w, v in re.findall(r'\((\d+), (\d+)%N, (0x[0-9a-f]+|\d+)\)', body)]
        regs.append((int(base, 0), int(size), ch))
    newrod = []
    moved = []
    for base, size, ch in regs:
        if base == 0xa62a0 or base == 0x9e100:
            need(base == G, 'descriptor region base 0x%x is asan_globals' % base)
            ch = [(64 * i + o, 8, desc[i][o // 8]) for i in range(len(desc)) for o in READ_OFFS]
            size = GB
        elif base == PAIR:
            need(size == 16 and [c[0] for c in ch] == [0, 8], 'pair region shape')
            ch = [(0, 8, pair[0]), (8, 8, pair[1])]
        elif base not in lt and base in dmap:
            moved.append((base, dmap[base]))
            base = dmap[base]
        nch = []
        for o, w, v in ch:
            v2 = af(base + o, w)
            if v2 != v:
                need(base == PAIR or base == G, 'x2_rodata 0x%x+%d: base value 0x%x, AF0m 0x%x' % (base, o, v, v2 or 0))
            nch.append((o, w, v2))
        newrod.append((base, size, nch))
    print('x2_rodata: %d regions; moved by the pc-relative pairing: %s'
          % (len(newrod), ', '.join('0x%x -> 0x%x' % m for m in moved) or 'none'))

    def fmt_region(base, size, ch):
        cs = ['(%d, %d%%N, %s)' % (o, w, zfmt(v)) for o, w, v in ch]
        if base == G:
            rows = []
            for i in range(len(desc)):
                part = cs[7 * i:7 * i + 7]
                rows.append('; '.join(part[:4]) + ';')
                rows.append('; '.join(part[4:]) + (';' if i + 1 < len(desc) else ''))
            head = '(0x%x, %d, [' % (base, size)
            return [head + rows[0]] + rows[1:-1] + [rows[-1] + '])']
        return ['(0x%x, %d, [%s])' % (base, size, '; '.join(cs))]

    # keep the base's lines for unchanged regions; rebuild only the lines of changed regions
    rod_lines = b37[s + 1:e]
    starts = []
    for li, l in enumerate(rod_lines):
        for m in re.finditer(r'\((0x[0-9a-f]+), (\d+), \[', l):
            starts.append((li, int(m.group(1), 0)))
    need([x[1] for x in starts] == [r[0] for r in regs], 'x2_rodata region starts read twice the same')
    new_rod_lines = []
    for k, (li, base0) in enumerate(starts):
        lj = starts[k + 1][0] if k + 1 < len(starts) else len(rod_lines)
        seg = rod_lines[li:lj]
        if regs[k] != newrod[k]:
            body = fmt_region(*newrod[k])
            lead = '[ ' if k == 0 else ''
            tail = ' ].' if k + 1 == len(starts) else ';'
            body[0] = lead + body[0]
            body[-1] = body[-1] + tail
            seg = body
        new_rod_lines += seg
    b37n = b37[:s + 1] + new_rod_lines + b37[e:]
    # re-read what was written and check it against the computed regions
    chk = ' '.join(new_rod_lines)
    back = [(int(b, 0), int(z), [(int(o), int(w), int(v, 0)) for o, w, v in
                                 re.findall(r'\((\d+), (\d+)%N, (0x[0-9a-f]+|\d+)\)', body)])
            for b, z, body in re.findall(r'\((0x[0-9a-f]+), (\d+), \[(.*?)\]\)', chk)]
    need(back == newrod, 'x2_rodata text reads back as the computed regions')

    # ---------------- windows
    wins = []
    for i, d in enumerate(desc):
        beg, size, srz = d[0], d[1], d[2]
        need(beg % 8 == 0 and srz % 8 == 0, 'descriptor %d alignment' % i)
        wins.append(('d%d' % i, beg, size, srz, shadow(beg), srz // 8))
    wins.append(('array', G, GB, GB, shadow(G), GB // 8))
    zcover = []
    for k, (zs, zl) in enumerate(zrows):
        zcover.append((shadow(zs), shadow(zs) + zl // 8, k))
    shw_const, shw_zero, table = [], [], []
    nconst = nzero = 0
    for nm, beg, size, srz, lo, n in wins:
        runs_c, runs_z = [], []
        for o in range(lo, lo + n):
            c = o in shd
            zk = [k for zlo, zhi, k in zcover if zlo <= o < zhi]
            need(c != bool(zk), 'window %s byte 0x%x: const %s, zero rows %s' % (nm, o, c, zk))
            if c:
                nconst += 1
                if runs_c and runs_c[-1][0] + runs_c[-1][1] == o:
                    runs_c[-1][1] += 1
                else:
                    runs_c.append([o, 1])
            elif zk:
                nzero += 1
                need(len(zk) == 1, 'window %s byte 0x%x in two zero rows %s' % (nm, o, zk))
                if runs_z and runs_z[-1][0] + runs_z[-1][1] == o and runs_z[-1][2] == zk[0]:
                    runs_z[-1][1] += 1
                else:
                    runs_z.append([o, 1, zk[0]])
        shw_const += runs_c
        shw_zero += runs_z
        table.append((nm, beg, size, srz, lo, n, runs_c, runs_z))
    need(nconst == len(shd), 'the window const bytes are every Tfib_const_shadow row (%d of %d)' % (nconst, len(shd)))
    print('windows: %d (%d descriptors + the array), %d shadow bytes: %d const (Tfib_const_shadow), %d zero (Tfib_zero_shadow)'
          % (len(wins), len(desc), nconst + nzero, nconst, nzero))
    allw = sorted((w[4], w[4] + w[5]) for w in wins)
    need(all(allw[i][1] <= allw[i + 1][0] for i in range(len(allw) - 1)), 'the windows are disjoint')
    need(allw[0][0] >= IMG_TOP and allw[-1][1] <= 2 ** 47, 'the windows lie in [IMG_TOP, 2^47)')

    # ---------------- AE37 text
    # removed comments, by base line number: the donor's header (4-30) and the zero-shadow note before shbyte0
    z0 = [k for k, l in enumerate(b37) if l.startswith('(* The donor has ONE zero-shadow byte in its windows')]
    need(len(z0) == 1 and b37[z0[0] + 3].rstrip().endswith('*)'), 'AE37 base: the zero-shadow comment (4 lines)')
    need(b37[3].startswith('(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE37.v')
         and b37[29].rstrip().endswith('*)') and b37[30].startswith('From '), 'AE37 base: lines 4-30 are the header comment')
    for n in list(range(4, 31)) + list(range(z0[0] + 1, z0[0] + 5)):
        removed.append(('lib/A/AE37.v', n, b37[n - 1]))
    t = list(b37n)

    def find1(prefix):
        r = [i for i, l in enumerate(t) if l.startswith(prefix)]
        need(len(r) == 1, 'AE37: one line starts with %r' % prefix)
        return r[0]

    i = find1('Definition x2_shw : list (Z * Z) :=')
    t[i:i + 1] = wrap('Definition x2_shw : list (Z * Z) := [', ['(0x%x, %d)' % (w[4], w[5]) for w in wins], '].')
    i = find1(':: cellr 0x9e200 8 (SLit 1) true')
    t[i] = ':: cellr 0x%x 8 (SLit 1) true' % REG[0]
    i = find1('Definition x2_shw_const : list (Z * Z) :=')
    t[i:i + 1] = wrap('Definition x2_shw_const : list (Z * Z) := [', ['(0x%x, %d)' % (o, c) for o, c in shw_const], '].')
    # the check lemmas state their forallb itself: the kernel, checking `unfold CHK in H` against a closed boolean
    # check, evaluates the whole check in its lazy machine (Qed of shbytes_present 562 s with shbyte_chk folded)
    i = find1('Definition shbyte_chk (ly : alayout) : bool :=')
    need(t[i + 4] == 'Lemma shbyte_chk_true : forall ly, shbyte_chk ly = true.' and
         t[i + 5] == 'Proof. intros ly. vm_compute. reflexivity. Qed.', 'AE37 shbyte_chk and its lemma')
    need(t[i + 3].endswith(') x2_shbytes.'), 'AE37 shbyte_chk body')
    t[i:i + 5] = ['Lemma shbyte_chk_true : forall ly,'] + t[i + 1:i + 3] + [t[i + 3][:-1] + ' = true.']
    k = find1('intros ly S H mem a HM Hin. pose proof (shbyte_chk_true ly) as Hc. unfold shbyte_chk in Hc.')
    t[k] = 'intros ly S H mem a HM Hin. pose proof (shbyte_chk_true ly) as Hc.'
    new_defs = [
        'Definition x2_inw (ws : list (Z * Z)) (o : Z) : bool := existsb (fun w => (fst w <=? o) && (o <? fst w + snd w)) ws.',
        *wrap('Definition x2_shw_zero : list (Z * Z * nat) := [', ['(0x%x, %d, %d%%nat)' % (o, c, k) for o, c, k in shw_zero], '].'),
        'Definition x2_zrow (z : Z * Z * nat) : Z * Z := nth (snd z) Tfib_zero_shadow (0, 0).',
        'Lemma shz_chk_true :',
        'forallb (fun z => Nat.ltb (snd z) (length Tfib_zero_shadow) &&',
        '(shadow_of_addr SHADOW_OFF (fst (x2_zrow z)) <=? fst (fst z)) &&',
        '(fst (fst z) + snd (fst z) <=? shadow_of_addr SHADOW_OFF (fst (x2_zrow z)) + snd (x2_zrow z) / 8)) x2_shw_zero = true.',
        'Proof. vm_compute. reflexivity. Qed.',
        'Lemma shw_cover_chk_true :',
        'forallb (fun w => (TFIB_IMG_END <=? fst w) && (fst w + snd w <=? 2 ^ 47) &&',
        'forallb (fun o => x2_inw x2_shw_const o || x2_inw (map fst x2_shw_zero) o) (zrange (fst w) (Z.to_nat (snd w)))) x2_shw = true.',
        'Proof. vm_compute. reflexivity. Qed.',
    ]
    need(t[i + 4] == 'Proof. intros ly. vm_compute. reflexivity. Qed.', 'AE37: new defs go after shbyte_chk_true')
    t[i + 5:i + 5] = new_defs
    # the per-byte zero-shadow lemmas and shw_ok of the base -> one lemma over x2_shw_zero, one over x2_shw, shw_ok
    s0 = [k for k, l in enumerate(t) if l.startswith('(* The donor has ONE zero-shadow byte in its windows')]
    need(len(s0) == 1, 'AE37: the zero-shadow comment')
    s0 = s0[0]
    e0 = find1('Lemma zi8_14ea00 :')
    need(t[e0 - 1] == 'Qed.', 'AE37: the replaced block ends at shw_ok\'s Qed')
    new_block = [
        'Lemma shz_present : forall ly S (H : word -> bool) mem z o,',
        'ARm B ly S (aview tfibsegs H mem) -> In z x2_shw_zero -> fst (fst z) <= o < fst (fst z) + snd (fst z) ->',
        'exists b, mbyte tfibsegs (mrestrict H mem) o = Some b.',
        'Proof.',
        'intros ly S H mem z o HM Hin Ho. pose proof shz_chk_true as Hc.',
        'rewrite forallb_forall in Hc. specialize (Hc z Hin). cbn beta in Hc.',
        'apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 H2].',
        'apply Nat.ltb_lt in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.',
        'pose proof (proj1 (Forall_forall _ _) (am_zshadow B ly S _ HM) (x2_zrow z)',
        'ltac:(unfold zero_shadow_ranges, x2_zrow; right; rewrite (ts_zsh _ TB); apply nth_In; exact H1)) as HZ.',
        'specialize (HZ (o - shadow_of_addr SHADOW_OFF (fst (x2_zrow z))) ltac:(lia)).',
        'replace (shadow_of_addr SHADOW_OFF (fst (x2_zrow z)) + (o - shadow_of_addr SHADOW_OFF (fst (x2_zrow z)))) with o in HZ by lia.',
        'unfold aview in HZ. destruct (mbyte tfibsegs (mrestrict H mem) o) as [b|]; [exists b; reflexivity | discriminate].',
        'Qed.',
        'Lemma shw_byte_present : forall ly S (H : word -> bool) mem w o,',
        'ARm B ly S (aview tfibsegs H mem) -> In w x2_shw -> fst w <= o < fst w + snd w ->',
        'exists b, mbyte tfibsegs (mrestrict H mem) o = Some b.',
        'Proof.',
        'intros ly S H mem w o HM Hin Ho. pose proof shw_cover_chk_true as Hc.',
        'rewrite forallb_forall in Hc. specialize (Hc w Hin). cbn beta in Hc.',
        'apply andb_prop in Hc as [_ Hc]. rewrite forallb_forall in Hc.',
        'specialize (Hc o ltac:(apply In_zrange; rewrite Z2Nat.id by lia; lia)). cbn beta in Hc.',
        'apply orb_prop in Hc as [Hc|Hc]; unfold x2_inw in Hc; apply existsb_exists in Hc as (v & Hv & Hvo); cbn beta in Hvo;',
        'apply andb_prop in Hvo as [Hv1 Hv2]; apply Z.leb_le in Hv1; apply Z.ltb_lt in Hv2.',
        '- apply (shbytes_present ly S H mem o HM). unfold x2_shbytes. apply in_flat_map. exists v. split; [exact Hv|].',
        'cbn beta. apply In_zrange. rewrite Z2Nat.id by lia. lia.',
        '- apply in_map_iff in Hv as (z & <- & Hz). exact (shz_present ly S H mem z o HM Hz ltac:(lia)).',
        'Qed.',
        'Lemma shw_ok : forall ly S (H : word -> bool) mem E,',
        'ARm B ly S (aview tfibsegs H mem) -> Forall (region_ok tfibsegs E (mrestrict H mem)) (map shw_region x2_shw).',
        'Proof.',
        'intros ly S H mem E HM. apply Forall_map. apply Forall_forall. intros [lo n] Hin.',
        'pose proof shw_cover_chk_true as Hc. rewrite forallb_forall in Hc.',
        'specialize (Hc _ Hin). cbn beta in Hc. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [H1 H2].',
        'apply Z.leb_le in H1. apply Z.leb_le in H2. cbn [fst snd] in H1, H2. unfold TFIB_IMG_END, pcap_img_end, YImgTop.IMG_TOP in H1.',
        'unfold shw_region, region_ok. cbn [fst snd YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].',
        'split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. rewrite Z.add_0_l.',
        'destruct (shw_byte_present ly S H mem (lo, n) o HM Hin ltac:(cbn [fst snd]; lia)) as [b Hb].',
        'apply (mbyte_high_writable _ o b); [unfold TFIB_IMG_END, pcap_img_end, YImgTop.IMG_TOP; lia | exact Hb].',
        'Qed.',
    ]
    old_block = t[s0:e0]
    need(sum(1 for l in old_block if l.startswith('Lemma shbyte')) == 3 and
         sum(1 for l in old_block if l.startswith('Lemma shw_ok')) == 1, 'AE37: replaced block = shbyte0/2/3 + shw_ok')
    t[s0:e0] = new_block
    i = find1('Lemma zi8_14ea00 :')
    t[i] = t[i].replace('(Z_to_bv 64 0x9e200)', '(Z_to_bv 64 0x%x)' % REG[0])
    i = find1('repeat (destruct Ht as [Hq|Ht]; [injection Hq as <- <- <-; cbn [base_val] in Hr; lia|]). destruct Ht.')
    t[i] = ('repeat (destruct Ht as [Hq|Ht]; [injection Hq as <- <- <-; cbn [base_val] in Hr;'
            ' first [left; lia | right; repeat (first [left; lia | right]); lia]|]). destruct Ht.')
    # the pairwise disjointness of the 60 start regions is 1770 lia goals: run them in a context of Hsp44 only
    i = find1('cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.')
    t[i] = 'cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. clear - Hsp44. repeat split; lia.'
    for k, l in enumerate(t):
        if 'wseg_writable _ 0x9e200 8' in l:
            t[k] = l.replace('wseg_writable _ 0x9e200 8', 'wseg_writable _ 0x%x 8' % REG[0])
        if 'mem 0x9e200 8 1 HM' in t[k]:
            t[k] = t[k].replace('mem 0x9e200 8 1 HM', 'mem 0x%x 8 1 HM' % REG[0])
    need(t[3:30] == b37[3:30], 'AE37 header comment is still the base text')
    t = t[:3] + t[30:]

    # ---------------- AE23 text
    u = list(b23)
    need(u[34].startswith('Definition XW2 (a : Z) : Prop := (0x9e200 <= a < 0xa6d88)') and u[36].endswith('.'),
         'AE23:35-37 is XW2')
    xw = ['(0x%x <= a < 0x%x)' % (REG[0], REG[0] + 8), '(0x%x <= a < 0x%x)' % (MU[0], MU[0] + 8)]
    xw += ['(0x%x <= a < 0x%x)' % (w[4], w[4] + w[5]) for w in wins]
    rows = [' \\/ '.join(xw[k:k + 3]) for k in range(2, len(xw), 3)]
    xw_lines = ['Definition XW2 (a : Z) : Prop := %s \\/ %s \\/' % (xw[0], xw[1])]
    xw_lines += [r + ' \\/' for r in rows[:-1]] + [rows[-1] + '.']
    need(u[37].startswith('(* the shadow __asan_unregister_globals writes') and u[41].rstrip().endswith('*)'),
         'AE23:38-42 is the XW2 comment')
    for n in range(38, 43):
        removed.append(('lib/A/AE23.v', n, u[n - 1]))
    OL = sym1('ofl_lock', 'STT_OBJECT')
    OH = sym1('ofl_head', 'STT_OBJECT')
    oend = OH[0] + OH[1]
    need(OL[0] == 0x652300 and OH[0] == OL[0] + 8, 'musl ofl_lock / ofl_head at 0x652300 / 0x652308')
    for n in (102, 131):
        need('YP09.mkRegion None 0x652300 0x5f4f90 0x652300 0x652300' in u[n - 1], 'AE23:%d is the ofl region' % n)
        u[n - 1] = u[n - 1].replace('0x652300 0x5f4f90 0x652300', '0x652300 0x%x 0x652300' % oend)
    u = u[:34] + xw_lines + u[42:]

    for nm, txt, hdr in (('AE23', u, 4), ('AE37', t, 3)):
        body = '\n'.join(txt)
        for tok in PCAP_LEFT:
            need(re.search(r'(?<![0-9a-fx])' + re.escape(tok) + r'(?![0-9a-f])', body) is None,
                 '%s still holds pcap numeral %s' % (nm, tok))
        need(all(l.startswith('(*') for l in txt[:hdr]) and not any('(*' in l for l in txt[hdr:]),
             '%s: comments only in header lines 1-%d' % (nm, hdr))
    open(a.out_ae37, 'w').write('\n'.join(t))
    open(a.out_ae23, 'w').write('\n'.join(u))

    with open(a.removed, 'w') as f:
        f.write('file\tline\ttext\n')
        for fn, n, l in removed:
            f.write('%s\t%d\t%s\n' % (fn, n, l))
    with open(a.table, 'w') as f:
        f.write('# ae37gen.py: XW2 / x2_shw window of each asan_globals descriptor of link.asan and of the array; '
                'const runs are rows of AF0m Tfib_const_shadow, zero runs lie in the shadow of the named '
                'Tfib_zero_shadow row (0-based index k)\n')
        f.write('window\tdesc_addr\tbeg\tsize\tsize_with_redzone\tXW2 [lo, hi)\tx2_shw (lo, n)\tconst runs (lo, n)\tzero runs (lo, n, row k = (start, len))\n')
        for k, (nm, beg, size, srz, lo, n, rc, rz) in enumerate(table):
            da = '0x%x' % (G + 64 * k) if nm != 'array' else '-'
            f.write('%s\t%s\t0x%x\t%d\t%d\t[0x%x, 0x%x)\t(0x%x, %d)\t%s\t%s\n' % (
                nm, da, beg, size, srz, lo, lo + n, lo, n,
                ' '.join('(0x%x, %d)' % (o, c) for o, c in rc) or '-',
                ' '.join('(0x%x, %d, %d = (0x%x, 0x%x))' % (o, c, kk, zrows[kk][0], zrows[kk][1]) for o, c, kk in rz) or '-'))
        f.write('# pair cell 0x%x = (0x%x, 0x%x) (image; asan.module_dtor ld at +%s); ___asan_globals_registered 0x%x size %d '
                '(twin OBJECT; module_dtor addi); mu_for_globals 0x%x size %d (twin OBJECT); musl ofl_head 0x%x + %d = 0x%x\n'
                % (PAIR, pair[0], pair[1], ', +'.join('0x%x' % (x[1] - DTOR[0]) for x in dt if x[2] == 'ld'),
                   REG[0], REG[1], MU[0], MU[1], OH[0], OH[1], oend))
        for m in moved:
            f.write('# x2_rodata region moved by the pc-relative pairing: pcap 0x%x -> link 0x%x\n' % m)
    print('wrote %s (%d lines), %s (%d lines), %s, %s (%d removed lines)'
          % (a.out_ae23, len(u), a.out_ae37, len(t), a.table, a.removed, len(removed)))
    print('VERDICT: ' + ('PASS' if not bad else 'FAIL (%d)' % len(bad)))
    sys.exit(0 if not bad else 1)


if __name__ == '__main__':
    main()
