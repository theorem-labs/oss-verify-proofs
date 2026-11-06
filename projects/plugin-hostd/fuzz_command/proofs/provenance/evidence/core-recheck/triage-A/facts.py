"""Measured facts for triage.py: every expected value with the text that says how it was measured.
F[key] = (value, text). A value of None means the measurement did not confirm the fact (the rule then refuses)."""
import re


class Facts:
    def __init__(self, O, D, U, UD):
        self.O, self.D, self.U, self.UD = O, D, U, UD
        self.v = {}
        self.dv = {}  # the donor image's value of the same fact (known-answer control)
        self._dwarf = None
        self.build()

    def put(self, k, val, text):
        self.v[k] = (val, text)

    def __getitem__(self, k):
        return self.v[k]

    def __contains__(self, k):
        return k in self.v

    def img(self, I=None):
        I = I or self.O
        return f'{I.role} {I.sha_pin}'

    # ------------------------------------------------------------------ DWARF of the twin (the program's CUs)
    def dwarf(self):
        if self._dwarf is not None:
            return self._dwarf
        from elftools.elf.elffile import ELFFile
        out = {'struct': {}, 'var': {}}
        fh = open(self.O.twin_path, 'rb')
        dw = ELFFile(fh).get_dwarf_info()

        def nm(d):
            a = d.attributes.get('DW_AT_name')
            return a.value.decode() if a else None

        def size_of(t):
            """byte size of a type DIE; pointers without DW_AT_byte_size take the CU address size."""
            while t is not None and 'DW_AT_byte_size' not in t.attributes:
                if t.tag in ('DW_TAG_pointer_type', 'DW_TAG_reference_type'):
                    return t.cu.header['address_size']
                if 'DW_AT_type' not in t.attributes:
                    return None
                t = t.get_DIE_from_attribute('DW_AT_type')
            return t.attributes['DW_AT_byte_size'].value if t is not None else None

        for cu in dw.iter_CUs():
            cun = nm(cu.get_top_DIE())
            if not cun or 'compiler-rt' in cun:
                continue
            for d in cu.iter_DIEs():
                if d.tag == 'DW_TAG_structure_type' and nm(d) and 'DW_AT_byte_size' in d.attributes:
                    mem = [(nm(c), c.attributes['DW_AT_data_member_location'].value,
                            size_of(c.get_DIE_from_attribute('DW_AT_type')))
                           for c in d.iter_children() if c.tag == 'DW_TAG_member']
                    out['struct'].setdefault(nm(d), (d.attributes['DW_AT_byte_size'].value, mem, cun))
                elif d.tag == 'DW_TAG_variable' and nm(d) and 'DW_AT_type' in d.attributes:
                    t = d.get_DIE_from_attribute('DW_AT_type')
                    tt = t
                    while tt is not None and tt.tag in ('DW_TAG_volatile_type', 'DW_TAG_const_type', 'DW_TAG_typedef'):
                        tt = tt.get_DIE_from_attribute('DW_AT_type') if 'DW_AT_type' in tt.attributes else None
                    out['var'].setdefault(nm(d), (size_of(t), nm(tt) if tt is not None else None, cun))
        fh.close()
        self._dwarf = out
        return out

    def field(self, struct, name):
        sz, mem, cun = self.dwarf()['struct'][struct]
        for n, off, s in mem:
            if n == name:
                return off, s
        raise KeyError(name)

    # ------------------------------------------------------------------ the facts
    def build(self):
        O, D, U = self.O, self.D, self.U
        im = self.img()
        cls = 64 if O.pin_bytes[4] == 2 else 32
        attrs = O.pin_bytes  # .riscv.attributes arch string is read from the twin below
        arch = ''
        with open(O.twin_path, 'rb') as fh:
            from elftools.elf.elffile import ELFFile
            e = ELFFile(fh)
            s = e.get_section_by_name('.riscv.attributes')
            if s is not None:
                m = re.search(rb'rv64[a-z0-9_]+', s.data())
                arch = m.group(0).decode() if m else ''
            al = sorted({p['p_align'] for p in e.iter_segments() if p['p_type'] == 'PT_LOAD'})
        self.arch = arch
        # ---- ISA / ABI, selected by the image's ELF header
        self.put('xlen', cls, f'ELF header of {im}: ELFCLASS{cls}, {O.machine}: XLEN {cls} (2 ^ {cls} words, Z_to_bv {cls})')
        self.put('two', 2, f'base 2 of 2 ^ XLEN ({im} is ELFCLASS{cls})')
        self.put('xregbits', 5, f'{O.machine} {arch[:8]}: 32 integer registers x0..x31, register index width 5 bits (bvmap 5 / bv 5)')
        self.put('fregbits', 5 if ('_f' in arch and '_d' in arch) else None,
                 f'{im} .riscv.attributes arch {arch[:20]}.. has F and D: 32 float registers f0..f31, index width 5 bits')
        for k, n, why in (('ra', 1, 'ra = x1'), ('sp', 2, 'sp = x2'), ('gp', 3, 'gp = x3'), ('tp', 4, 'tp = x4'),
                          ('a0', 10, 'a0 = x10 (first argument and return value)')):
            self.put(k, n, f'RISC-V psABI integer register number: {why}')
        self.put('fa0', 10, 'RISC-V psABI: fa0 = f10, the float return register (the one float register a call returns in)')
        self.put('frm_shift', 5, 'RISC-V fcsr layout: fflags bits 0..4, frm bits 5..7 (frm = fcsr >> 5)')
        self.put('frm_mask', 7, 'RISC-V fcsr layout: frm is 3 bits (mask 7)')
        self.put('rne', 0, 'RISC-V frm encoding 000 = RNE (round to nearest, ties to even): rounding mode 0')
        self.put('byte_card', 256, 'a byte has 8 bits: 0 <= v < 256')
        self.put('zero', 0, 'zero: the zero byte (rd a = Some 0), the null address, a lower bound 0 of an offset')
        self.put('wordb', 8, f'{cls}-bit word = 8 bytes (rdword / val_mem width 8, word alignment 8)')
        self.put('w32b', 4, '32-bit read = 4 bytes (rd32 / val_mem width 4)')
        self.put('page', 4096 if al == [4096] else None, f'PT_LOAD p_align of {im} = {al}: page size 4096')
        self.put('page_m1', 4095, 'page size 4096 - 1 = 4095 (round-up addend of a page ceiling)')
        lo, top = O.hull()
        self.put('img_lo', lo, f'{im}: first PT_LOAD page {lo:#x}')
        self.put('img_top', top, f'{im}: end of the last PT_LOAD (vaddr + memsz) rounded up to a page = {top:#x}')
        b0, b1 = O.sec('.bss')
        self.put('bss_lo', b0, f'{im} section header: .bss starts at {b0:#x}')
        # ---- unit model constants that the ported sentences restate
        yg0f = U.text('Reusable/YG0f.v')
        so = int(re.search(r'Definition SHADOW_OFF : Z := (0x[0-9a-f]+)', yg0f).group(1), 16)
        self.shadow_off = so
        self.put('shadow_gran', 8 if 'shadow_addr (a : Z) : Z := SHADOW_OFF + a / 8' in yg0f else None,
                 'lib/Reusable/YG0f.v:87 shadow_addr a = SHADOW_OFF + a / 8: one shadow byte per 8-byte granule')
        self.put('shadow_gran_m1', 7, 'granule 8 - 1 = 7: round-up addend of (n + 7) / 8 (lib/Reusable/YG0n.v:202 writes the same)')
        self.put('img_sh_lo', so + lo // 8, f'shadow_addr of the image base: {so:#x} (YG0f.v:12 SHADOW_OFF) + {lo:#x} / 8 = {so + lo // 8:#x}')
        self.put('img_sh_len', (top - lo) // 8, f'shadow bytes of the image [{lo:#x}, {top:#x}): ({top:#x} - {lo:#x}) / 8 = {(top - lo) // 8:#x}')
        dlo, dtop = D.hull()
        self.dv.update({'img_lo': dlo, 'img_top': dtop, 'bss_lo': D.sec('.bss')[0], 'img_sh_lo': so + dlo // 8,
                        'img_sh_len': (dtop - dlo) // 8})
        self.put('elit0', 0, 'kn_vis base ELit 0: an absolute address range')
        # astrace_at and the inner malloc entry's premises (lib/A/Rt/RtDDefs.v)
        rt = U.text('A/Rt/RtDDefs.v')
        need = ('rdword (aview segs (w_H W) mem) p = Some (p + 16)', 'rd32 (aview segs (w_H W) mem) (p + 8) (Z.of_nat (length tr))',
                'rd32 (aview segs (w_H W) mem) (p + 12) 0', '(p + 16 + 8 * Z.of_nat i)', 'getr regs 11 = w64 p',
                'p mod 8 = 0 -> p + 16 + 8 * 30 <= ly_stk_hi ly', '(1 <= length tr)%nat -> (length tr <= kUnwindMax)%nat')
        ok = all(s in rt for s in need)
        yg00 = U.text('Reusable/YG00.v')
        kum = int(re.search(r'Definition kUnwindMax : nat := (\d+)%nat', yg00).group(1))
        a = 'lib/A/Rt/RtDDefs.v:82-86 astrace_at'
        self.put('tr_buf', 16 if ok else None, f'{a}: the word at p holds p + 16, the frame buffer')
        self.put('tr_len', 8 if ok else None, f'{a}: the 32-bit size at p + 8 (with the 32-bit tag 0 at p + 12, one word)')
        self.put('tr_tag', 12 if ok else None, f'{a}: the 32-bit tag 0 at p + 12')
        self.put('tr_frame', 8 if ok else None, f'{a}: frame i at p + 16 + 8 * i (8-byte frames)')
        self.put('tr_min', 1 if ok else None, 'lib/A/Rt/RtDDefs.v:113 premise (1 <= length tr)%nat')
        self.put('tr_max', kum, f'lib/Reusable/YG00.v:37 kUnwindMax = {kum} (RtDDefs.v:112-113: p + 16 + 8 * 30, length tr <= kUnwindMax)')
        self.put('tr_obj', 16 + 8 * kum, f'trace object extent 16 + 8 * kUnwindMax = 16 + 8 * {kum} = {16 + 8 * kum} (RtDDefs.v:112)')
        self.put('tr_al', 8 if ok else None, 'lib/A/Rt/RtDDefs.v:112 premise p mod 8 = 0 (8-aligned trace object)')
        am = [s for s in O.at(0x34528) if s[3] == 'STT_FUNC']
        sig = am[0][2] if am else ''
        good = ok and sig == '_ZN6__asan11asan_mallocEmPN11__sanitizer18BufferedStackTraceE'
        self.put('a1', 11 if good else None,
                 f'trace object pointer = a1 = x11: {im} symtab has PC_asan_malloc 0x34528 (lib/A/Rt/RtDDefs.v:28) = {sig}, '
                 f'asan_malloc(unsigned long, BufferedStackTrace*), 2nd argument = a1; RtDDefs.v:105 getr regs 11 = w64 p')
        yi04 = U.text('Reusable/YI04.v')
        yp01 = U.text('Reusable/YP01.v')
        atom = 'sr_atoms : list sv := SLit 0 :: atom_regs 1 31' in yi04 and 'match n with O => [] | S n\' => SOff k 0 :: atom_regs (S k) n\' end' in yp01
        self.atom_note = ('atom r = register r\'s entry value (lib/Reusable/YI04.v:81 sr_atoms = SLit 0 :: atom_regs 1 31, '
                          'YP01.v:42-43 atom_regs k n = SOff k 0 :: ..)') if atom else None
        self.put('atom_sp', 2 if atom else None, f'atom of sp = x2: {self.atom_note}')
        self.put('atom_a1', 11 if (atom and good) else None, f'atom of a1 = x11 (the trace object pointer pT): {self.atom_note}; {sig}')
        self.put('atom_tp', 4 if atom else None, f'tp = x4: {self.atom_note}')
        self.put('c_ext', 256 if '(ly_C ly, 256)' in yg0f else None, 'lib/Reusable/YG0f.v:301 owned_extents: (ly_C ly, 256), the C object is 256 bytes')
        self.put('d_ext', 4096 if '(ly_D ly, 4096)' in yg0f else None, 'lib/Reusable/YG0f.v:302 owned_extents: (ly_D ly, 4096), the D object is 4096 bytes')
        yg01 = U.text('Reusable/YG01.v')
        cap = int(re.search(r'Definition DEPOT_CAP : Z := (\d+)', yg01).group(1))
        self.cap = cap
        self.put('depot_ids', cap + 1, f'lib/Reusable/YG01.v:151 DEPOT_CAP = {cap}; depot_ids = 1 + length depot (YG00.v:398): ids <= {cap + 1}')
        self.put('depot_ids1', cap + 2, f'one id above the depot_ids bound (an insertion): DEPOT_CAP + 2 = {cap + 2} (YG01.v:151)')
        tot = 31 * (cap + 2) + 32
        self.put('depot_tot', tot, f'TOT = length tr0 + 1 + depot_frames (AFem.v:87) <= 31 + 1 + 31 * DEPOT_CAP = {31 * cap + 32} '
                                   f'(YG0f.v:330 lo_tr0 <= 31, YG01.v:178 depot_inv_frames <= 31 * length); bound written = '
                                   f'31 * (DEPOT_CAP + 2) + 32 = {tot} (the donor 127070 = 31 * (4096 + 2) + 32, same formula)')
        kfa = int(re.search(r'Definition kFreeArrayOffset : Z := (\d+)', yg00).group(1))
        self.put('kfao', kfa, f'lib/Reusable/YG00.v:14 kFreeArrayOffset = {kfa} = {kfa:#x} (region 2^32 less its free array 2^32 / 8)')
        e = 0
        while 2 ** e < kfa // 16:
            e += 1
        self.put('cp_exp', e, f'compact pointer CPv (NBv = SB + 24 * 2^32 + 16 * CPv, b + kBatchBytes <= SB + 24 * 2^32 + kFreeArrayOffset): '
                              f'CPv < kFreeArrayOffset / 16 = {kfa // 16:#x} <= 2 ^ {e} (and > 2 ^ {e - 1})')
