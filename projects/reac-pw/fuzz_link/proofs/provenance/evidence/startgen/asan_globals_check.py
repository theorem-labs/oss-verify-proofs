#!/usr/bin/env python3
"""asan_globals_check.py -- condition 3 of the link.asan start-up brief.

Reads the pinned image reac-pw/fuzz_link fuzz_link.asan and its unstripped twin, decodes the asan_globals
descriptor array (8 little-endian 64-bit words per descriptor: beg, size, size_with_redzone, name, module_name,
has_dynamic_init, source_location, odr_indicator), and checks:
  1. the image and the twin are the pinned bytes (sha256);
  2. the section asan_globals starts at 0xa62a0 and holds 2752 bytes = 43 descriptors;
  3. for every descriptor: beg is the start of a twin symbol of type OBJECT whose st_size equals size_with_redzone (the
     instrumented global is the original object followed by its right redzone), beg lies in an allocated section,
     size_with_redzone equals the instrumentation's rule (LLVM AddressSanitizer getRedzoneSizeForGlobal, min redzone 32:
     size <= 16 -> redzone 32 - size; else redzone = clamp((size / 32 / 4) * 32, 32, 2^18) padded so that size +
     redzone is a multiple of 32), and the name pointer reads a NUL-terminated string in the image;
  4. odr_indicator: reported per descriptor (0 or 0xffffffffffffffff = no ODR check; else the address and the twin
     symbol it names).
With --shadow-tsv it writes the shadow cells the runtime's registration sets for these descriptors (one row per shadow
byte: address, value, reason): for each descriptor the partial-granule byte (size mod 8) when size is not a multiple
of 8, then 0xf9 for every granule from ceil(size / 8) to size_with_redzone / 8; and 0xf9 for every granule of the
descriptor array itself (43 * 64 / 8 = 344 bytes). Shadow address = (a >> 3) + 0x7fff8000.
With --check-af0m FILE it compares those rows with FILE's Tfib_const_shadow rows (`zW (ANum a) v` or
`ACell (ANum a) W (AV (ANum v))`, little-endian over W bytes) and
with FILE's owned statics; with --check-ab01-tsv FILE (address<TAB>value rows read from the hand-off states) likewise.
Exit 0 only when every check passes.
"""
import argparse, hashlib, re, struct, sys
from elftools.elf.elffile import ELFFile

PIN = '059dae63e07ca2d80ae9227fa125d40586a02172c96d2b6884f8617ab912061d'
TWIN = '66cd0f159895f119b29a44eb3760cfda78506402a019729057dba69562af9d9f'
ADDR, BYTES, NDESC = 0xa62a0, 2752, 43
SHADOW_OFF = 0x7fff8000


def sha(path):
    return hashlib.sha256(open(path, 'rb').read()).hexdigest()


def rz_rule(size):
    """LLVM AddressSanitizer getRedzoneSizeForGlobal (MinRZ = 32, kMaxRZ = 2^18); returns size + redzone."""
    min_rz = 32
    if size <= min_rz // 2:
        rz = min_rz - size
    else:
        rz = min(max((size // min_rz // 4) * min_rz, min_rz), 1 << 18)
        if size % min_rz:
            rz += min_rz - (size % min_rz)
    return size + rz


# known answers of the redzone rule (worked by hand from the rule, both branches and the 2^18 clamp); exit 3 if one moves
for _s, _w in ((1, 32), (16, 32), (17, 64), (24, 64), (32, 64), (148, 192), (271992, 339968), (4096, 5120), (2 ** 21, 2 ** 21 + 2 ** 18)):
    if rz_rule(_s) != _w:
        print('SELFTEST FAILED: rz_rule(%d) = %d, expected %d' % (_s, rz_rule(_s), _w))
        sys.exit(3)


class Img:
    def __init__(self, path):
        self.f = open(path, 'rb')
        self.e = ELFFile(self.f)
        self.secs = [s for s in self.e.iter_sections() if s['sh_flags'] & 2]  # SHF_ALLOC

    def read(self, a, n):
        for seg in self.e.iter_segments():
            if seg['p_type'] != 'PT_LOAD':
                continue
            lo, fs = seg['p_vaddr'], seg['p_filesz']
            if lo <= a and a + n <= lo + seg['p_memsz']:
                out = b''
                for k in range(n):
                    x = a + k
                    if x < lo + fs:
                        self.f.seek(seg['p_offset'] + x - lo)
                        out += self.f.read(1)
                    else:
                        out += b'\0'
                return out
        raise ValueError('0x%x+%d not in a PT_LOAD' % (a, n))

    def section_of(self, a):
        for s in self.secs:
            if s['sh_addr'] <= a < s['sh_addr'] + max(1, s['sh_size']):
                return s.name
        return None

    def cstr(self, a, lim=4096):
        b = b''
        while len(b) < lim:
            c = self.read(a + len(b), 1)
            if c == b'\0':
                return b.decode('latin-1')
            b += c
        return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--image', required=True)
    ap.add_argument('--twin', required=True)
    ap.add_argument('--shadow-tsv')
    ap.add_argument('--check-af0m')
    ap.add_argument('--check-ab01-tsv')
    a = ap.parse_args()
    bad = []
    hi, ht = sha(a.image), sha(a.twin)
    print('image %s sha256 %s (%s)' % (a.image, hi, 'PIN' if hi == PIN else 'NOT THE PIN'))
    print('twin  %s sha256 %s (%s)' % (a.twin, ht, 'PIN' if ht == TWIN else 'NOT THE PIN'))
    if hi != PIN: bad.append('image sha256')
    if ht != TWIN: bad.append('twin sha256')
    img, twin = Img(a.image), Img(a.twin)
    sec = img.e.get_section_by_name('asan_globals')
    if sec is None:
        sys.exit('REFUSED: no asan_globals section')
    print('asan_globals: addr 0x%x size %d (%d descriptors of 64 bytes); expected addr 0x%x size %d (%d)'
          % (sec['sh_addr'], sec['sh_size'], sec['sh_size'] // 64, ADDR, BYTES, NDESC))
    if (sec['sh_addr'], sec['sh_size']) != (ADDR, BYTES) or sec['sh_size'] % 64:
        bad.append('asan_globals geometry')
    n = sec['sh_size'] // 64
    raw = img.read(sec['sh_addr'], sec['sh_size'])
    st = twin.e.get_section_by_name('.symtab')
    syms = {}
    for s in st.iter_symbols():
        if s['st_info']['type'] == 'STT_OBJECT' and s['st_value']:
            syms.setdefault(s['st_value'], []).append((s.name, s['st_size']))
    allsyms = {}
    for s in st.iter_symbols():
        if s['st_value']:
            allsyms.setdefault(s['st_value'], []).append(s.name)
    rows = []
    owned_exp = [(sec['sh_addr'], sec['sh_size'], 'descriptor array')]
    print('i\tdesc_addr\tbeg\tsize\tsize_with_rz\trz_rule\tsection\tsymbol\tsym_size\tname\todr_indicator\todr_symbol\tverdict')
    for i in range(n):
        beg, size, swr, name, mod, dyn, loc, odr = struct.unpack_from('<8Q', raw, 64 * i)
        exp = rz_rule(size)
        sname = img.cstr(name)
        cand = syms.get(beg, [])
        match = [c for c in cand if c[1] == swr]
        secn = img.section_of(beg)
        odr_s = '-' if odr in (0,) else ('none(-1)' if odr == 0xffffffffffffffff else ','.join(allsyms.get(odr, ['?'])))
        ok = bool(match) and swr == exp and secn is not None and sname is not None and swr % 8 == 0
        if not ok:
            bad.append('descriptor %d' % i)
        print('%d\t0x%x\t0x%x\t%d\t%d\t%d\t%s\t%s\t%s\t%s\t0x%x\t%s\t%s' % (
            i, ADDR + 64 * i, beg, size, swr, exp, secn, (match or cand or [('NONE', 0)])[0][0],
            (match or cand or [('NONE', 0)])[0][1], sname, odr, odr_s, 'OK' if ok else 'FAIL'))
        owned_exp.append((beg + size, swr - size, 'redzone d%d' % i))
        # shadow rows set at registration
        full = size // 8
        if size % 8:
            rows.append(((beg >> 3) + SHADOW_OFF + full, size % 8, 'partial d%d' % i))
            full += 1
        for g in range(full, swr // 8):
            rows.append(((beg >> 3) + SHADOW_OFF + g, 0xf9, 'redzone d%d' % i))
    for g in range(sec['sh_size'] // 8):
        rows.append(((sec['sh_addr'] >> 3) + SHADOW_OFF + g, 0xf9, 'descriptor array'))
    addrs = [r[0] for r in rows]
    if len(set(addrs)) != len(addrs):
        bad.append('overlapping shadow rows')
    nodr = sum(1 for i in range(n) if struct.unpack_from('<8Q', raw, 64 * i)[7] not in (0, 0xffffffffffffffff))
    print('summary: %d descriptors; %d with an odr_indicator; %d shadow rows (%d redzone/partial + %d descriptor-array)'
          % (n, nodr, len(rows), len(rows) - sec['sh_size'] // 8, sec['sh_size'] // 8))
    if a.shadow_tsv:
        with open(a.shadow_tsv, 'w') as o:
            for r in sorted(rows):
                o.write('0x%x\t0x%x\t%s\n' % r)
        print('wrote %s (%d rows)' % (a.shadow_tsv, len(rows)))
    exp_map = {r[0]: r[1] for r in rows}
    if a.check_af0m:
        txt = re.sub(r'\(\*.*?\*\)', ' ', open(a.check_af0m).read(), flags=re.S)
        m = re.search(r'Definition\s+\w*const_shadow\b[^:]*:[^:]*:=\s*\[(.*?)\]\s*\.', txt, re.S)
        if not m:
            bad.append('af0m: no const_shadow list')
        else:
            got = {}
            num = r'(0x[0-9a-fA-F]+|\d+)'
            cells = [(ad, w, v) for ad, w, v in re.findall(r'ACell\s*\(ANum\s+' + num + r'\)\s*(\d+)\s*\(AV\s*\(ANum\s+' + num + r'\)\)', m.group(1))]
            cells += [(ad, w, v) for w, ad, v in re.findall(r'\bz(\d)\s*\(ANum\s+' + num + r'\)\s*' + num, m.group(1))]
            for ad, w, v in cells:
                ad, w, v = int(ad, 0), int(w), int(v, 0)
                for k in range(w):
                    got[ad + k] = (v >> (8 * k)) & 0xff
            miss = sorted(x for x in exp_map if got.get(x) != exp_map[x])
            extra = sorted(x for x in got if x not in exp_map)
            print('af0m %s: Tfib_const_shadow %d bytes; expected %d; mismatched or missing %d; extra %d' % (
                a.check_af0m, len(got), len(exp_map), len(miss), len(extra)))
            for x in miss[:20]:
                print('  MISSING/DIFF 0x%x expected 0x%x got %s' % (x, exp_map[x], got.get(x)))
            for x in extra[:20]:
                print('  EXTRA 0x%x = 0x%x' % (x, got[x]))
            if miss:
                bad.append('af0m const_shadow')
            mo = re.search(r'Definition\s+\w*owned_static\b[^:]*:[^:]*:=\s*\[(.*?)\]\s*\.', txt, re.S)
            if not mo:
                bad.append('af0m: no owned_static list')
            else:
                def ev(s):
                    s = s.strip()
                    if not re.fullmatch(r'[0-9a-fA-Fx+\- ]+', s):
                        return None
                    return eval(s, {'__builtins__': {}})
                rng, unparsed = [], 0
                for lo, ln in re.findall(r'\(\s*([^,()]+?)\s*,\s*([^()]+?)\s*\)', mo.group(1)):
                    x, y = ev(lo), ev(ln)
                    if x is None or y is None:
                        unparsed += 1
                    else:
                        rng.append((x, y))
                exact = [o for o in owned_exp if (o[0], o[1]) in rng]
                covered = [o for o in owned_exp
                           if all(any(r0 <= b < r0 + rl for r0, rl in rng) for b in range(o[0], o[0] + o[1]))]
                print('af0m %s: Tfib_owned_static %d rows (%d not evaluated); expected owned ranges %d (%d redzones + '
                      'the descriptor array): %d present as exact rows, %d covered byte for byte' % (
                          a.check_af0m, len(rng), unparsed, len(owned_exp), n, len(exact), len(covered)))
                for o in owned_exp:
                    if o not in covered:
                        print('  NOT OWNED (0x%x, %d) %s' % o)
                if len(covered) != len(owned_exp):
                    bad.append('af0m owned_static')
    if a.check_ab01_tsv:
        got = {}
        for line in open(a.check_ab01_tsv):
            p = line.split()
            if len(p) >= 3:
                got.setdefault(int(p[1], 0), set()).add(int(p[2], 0))
        nst = len(set(line.split()[0] for line in open(a.check_ab01_tsv) if line.strip()))
        miss = [x for x in exp_map if got.get(x) != {exp_map[x]}]
        print('ab01 states %s: %d states; expected %d shadow bytes; not equal in every state: %d' % (
            a.check_ab01_tsv, nst, len(exp_map), len(miss)))
        for x in miss[:20]:
            print('  0x%x expected 0x%x got %s' % (x, exp_map[x], got.get(x)))
        if miss:
            bad.append('ab01 shadow')
    print('VERDICT: %s' % ('PASS' if not bad else 'FAIL: ' + '; '.join(bad)))
    sys.exit(0 if not bad else 1)


if __name__ == '__main__':
    main()
