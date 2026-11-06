#!/usr/bin/env python3
"""imgread_check.py -- check that the image-read literals of a start-up file (AB1h / AB1k / AB1v / AE37 / AB12 of
reac-pw/fuzz_link image A) are link.asan's own values.

  imgread_check.py --image ELF --twin UNSTRIPPED [--atable AB12.v] FILE.v...

Per file it reads, and checks against the ELF (pyelftools; the image is the pinned asan build):
  F  `fetch_word <segs> (Z_to_bv 64 X) = Some (0xW%bv : bv 32)` with X a literal or `x_<field> TFIB [+|- k]` (fields
     from --atable): the 4 bytes at X in the image equal W;
  T  `Definition <p>_text_start : Z := A.` with `<p>_text_count : nat := N.` (and `<p>guard_start` / `_count`): [A, A+4N)
     lies in one executable PT_LOAD as the image module loads it (page floor to page ceiling); the words past p_memsz
     are counted (they read as zero); the symbol at A and the symbol holding A+4N-4 are printed (the reader judges the role);
  R  `segments_reserved ... = [(Z_to_bv 64 B, Z_to_bv 64 L); ...]`: equals the page-rounded PT_LOADs of the image;
  S  `sum_sizes ... = V`: the sum of those lengths;
  L  `PrimString.length Asan_seg_bytes_00K ... = N%N` and `scanN Asan_seg_bytes_00K 64 0 N`: N = p_memsz of PT_LOAD K
     rounded as the image module rounds it (reported, compared with p_memsz and p_filesz);
  W  `<lo> <= bv_unsigned x < <hi> -> wview` (the writable window): lo = page floor of the first writable PT_LOAD,
     hi = the image top (page-rounded end of the last PT_LOAD);
  any other hex literal >= 0x10000 is listed with the section / symbol it falls in (UNCLASSIFIED, for the reader).
Exit 1 on any F / T / R / S / W mismatch.
"""
import argparse, bisect, re, sys
from elftools.elf.elffile import ELFFile

PG = 0x1000


class Img:
    def __init__(self, path, twin):
        self.f = open(path, 'rb')
        self.e = ELFFile(self.f)
        self.loads = [p for p in self.e.iter_segments() if p['p_type'] == 'PT_LOAD']
        t = ELFFile(open(twin, 'rb'))
        syms = []
        for s in t.get_section_by_name('.symtab').iter_symbols():
            if s.name and s['st_value'] and s['st_info']['type'] in ('STT_FUNC', 'STT_OBJECT', 'STT_NOTYPE') \
                    and not s.name.startswith('$'):
                syms.append((s['st_value'], s['st_size'], s.name))
        syms.sort()
        self.syms, self.sa = syms, [s[0] for s in syms]
        self.secs = [(s['sh_addr'], s['sh_size'], s.name) for s in self.e.iter_sections() if s['sh_addr']]

    def word(self, a, n=4):
        for p in self.loads:
            if p['p_vaddr'] <= a and a + n <= p['p_vaddr'] + p['p_filesz']:
                self.f.seek(p['p_offset'] + a - p['p_vaddr'])
                return int.from_bytes(self.f.read(n), 'little')
        return None

    def sym(self, a):
        i = bisect.bisect_right(self.sa, a) - 1
        while i >= 0:
            v, sz, n = self.syms[i]
            if v <= a < v + max(sz, 1):
                return '%s+%#x' % (n, a - v)
            if a - v > 0x100000:
                break
            i -= 1
        return '?'

    def sec(self, a):
        for lo, sz, n in self.secs:
            if lo <= a < lo + sz:
                return n
        return '-'

    def exec_load(self, a, b):
        """(inside the page-rounded executable PT_LOAD, bytes of [a, b) past its p_memsz)"""
        for p in self.loads:
            if p['p_flags'] & 1:
                lo, end = p['p_vaddr'] & ~(PG - 1), p['p_vaddr'] + p['p_memsz']
                if lo <= a and b <= (end + PG - 1) & ~(PG - 1):
                    return True, max(0, b - max(a, end))
        return False, None


def atable_fields(path):
    t = open(path).read()
    return {k: int(v, 0) for k, v in re.findall(r'\b(x_\w+|img_\w+|rw_\w+)\s*:=\s*\(?(0x[0-9a-fA-F]+|\d+)', t)}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--image', required=True); ap.add_argument('--twin', required=True)
    ap.add_argument('--atable'); ap.add_argument('files', nargs='+')
    a = ap.parse_args()
    I = Img(a.image, a.twin)
    fld = atable_fields(a.atable) if a.atable else {}
    res = [(p['p_vaddr'] & ~(PG - 1), ((p['p_vaddr'] + p['p_memsz'] + PG - 1) & ~(PG - 1)) - (p['p_vaddr'] & ~(PG - 1)))
           for p in I.loads]
    top = res[-1][0] + res[-1][1]
    wlo = min(p['p_vaddr'] for p in I.loads if p['p_flags'] & 2) & ~(PG - 1)
    bad = 0
    for fn in a.files:
        txt = open(fn).read()
        print('== %s' % fn)
        seen = set()
        n_f = 0
        for m in re.finditer(r'fetch_word\s+\w+\s+\(Z_to_bv 64 \(?([^)]*?)\)?\)\s*=\s*Some\s*\(0x([0-9a-fA-F]+)%bv', txt):
            ex, w = m.group(1).strip(), int(m.group(2), 16)
            mm = re.fullmatch(r'(0x[0-9a-fA-F]+|\d+)', ex) or None
            if mm:
                addr = int(ex, 0)
            else:
                m2 = re.fullmatch(r'(x_\w+)\s+TFIB(?:\s*([+-])\s*(\d+))?', ex)
                if not m2 or m2.group(1) not in fld:
                    print('  F UNRESOLVED %s' % ex); bad += 1; continue
                addr = fld[m2.group(1)] + (int(m2.group(3)) * (1 if m2.group(2) == '+' else -1) if m2.group(2) else 0)
            got = I.word(addr)
            n_f += 1
            seen.add(addr)
            if got != w:
                print('  F MISMATCH %#x (%s): file 0x%08x image %s' % (addr, I.sym(addr), w, None if got is None else '0x%08x' % got))
                bad += 1
        print('  F %d fetch facts checked against the image bytes' % n_f)
        for p, st in re.findall(r'Definition\s+(\w+?)_?(?:text_)?start\s*:\s*Z\s*:=\s*(0x[0-9a-fA-F]+)', txt):
            mc = re.search(r'Definition\s+%s_?(?:text_)?count\s*:\s*nat\s*:=\s*(\d+)' % re.escape(p), txt)
            if not mc:
                continue
            lo, n = int(st, 16), int(mc.group(1))
            ok, past = I.exec_load(lo, lo + 4 * n)
            print('  T %s: [%#x, %#x) %d words; start %s, last word %s, end %s; %s' % (
                p, lo, lo + 4 * n, n, I.sym(lo), I.sym(lo + 4 * n - 4), I.sym(lo + 4 * n),
                ('in the executable segment, %d bytes past its p_memsz end' % past) if ok else 'NOT IN THE EXECUTABLE SEGMENT'))
            bad += 0 if ok else 1
        mr = re.search(r'segments_reserved\s+\w+\s*=\s*\[(.*?)\]\s*\.', txt, re.S)
        if mr:
            got = [(int(x, 16), int(y, 16)) for x, y in re.findall(r'Z_to_bv 64 (0x[0-9a-fA-F]+)\s*,\s*Z_to_bv 64 (0x[0-9a-fA-F]+)', mr.group(1))]
            ok = got == res
            print('  R segments_reserved %s: %s (image %s)' % ('EQUAL' if ok else 'DIFFERENT', [(hex(x), hex(y)) for x, y in got], [(hex(x), hex(y)) for x, y in res]))
            bad += 0 if ok else 1
        for v in re.findall(r'sum_sizes\s*\(segments_reserved\s+\w+\)\s*=\s*(0x[0-9a-fA-F]+)', txt):
            ok = int(v, 16) == sum(y for _, y in res)
            print('  S sum_sizes %s: %s (image %#x)' % (v, 'EQUAL' if ok else 'DIFFERENT', sum(y for _, y in res)))
            bad += 0 if ok else 1
        for k, n in re.findall(r'length\s+Asan_seg_bytes_(\d+)\)\s*/\s*2\)\s*=\s*(\d+)%N', txt):
            p = I.loads[int(k)]
            print('  L segment %s length %s: p_memsz %d p_filesz %d (page-rounded memsz %d)' % (
                k, n, p['p_memsz'], p['p_filesz'], ((p['p_vaddr'] + p['p_memsz'] + PG - 1) & ~(PG - 1)) - p['p_vaddr']))
        for lo, hi in re.findall(r'(0x[0-9a-fA-F]+)\s*<=\s*bv_unsigned x\s*<\s*(0x[0-9a-fA-F]+)\s*->\s*wview', txt):
            ok = int(lo, 16) == wlo and int(hi, 16) == top
            print('  W writable window [%s, %s): %s (image [%#x, %#x))' % (lo, hi, 'EQUAL' if ok else 'DIFFERENT', wlo, top))
            bad += 0 if ok else 1
        rest = sorted({int(x, 16) for x in re.findall(r'\b0x([0-9a-fA-F]+)\b', re.sub(r'\(\*.*?\*\)', ' ', txt, flags=re.S))
                       if 0x10000 <= int(x, 16) < 0x100000000} - seen)
        if rest:
            print('  other address-range literals (%d): %s' % (len(rest), ', '.join('%#x[%s %s]' % (x, I.sec(x), I.sym(x)) for x in rest[:80])))
    print('VERDICT: %s' % ('PASS' if not bad else 'FAIL (%d)' % bad))
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
