#!/usr/bin/env python3
"""Symbol + offset sweep over the PAIRED rows of port_addr_check full.tsv runs.

Rule: a relocated numeral that names an object must equal TARGET(S) + o, where S + o is the DONOR value read in the
donor's unstripped twin symtab. A value that lands in .got / .got.plt, or on another symbol than the donor's, is a
mismatch.

Per run: `--run NAME TSV DONOR_PIN DONOR_TWIN OURS_PIN OURS_TWIN` (repeatable). The script checks that the image
sha256 prefixes match the ones the TSV header records. Output: rows.tsv (one row per checked numeral) and
skipped.tsv (counts of rows not checked, by reason), in --out.

Row selection (in this order):
  * paired: both src_value and dst_value present (UNPAIRED-* and NAMED-CONSTANT rows have one side empty);
  * kind `ident` skipped: an identifier suffix is a name; it is never relocated (src_value = dst_value on every row);
  * instruction words skipped: src_class INSN (a literal typed `bv 32`) or a dst_res `insn 0x...`;
  * address-valued in the donor: src_value inside a PT_LOAD [p_vaddr, p_vaddr + p_memsz) of the donor pin;
  * NONADDR rows whose reason is a size / count BY NAME are skipped (`size <header quantity>`, `size-like (NAME)`
    where NAME matches the tool's SIZE_NAME and not its ADDR_NAME, an allocator-operation / size-list argument, a
    constructor field declared as a length); such a row is kept when src_value is the start of a named donor symbol.

Resolution of a value v in one image (symtab of the twin, sections, PT_LOAD and bytes of the pin):
  * section: the SHF_ALLOC section holding v (.tbss excluded: its addresses are TLS offsets);
  * cover: every named OBJECT / FUNC symbol with size > 0 and st_value <= v < st_value + st_size; the primary one is
    the smallest (innermost);
  * start aliases: every named symbol (any type but FILE / SECTION / TLS, mapping symbols $d / $x excluded) with
    st_value = v; end: every sized OBJECT / FUNC with st_value + st_size = v (candidate S + st_size);
  * near: with no cover, the nearest preceding named symbol of the same section (S + (v - st_value));
  * boundaries: section start / end, PT_LOAD start / end, and PT_LOAD k + off for a value in no section (the ELF
    header and program headers at the base);
  * .got / .got.plt: the slot (v - section start) // 8, the byte within it, and the 64-bit word the pin holds in that
    slot (the pointee), itself resolved as above.
A symbol is keyed by its name (global / weak) or `file:name` (local; file = the STT_FILE entry it follows).

Status of a pair (donor v, ours w):
  LANDS-IN-GOT               w is in .got / .got.plt and v is not, or both are and the two slots' pointees differ;
  SAME                       a common (key, offset) candidate, or w = ours(S) + o for a donor candidate S + o that stays
                             inside (or outside) S the same way on both sides; basis names which;
  SAME-SYMBOL-OFFSET-DIFFERS a common key with a different offset;
  NO-SYMBOL                  either side has no cover and no start alias (only a neighbour, or nothing);
  DIFFERENT-SYMBOL           both sides named, no common key (a donor .got cell against a non-GOT w included).
"""
import argparse
import bisect
import collections
import hashlib
import re
import struct
import sys

from elftools.elf.elffile import ELFFile

# port_addr_check 3d2eee813cce, port_addr_check.py:194-196 (the names the tool reads as sizes)
SIZE_NAME = re.compile(r'(SIZE|_SZ\b|_SZ_|SZ$|CAP\b|CAP_|_MAX|MAX_|_MIN|MIN_|NODES|BLOCK|_LOG\b|LOG_|_LEN|LEN_|COUNT|'
                       r'NUM|TAX|_STACK$|MAGIC|MASK|BYTES|LIMIT|THRESH|threshold|FRAMES|^K[A-Z]|^T_|^CTX_)')
ADDR_NAME = re.compile(r'^(A_|A[A-Z]|GOT_|PC0_|PC_)|ADDR|_PC$|_LO$|_HI$|_BEG|_END')
GOTS = ('.got', '.got.plt')
COLS = ['verdict', 'kernel_checked', 'image', 'src_file', 'src_line', 'dst_file', 'dst_line', 'sentence', 'idx',
        'kind', 'src_value', 'dst_value', 'src_class', 'src_res', 'dst_res', 'note']


def sha12(path):
    with open(path, 'rb') as f:
        return hashlib.sha256(f.read()).hexdigest()[:12]


class Sym:
    __slots__ = ('name', 'key', 'value', 'size', 'type', 'sec')

    def __init__(self, name, key, value, size, typ, sec):
        self.name, self.key, self.value, self.size, self.type, self.sec = name, key, value, size, typ, sec


class Img:
    def __init__(self, pin, twin):
        self.pin, self.twin = pin, twin
        self.pin_sha, self.twin_sha = sha12(pin), sha12(twin)
        with open(pin, 'rb') as f:
            self.data = f.read()
        pe = ELFFile(open(pin, 'rb'))
        self.loads = [(s.header.p_vaddr, s.header.p_memsz, s.header.p_filesz, s.header.p_offset)
                      for s in pe.iter_segments() if s.header.p_type == 'PT_LOAD']
        self.secs = sorted((s.header.sh_addr, s.header.sh_addr + s.header.sh_size, s.name)
                           for s in pe.iter_sections()
                           if s.header.sh_flags & 2 and s.header.sh_addr and s.name != '.tbss')
        self.sec_lo = [a for a, _, _ in self.secs]
        te = ELFFile(open(twin, 'rb'))
        tloads = [(s.header.p_vaddr, s.header.p_memsz, s.header.p_filesz)
                  for s in te.iter_segments() if s.header.p_type == 'PT_LOAD']
        if tloads != [x[:3] for x in self.loads]:
            sys.exit(f'{twin}: PT_LOAD differs from {pin}')
        names = {i: s.name for i, s in enumerate(te.iter_sections())}
        self.syms, cur = [], None
        for sy in te.get_section_by_name('.symtab').iter_symbols():
            t, b, sh = sy['st_info']['type'], sy['st_info']['bind'], sy['st_shndx']
            if t == 'STT_FILE':
                cur = sy.name
                continue
            if (t in ('STT_SECTION', 'STT_TLS') or not isinstance(sh, int) or not sy.name
                    or sy.name in ('$d', '$x') or sy.name.startswith(('$d.', '$x.'))):
                continue
            sec = names.get(sh)
            if not any(n == sec for _, _, n in self.secs):
                continue
            self.syms.append(Sym(sy.name, f'{cur}:{sy.name}' if b == 'STB_LOCAL' else '', sy['st_value'], sy['st_size'],
                                 t, sec))
        # key: the bare name where the image holds it once (a local of one file included: the STT_FILE name of a
        # program's own source differs between two programs); `file:name` for a name several symbols share
        nc = collections.Counter(s.name for s in self.syms)
        for s in self.syms:
            s.key = s.name if nc[s.name] == 1 or not s.key else s.key
        self.by_key = collections.defaultdict(list)
        for s in self.syms:
            self.by_key[s.key].append(s)
        self.sized = sorted((s for s in self.syms if s.type in ('STT_OBJECT', 'STT_FUNC') and s.size),
                            key=lambda s: s.value)
        self.sized_lo = [s.value for s in self.sized]
        self.maxsize = max(s.size for s in self.sized)
        self.starts = collections.defaultdict(list)
        self.ends = collections.defaultdict(list)
        for s in self.syms:
            self.starts[s.value].append(s)
        for s in self.sized:
            self.ends[s.value + s.size].append(s)
        self.by_sec = collections.defaultdict(list)
        for s in sorted(self.syms, key=lambda s: (s.value, s.size)):
            self.by_sec[s.sec].append(s)
        self.by_sec_lo = {k: [s.value for s in v] for k, v in self.by_sec.items()}

    def inload(self, v):
        return any(a <= v < a + m for a, m, _, _ in self.loads)

    def load_of(self, v):
        for i, (a, m, _, _) in enumerate(self.loads):
            if a <= v < a + m:
                return i, v - a
        return None

    def mem(self, v, n):
        for a, m, fs, off in self.loads:
            if a <= v and v + n <= a + m:
                b = self.data[off + v - a: off + min(v - a + n, fs)] if v - a < fs else b''
                return b + b'\0' * (n - len(b))
        return None

    def section(self, v):
        i = bisect.bisect_right(self.sec_lo, v) - 1
        if i >= 0 and self.secs[i][0] <= v < self.secs[i][1]:
            return self.secs[i]
        return None

    def unique(self, key):
        xs = self.by_key.get(key) or []
        return xs[0] if len(xs) == 1 else None

    def cstr(self, v):
        """`str:"TEXT"+k` when v lies in a NUL-terminated printable string of .rodata, else ''."""
        sec = self.section(v)
        if not sec or sec[2] != '.rodata':
            return ''
        lo = max(sec[0], v - 512)
        back = self.mem(lo, v - lo) or b''
        i = back.rfind(b'\0')
        start = lo + i + 1 if i >= 0 else lo
        fwd = self.mem(v, min(512, sec[1] - v)) or b''
        j = fwd.find(b'\0')
        if j < 0:
            return ''
        s = self.mem(start, v - start + j)
        if not s or any(not (0x20 <= c < 0x7f or c in (9, 10, 13)) for c in s):
            return ''
        txt = s.decode('ascii').encode('unicode_escape').decode('ascii').replace('"', '\\"')
        return f'str:"{txt}"+{v - start}'

    def key_of(self, r):
        for k in ('cover', 'alias', 'end'):
            if r[k]:
                return r[k][0].key
        return r['near'].key if r['near'] is not None else None

    def resolve(self, v, depth=0):
        """Resolution record of v: dict with sec, secoff, cover, alias, end, near, bnd, got, cands, primary."""
        r = {'v': v, 'sec': None, 'secoff': None, 'cover': [], 'alias': [], 'end': [], 'near': None, 'bnd': [],
             'got': None}
        sec = self.section(v)
        if sec:
            r['sec'], r['secoff'] = sec[2], v - sec[0]
            if v == sec[0]:
                r['bnd'].append(('sec:' + sec[2], 0))
        for lo, hi, n in self.secs:
            if v == hi:
                r['bnd'].append(('secend:' + n, 0))
        for i, (a, m, _, _) in enumerate(self.loads):
            if v == a:
                r['bnd'].append((f'load{i}', 0))
            if v == a + m:
                r['bnd'].append((f'load{i}.end', 0))
        if not sec:
            lo = self.load_of(v)
            if lo:
                r['bnd'].append((f'load{lo[0]}+nosec', lo[1]))
        j = bisect.bisect_right(self.sized_lo, v)
        while j > 0:
            j -= 1
            s = self.sized[j]
            if s.value + self.maxsize <= v:
                break
            if s.value <= v < s.value + s.size:
                r['cover'].append(s)
        r['cover'].sort(key=lambda s: (s.size, s.type != 'STT_OBJECT' and s.type != 'STT_FUNC', s.name))
        r['alias'] = sorted(self.starts.get(v, []), key=lambda s: s.name)
        r['end'] = sorted(self.ends.get(v, []), key=lambda s: s.name)
        if not r['cover'] and sec:
            lst = self.by_sec.get(sec[2], [])
            k = bisect.bisect_right(self.by_sec_lo.get(sec[2], []), v) - 1
            if k >= 0:
                r['near'] = lst[k]
        if sec and sec[2] in GOTS and depth == 0:
            slot, within = divmod(v - sec[0], 8)
            w = self.mem(sec[0] + slot * 8, 8)
            p = struct.unpack('<Q', w)[0] if w else None
            r['got'] = {'sec': sec[2], 'slot': slot, 'within': within, 'pointee': p,
                        'pres': self.resolve(p, 1) if p and self.inload(p) else None}
        r['cands'] = cands(r)
        r['primary'] = primary(r)
        return r


def cands(r):
    """(key, offset) candidates of a resolution."""
    v, out = r['v'], set()
    for s in r['cover']:
        out.add((s.key, v - s.value))
    for s in r['alias']:
        out.add((s.key, 0))
    for s in r['end']:
        out.add((s.key, s.size))
    if r['near'] is not None:
        out.add((r['near'].key, v - r['near'].value))
    out.update(r['bnd'])
    return out


def got_cands(r):
    """What a GOT slot holds: the pointee's candidates, NULL, or (a word outside the image, e.g. a TLS offset or a
    flag value) the word itself."""
    g = r['got']
    if g['pointee'] is None:
        return set()
    if g['pointee'] == 0:
        return {('GOT->NULL', 0)}
    if g['pres'] is None:
        return {('GOT-WORD', g['pointee'])}
    return {('GOT->' + k, o) for k, o in g['pres']['cands']}


def named(r):
    return bool(r['cover'] or r['alias'])


def fmt_sym(s, off):
    return f'{s.name}+{off:#x}'


def primary(r):
    v = r['v']
    if r['got']:
        g = r['got']
        p = g['pointee']
        pp = g['pres']['primary'][0] if g['pres'] else ('NULL' if p == 0 else 'a word outside the image')
        return (f"{g['sec']}[{g['slot']}]+{g['within']}", f"GOT cell holding {p:#x} = {pp}" if p is not None else '')
    if r['cover']:
        s = r['cover'][0]
        return (fmt_sym(s, v - s.value), 'cover')
    if r['alias']:
        s = r['alias'][0]
        return (fmt_sym(s, 0), 'start')
    if r['end']:
        s = r['end'][0]
        return (fmt_sym(s, s.size), 'end')
    if r['near'] is not None:
        s = r['near']
        return (fmt_sym(s, v - s.value), 'near')
    if r['bnd']:
        k, o = r['bnd'][0]
        return (f'{k}+{o:#x}', 'boundary')
    return ('', 'none')


def status(d, o, D, O):
    """(status, basis) of a donor resolution d against an ours resolution o."""
    if o['got'] and not d['got']:
        return 'LANDS-IN-GOT', 'ours in ' + o['got']['sec'] + ', donor in ' + str(d['sec'])
    if d['got'] and o['got']:
        if got_cands(d) & got_cands(o) and d['got']['within'] == o['got']['within']:
            return 'SAME', 'got-pointee'
        return 'LANDS-IN-GOT', 'GOT slots with different pointees'
    if d['got'] and not o['got']:
        return 'DIFFERENT-SYMBOL', 'donor is a GOT cell, ours is not'
    dc, oc = d['cands'], o['cands']
    common = dc & oc
    if common:
        kinds = []
        for k, off in common:
            if k.startswith(('sec:', 'secend:', 'load')):
                kinds.append('boundary')
            elif any(s.key == k for s in o['cover']) and any(s.key == k for s in d['cover']):
                kinds.append('cover')
            elif any(s.key == k for s in o['alias']) and any(s.key == k for s in d['alias']):
                kinds.append('start')
            elif any(s.key == k for s in o['end']) and any(s.key == k for s in d['end']):
                kinds.append('end')
            else:
                kinds.append('near')
        for want in ('cover', 'start', 'end', 'boundary', 'near'):
            if want in kinds:
                return 'SAME', want
    w = o['v']
    for k, off in sorted(dc):
        S = D.unique(k)
        T = O.unique(k)
        if not S or not T or T.value + off != w:
            continue
        if (off < S.size) == (off < T.size) or (not S.size and not T.size):
            return 'SAME', 'predicted'
    dk = {k for k, _ in dc if not k.startswith(('sec:', 'secend:', 'load'))}
    ok = {k for k, _ in oc if not k.startswith(('sec:', 'secend:', 'load'))}
    if dk & ok:
        return 'SAME-SYMBOL-OFFSET-DIFFERS', ','.join(sorted(dk & ok)[:3])
    if not named(d) or not named(o):
        return 'NO-SYMBOL', ('donor' if not named(d) else '') + ('+' if not named(d) and not named(o) else '') + (
            'ours' if not named(o) else '') + ' unnamed'
    return 'DIFFERENT-SYMBOL', ''


def size_by_name(r):
    res = r[13]
    if r[12] != 'NONADDR':
        return False
    if res.startswith('size ') or res.startswith('an allocator operation argument') or (
            res.startswith('argument ') and 'declared `' in res):
        return True
    m = re.match(r'size-like \(([^)]*)\)', res)
    if m:
        nm = m.group(1)
        return nm != 'context' and bool(SIZE_NAME.search(nm)) and not ADDR_NAME.search(nm)
    return False


def header_shas(path):
    src = dst = None
    with open(path) as f:
        for ln in f:
            if not ln.startswith('#'):
                break
            m = re.match(r'#\s+image (src|dst) \S+\s+\S+\s+sha256 (\w+) .*symtab of \S+ (\w+)', ln)
            if m:
                if m.group(1) == 'src':
                    src = (m.group(2), m.group(3))
                else:
                    dst = (m.group(2), m.group(3))
    return src, dst


def desc(r):
    p = r['primary']
    sec = r['sec'] or 'no-section'
    nb = ''
    if p[1] in ('near', 'boundary', 'none'):
        nb = f" (neighbour {fmt_sym(r['near'], r['v'] - r['near'].value)})" if r['near'] is not None else ''
    return sec, p[0], p[1] + nb


OUT_COLS = ['run', 'src', 'dst', 'sentence', 'idx', 'kind', 'src_class', 'gate_verdict', 'src_value', 'dst_value',
            'donor_sec', 'donor_symoff', 'donor_how', 'ours_sec', 'ours_symoff', 'ours_how', 'status', 'basis',
            'donor_end_of', 'ours_end_of', 'donor_str', 'ours_str', 'donor_key_in_ours', 'ours_key_in_donor']


def presence(key, img):
    if key is None:
        return ''
    n = len(img.by_key.get(key) or [])
    return 'no' if n == 0 else 'yes' if n == 1 else f'{n} entries'


def sweep(name, tsv, D, O, out, skipped, other_images=False):
    hs, hd = header_shas(tsv)
    for side, h, X in (('donor', hs, D), ('our', hd, O)):
        if h and (h[0] != X.pin_sha or h[1] != X.twin_sha):
            if not other_images:
                sys.exit(f'{name}: {side} images {X.pin_sha}/{X.twin_sha} are not the run\'s {h}')
            print(f'{name}: RE-RESOLUTION: the run read {side} images {h[0]}/{h[1]}; this sweep resolves its pairs '
                  f'in {X.pin_sha}/{X.twin_sha}')
    cache_d, cache_o = {}, {}
    n = 0
    with open(tsv) as f:
        for ln in f:
            if ln.startswith('#'):
                continue
            r = ln.rstrip('\n').split('\t')
            if len(r) < 16 or r[0] == 'verdict':
                continue
            if not r[10] or not r[11]:
                skipped[(name, 'not paired (one side empty)')] += 1
                continue
            if r[9] == 'ident':
                skipped[(name, 'identifier suffix (kind ident)')] += 1
                continue
            if r[12] == 'INSN' or r[14].startswith('insn '):
                skipped[(name, 'instruction word (INSN)')] += 1
                continue
            sv, dv = int(r[10], 16), int(r[11], 16)
            jt = ''
            if r[12] == 'JTREL':
                # a jump-table word is target - table base (port_addr_check reads the base from the code that indexes
                # the table and names it in src_res / dst_res): resolve the TARGET on each side
                bs, bd = (re.search(r'table base (0x[0-9a-f]+)', x) for x in (r[13], r[14]))
                if not bs or not bd:
                    skipped[(name, 'jump-table word without a stated table base')] += 1
                    continue
                bs, bd = int(bs.group(1), 16), int(bd.group(1), 16)
                sx = lambda w: w - (1 << 32) if w & 0x80000000 else w
                ts, td = (bs + sx(sv)) & ((1 << 64) - 1), (bd + sx(dv)) & ((1 << 64) - 1)
                jt = f'jt-target {ts:#x} (base {bs:#x}) / {td:#x} (base {bd:#x}); '
                sv_r, dv_r = ts, td
            else:
                sv_r, dv_r = sv, dv
            if not D.inload(sv_r):
                skipped[(name, 'src value outside every donor PT_LOAD')] += 1
                continue
            if size_by_name(r) and not D.starts.get(sv):
                skipped[(name, 'NONADDR, a size / count by name')] += 1
                continue
            d = cache_d.get(sv_r) or cache_d.setdefault(sv_r, D.resolve(sv_r))
            o = cache_o.get(dv_r) or cache_o.setdefault(dv_r, O.resolve(dv_r))
            st, basis = status(d, o, D, O)
            basis = jt + basis
            ds, dp, dh = desc(d)
            os_, op, oh = desc(o)
            out.write('\t'.join([name, f'{r[3]}:{r[4]}', f'{r[5]}:{r[6]}', r[7], r[8], r[9], r[12], r[0],
                                 f'{sv:#x}', f'{dv:#x}', ds, dp, dh, os_, op, oh, st, basis,
                                 ','.join(s.name for s in d['end']), ','.join(s.name for s in o['end']),
                                 D.cstr(sv_r), O.cstr(dv_r), presence(D.key_of(d), O), presence(O.key_of(o), D)]) + '\n')
            n += 1
    return n


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--run', nargs=6, action='append', default=[],
                    metavar=('NAME', 'TSV', 'DONOR_PIN', 'DONOR_TWIN', 'OURS_PIN', 'OURS_TWIN'))
    ap.add_argument('--reresolve', nargs=6, action='append', default=[],
                    metavar=('NAME', 'TSV', 'DONOR_PIN', 'DONOR_TWIN', 'OURS_PIN', 'OURS_TWIN'),
                    help='like --run, for a run whose pairs are resolved in OTHER images than the run read')
    ap.add_argument('--out', required=True)
    ap.add_argument('--rows', default='rows.tsv')
    a = ap.parse_args()
    imgs = {}
    skipped = collections.Counter()
    with open(f'{a.out}/{a.rows}', 'w') as out:
        out.write('\t'.join(OUT_COLS) + '\n')
        for other, specs in ((False, a.run), (True, a.reresolve)):
            for name, tsv, dp, dt, op, ot in specs:
                D = imgs.get((dp, dt)) or imgs.setdefault((dp, dt), Img(dp, dt))
                O = imgs.get((op, ot)) or imgs.setdefault((op, ot), Img(op, ot))
                n = sweep(name, tsv, D, O, out, skipped, other)
                print(f'{name}: checked {n} rows (donor {D.pin_sha}/{D.twin_sha}, ours {O.pin_sha}/{O.twin_sha})')
    with open(f'{a.out}/{a.rows[:-4]}.skipped.tsv', 'w') as f:
        f.write('run\treason\tcount\n')
        for (name, why), c in sorted(skipped.items()):
            f.write(f'{name}\t{why}\t{c}\n')


if __name__ == '__main__':
    main()
