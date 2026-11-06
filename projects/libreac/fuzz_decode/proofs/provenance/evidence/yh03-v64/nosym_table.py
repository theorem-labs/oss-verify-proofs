#!/usr/bin/env python3
"""nosym_table.py KIT_DIR YH03.v PIN TWIN READERS.tsv -- judge every NOSYM cell of a YH03 address table. Read-only.

yh03check fb3bfbc1eea8 leaves a D cell NOSYM when no symbol carries the cell's name, and checks nothing about it. This
tool reads each such cell against the unit's PIN (the bytes) and TWIN (the symbols), by the rule its name states:

  const   `D_const_double_<c>`, `D_const_u64_<c>`, `D_const_<WORD>_0x<16 hex>`: the 8 bytes at the value must be the
          constant the name encodes. A name that lists several constants (the slug joined them) is satisfied by its
          FIRST one, and the row says which of the listed constants the image holds.
  got     `D_got_<x>`: the 8 bytes at the value must be the address of the symbol <x> (`<x>`, `_<x>` or `__<x>`) of the
          twin, or 0 when the twin defines no such symbol (a weak undefined reference). The row also gives the code
          that forms the slot's address.
  table   `D_jt_<fn>_<n>`, `D_debruijn32`, `D_size_classes`: the real object the name says. A jump table: every word of
          the image that forms the value lies in the function the name says, and the words that use it are the table
          shape `slli / add / lw / add / jr`. The De Bruijn table: 32 bytes that are a permutation of 0..31, formed by
          code. size_classes: a sized OBJECT symbol starts exactly there.
  object  every other cell (the driver's, atexit's and the stream buffers'): a sized OBJECT symbol of the twin starts
          exactly at the value,
          and its name (or the STT_FILE of its compilation unit) is the one the cell name says.

Each row gets TRUE (the rule holds), FALSE (it does not) or UNSETTLED (the rule does not apply; never silently passed).
READERS.tsv is `cell <TAB> count <TAB> lines` for the cell's readers outside the two YH03.v, as git grep -w gives them.
Targets are the comparison kit's own pass (strictcmp3.py / drvcmp.py of KIT_DIR over bytecmp's words).
The scanner of record blocks one driver prefix outside .v files, so `--mask WORD` replaces WORD by `CODENAME` in every
field this tool prints and in the keys it looks up in READERS.tsv (whose rows the caller masks the same way). The two
YH03.v keep the real names: a row's file and line name the definition.
usage: nosym_table.py KIT_DIR YH03.v PIN TWIN READERS.tsv [--mask WORD]   (TSV on stdout, the detail on stderr)"""
import importlib.util, os, re, struct, sys
from elftools.elf.elffile import ELFFile

KIT, VFILE, PIN, TWIN, READERS = sys.argv[1:6]
MASK = sys.argv[7] if len(sys.argv) > 7 and sys.argv[6] == '--mask' else None


def mask(x):
    return x.replace(MASK, 'CODENAME') if MASK else x
sp = importlib.util.spec_from_file_location('strictcmp3_kit', os.path.join(KIT, 'strictcmp3.py'))
S = importlib.util.module_from_spec(sp); sp.loader.exec_module(S)
DEF = re.compile(r'Definition\s+src0_(\S+)\s*:\s*Z\s*:=\s*(0x[0-9a-fA-F]+|\d+)\.')
JT = re.compile(r'^D_jt_(.+?)(?:_(\d+))?$')
HEX16 = re.compile(r'0x([0-9a-fA-F]{16})')
# the 8-byte constants whose name is a word, not a literal, with the arithmetic that gives them
NAMED = {'u64_fmt_fp_1e9_recip_misc': (-(-2 ** 84 // 10 ** 9),
         'ceil(2^84 / 1e9), the unsigned-division magic for /1e9: mulhu by it, then shift right 84 - 64 = 20')}


def pin_image(p):
    e = ELFFile(open(p, 'rb'))
    segs = [(s['p_vaddr'], s['p_filesz'], s.data()) for s in e.iter_segments() if s['p_type'] == 'PT_LOAD']
    secs = [(x.name, x['sh_addr'], x['sh_size']) for x in e.iter_sections() if x['sh_addr']]
    return segs, secs


def rd(segs, a, n):
    for v, fz, d in segs:
        if v <= a < v + fz:
            b = d[a - v:a - v + n]
            return b if len(b) == n else None
    return None


def sec(secs, a):
    return next((n for n, v, z in secs if v <= a < v + z), '(none)')


def files_of(p):
    e = ELFFile(open(p, 'rb'))
    out, cur = {}, None
    for y in e.get_section_by_name('.symtab').iter_symbols():
        if y['st_info']['type'] == 'STT_FILE':
            cur = y.name
        elif y.name and y['st_info']['bind'] == 'STB_LOCAL':
            out[(y['st_value'], y.name)] = cur
    return out


def double_of(tok):
    m = re.match(r'0x1p(_?)(\d+)', tok)
    if m:
        return float.fromhex('0x1p%s%s' % ('-' if m.group(1) else '', m.group(2))), '0x1p%s%s' % ('-' if m.group(1) else '', m.group(2))
    m = re.match(r'^(\d+)_(\d+)$', tok)
    if m:
        return float('%s.%s' % m.groups()), '%s.%s' % m.groups()
    return None, None


def first_double(slug):
    """the first constant a `const_double_...` slug names, and every constant it lists"""
    toks, all_ = [], []
    for t in re.findall(r'0x1p_?\d+|\d+_\d+', slug):
        v, txt = double_of(t)
        if v is not None:
            all_.append(txt)
            toks.append(v)
    return (toks[0] if toks else None), all_


exact = {}
inside = []
Tw = S.Img(TWIN)
tfiles = files_of(TWIN)
for v, z, nm, t in Tw.syms:
    if nm.startswith('$'):
        continue
    exact.setdefault(v, []).append((nm, t, z))
    if z and t in ('STT_FUNC', 'STT_OBJECT'):
        inside.append((v, z, nm, t))
byname = {}
for v, z, nm, t in Tw.syms:
    byname.setdefault(nm, []).append(v)


def qn(v, nm):
    f = tfiles.get((v, nm))
    return '%s{%s}' % (nm, f) if f else nm


psegs, psecs = pin_image(PIN)
cells = {}
lines = {}
for i, ln in enumerate(open(VFILE), 1):
    for m in DEF.finditer(ln):
        cells[m.group(1)] = int(m.group(2), 0)
        lines[m.group(1)] = i
readers = {}
for ln in open(READERS):
    c = ln.rstrip('\n').split('\t')
    readers[c[0]] = (int(c[1]), c[2] if len(c) > 2 else '')

# every address the image forms, from the kit's target pass, with the function and the words that use it
forms = {}
for v, z, nm, t in sorted(Tw.syms):
    if t != 'STT_FUNC' or not z:
        continue
    b = S.frd(Tw, v, z)
    if b is None:
        continue
    w = S.bc_words(b)
    for i, (kind, tgt) in S._g['targets'](v, b).items():
        forms.setdefault(tgt, []).append((nm, w[i][0], [x[1] for x in w[i + 1:i + 5]]))

JTSHAPE = ('add', 'lw', 'add', 'jr')


def jt_shape(words):
    """the four words after the addi, as (mnemonic) names, by opcode"""
    out = []
    for x in words:
        op, f3 = x & 0x7f, (x >> 12) & 7
        out.append('add' if op == 0x33 and f3 == 0 else 'lw' if op == 0x03 and f3 == 2 else
                   'jr' if op == 0x67 else 'other')
    return tuple(out)


print('\t'.join(['file', 'line', 'cell', 'value', 'section', 'class', 'expected', 'found', 'verdict', 'readers']))
want = [n for n in sorted(cells, key=lambda x: lines[x]) if mask(n) in readers]
for n in want:
    a = cells[n]
    line, (nread, rtxt) = lines[n], readers[mask(n)]
    cls, exp, got, verdict, detail = '?', '', '', 'UNSETTLED', ''
    at = ', '.join(qn(a, nm) for nm, t, z in exact.get(a, []))
    sized = [(z, v, nm, t) for v, z, nm, t in inside if v == a]
    if n.startswith('D_const_'):
        cls = 'const'
        slug = n[len('D_const_'):]
        b = rd(psegs, a, 8)
        got = b.hex() if b else '(no file bytes)'
        if b is None:
            detail = 'the pin holds no 8 bytes at the value'
        elif slug in NAMED or ('u64' in slug and slug in NAMED):
            v, why = NAMED[slug]
            exp = '%016x (%s)' % (v, why)
            verdict = 'TRUE' if struct.unpack('<Q', b)[0] == v else 'FALSE'
        elif HEX16.search(slug):
            v = int(HEX16.search(slug).group(1), 16)
            exp = '%016x' % v
            verdict = 'TRUE' if struct.unpack('<Q', b)[0] == v else 'FALSE'
        elif slug.startswith('double_'):
            v, all_ = first_double(slug[len('double_'):])
            if v is None:
                detail = 'no constant could be read from the name'
            else:
                exp = '%016x (double %s)' % (struct.unpack('<Q', struct.pack('<d', v))[0], all_[0])
                verdict = 'TRUE' if struct.unpack('<d', b)[0] == v else 'FALSE'
                if len(all_) > 1:
                    detail = 'the name lists %s; the image holds the first at this value' % ', '.join(all_)
        if verdict != 'UNSETTLED':
            got += ' (double %r)' % struct.unpack('<d', b)[0]
    elif n.startswith('D_got_'):
        cls = 'got'
        x = n[len('D_got_'):]
        cand = [c for c in (x, '_' + x, '__' + x) if c in byname]
        b = rd(psegs, a, 8)
        got = b.hex() if b else '(no file bytes)'
        want_v = min(byname[cand[0]]) if cand else 0
        exp = '%016x (%s)' % (want_v, '%s at %#x' % (cand[0], want_v) if cand else 'no symbol %s / _%s / __%s in the twin: a weak undefined reference, slot 0' % (x, x, x))
        if b is not None:
            verdict = 'TRUE' if struct.unpack('<Q', b)[0] == want_v else 'FALSE'
            got += ' (%s)' % (', '.join(qn(struct.unpack('<Q', b)[0], nm) for nm, t, z in exact.get(struct.unpack('<Q', b)[0], [])) or 'no symbol')
        detail = 'slot address formed by: %s' % ('; '.join('%s+%#x' % (f, o) for f, o, _ in forms.get(a, [])) or 'no code of the image')
    elif n == 'D_debruijn32':
        cls = 'table'
        b = rd(psegs, a, 32)
        exp = '32 bytes that are a permutation of 0..31, formed by code'
        got = b.hex() if b else '(no file bytes)'
        perm = b is not None and sorted(b) == list(range(32))
        verdict = 'TRUE' if perm and forms.get(a) else 'FALSE'
        detail = 'permutation of 0..31: %s; formed by: %s' % (perm, '; '.join('%s+%#x' % (f, o) for f, o, _ in forms.get(a, [])) or 'no code')
    elif JT.match(n) and n.startswith('D_jt_'):
        cls = 'table'
        fn = JT.match(n).group(1)
        use = forms.get(a, [])
        exp = 'formed only inside %s, as a jump table (slli / add / lw / add / jr)' % fn
        shapes = [(f, '+%#x' % o, jt_shape(ws)) for f, o, ws in use]
        got = '; '.join('%s%s %s' % (f, o, '/'.join(s)) for f, o, s in shapes) or 'no code forms this address'
        verdict = 'TRUE' if use and all(f == fn and s == JTSHAPE for f, o, s in shapes) else 'FALSE'
    else:
        cls = 'object'
        tail = n.split('_')[-1]
        pref = n.split('_')[1]
        if sized:
            z, v, nm, t = min(sized)
            f = tfiles.get((v, nm)) or ''
            ok = nm.endswith(tail) or tail in nm or pref in (f or '').replace('.c', '') or pref in nm
            exp = 'a sized OBJECT starting here whose name or file says %s / %s' % (pref, tail)
            got = '%s (size %d, %s)' % (qn(v, nm), z, t)
            verdict = 'TRUE' if ok and t == 'STT_OBJECT' else 'FALSE'
        else:
            exp = 'a sized OBJECT starting at the value'
            got = 'no sized symbol starts here (%s)' % (at or 'no symbol at all')
            verdict = 'FALSE'
    print('\t'.join(mask(x) for x in [VFILE, str(line), n, '%#x' % a, sec(psecs, a), cls, exp, got, verdict,
                                      str(nread)]))
    sys.stderr.write(mask('%s\t%s\t%s\tat: %s\t%s\n' % (n, verdict, detail, at or '-', rtxt[:200])))
