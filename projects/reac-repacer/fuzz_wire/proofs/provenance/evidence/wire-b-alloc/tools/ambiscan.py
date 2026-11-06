#!/usr/bin/env python3
"""ambiscan.py -- did a by-name function compare take the wrong copy of a name that several functions carry? Read-only.

A by-name compare (drvcmp.py / strictcmp.py / strictcmp2.py `cmp`, closure_strict.py / closure_strict2.py, jtcheck.py,
bsurvey) looks a function NAME up in each image. When several sized FUNC symbols carry that name (musl / asan statics:
`_ZN6__asanL11MemToShadowEm` has 5 copies in fuzz_uci.asan, one per .cpp), Img.fsym and strictcmp2 `cmp` silently take
the LOWEST-address copy (the asan_errors.cpp one), while the callers use other copies. ambiscan reads a record's output
files, collects every function name they compared, and reports each name that several distinct sized FUNC copies
(different address or size) carry in image X or in image Y. strictcmp3.py `cmp` refuses such names itself; this tool
checks outputs that older tools already wrote.

usage: ambiscan.py X_ELF Y_ELF OUTFILE [OUTFILE ...]
  X_ELF, Y_ELF: the two images the compares used (both with .symtab). Each OUTFILE is a file or a directory
  (every regular file under it, recursively, directory symlinks not followed). A file is skipped (one line on stderr)
  when it has a NUL byte in its first 4 KiB (binary) or is larger than 50 MB. Run with PYTHONPATH holding pyelftools.
  Loads strictcmp3.py from its own directory (Img, fcopies, _meta, qname).

Names a line compared (one token per line; lines starting with '#' and the `fn<TAB>pair` header are skipped):
  cmp       drvcmp / strictcmp / strictcmp2 / strictcmp3 `cmp` rows: the 1st tab field of a line whose 2nd tab field
            is TAG:TAG;
  cstr      CSTR rows (CSTR, function, pair, ...) of any tool: the 2nd tab field;
  closure-root    closure_strict / closure_strict2 root rows `ROOT<TAB>closure N functions...`, `ROOT<TAB>ABSENT...`,
            `ROOT<TAB>AMBIGUOUS...`: ROOT;
  closure-member  member lines `   NAME @0xADDR: ...`: NAME (0xADDR is the X address of the member);
  closure-accept  `   ACCEPT NAME @0xA/0xB: ...`: NAME (0xA in X, 0xB in Y);
  jtcheck   jtcheck per-function lines `NAME<TAB>X 0xA Y 0xB size N<TAB>...`, `NAME<TAB>SKIP ...`,
            `NAME<TAB>REAL difference ...`, `NAME<TAB>UNREADABLE ...`: NAME;
  jtcheck-accept  `   ACCEPT NAME KIND +0xOFF [...]`: NAME;
  bsurvey   bsurvey / bsurvey_all rows `NAME<TAB>0xXADDR<TAB>SIZE<TAB>DONOR<TAB>0xDONORADDR<TAB>...` (the X copy is
            given by address, the donor copy was looked up by name with Img.fsym): NAME;
  other     any other line: its first tab / space separated token.
  A token NAME{FILE} or 0xADDR is a resolved item, not a by-name lookup: it is reported only if strictcmp3.fcopies says
  it still names several copies. A token that names no sized FUNC symbol in X or Y is ignored.

Output (stdout, TSV): two '#' lines (the images), then one row per (file, line, name, image) hit:
  AMBIG  file  line  name  image (X|Y)  number of copies
         copies `addr/size/STT_FILE/qname ; ...` (STT_FILE '-' for a symbol with no file, qname '(no unique name)' when
         strictcmp3.qname gives none)
         the copy a lowest-address lookup (Img.fsym) takes
         how the line was read: its format, and which copy each hex address on the line is when it is the address of a
         copy in this image (for closure-member lines: the member's @0xADDR), and whether the line itself says
         AMBIGUOUS (the tool refused the name: jtcheck SKIP AMBIGUOUS, closure AMBIGUOUS root)
then one TOTAL row: files read, by-name compares seen (distinct names that are sized FUNC names in X or Y), ambiguous
hits, distinct ambiguous names (then: lines with a function token, distinct resolved items, files skipped).
TOTAL with 0 ambiguous hits means no by-name compare in those files hit a duplicated name, in X or in Y.
Exit status 0; 2 on a usage error, an image without .symtab, or an OUTFILE path that does not exist."""
import sys, os, re, importlib.util
from elftools.elf.elffile import ELFFile
HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location('strictcmp3', os.path.join(HERE, 'strictcmp3.py'))
s3 = importlib.util.module_from_spec(spec); spec.loader.exec_module(s3)

MAX_BYTES = 50 * 1024 * 1024
PAIR = re.compile(r'[^\s:]+:[^\s:]+$')
HEX = re.compile(r'0x[0-9a-fA-F]+$')
LINE_HEX = re.compile(r'(?<![0-9A-Za-z_])0x[0-9a-fA-F]+')
CL_ROOT = re.compile(r'closure \d+ functions|ABSENT|AMBIGUOUS')
CL_MEMBER = re.compile(r'   (\S+) @(0x[0-9a-f]+): ')
CL_ACCEPT = re.compile(r'   ACCEPT (\S+) @(0x[0-9a-f]+)/(0x[0-9a-f]+): ')
JT_FN = re.compile(r'X 0x[0-9a-f]+ Y 0x[0-9a-f]+ size \d+|SKIP|REAL difference|UNREADABLE')
JT_ACCEPT = re.compile(r'   ACCEPT (\S+) \S+ \+')


def load(tag, path):
    with open(path, 'rb') as fh:
        if ELFFile(fh).get_section_by_name('.symtab') is None:
            sys.stderr.write('ambiscan.py: %s image %s has no .symtab (stripped): nothing to look names up in\n' % (tag, path))
            raise SystemExit(2)
    I = s3.Img(path)
    I.tag = tag
    I.fnames = {nm for v, z, nm, t in I.syms if t == 'STT_FUNC' and z > 0}
    I.faddrs = {v for v, z, nm, t in I.syms if t == 'STT_FUNC' and z > 0}
    I.cache = {}
    return I


def token(line):
    """(token, format) of the function a line compared, or (None, None)"""
    if not line.strip() or line.startswith('#'):
        return None, None
    f = line.split('\t')
    if len(f) > 1:
        if f[0] == 'fn' and f[1] == 'pair':
            return None, None
        if f[0] == 'CSTR' and len(f) > 2:
            return f[1], 'cstr'
        if f[0] and not f[0][0].isspace():
            if PAIR.match(f[1]): return f[0], 'cmp'
            if CL_ROOT.match(f[1]): return f[0], 'closure-root'
            if JT_FN.match(f[1]): return f[0], 'jtcheck'
            if len(f) > 5 and HEX.match(f[1]) and f[2].isdigit(): return f[0], 'bsurvey'
    for rx, fmt in ((CL_ACCEPT, 'closure-accept'), (JT_ACCEPT, 'jtcheck-accept'), (CL_MEMBER, 'closure-member')):
        m = rx.match(line)
        if m: return m.group(1), fmt
    t = line.split()
    return t[0], 'other'


def kind(tok):
    if HEX.match(tok): return 'addr'
    if '{' in tok and tok.endswith('}'): return 'qualified'
    return 'name'


def isfunc(I, tok, k):
    if k == 'addr': return int(tok, 16) in I.faddrs
    return (tok.split('{', 1)[0] if k == 'qualified' else tok) in I.fnames


def copies(I, tok, k):
    if tok not in I.cache:
        I.cache[tok] = s3.fcopies(I, tok) if isfunc(I, tok, k) else []
    return I.cache[tok]


def fil(I, v, nm):
    return s3._meta(I)['fil'].get((v, nm)) or '-'


def describe(I, c):
    return ' ; '.join('%#x/%d/%s/%s' % (v, z, fil(I, v, nm), s3.qname(I, nm, v) or '(no unique name)') for v, z, nm in c)


def which(I, c, v, z=None):
    """copy number k of n and its STT_FILE for address v (and size z) among copies c"""
    ks = [i for i, e in enumerate(c) if e[0] == v and (z is None or e[1] == z)]
    if not ks: return 'no copy'
    return ', '.join('copy %d/%d (%s)' % (i + 1, len(c), fil(I, c[i][0], c[i][2])) for i in ks)


def fsym_text(I, tok, k, c):
    if k == 'addr':
        return 'n/a: 0xADDR item (no name lookup)'
    nm = tok.split('{', 1)[0]
    s = I.fsym(nm)
    allc = c if k == 'name' else copies(I, nm, 'name')
    t = '%#x/%d = %s' % (s[0], s[1], which(I, allc, s[0], s[1])) if s else 'none'
    return t if k == 'name' else 'NAME{FILE} item is resolved by qname, not fsym; Img.fsym(%s) = %s' % (nm, t)


def line_text(I, line, fmt, c):
    at = [int(x, 16) for x in LINE_HEX.findall(line)]
    own = {e[0] for e in c}
    seen = []
    for a in at:
        if a in own and a not in seen: seen.append(a)
    t = fmt + '; ' + ('line address(es) that are copies here: ' + ', '.join('%#x = %s' % (a, which(I, c, a)) for a in seen)
                      if seen else 'no hex address on the line is a copy here')
    if fmt == 'closure-member':
        a = int(CL_MEMBER.match(line).group(2), 16)
        t += '; member @%#x = %s' % (a, which(I, c, a))
    if 'AMBIGUOUS' in line:
        t += '; the line itself says AMBIGUOUS (the tool refused the name)'
    return t


def files(args):
    out, missing = [], []
    for a in args:
        if os.path.isdir(a):
            for d, ds, fs in os.walk(a):
                ds.sort()
                out += [os.path.join(d, f) for f in sorted(fs) if os.path.isfile(os.path.join(d, f))]
        elif os.path.isfile(a):
            out.append(a)
        else:
            missing.append(a)
    return out, missing


def main(argv):
    if len(argv) < 4:
        sys.stderr.write(__doc__ + '\n'); return 2
    paths, missing = files(argv[3:])
    for m in missing: sys.stderr.write('ambiscan.py: no such file or directory: %s\n' % m)
    if missing: return 2
    imgs = [load('X', argv[1]), load('Y', argv[2])]
    for I, p in zip(imgs, argv[1:3]):
        print('# %s = %s sha256 %s' % (I.tag, p, s3.sha(p)[:12]))
    print('# AMBIG\tfile\tline\tname\timage\tcopies\taddr/size/STT_FILE/qname ; ...\tImg.fsym takes\thow the line was read')
    nread = nskip = nlines = hits = 0
    byname, resolved, ambnames = set(), set(), set()
    for p in paths:
        try:
            z = os.path.getsize(p)
            if z > MAX_BYTES:
                sys.stderr.write('SKIP\t%s\tlarger than 50 MB (%d bytes)\n' % (p, z)); nskip += 1; continue
            with open(p, 'rb') as fh:
                data = fh.read()
        except OSError as e:
            sys.stderr.write('SKIP\t%s\tunreadable: %s\n' % (p, e)); nskip += 1; continue
        if b'\0' in data[:4096]:
            sys.stderr.write('SKIP\t%s\tbinary (NUL in the first 4 KiB)\n' % p); nskip += 1; continue
        nread += 1
        for ln, line in enumerate(data.decode('utf-8', 'replace').split('\n'), 1):
            tok, fmt = token(line.rstrip('\r'))
            if tok is None: continue
            k = kind(tok)
            if not any(isfunc(I, tok, k) for I in imgs): continue
            nlines += 1
            (byname if k == 'name' else resolved).add(tok)
            for I in imgs:
                c = copies(I, tok, k)
                if len({(v, sz) for v, sz, nm in c}) < 2: continue
                hits += 1; ambnames.add(tok)
                print('AMBIG\t%s\t%d\t%s\t%s\t%d\t%s\t%s\t%s' % (p, ln, tok, I.tag, len(c), describe(I, c),
                                                         fsym_text(I, tok, k, c), line_text(I, line, fmt, c)))
    print('TOTAL\tfiles read %d\tby-name compares seen (distinct names) %d\tambiguous hits %d\tdistinct ambiguous names %d'
          '\tlines with a function token %d\tresolved items NAME{FILE}/0xADDR (distinct) %d\tfiles skipped %d'
          % (nread, len(byname), hits, len(ambnames), nlines, len(resolved), nskip))
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
