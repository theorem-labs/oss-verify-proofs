#!/usr/bin/env python3
"""resolve.py KIT HUB COMMIT NUMDIFF.TSV NUMERALS.TSV OUT.TSV -- read-only.

Every numeral the 47 shipped libreac/fuzz_decode headers at COMMIT say was moved ('its N image addresses moved by
code-verified function pairs (N port_addr_check MAPS predictions, each code one re-derived by funcpair.py)'), with
its file:line, resolved in decode A's OWN .symtab (the unstripped twin of pin 5973b76807d8) and in the donor's, and
checked:

  CODE pc   the donor value must resolve in the donor to the same symbol + offset as the placed value resolves to in
            decode A, and the instruction word at the two addresses must be equal or differ pc-relatively (bytecmp
            1480ca2faea0's rule, the word the proof's own site reads).
  DATA      the same symbol + offset on both sides, with the offset inside the object.
  EXTENT /  no symbol: the value is checked against decode A's own PT_LOAD boundaries.
  NON-ADDR

Each numeral is reported as
  (a) used by a proof term and RIGHT, (b) used by a proof term and WRONG, (c) not read by any term (comment only).
A name that several STT_FUNC symbols of decode A carry is flagged, with every copy, and the copy the numeral lands in.
"""
import bisect, collections, importlib.util, os, subprocess, sys
from elftools.elf.elffile import ELFFile

KIT, HUB, COMMIT, NUMDIFF, NUM, OUT = sys.argv[1:7]
sys.dont_write_bytecode = True
sp = importlib.util.spec_from_file_location('s2', os.path.join(KIT, 'strictcmp2.py'))
S = importlib.util.module_from_spec(sp); sp.loader.exec_module(S)
C = 'DONOR_TWIN'
A = 'DECODE_A_TWIN'
I = {'C': S.Img(C), 'A': S.Img(A)}


def git(*a):
    return subprocess.run(['git', '-C', HUB] + list(a), capture_output=True, text=True, check=True).stdout


hdr_files = {l.split(':', 1)[1].rsplit('/', 1)[1][:-2]: l.split(':', 1)[1] for l in
             git('grep', '-l', 're-derived by funcpair.py', COMMIT, '--', 'proofs/libreac/fuzz_decode').splitlines()}


def symtab(path):
    out = collections.defaultdict(list)
    for s in ELFFile(open(path, 'rb')).get_section_by_name('.symtab').iter_symbols():
        if s['st_info']['type'] in ('STT_FUNC', 'STT_OBJECT') and s.name:
            out[s.name].append((s['st_value'], s['st_size'], s['st_info']['type']))
    return out


SY = {'C': symtab(C), 'A': symtab(A)}
# sorted (addr, size, name, type) of FUNC/OBJECT, for containment lookup
TAB = {k: sorted((v, z, n, t) for n, l in SY[k].items() for (v, z, t) in l) for k in 'CA'}
ST = {k: [r[0] for r in TAB[k]] for k in 'CA'}
SHADOW_OFF, IMG_HI = 0x7fff8000, 0x5f6000          # decode A's own, lib/A/AB12.v TFIB record at 88154566652a
SHADOW_LO, SHADOW_HI = 0x7fff8000, 0x80100000
SEG = {k: [(g['p_vaddr'], g['p_memsz'], g['p_filesz'])
           for g in ELFFile(open(p, 'rb')).iter_segments() if g['p_type'] == 'PT_LOAD']
       for k, p in (('C', C), ('A', A))}


def res(k, a):
    """the smallest FUNC / OBJECT symbol containing a -> (name, offset, size, type, copies of the name); else None"""
    i = bisect.bisect_right(ST[k], a) - 1
    best = None
    while i >= 0 and a - TAB[k][i][0] < 0x200000:
        v, z, n, t = TAB[k][i]
        if v <= a < v + z and (best is None or z < best[2]): best = (n, a - v, z, t, len(SY[k][n]))
        i -= 1
    return best


def word(k, a):
    b = S.frd(I[k], a, 4)
    return int.from_bytes(b, 'little') if b else None


def pcrel_ok(x, y):
    """bytecmp 1480ca2faea0's rule for ONE word pair, without its flow context: equal, or an auipc / jal whose rd is
    equal, or an I/S-type word whose non-immediate fields are equal (the shape the relocation's pc moves produce)"""
    if x == y: return 'identical'
    if x is None or y is None: return 'unreadable'
    if (x & 0x7f) != (y & 0x7f): return 'DIFFERENT'
    op = x & 0x7f
    if op in (0x17, 0x6f) and ((x >> 7) & 31) == ((y >> 7) & 31): return 'pc-relative'
    mask = 0x01fff07f if op in (0x23, 0x27) else 0x000fffff
    if op in (0x13, 0x03, 0x23, 0x67, 0x07, 0x27) and (x & mask) == (y & mask): return 'pc-relative(lo12)'
    return 'DIFFERENT'


def seg_match(k, v):
    for i, (va, mz, fz) in enumerate(SEG[k]):
        if v == va: return 'PT_LOAD[%d] start' % i
        if v == va + mz: return 'PT_LOAD[%d] end (vaddr+memsz)' % i
        if v == va + fz: return 'PT_LOAD[%d] file end' % i
    top = max(va + mz for va, mz, _ in SEG[k])
    if v == top: return 'image top'
    return None


mapped = set()
for l in open(NUM).read().splitlines()[1:]:
    if l.strip():
        c = l.split('\t'); mapped.add((c[0], c[1], c[2]))

rows, wrong, dupflag = [], [], []
cat = collections.Counter(); kinds = collections.Counter()
for l in open(NUMDIFF).read().splitlines()[1:]:
    if not l.strip(): continue
    c = (l.split('\t') + [''] * 7)[:7]
    f, line, sv, nv, sres = c[0], c[1], c[2], c[3], c[4]
    if f not in hdr_files: continue
    comment = 'comment' in sres
    sval = int(sv, 0) if sv.startswith('0x') else int(sv)
    nval = int(nv, 0) if nv.startswith('0x') else int(nv)
    rc, ra = res('C', sval), res('A', nval)
    kind = ('code' if '[code]' in sres else 'data' if '[data]' in sres else
            'extent' if 'EXTENT' in sres else 'comment' if comment else 'non-address')
    kinds[kind] += 1
    note, verdict = [], 'RIGHT'
    if ra and rc:
        if (rc[0], rc[1]) != (ra[0], ra[1]):
            verdict = 'WRONG'; note.append('donor %s+%#x vs decode %s+%#x' % (rc[0], rc[1], ra[0], ra[1]))
        if ra[4] > 1:
            note.append('name carried by %d symbols of decode A: %s' % (
                ra[4], ' '.join('%#x/%d' % (v, z) for v, z, _t in SY['A'][ra[0]])))
            dupflag.append((f, line, nv, ra[0], ra[4]))
    elif ra or rc:
        verdict = 'WRONG' if kind in ('code', 'data') else 'RIGHT'
        note.append('resolved on one side only: donor %s, decode %s' % (rc, ra))
    elif SHADOW_LO <= nval < SHADOW_HI or 'shadow(' in sres:
        # an ASan shadow address: shadow(a) = a / 8 + shadow_off, shadow_off = 0x7fff8000 and the image bounds
        # img_lo 0x10000 / img_hi 0x5f6000 are decode A's own (lib/A/AB12.v's TFIB record at this commit)
        pre = (nval - SHADOW_OFF) * 8
        m = seg_match('A', pre) or ('image top 0x5f6000' if pre == IMG_HI else None)
        r = res('A', pre)
        note.append('shadow address: shadow^-1 = %#x, %s' % (pre, m or (r and '%s+%#x' % (r[0], r[1])) or
                                                             'no boundary and no symbol'))
        if not m and not r: verdict = 'WRONG'
    else:
        m = seg_match('A', nval)
        note.append('no symbol; decode A %s' % (m or 'no PT_LOAD boundary'))
        if kind in ('code', 'data'): verdict = 'WRONG'
    w = ''
    if kind == 'code' and not comment:
        w = pcrel_ok(word('C', sval), word('A', nval))
        if w == 'DIFFERENT': verdict = 'WRONG'; note.append('instruction word differs really')
    k_cat = 'c' if comment else ('a' if verdict == 'RIGHT' else 'b')
    cat[k_cat] += 1
    if k_cat == 'b': wrong.append((f, line, sv, nv, sres[:60], '; '.join(note)))
    rows.append([f, line, sv, nv, kind, 'comment' if comment else 'term',
                 '%s+%#x' % (rc[0], rc[1]) if rc else '-', '%s+%#x' % (ra[0], ra[1]) if ra else '-',
                 str(ra[4]) if ra else '-', w, 'in this re-run' if (f, sv, nv) in mapped else 'not a funcpair numeral',
                 k_cat, '; '.join(note)])

hdrs = ['file', 'src_line', 'donor_value', 'decode_value', 'kind', 'read_by', 'donor_res', 'decode_res',
        'copies_of_name_in_A', 'word_class', 'in_rerun', 'category', 'notes']
open(OUT, 'w').write('\n'.join('\t'.join(r) for r in [hdrs] + rows) + '\n')
print('# kit', KIT, 'strictcmp2', S.sha(os.path.join(KIT, 'strictcmp2.py'))[:12])
print('# C', C, S.sha(C)[:12]); print('# A', A, S.sha(A)[:12])
print('# headers', len(hdr_files), 'at', COMMIT)
print('numerals listed by those headers (numdiff rows of those files):', len(rows), dict(kinds))
print('(a) used by a proof term and RIGHT: %d' % cat['a'])
print('(b) used by a proof term and WRONG: %d' % cat['b'])
print('(c) not read by any term (comment only): %d' % cat['c'])
print('numerals in a function whose NAME has several copies in decode A:', len(dupflag), dupflag[:20])
print()
for r in wrong:
    print('WRONG', r)
