#!/usr/bin/env python3
"""size_moves_classify.py SCAN.tsv FINAL_LIB WIRE_TWIN OUT.tsv RUN=GATE_RAW.tsv=STAGE_OUT_DIR=DONOR_TWIN ...

Classify every move of size_moves.py (a numeral port_core CHANGED whose donor value is a power of two or a multiple
of 0x1000) by what the value IS in the donor's image and in wire's image.

1. Rows. SCAN.tsv is size_moves.py's output (stage map pairing). The run's own port_addr_check rows (GATE_RAW.tsv,
   columns verdict ... src_value dst_value) are read too: a gate row with a changed power-of-two / page-aligned
   donor value that no scan row matches (same file and values, dst_line + 0..3 = the scan's stage-out line) is added,
   with its text read from STAGE_OUT_DIR at the line that carries the wire value.
2. Roles. Each role is a quantity of an image, computed here from the ELF file (program headers, symtab):
   seg<i>.lo / seg<i>.hi = the page-rounded start / end of PT_LOAD i, seg<i>.len = hi - lo, image.top = seg3.hi,
   image.span = image.top - 0x10000 (the image's lowest mapped address), and the named-symbol roles of SYMROLES
   (a symbol's start / end, the 4 KiB page of its start and the page after it, the page above start + offset),
   each chosen from the use of the value in the proof text (see the comments there). A row's roles are every
   role whose value in the DONOR image equals the donor value; for each, wire's own measured value is reported.
   Relocated-symbol reading: the donor value read as an ADDRESS of the donor image (the innermost sized symbol
   that holds it, else the symbol that ends at it, else the nearest symbol below it; mapping symbols `$x` / `$d`
   excluded) plus its offset, carried to the same-named symbol of wire's image (start + offset, or end).
   verdict (rule of 05:48Z): RIGHT when the new value equals wire's own measured value for one of the row's
   roles; WRONG when it equals the relocated-symbol reading and NOT wire's measured value for the role;
   UNDECIDED otherwise.
3. Use. Where the relocated line is in FINAL_LIB (exact line; else the closest line of the same file that still
   carries the wire value or, for image.top, the notation YImgTop.IMG_TOP = its value; else `not in final tree`),
   the enclosing sentence (on a line that holds several sentences, the last one that starts before the value),
   whether the value is in its statement / definition body or its proof, and its readers: uses of its name after
   its own sentence in its file, plus qualified uses <Module>.<name> and unqualified uses in the files that
   Require its module (a name-level count: a same-named local in such a file is counted too).
"""
import bisect, difflib, os, re, sys
sys.path.insert(0, os.environ.get('PYLIB', ''))
from elftools.elf.elffile import ELFFile

NUM = re.compile(r"(?<![\w.'])(0x[0-9a-fA-F]+|\d+)(?![\w'])")
DEF = re.compile(r"^\s*(?:Local\s+|#\[[^\]]*\]\s*)?(Definition|Lemma|Theorem|Fact|Corollary|Fixpoint|Let|Example|"
                 r"Remark|Notation|Record|Inductive|Hypothesis|Hypotheses|Variable|Variables)\s+([A-Za-z_][\w']*)")
DEF_IN = re.compile(r"\b(Definition|Lemma|Theorem|Fact|Corollary|Fixpoint|Let|Example|Remark|Notation)\s+([A-Za-z_][\w']*)")
REQ = re.compile(r"\bRequire\b[^\n]*?\.(?=\s|$)")
TOK = re.compile(r"[A-Za-z_][\w']*")
SYMROLES = [  # (role, symbol, kind, offset)
    ('_Exit.end', '_Exit', 'end', 0),
    ('__stdout_FILE.end', '__stdout_FILE', 'end', 0),
    ('RunMallocHooks.start', '_ZN11__sanitizer14RunMallocHooksEPvm', 'start', 0),
    # the window end of b2_mod_cells_kept: the page above the last cell its mod_cells / mnr_cells read, the byte at
    # common_flags_dont_use + 0x104 (cells: 2 GOT slots, PageSizeCached, common_flags_dont_use + 0x90 / + 0x104)
    ('page_up(common_flags_dont_use+0x105)', '_ZN11__sanitizer21common_flags_dont_useE', 'pageup', 0x105),
    ('page(stackStore)', '_ZN11__sanitizerL10stackStoreE', 'page', 0),
    ('page(stackStore)+0x1000', '_ZN11__sanitizerL10stackStoreE', 'page', 0x1000),
]


def val(s):
    return int(s, 16) if s.lower().startswith('0x') else int(s)


def sized(v):
    return v > 0 and (v & (v - 1) == 0 or v % 0x1000 == 0)


def roles(path):
    e = ELFFile(open(path, 'rb'))
    r = {}
    loads = [s for s in e.iter_segments() if s['p_type'] == 'PT_LOAD']
    for i, s in enumerate(loads):
        lo = s['p_vaddr'] & ~0xfff
        hi = (s['p_vaddr'] + s['p_memsz'] + 0xfff) & ~0xfff
        r['seg%d.lo' % i] = (lo, 'PT_LOAD %d vaddr 0x%x page-down' % (i, s['p_vaddr']))
        r['seg%d.hi' % i] = (hi, 'PT_LOAD %d end 0x%x page-up' % (i, s['p_vaddr'] + s['p_memsz']))
        r['seg%d.len' % i] = (hi - lo, '0x%x - 0x%x' % (hi, lo))
    top = r['seg%d.hi' % (len(loads) - 1)][0]
    r['image.top'] = (top, r['seg%d.hi' % (len(loads) - 1)][1])
    r['image.span'] = (top - 0x10000, '0x%x - 0x10000' % top)
    syms = {s.name: s for s in e.get_section_by_name('.symtab').iter_symbols() if s['st_value']}
    for role, name, kind, off in SYMROLES:
        s = syms.get(name)
        if s is None:
            continue
        a, z = s['st_value'], s['st_size']
        v = {'start': a + off, 'end': a + z + off, 'page': (a & ~0xfff) + off,
             'pageup': (a + off + 0xfff) & ~0xfff}[kind]
        r[role] = (v, '%s 0x%x size 0x%x' % (name, a, z))
    return r


def is_length(role):
    return role.endswith('.len') or role == 'image.span'


class Syms:
    def __init__(self, path):
        e = ELFFile(open(path, 'rb'))
        self.secs = [(s['sh_addr'], s['sh_addr'] + s['sh_size'], s.name) for s in e.iter_sections() if s['sh_addr']]
        self.syms = sorted((s['st_value'], s['st_size'], s.name) for s in e.get_section_by_name('.symtab').iter_symbols()
                           if s['st_value'] and s.name and not s.name.startswith('$')
                           and s['st_info']['type'] in ('STT_OBJECT', 'STT_FUNC', 'STT_NOTYPE'))
        self.keys = [x[0] for x in self.syms]
        self.byname = {}
        for x in self.syms:
            self.byname.setdefault(x[2], []).append(x)

    def sec(self, v):
        return next((n for a, b, n in self.secs if a <= v < b), 'no section')

    def read(self, v):
        """(name, kind, offset): kind '+' = start + offset, 'end' = end of the symbol."""
        i = bisect.bisect_right(self.keys, v)
        inside = [x for x in self.syms[max(0, i - 400):i] if x[1] and x[0] <= v < x[0] + x[1]]
        if inside:
            s = max(inside)
            return s[2], '+', v - s[0]
        ends = [x for x in self.syms[max(0, i - 400):i] if x[1] and x[0] + x[1] == v]
        if ends:
            s = max(ends)
            return s[2], 'end', 0
        if i:
            s = self.syms[i - 1]
            return s[2], '+', v - s[0]
        return None, '-', 0


def sym_reading(v, dsym, wsym):
    name, kind, off = dsym.read(v)
    if name is None:
        return None, 'no donor symbol at or below 0x%x' % v
    w = wsym.byname.get(name)
    short = name if len(name) <= 48 else name[:45] + '...'
    what = ('end of %s' % short) if kind == 'end' else ('%s+0x%x' % (short, off))
    if not w:
        return None, '%s [donor %s] -> not in wire' % (what, dsym.sec(v))
    s = w[0]
    nv = s[0] + s[1] if kind == 'end' else s[0] + off
    return nv, '%s [donor %s] -> wire 0x%x%s' % (what, dsym.sec(v), nv, ' (%d same-named)' % len(w) if len(w) > 1 else '')


def main():
    scan_p, final, wire_twin, out = sys.argv[1:5]
    runs = {}
    for spec in sys.argv[5:]:
        name, gate, so, twin = spec.split('=')
        runs[name] = (gate, so, twin)
    wire = roles(wire_twin)
    donor = {n: roles(t) for n, (_, _, t) in runs.items()}
    wsym = Syms(wire_twin)
    dsyms = {n: Syms(t) for n, (_, _, t) in runs.items()}
    symroles = {x[0] for x in SYMROLES}
    hdr = open(scan_p).readline().rstrip('\n').split('\t')
    rows = [dict(zip(hdr, l.rstrip('\n').split('\t'))) for l in open(scan_p).readlines()[1:]]
    for r in rows:
        r['source'] = 'stage map'
    # 1. gate rows the scan did not pair
    for name, (gate, so, _) in runs.items():
        have = {}
        for r in rows:
            if r['run'] == name:
                have.setdefault((r['file'], val(r['donor']), val(r['wire'])), []).append(int(r['stage-out line']))
        G = open(gate).read().splitlines()
        gh = G[0].split('\t')
        for l in G[1:]:
            g = dict(zip(gh, l.split('\t')))
            try:
                a, b = val(g['src_value']), val(g['dst_value'])
            except (KeyError, ValueError):
                continue
            if a == b or not sized(a):
                continue
            k = (g['dst_file'], a, b)
            d = int(g['dst_line'])
            hit = next((x for x in have.get(k, []) if 0 <= x - d <= 3), None)
            if hit is not None:
                have[k].remove(hit)
                continue
            lines = open(os.path.join(so, g['dst_file']), errors='replace').read().split('\n')
            ln = next((d + j for j in range(4) if d + j <= len(lines) and
                       any(val(x) == b for x in NUM.findall(lines[d + j - 1]))), d)
            rows.append({'run': name, 'file': g['dst_file'], 'stage-out line': str(ln), 'donor': g['src_value'],
                         'wire': g['dst_value'], 'line text': lines[ln - 1].strip()[:220], 'source': 'gate only'})
    for r in rows:
        r['gate'] = '-'
    for name, (gate, _, _) in runs.items():
        G = open(gate).read().splitlines()
        gh = G[0].split('\t')
        idx = {}
        for l in G[1:]:
            g = dict(zip(gh, l.split('\t')))
            try:
                idx.setdefault((g['dst_file'], val(g['src_value']), val(g['dst_value'])), []).append(
                    (int(g['dst_line']), g['verdict'], g.get('src_res', '')[:60]))
            except (KeyError, ValueError):
                continue
        for r in rows:
            if r['run'] != name:
                continue
            c = idx.get((r['file'], val(r['donor']), val(r['wire'])), [])
            ln = int(r['stage-out line'])
            m = next((x for x in c if 0 <= ln - x[0] <= 3), None)
            if m:
                r['gate'] = '%s (%s)' % (m[1], m[2])
    # 3. final tree
    ftxt, fjoin, freq = {}, {}, {}
    for dp, _, fn in os.walk(final):
        for f in fn:
            if f.endswith('.v'):
                p = os.path.join(dp, f)
                t = open(p, errors='replace').read()
                rel = os.path.relpath(p, final)
                ftxt[rel], fjoin[rel] = t.split('\n'), t
                freq[rel] = set(TOK.findall(' '.join(m.group(0) for m in REQ.finditer(t))))
    rcache = {}

    def where(r, k):
        """(final line index or None, how, value the final tree holds at the moved numeral's position or None).
        k: which copy of the wire value on the stage-out line this row is (0-based)."""
        rel = r['file']
        so = open(os.path.join(runs[r['run']][1], rel), errors='replace').read().split('\n')[int(r['stage-out line']) - 1]
        L = ftxt.get(rel, [])
        wv = val(r['wire'])
        ex = [i for i, l in enumerate(L) if l.strip() == so.strip()]
        if ex:
            return ex[0], 'relocated line, verbatim', wv
        best, bi = 0.0, None
        for i, l in enumerate(L):
            sm = difflib.SequenceMatcher(None, so.strip(), l.strip(), autojunk=False)
            if sm.real_quick_ratio() < 0.6 or sm.quick_ratio() < 0.6:
                continue
            q = sm.ratio()
            if q > best:
                best, bi = q, i
        if bi is None or best < 0.6:
            return None, 'not in final tree', None
        ns, nf = NUM.findall(so), NUM.findall(L[bi])
        pos = [j for j, x in enumerate(ns) if val(x) == wv]
        fv = None
        if len(ns) == len(nf) and k < len(pos):
            fv = val(nf[pos[k]])
        elif wv in {val(x) for x in nf}:
            fv = wv
        elif 'YImgTop.IMG_TOP' in L[bi] and wv == wire['image.top'][0]:
            fv = wv
        how = 'same sentence edited later (ratio %.2f); the final tree holds %s there' % (
            best, '0x%x' % fv if fv is not None else 'no numeral of the same position')
        if fv is not None and fv == wv and 'YImgTop.IMG_TOP' in L[bi] and wv not in {val(x) for x in nf}:
            how += ' (by the notation YImgTop.IMG_TOP)'
        return bi, how, fv

    def readers(rel, j, nm):
        if (rel, j, nm) in rcache:
            return rcache[(rel, j, nm)]
        mod = os.path.basename(rel)[:-2]
        w = re.compile(r"(?<![\w'.])%s(?![\w'])" % re.escape(nm))
        q = re.compile(r"\b%s\.%s(?![\w'])" % (re.escape(mod), re.escape(nm)))
        n = sum(len(w.findall(l)) for l in ftxt[rel][j + 1:])
        for f, t in fjoin.items():
            if f == rel or nm not in t:
                continue
            n += len(q.findall(t))
            if mod in freq[f]:
                n += len(w.findall(t))
        rcache[(rel, j, nm)] = n
        return n

    def sentence(rel, i, wv):
        L = ftxt[rel]
        here = next((m.start() for m in NUM.finditer(L[i]) if val(m.group(1)) == wv), None)
        if here is not None:
            ins = [m for m in DEF_IN.finditer(L[i]) if m.start() < here]
            if ins:
                return ins[-1].group(1), ins[-1].group(2), 'statement / body', readers(rel, i, ins[-1].group(2))
        for j in range(i, -1, -1):
            m = DEF.match(L[j])
            if m:
                kind, nm = m.group(1), m.group(2)
                pos = 'statement / body'
                for k in range(j, i + 1):
                    if re.match(r'\s*Proof\b', L[k]) or (re.search(r'\bProof\.\s*$', L[k]) and k < i):
                        pos = 'proof'
                        break
                return kind, nm, pos, readers(rel, j, nm)
        return '-', '-', '-', 0

    out_rows = []
    seen = {}
    for r in rows:
        dv, wv = val(r['donor']), val(r['wire'])
        key = (r['run'], r['file'], r['stage-out line'], wv)
        k = seen.get(key, 0)
        seen[key] = k + 1
        i, how, fv = where(r, k)
        # the value judged: what the FINAL tree holds at the moved position; the run's own value where the final tree
        # does not carry the sentence
        nv = fv if i is not None and fv is not None else wv
        D = donor[r['run']]
        drole = [k_ for k_ in D if D[k_][0] == dv and k_ in wire]   # every role the donor value has in its own image
        match = [k_ for k_ in drole if wire[k_][0] == nv]
        sv, stxt = sym_reading(dv, dsyms[r['run']], wsym)
        measured = '; '.join('%s = 0x%x' % (k_, wire[k_][0]) for k_ in drole) or '-'
        if match and sv == nv:
            equals = 'both (measured = relocated symbol)'
        elif match:
            equals = 'measured'
        elif sv == nv:
            equals = 'relocated symbol'
        else:
            equals = 'neither'
        if match and all(k_ in symroles for k_ in match) and not any('page' in k_ for k_ in match):
            verdict = 'RIGHT (address: wire symbol %s)' % ', '.join(match)
        elif match:
            verdict = 'RIGHT (= wire measured %s)' % ', '.join(match)
        elif sv == nv:
            verdict = 'WRONG (= relocated symbol address, not wire measured %s)' % (', '.join(drole) or 'role')
        else:
            verdict = 'UNDECIDED'
        if i is None:
            fl, kind, nm, pos, rd = '-', '-', '-', '-', '-'
        else:
            kind, nm, pos, rd = sentence(r['file'], i, nv)
            fl = '%s:%d' % (r['file'], i + 1)
        rk = lambda k_: ('length' if is_length(k_) else 'page bound' if 'page' in k_ else
                         'symbol address' if k_ in symroles else 'image boundary')
        out_rows.append([r['run'], '%s:%s' % (r['file'], r['stage-out line']), r['donor'], r['wire'],
                         ', '.join(drole) or '-', ', '.join(sorted({rk(k_) for k_ in drole})) or '-',
                         '; '.join('%s = %s' % (k_, D[k_][1]) for k_ in drole) or '-',
                         measured,
                         '; '.join('%s = %s' % (k_, wire[k_][1]) for k_ in drole) or '-',
                         stxt, equals, verdict, fl, how,
                         ('0x%x' % nv) + ('' if i is not None else ' (run value; not in final tree)'),
                         '%s %s' % (kind, nm), pos, str(rd), r['gate'], r['source'], r['line text'][:200]])
    with open(out, 'w') as o:
        o.write('\t'.join(['run', 'stage-out file:line', 'donor value', 'run value (stage-out)', 'role(s)', 'role kind',
                           'donor image (role)', 'wire measured value (role)', 'wire image (role)',
                           'relocated-symbol reading (donor value as an address)', 'judged value equals', 'verdict',
                           'final-tree file:line', 'final-tree match', 'judged value', 'enclosing sentence',
                           'position', 'readers of the sentence name', 'port_addr_check row', 'row source',
                           'stage-out line text']) + '\n')
        for x in out_rows:
            o.write('\t'.join(x) + '\n')
    from collections import Counter
    print('size_moves_classify: %d move(s); verdicts %s; judged value equals %s; role kinds %s; in final tree %d; '
          'final value differs from the run value %d' % (
              len(out_rows), dict(Counter(x[11].split(' (')[0] for x in out_rows)), dict(Counter(x[10] for x in out_rows)),
              dict(Counter(x[5] for x in out_rows)), sum(x[12] != '-' for x in out_rows),
              sum(x[12] != '-' and val(x[14].split(' ')[0]) != val(x[3]) for x in out_rows)))


if __name__ == '__main__':
    main()
