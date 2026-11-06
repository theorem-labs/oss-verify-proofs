#!/usr/bin/env python3
"""feq_check.py -- re-check, another way, the rows of port_addr_check 3d2eee813cce whose OK verdict belongs to a known
FALSE-EQUAL class: SAME-CONTENT, INSN-SAME and ROUND-CONSTANT-SAME.

  SAME-CONTENT         name the object that holds the donor value in the donor image and the ported value in ours
                       (twin symbol table, and the NUL-terminated string start); OK when the same symbol + offset or
                       the same whole string + offset.
  INSN-SAME            decode every word (RV64); find the pc each file gives the word at (a fetch fact on the line,
                       the fetch of the word definition, a code_at table, a clookup / table lemma, the sibling fetch
                       of a decode lemma); read our image's 4 bytes at our pc; name both pcs; for a jal / branch the
                       target, for an auipc the auipc + next-word target, by symbol + offset in each image.
  ROUND-CONSTANT-SAME  the role of the value is read from the line (roles.tsv, written by hand from the text), and an
                       image quantity / address is measured in our image (feq_roles.py).

Usage: feq_check.py --run RA|RB|RU --gate-tsv full.tsv --out rows.RA.tsv  (see run.sh)
"""
import argparse, collections, json, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import feq_lib as L  # noqa: E402

CLASSES = ('SAME-CONTENT', 'INSN-SAME', 'ROUND-CONSTANT-SAME')
STMT = re.compile(r"(?:Lemma|Theorem|Fact|Example|Corollary|Remark|Goal|Definition|Ltac)\b\s*([\w']*)")


def norm(n):
    n = re.sub(r'\.llvm\.\d+', '', n or '')
    return re.sub(r'(\.\d+)+$', '', n)


def split_where(w):
    """('name', off) of `name+0xoff`, else (w, None)."""
    m = re.match(r'^(.*)\+(0x[0-9a-f]+)', w or '')
    return (m.group(1), int(m.group(2), 16)) if m else (w, None)


class Side:
    """One tree (donor or ours) with its images by key."""

    def __init__(self, name, tree, imgs):
        self.name, self.T, self.imgs = name, tree, imgs
        self._facts, self._index, self._lines = {}, None, {}

    def clines(self, rel):
        if rel not in self._lines:
            self._lines[rel] = self.T.text[rel].split('\n')
        return self._lines[rel]

    def key_of(self, rel, text, depth=0):
        """The image key (A / B / P / U) a segments or table expression names, else None (abstract)."""
        if text is None or depth > 6:
            return None
        if 'AsanUbsan.M' in text:
            return 'B'
        if 'Asan.M' in text:
            return 'A'
        if 'Plain.M' in text:
            return 'P'
        if 'Ubsan.M' in text:
            return 'U'
        for name in re.findall(r"[A-Za-z_][\w'.]*", text):
            if name in ('Eval', 'vm_compute', 'in', 'build_table', 'TEmpty', 'nat', 'Z', 'list', 'Segment'):
                continue
            rhs, f = self.T.lookup(rel, name)
            if rhs is not None:
                k = self.key_of(f, rhs, depth + 1)
                if k:
                    return k
        return None

    def value_of(self, rel, rhs):
        if isinstance(rhs, int):
            return rhs
        t, f = self.T.lookup(rel, rhs)
        if t is None:
            return None
        t = re.sub(r'%bv|:\s*bv\s*32', ' ', t).strip()
        t = re.sub(r'^Z_to_bv\s+32\s+', '', t).strip()
        return L.num(t) if L.NUM.fullmatch(t) else None

    def facts(self, rel):
        """Every fetch fact of the file: dict(segs, key, pc, val, rhs, line, lemma)."""
        if rel in self._facts:
            return self._facts[rel]
        c = self.T.text[rel]
        out = []
        for segs, expr, rhs, off, j in L.fetch_facts(c):
            pre = c[max(0, off - 600):off]
            ms = list(STMT.finditer(pre))
            lemma = ms[-1].group(1) if ms else ''
            out.append(dict(segs=segs, key=self.key_of(rel, segs), pc=L.eval_expr(self.T, rel, expr), expr=expr,
                            rhs=rhs, val=self.value_of(rel, rhs), line=c.count('\n', 0, j) + 1, lemma=lemma,
                            file=rel, how='fetch'))
        self._facts[rel] = out
        return out

    CODE_AT = re.compile(r"code_at\s+([\w.']+)\s+(\([^()]*\)|[\w.']+)\s+(0x[0-9a-fA-F]+|\d+)\s+([\w.']+)")

    def index(self):
        """word NAME -> facts in any file that fetch NAME or lay it out in a concrete code_at table."""
        if self._index is not None:
            return self._index
        idx = collections.defaultdict(list)
        for rel, c in self.T.text.items():
            if 'fetch_word' in c:
                for f in self.facts(rel):
                    if isinstance(f['rhs'], str):
                        idx[f['rhs'].split('.')[-1]].append(f)
            for m in self.CODE_AT.finditer(c):
                segs, base, off, lst = m.groups()
                lst = lst.rstrip('.')
                key = self.key_of(rel, segs)
                if key is None:
                    continue
                rhs, lf = self.T.lookup(rel, lst)
                if rhs is None or not rhs.lstrip().startswith('['):
                    continue
                b = L.eval_expr(self.T, rel, base)
                names = re.findall(r"[A-Za-z_][\w'.]*", rhs)
                ln = c.count('\n', 0, m.start()) + 1
                for i, n in enumerate(names):
                    idx[n.split('.')[-1]].append(dict(
                        segs=segs, key=key, pc=None if b is None else b + L.num(off) + 4 * i, rhs=n, val=None,
                        line=ln, lemma=f'code_at {lst}[{i}]', file=rel, how='code_at', expr=f'{base} + {off} + 4*{i}'))
        self._index = idx
        return idx

    # ---------------------------------------------------------------- the pcs a row's word is stated at
    def resolve(self, rel, ln, v, runkey):
        """([cand], how): cand = dict(key, pc, how, ...). key None = abstract segments."""
        cl = self.clines(rel)
        line = cl[ln - 1] if 0 < ln <= len(cl) else ''
        facts = self.facts(rel)
        a = [f for f in facts if f['line'] == ln and f['val'] == v]
        if a:
            return a, 'fetch fact on the line'
        m = re.search(r"Definition\s+([\w']+)\s*:\s*bv\s*32\s*:=\s*(0x[0-9a-fA-F]+|\d+)", line)
        if m and L.num(m.group(2)) == v:
            name = m.group(1)
            own = [f for f in facts if f['rhs'] == name]
            if own and any(f['key'] for f in own):
                return own, f'fetch fact of {name} in the file'
            users = [f for f in self.index().get(name, ()) if f['file'] != rel and rel in self.T.closure(f['file'])
                     and f['key']]
            if users:
                return users, f'{name} as stated by files that Require this one'
            if own:
                return own, f'fetch fact of {name} in the file'
            found = self.table_search(rel, name)
            if found:
                return found, found[0]['how']
        for rx, how in ((r"clookup\s+([\w.']+)\s+(0x[0-9a-fA-F]+|\d+)\s*=\s*Some\s*\(?\s*(0x[0-9a-fA-F]+|\d+)",
                         'clookup'),):
            for mm in re.finditer(rx, line):
                if L.num(mm.group(3)) == v:
                    rhs, f = self.T.lookup(rel, mm.group(1))
                    key = self.key_of(f or rel, rhs) or runkey
                    return [dict(key=key, pc=L.num(mm.group(2)), how=f'clookup {mm.group(1)}', line=ln,
                                 file=rel, lemma='', segs=mm.group(1))], 'clookup on the line'
        mm = re.search(r"([\w.']*tbl_ok)\s+(0x[0-9a-fA-F]+|\d+)\s+(0x[0-9a-fA-F]+|\d+)", line)
        if mm and L.num(mm.group(3)) == v:
            return [dict(key=runkey, pc=L.num(mm.group(2)), how=mm.group(1), line=ln, file=rel, lemma='',
                         segs=mm.group(1))], 'table lemma on the line'
        mm = re.search(r"(step_\w+)\s+([\w.']+)\s+_\s+\(Z_to_bv\s+64\s+(0x[0-9a-fA-F]+|\d+)\)", line)
        if mm and re.search(r"Z_to_bv\s+32\s+%s\b" % re.escape(f'{v:#x}'), line, re.I):
            return [dict(key=self.key_of(rel, mm.group(2)), pc=L.num(mm.group(3)), how=mm.group(1), line=ln,
                         file=rel, lemma='', segs=mm.group(2))], 'step lemma on the line'
        # the statement this line belongs to
        k = ln
        while k > 0 and not re.match(r"\s*(?:Lemma|Theorem|Fact|Example|Corollary|Remark|Goal|Definition|Ltac)\b",
                                     cl[k - 1]):
            k -= 1
        stmt_name = ''
        if k > 0:
            ms = STMT.match(cl[k - 1].strip())
            stmt_name = ms.group(1) if ms else ''
            inside = [f for f in facts if k <= f['line'] <= ln and f['val'] == v]
            if inside:
                return inside, f'fetch fact of the enclosing statement {stmt_name}'
        same = [f for f in facts if f['val'] == v]
        if same:
            sib = {re.sub(r'^D', 'F', stmt_name), stmt_name.replace('_D', '_F', 1),
                   stmt_name.replace('decode', 'fetch')} - {stmt_name}
            s = [f for f in same if f['lemma'] in sib]
            if s:
                return s, f'sibling fetch {s[0]["lemma"]} of {stmt_name}'
            if len({(f['key'], f['pc']) for f in same}) == 1:
                return same[:1], f'the one fetch of this word in the file ({same[0]["lemma"]})'
            return same, f'this word is fetched at {len(same)} pcs in the file'
        return [], f'no pc: no fetch fact, table or code_at for this word (statement {stmt_name or "?"})'

    WDEF = re.compile(r"Definition\s+(W_([0-9a-f]+))\s*:\s*bv\s*32\s*:=\s*(0x[0-9a-fA-F]+|\d+)")

    def table_search(self, rel, name):
        """The file's own table: the run of consecutive `W_<hex>` word definitions that holds NAME, located by its
        bytes in each image of this side (executable segments). One hit in an image gives every word of the run a
        pc there."""
        c = self.T.text[rel]
        defs = [(m.group(1), int(m.group(2), 16), L.num(m.group(3))) for m in self.WDEF.finditer(c)]
        runs, cur = [], []
        for d in defs:
            if cur and d[1] != cur[-1][1] + 4:
                runs.append(cur)
                cur = []
            cur.append(d)
        if cur:
            runs.append(cur)
        for run in runs:
            idx = [i for i, d in enumerate(run) if d[0] == name]
            if not idx or len(run) < 4:
                continue
            pat = b''.join(w.to_bytes(4, 'little') for _, _, w in run)
            out = []
            for k in sorted(self.imgs):
                hits = self.imgs[k].find_all(pat)
                if len(hits) == 1:
                    out.append(dict(key=k, pc=hits[0] + 4 * idx[0], file=rel, line=None, lemma='', segs=k,
                                    how=f'the file\'s own table {run[0][0]}..{run[-1][0]} ({len(run)} words) found '
                                        f'once in image {k} at {hits[0]:#x}'))
            return out
        return []


def where2(img, a):
    return img.where(a) if img is not None and a is not None else '-'


def measure_insn(side, cand, w):
    """What the image says at this candidate pc."""
    img = side.imgs.get(cand['key']) if cand.get('key') else None
    pc = cand.get('pc')
    r = dict(key=cand.get('key'), pc=pc, how=cand.get('how'), file=cand.get('file'), line=cand.get('line'),
             img=img)
    if img is None or pc is None:
        r['state'] = 'abstract' if cand.get('key') is None else 'no-pc-value'
        return r
    r['word'] = img.word(pc)
    r['eq'] = r['word'] == w
    r['pcwhere'] = img.where(pc)
    kind, text, rel = L.decode(w)
    r['kind'], r['text'] = kind, text
    if kind in ('j', 'jal', 'branch'):
        t = pc + rel
        r['tgt'] = t
        r['tgtwhere'] = img.where(t)
        r['tgtexec'] = img.exec_at(t)
    elif kind == 'auipc':
        t, w2 = L.pair_target(img, pc, w)
        r['tgt'] = t
        r['w2'] = w2
        r['tgtwhere'] = img.where(t) if t is not None else '-'
    r['state'] = 'ok'
    return r


def same_place(a, b):
    na, oa = split_where(a)
    nb, ob = split_where(b)
    return norm(na) == norm(nb) and oa == ob, norm(na) == norm(nb)


def insn_row(run, row, SRC, DST, runkeys):
    sv, tv = int(row['sv'], 16), int(row['tv'], 16)
    S, hs = SRC.resolve(row['src_file'], row['src_line'], sv, runkeys[0])
    D, hd = DST.resolve(row['dst_file'], row['dst_line'], tv, runkeys[1])
    kind, text, rel = L.decode(tv)
    ks, texts, rels = L.decode(sv)
    meas = [f'decoded ours {tv:#010x}: {text}' + ('' if sv == tv else f'; donor {sv:#010x}: {texts}')]
    status, why = 'OK', []
    ms = [measure_insn(SRC, c, sv) for c in S]
    md = [measure_insn(DST, c, tv) for c in D]
    md_img = [m for m in md if m['state'] == 'ok']
    ms_img = [m for m in ms if m['state'] == 'ok']
    if not md_img:
        # no image pc on our side
        abstract = bool(D) and all(m['state'] == 'abstract' for m in md)
        if abstract:
            reason = (f'the word is fetched only over abstract segments ({D[0].get("segs")}, '
                      f'{D[0].get("lemma") or "the statement"}): no image pc')
        else:
            reason = hd
        if sv != tv:
            meas.append(reason + '; the word differs from the donor in a relocation field and no pc is stated')
            return 'NOT-CHECKABLE', meas, 'no pc, word differs'
        if kind == 'not32' or kind.startswith('op0x'):
            meas.append(reason + '; not an RV64G instruction word (' + text + '): a bv 32 constant of the '
                                 'statement, equal to the donor value')
            return 'OK', meas, 'not an instruction'
        if kind == 'j' and rel == 0:
            meas.append(reason + '; jal x0, 0 jumps to its own pc in any image (a spin); equal to the donor word')
            return 'OK', meas, 'self-jump'
        if abstract:
            meas.append(reason + '; the word equals the donor word bit for bit; nothing in it depends on an image')
            return 'OK', meas, 'abstract segments'
        if kind in ('j', 'jal', 'branch', 'auipc'):
            meas.append(reason + '; a pc-relative word with no pc: its target cannot be named')
            return 'NOT-CHECKABLE', meas, 'no pc, pc-relative'
        meas.append(reason + '; the word equals the donor word bit for bit and has no pc-relative field')
        return 'OK', meas, 'no pc, not pc-relative'
    # our side has image pcs: pair each with the donor's pc in the same image key, by order
    by_key = collections.defaultdict(list)
    for m in ms_img:
        by_key[m['key']].append(m)
    seen = collections.Counter()
    for d in md_img:
        grp = by_key.get(d['key'], [])
        j = seen[d['key']]
        seen[d['key']] += 1
        s = grp[j] if j < len(grp) else (grp[0] if grp else None)
        img = d['img']
        where_stated = f'{d["how"]} {d["file"]}' + (f':{d["line"]}' if d.get('line') else '')
        part = (f'ours {img.role} {img.pin_sha}: pc {d["pc"]:#x} ({where_stated}) = '
                f'{d["pcwhere"]}, image word {d["word"]:#010x}' if d['word'] is not None else
                f'ours {img.role}: pc {d["pc"]:#x} outside the image')
        if not d['eq']:
            status = 'FINDING'
            why.append(f'our image word at {d["pc"]:#x} is not the stated word')
        if s is not None:
            simg = s['img']
            part += (f'; donor {simg.role} {simg.pin_sha}: pc {s["pc"]:#x} = {s["pcwhere"]}, image word '
                     f'{s["word"]:#010x}' if s['word'] is not None else f'; donor pc {s["pc"]:#x} outside the image')
            if s['word'] != sv:
                part += ' (the donor file states another word there)'
            exact, samefn = same_place(s['pcwhere'], d['pcwhere'])
            if not samefn:
                if status == 'OK':
                    status = 'CANDIDATE'
                why.append(f'pc in another function: donor {s["pcwhere"]}, ours {d["pcwhere"]}')
            elif not exact:
                part += ' (same function, other offset)'
        else:
            part += f'; donor pc not found ({hs})'
        if 'tgt' in d:
            part += f'; target ours {d["tgt"]:#x} = {d["tgtwhere"]}' if d['tgt'] is not None else '; target ours -'
            if s is not None and s.get('tgt') is not None:
                part += f', donor {s["tgt"]:#x} = {s["tgtwhere"]}'
                exact, samefn = same_place(s['tgtwhere'], d['tgtwhere'])
                if not exact:
                    if status == 'OK':
                        status = 'CANDIDATE'
                    why.append(f'target differs: donor {s["tgtwhere"]}, ours {d["tgtwhere"]}')
            elif d['kind'] in ('j', 'jal', 'branch', 'auipc'):
                if status == 'OK':
                    status = 'CANDIDATE'
                why.append('no donor target to compare' + ('; target outside executable code'
                                                           if d.get('tgtexec') is False else ''))
        meas.append(part)
    if not ms_img:
        meas.append(f'donor side: {hs}')
    return status, meas + (['CHECK: ' + '; '.join(why)] if why else []), hd


# ------------------------------------------------------------------------------------------------ SAME-CONTENT
def holder(img, v):
    """(symbol name, symbol start, offset in symbol, string start, string bytes, offset in string)."""
    c = img.covering(v)
    s = img.cstr(v)
    if s is None:
        return None
    st, b, off = s
    if c and c[0] > st:          # never read a string across its symbol's start
        b = img.read(c[0], v - c[0]) + b[v - st:]
        st, off = c[0], v - c[0]
    return dict(sym=c[2] if c else None, symstart=c[0] if c else None, symoff=v - c[0] if c else None,
                symsize=c[1] if c else None, start=st, text=b, off=off, sec=img.sec(v))


CELL_RX = (
    (re.compile(r"\bz(\d)\s+\(ANum\s+(0x[0-9a-fA-F]+|\d+)\)\s+(0x[0-9a-fA-F]+|\d+)"), lambda m: (m[2], m[1], m[3])),
    (re.compile(r"\blit(\d)\s+(0x[0-9a-fA-F]+|\d+)\s+(0x[0-9a-fA-F]+|\d+)"), lambda m: (m[2], m[1], m[3])),
    (re.compile(r"mkChunk\s+(0x[0-9a-fA-F]+|\d+)\s+\(CVal\s+(\d+)\s+\(SLit\s+(0x[0-9a-fA-F]+|\d+)\)\)"),
     lambda m: (m[1], m[2], m[3])),
    (re.compile(r"val_mem\s+[\w.']+\s+\([^()]*(?:\([^()]*\)[^()]*)*\)\s+(0x[0-9a-fA-F]+|\d+)\s+(\d+)\s+"
                r"(0x[0-9a-fA-F]+|\d+)"), lambda m: (m[1], m[2], m[3])),
)


def cells(line):
    """[(addr, size, value)] of every memory cell the line states: `zN (ANum A) V`, `litN A V`,
    `mkChunk A (CVal N (SLit V))`, `val_mem SEGS (MEM) A N V`."""
    out = []
    for rx, f in CELL_RX:
        for m in rx.finditer(line):
            a, n, v = f(m)
            out.append((L.num(a), int(n), L.num(v)))
    return out


def cell_check(img, line, v, who):
    """The cells of the line that hold v as address or as content, read in the image. A cell in .bss is written at
    run time (the image holds zeros there): it is named, not compared."""
    out, bad = [], False
    for a, n, c in cells(line):
        if v not in (a, c):
            continue
        if img.sec(a) in ('.bss', '.tbss'):
            out.append(f'{who} cell [{a:#x}, {n} bytes] = {img.where(a)} in .bss: written at run time, stated {c:#x}')
            continue
        b = img.read(a, n)
        got = int.from_bytes(b, 'little') if b is not None else None
        ok = got == c
        bad |= not ok
        out.append(f'{who} cell [{a:#x}, {n} bytes] = {img.where(a)}: stated {c:#x}, image {got:#x}'
                   if got is not None else f'{who} cell [{a:#x}, {n} bytes] outside the image')
    return out, bad


def refs(img, v):
    """Where the image refers to v: 8-aligned data words that hold it, and auipc / lui pairs that form it."""
    data = [a for a in img.find_all(v.to_bytes(8, 'little'), exec_only=False) if a % 8 == 0 and not img.exec_at(a)]
    code = img.xrefs().get(v, [])
    return ([f'data word {a:#x} = {img.where(a)}' for a in data[:3]] +
            [f'code {img.where(p)}' for p in code[:3]]) or ['none']


def content_row(run, row, SRC, DST, key):
    SI, DI = SRC.imgs[key], DST.imgs[key]
    sv, tv = int(row['sv'], 16), int(row['tv'], 16)
    hs, hd = holder(SI, sv), holder(DI, tv)
    if hs is None or hd is None:
        return 'NOT-CHECKABLE', [f'value outside the image (donor {sv:#x}: {hs}, ours {tv:#x}: {hd})'], ''

    def fmt(h, v, img):
        return (f'{v:#x} in {h["sec"]}: symbol {h["sym"]}@{h["symstart"]:#x} size {h["symsize"]} +{h["symoff"]:#x}; '
                f'string at {h["start"]:#x} {h["text"].decode("latin-1")!r} +{h["off"]}'
                if h['sym'] else f'{v:#x} in {h["sec"]}: no symbol of the twin symtab covers it; NUL-terminated '
                                 f'string at {h["start"]:#x} {h["text"].decode("latin-1")!r} +{h["off"]}')
    meas = [f'donor {SI.role} {SI.pin_sha}: ' + fmt(hs, sv, SI), f'ours {DI.role} {DI.pin_sha}: ' + fmt(hd, tv, DI)]
    meas.append('the image refers to the value at: donor ' + '; '.join(refs(SI, sv)) + ' | ours ' +
                '; '.join(refs(DI, tv)))
    cs, bs = cell_check(SI, SRC.clines(row['src_file'])[row['src_line'] - 1], sv, 'donor')
    cd, bd = cell_check(DI, DST.clines(row['dst_file'])[row['dst_line'] - 1], tv, 'ours')
    meas += cs + cd
    samesym = hs['sym'] and hd['sym'] and norm(hs['sym']) == norm(hd['sym']) and hs['symoff'] == hd['symoff']
    samestr = hs['text'] == hd['text'] and hs['off'] == hd['off']
    if bd:
        meas.append('CHECK: a cell of our line is not what our image holds')
        return 'CANDIDATE', meas, ''
    if samesym and samestr:
        meas.append('same symbol name and offset, same whole string and offset')
        return 'OK', meas, ''
    if samestr:
        meas.append('same whole string and offset' + (f' (symbol names differ: {hs["sym"]} / {hd["sym"]})'
                                                       if hs['sym'] and hd['sym'] else ''))
        return 'OK', meas, ''
    meas.append('CHECK: the holder differs')
    return 'CANDIDATE', meas, ''


# ------------------------------------------------------------------------------------------------ driver
def read_gate(path):
    rows = []
    with open(path) as f:
        for line in f:
            if line.startswith('#'):
                continue
            c = line.rstrip('\n').split('\t')
            if c[0] in CLASSES:
                rows.append(dict(verdict=c[0], kernel=c[1], image=c[2], src_file=c[3], src_line=int(c[4]),
                                 dst_file=c[5], dst_line=int(c[6]), sentence=c[7], idx=c[8], kind=c[9], sv=c[10],
                                 tv=c[11], src_res=c[13], dst_res=c[14], note=c[15] if len(c) > 15 else ''))
    return rows


# run -> (donor folder under the donor lib, our folder under our lib, image key)
RUNS = {'RA': ('A/', 'A/', 'A'), 'RB': ('', 'B/', 'B'), 'RU': ('', 'Reusable/', 'B')}
DONOR_LIB = 'proofs/cgif/cgif_file_fuzzer/lib/'
HEAD = ('run', 'verdict', 'src', 'dst', 'sentence', 'src_value', 'dst_value', 'measured', 'status', 'finding_kind',
        'new_value', 'read_by')


def check_row(run, row, SRC, DST):
    """(status, [measured]) of one gate row; row files already carry the run's folder."""
    import feq_roles
    key = RUNS[run][2]
    if row['verdict'] == 'INSN-SAME':
        st, meas, _ = insn_row(run, row, SRC, DST, (key, key))
    elif row['verdict'] == 'SAME-CONTENT':
        st, meas, _ = content_row(run, row, SRC, DST, key)
    else:
        st, m = feq_roles.round_row(row, SRC, DST, key)
        meas = [m]
    return st, meas


def run_all(gates, SRC, DST):
    """gates: run -> gate rows. Returns the TSV rows (dicts)."""
    out = []
    for run in ('RA', 'RB', 'RU'):
        for g in gates.get(run, ()):
            row = dict(g)
            row['src_file'] = RUNS[run][0] + g['src_file']
            row['dst_file'] = RUNS[run][1] + g['dst_file']
            st, meas = check_row(run, row, SRC, DST)
            text = '; '.join(m.replace('\t', ' ').replace('\n', ' ') for m in meas)
            text = re.sub(r'(?<![\w/])(A|B|Reusable)/(\w+\.v)', r'lib/\1/\2', text)
            out.append(dict(run=run, verdict=g['verdict'], src=f'{DONOR_LIB}{row["src_file"]}:{g["src_line"]}',
                            dst=f'lib/{row["dst_file"]}:{g["dst_line"]}', sentence=g['sentence'],
                            src_value=g['sv'], dst_value=g['tv'],
                            measured=f'gate kernel_checked={g["kernel"]}; ' + text, status=st,
                            finding_kind='-', new_value='-', read_by='-'))
    return out


def emit(rows, path):
    with open(path, 'w') as f:
        f.write('\t'.join(HEAD) + '\n')
        for r in rows:
            f.write('\t'.join(str(r[h]) for h in HEAD) + '\n')


def counts(rows):
    c = collections.Counter((r['run'], r['verdict'], r['status']) for r in rows)
    return {f'{a}\t{b}\t{s}': n for (a, b, s), n in sorted(c.items())}


def load(base):
    """Trees and images from one copy root: base/tree/{cmd,cgif}/..., base/img/*, base/out/false-equal/img/*."""
    ours = L.Tree(os.path.join(base, 'tree/cmd/proofs/plugin-hostd/fuzz_command/lib'),
                  'OssFuzzTheorems.Proofs.plugin_hostd.fuzz_command.lib')
    cgif = L.Tree(os.path.join(base, 'tree/cgif/proofs/cgif/cgif_file_fuzzer/lib'),
                  'OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib')
    role = {'A': 'asan', 'B': 'asan-ubsan', 'P': 'plain'}
    img = {}
    for side, name in (('cgif', 'cgif_file_fuzzer'), ('cmd', 'fuzz_command')):
        for k in 'AB':
            img[side, k] = L.Img(f'{name}.{role[k]}', os.path.join(base, f'img/{side}.{k}.pin'),
                                 os.path.join(base, f'img/{side}.{k}.twin'))
        img[side, 'P'] = L.Img(f'{name}.plain', os.path.join(base, f'out/false-equal/img/{side}.P.pin'),
                               os.path.join(base, f'out/false-equal/img/{side}.P.twin'))
    SRC = Side('cgif', cgif, {k: img['cgif', k] for k in 'ABP'})
    DST = Side('cmd', ours, {k: img['cmd', k] for k in 'ABP'})
    return SRC, DST


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--base', required=True, help='copy root holding tree/, img/, runs/ and out/false-equal/img/')
    ap.add_argument('--out', required=True)
    a = ap.parse_args()
    SRC, DST = load(a.base)
    gates = {r: read_gate(os.path.join(a.base, f'runs/{r}/full.tsv')) for r in RUNS}
    rows = run_all(gates, SRC, DST)
    emit(rows, a.out)
    for k, n in counts(rows).items():
        print(f'{k}\t{n}')


if __name__ == '__main__':
    main()
