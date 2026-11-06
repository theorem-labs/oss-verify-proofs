#!/usr/bin/env python3
"""extract_pass2.py -- the per-value extract of the collector's pass-2 log that af0m.py (run by yf0m_regen.py) reads.

  extract_pass2.py --log PASS2.log --image IMAGE --cells CELLS --out PASS2_VALUES.tsv

The pass-2 log is the build log of the collector's Pass2 driver: it prints HSDUMPHOLES (the hole numbers) and HSDUMP (one
hand-off state per hole: `Some {| a_ss := SS pc [regs] [log] [kn] nxt; ... |}`). Of it the generator reads only:
  - the number of states;
  - the pc and the registers x1 (ra), x3 (gp), x4 (tp) of the FIRST state (TFIB_MAIN, TFIB_MAIN_RA, TFIB_GP, TFIB_TP);
  - for each cell [addr, addr + width) it reads, the set of values the states give it, over all states. A state's value
    comes from its kn list (KWord / KFill / KZero facts, and KImg ranges that take the image's bytes, so IMAGE is an
    input too); a state that does not determine every byte gives None, written '-'.
CELLS lists the cells, one `ADDR/WIDTH` per line or the `cell` rows of a table this script wrote; the rows come out
sorted by (addr, width), each once. The table of record lists exactly the cells af0m.py reads: af0m.py refuses a run that
reads a cell the table lacks or leaves a row unread. So re-running this on the log with the table of record as CELLS gives
the table byte for byte.

The log is parsed by the functions of hsform.py b1d794ec6122 (readlog without a --pass cut, split_top, match_close, norm,
qualify, dump_list, holes_of, state_parts) and the states are read by af0m.py 2ac2dbe25a9a's Mem and state_bytes, all
copied here unchanged in what they compute. Needs pyelftools.
"""
import argparse, hashlib, re
from elftools.elf.elffile import ELFFile


# --- hsform.py b1d794ec6122: the log parser
def split_top(body, sep=';'):
    elems, depth, cur = [], 0, []
    for ch in body:
        if ch in '[({':
            depth += 1
        elif ch in '])}':
            depth -= 1
        if ch == sep and depth == 0:
            elems.append(''.join(cur).strip()); cur = []
        else:
            cur.append(ch)
    t = ''.join(cur).strip()
    if t:
        elems.append(t)
    return elems


def match_close(s, i):
    """s[i] is an opening bracket; return the index just past its matching closer"""
    depth = 0
    for k in range(i, len(s)):
        ch = s[k]
        if ch in '[({':
            depth += 1
        elif ch in '])}':
            depth -= 1
            if depth == 0:
                return k + 1
    raise ValueError('unbalanced')


def norm(s):
    return ' '.join(s.split())


QUAL = re.compile(r'(?<![\w.])((?:ALUW?|M|MW)_[A-Z]+)\b')


def qualify(s):
    return QUAL.sub(r'Instr.\1', s)


TIMING = re.compile(r'proofs/\S+\.vo \(real: [^)]*\)\n')


def readlog(log):
    """the build log, with the `FILE.vo (real: ...)` lines that make -O TIMED=1 splices into a long term cut out"""
    return TIMING.sub('', open(log, errors='replace').read())


def dump_list(s0, marker, typ):
    i = s0.index('%s = 0' % marker)
    s = s0[i:]
    i = s.index('= [') + 2
    j = s.index('     : ' + typ)
    body = s[i:j].strip()
    assert body.startswith('[') and body.endswith(']'), body[-80:]
    return split_top(qualify(norm(body[1:-1])))


def holes_of(s0):
    t = s0[s0.index('HSDUMPHOLES = 0'):]
    t = t[t.index('= [') + 3:]
    body = t[:t.index(']')].strip()
    return [int(x.strip().replace('%nat', '')) for x in body.split(';')] if body else []


def state_parts(term):
    """term = `{| a_ss := SS pc [regs] [log] [kn] nxt; ... |}` -> (prefix, kn elements, suffix) with the kn list cut out"""
    k = term.index('a_ss := SS ')
    p = k + len('a_ss := SS ')
    m = re.match(r'\(?-?\d+\)?\s*', term[p:])
    p += m.end()
    for _ in range(2):           # regs, log
        assert term[p] == '[', term[p:p + 40]
        p = match_close(term, p)
        while term[p] == ' ':
            p += 1
    assert term[p] == '[', term[p:p + 40]
    q = match_close(term, p)
    kn = split_top(term[p + 1:q - 1]) if term[p + 1:q - 1].strip() else []
    return term[:p], kn, term[q:]


# --- af0m.py 2ac2dbe25a9a: a state's bytes
class Mem:
    def __init__(self, image):
        e = ELFFile(open(image, 'rb'))
        self.segs = [(s['p_vaddr'], s['p_filesz'], s['p_memsz'], s.data()) for s in e.iter_segments() if s['p_type'] == 'PT_LOAD']
        self.e = e

    def byte(self, a):
        for va, fs, ms, d in self.segs:
            if va <= a < va + ms:
                return d[a - va] if a - va < fs else 0
        return None


def state_bytes(kn, mem):
    known, imgr = {}, []
    for x in kn:
        m = re.match(r'KWord \{\| a_base := ELit 0; a_off := (\d+) \|\} (\d+) \(ELit (-?\d+)\)$', x)
        if m:
            a, w, v = int(m.group(1)), int(m.group(2)), int(m.group(3)) % (1 << 64)
            for i in range(w):
                known.setdefault(a + i, (v >> (8 * i)) & 0xff)
            continue
        m = re.match(r'KFill \{\| a_base := ELit 0; a_off := (\d+) \|\} \(ELit (\d+)\) (\d+)$', x)
        if m:
            a, n, b = int(m.group(1)), int(m.group(2)), int(m.group(3))
            for i in range(n):
                known.setdefault(a + i, b)
            continue
        m = re.match(r'KZero \{\| a_base := ELit 0; a_off := (\d+) \|\} \(ELit (\d+)\)$', x)
        if m:
            a, n = int(m.group(1)), int(m.group(2))
            (imgr.append(('zero', a, a + n)) if n >= 1 << 24 else [known.setdefault(a + i, 0) for i in range(n)])
            continue
        m = re.match(r'KImg (\d+) (\d+)$', x)
        if m:
            imgr.append(('img', int(m.group(1)), int(m.group(2))))

    def read(a, w):
        v = 0
        for i in range(w):
            b = known.get(a + i)
            if b is None:
                for k, lo, hi in imgr:
                    if lo <= a + i < hi:
                        b = 0 if k == 'zero' else mem.byte(a + i)
                        break
            if b is None:
                return None
            v |= b << (8 * i)
        return v
    return read


def sha256(path):
    return hashlib.sha256(open(path, 'rb').read()).hexdigest()


def cells_of(path):
    out = set()
    for line in open(path):
        line = line.split('#')[0].strip()
        if not line:
            continue
        p = line.split('\t')
        if p[0] == 'cell':
            out.add((int(p[1], 16), int(p[2])))
        elif '/' in line:
            ad, w = line.split('/')
            out.add((int(ad, 0), int(w)))
    return sorted(out)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--log', required=True); ap.add_argument('--image', required=True)
    ap.add_argument('--cells', required=True); ap.add_argument('--out', required=True)
    a = ap.parse_args()
    mem = Mem(a.image)
    s0 = readlog(a.log)
    holes = holes_of(s0)
    elems = dump_list(s0, 'HSDUMP', 'list (option acs)')
    reads = {}
    for h, e in zip(holes, elems):
        _, kn, _ = state_parts(e[len('Some'):].strip())
        reads[h] = state_bytes(kn, mem)
    pre = state_parts(elems[0][len('Some'):].strip())[0]
    sregs = re.search(r'SS (\d+) \[(.*?)\] \[\]', pre)
    regs = [x.strip() for x in sregs.group(2).split(';')]

    def reglit(i):
        m = re.fullmatch(r'ELit (\d+)', regs[i])
        return '%#x' % int(m.group(1)) if m else '-'
    rows = ['states\t%d' % len(holes), 'reg\tpc\t%#x' % int(sregs.group(1)),
            'reg\tx1\t%s' % reglit(1), 'reg\tx3\t%s' % reglit(3), 'reg\tx4\t%s' % reglit(4)]
    cells = cells_of(a.cells)
    nsplit = 0
    for ad, w in cells:
        vals = {reads[h](ad, w) for h in holes}
        nsplit += len(vals) != 1 or None in vals
        rows.append('cell\t%#x\t%d\t%s' % (ad, w, ','.join(['%#x' % v for v in sorted(x for x in vals if x is not None)]
                                                          + (['-'] if None in vals else []))))
    with open(a.out, 'w') as f:
        f.write('# per-value extract of the collector pass-2 log: only the values the YF0m generator reads\n')
        f.write('# log sha256 %s\n' % sha256(a.log))
        f.write('# image sha256 %s (KImg facts of a state read the image\'s bytes)\n' % sha256(a.image))
        f.write('# rows: states N | reg NAME VALUE (the first state: pc, x1 = ra, x3 = gp, x4 = tp) | '
                'cell ADDR WIDTH VALUES (the values of [ADDR, ADDR + WIDTH) over all states; one value = every state '
                'agrees; - = a state does not determine it)\n')
        f.write('\n'.join(rows) + '\n')
    print('extract_pass2: %d states, %d cells (%d not pinned to one value by every state) -> %s'
          % (len(holes), len(cells), nsplit, a.out))


if __name__ == '__main__':
    main()
