#!/usr/bin/env python3
"""Position-by-position numeral diff of two port_core stage-outs against the unit's files.

For one port_core input set: the run of record's stage-out (OLD), the port_core d9e0589898fd --dry stage-out (NEW),
the unit's lib (OURS) and the merged tree's lib (MERGED).

Output 1 (--files-out): file, sha256 of OLD / NEW / OURS / MERGED stage file, and equal/differs flags.
Output 2 (--rows-out): one row per differing token between OLD and NEW (aligned by line on numeral-blind text, so the
provenance header and identifier renames never shift the alignment), with OURS' token at the same place, plus one row
per OLD/NEW line whose non-numeral text differs. Comment positions come from a Coq lexer pass over each file.
Output 3 (--agree-out): lines where OLD and NEW are identical but OURS differs from both only inside comments
(stale comment numerals), and a count of lines where OURS differs in code.
"""
import argparse, difflib, hashlib, os, re, sys

NUM = re.compile(r"(?<![A-Za-z0-9_'.])(port_core_refused_[A-Za-z0-9_]+|0x[0-9a-fA-F]+|\d+)(?![A-Za-z0-9_'])")


def sha(p):
    try:
        with open(p, 'rb') as fh:
            return hashlib.sha256(fh.read()).hexdigest()
    except FileNotFoundError:
        return '-'


def eq_flag(x, y):
    if '-' in (x, y):
        return 'missing'
    return 'equal' if x == y else 'differs'


def read_lines(p):
    with open(p, encoding='utf-8') as fh:
        return fh.read().split('\n')


CTOK = re.compile(r'\(\*|\*\)|"')


def comment_mask(lines):
    """Per line, the list of (start, end) character ranges inside a Coq comment (* ... *) (nested; strings outside
    comments are skipped)."""
    depth = 0
    in_str = False
    masks = []
    for line in lines:
        iv = []
        start = 0 if depth > 0 else None
        for m in CTOK.finditer(line):
            t, p = m.group(), m.start()
            if depth == 0 and in_str:
                if t == '"':
                    in_str = False
                continue
            if t == '(*':
                if depth == 0:
                    start = p
                depth += 1
            elif t == '*)':
                if depth > 0:
                    depth -= 1
                    if depth == 0:
                        iv.append((start, p + 2))
                        start = None
            elif depth == 0:
                in_str = True
        if depth > 0:
            iv.append((start, len(line)))
        masks.append(iv)
    return masks


def in_comment(iv, pos):
    return any(s <= pos < e for s, e in iv)


def norm(line):
    return NUM.sub('#', line)


def code_part(line, iv):
    out, prev = [], 0
    for s, e in iv:
        out.append(line[prev:s])
        prev = e
    out.append(line[prev:])
    return ''.join(out)


def tokens(line):
    return [(m.group(1), m.start(1)) for m in NUM.finditer(line)]


def as_int(tok):
    if tok.startswith('port_core_refused_'):
        return None
    try:
        return int(tok, 16) if tok.lower().startswith('0x') else int(tok)
    except ValueError:
        return None


def align(a, b):
    """Map index in a -> index in b on numeral-blind text; inside unequal blocks pair by best ratio."""
    na = [norm(x) for x in a]
    nb = [norm(x) for x in b]
    out = {}
    if len(na) == len(nb) and sum(x == y for x, y in zip(na, nb)) >= 0.9 * len(na):
        # same line count and >= 90% numeral-blind equal lines (a stage-out pair): line i is line i
        for i in range(len(na)):
            out[i] = (i, 'exact' if na[i] == nb[i] else 'block')
        return out
    sm = difflib.SequenceMatcher(None, na, nb, autojunk=False)
    for tag, i1, i2, j1, j2 in sm.get_opcodes():
        if tag == 'equal':
            for k in range(i2 - i1):
                out[i1 + k] = (j1 + k, 'exact')
        elif tag == 'replace':
            if i2 - i1 == j2 - j1:
                for k in range(i2 - i1):
                    out[i1 + k] = (j1 + k, 'block')
            else:
                # unequal block: pair each line with the most similar unused line in a bounded window around its
                # proportional position (exact numeral-blind text first), ratio >= 0.6; blocks over 400 lines (a
                # regenerated file) are paired on exact numeral-blind text only
                used = set()
                exact = {}
                for j in range(j1, j2):
                    exact.setdefault(nb[j], []).append(j)
                for i in range(i1, i2):
                    hit = next((j for j in exact.get(na[i], []) if j not in used), None)
                    if hit is not None:
                        out[i] = (hit, 'fuzzy')
                        used.add(hit)
                        continue
                    if i2 - i1 > 400:
                        continue
                    mid = j1 + (i - i1) * (j2 - j1) // max(1, i2 - i1)
                    best, bj = 0.0, None
                    for j in range(max(j1, mid - 40), min(j2, mid + 41)):
                        if j in used:
                            continue
                        s = difflib.SequenceMatcher(None, na[i], nb[j], autojunk=False)
                        if s.real_quick_ratio() <= best or s.quick_ratio() <= best:
                            continue
                        r = s.ratio()
                        if r > best:
                            best, bj = r, j
                    if bj is not None and best >= 0.6:
                        out[i] = (bj, 'fuzzy')
                        used.add(bj)
    return out


def contexts(line, line_tokens):
    """Numeral-blind (left 24 chars, right 12 chars) context of each token, computed in one pass."""
    parts, starts, prev, pos = [], [], 0, 0
    for t, s in line_tokens:
        parts.append(line[prev:s])
        pos += s - prev
        starts.append(pos)
        pos += 1
        prev = s + len(t)
    parts.append(line[prev:])
    nl = '#'.join(parts)
    return [(nl[max(0, p - 24):p], nl[p + 1:p + 13]) for p in starts]


def token_in(line_tokens, line, pos_idx, ref_line, ref_tokens, cache):
    """Token of `line` at the place of ref_tokens[pos_idx] in ref_line (same index if the numeral-blind text matches,
    else the token with the same numeral-blind context: 24 chars left, 12 chars right)."""
    key = (line, ref_line)
    if key not in cache:
        cache.clear()
        same = norm(line) == norm(ref_line) and len(line_tokens) == len(ref_tokens)
        cache[key] = (same, None if same else contexts(line, line_tokens),
                      None if same else contexts(ref_line, ref_tokens))
    same, lc, rc = cache[key]
    if same:
        return line_tokens[pos_idx][0], 'same-text'
    cands = [t for (t, _), c in zip(line_tokens, lc) if c == rc[pos_idx]]
    if len(cands) == 1:
        return cands[0], 'context'
    if not cands:
        return '-', 'no-match'
    return '|'.join(sorted(set(cands))), 'ambiguous'


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--set', required=True)
    ap.add_argument('--old-out', required=True, help='run of record stage-out root (holds A/...)')
    ap.add_argument('--new-out', required=True, help='d9e0 stage-out root')
    ap.add_argument('--ours', required=True, help="the unit's lib/ root")
    ap.add_argument('--merged', required=True, help="the merged tree's lib/ root")
    ap.add_argument('--files-out', required=True)
    ap.add_argument('--rows-out', required=True)
    ap.add_argument('--agree-out', required=True)
    ap.add_argument('--chunk', default='0/1', help='K/N: process the K-th of N interleaved slices of the file list')
    a = ap.parse_args()

    files = []
    for root, _, names in os.walk(a.new_out):
        for n in names:
            if n.endswith('.v'):
                files.append(os.path.relpath(os.path.join(root, n), a.new_out))
    files.sort()
    k, n = (int(x) for x in a.chunk.split('/'))
    files = files[k::n]

    def opened(path, header):
        new_file = not os.path.exists(path) or os.path.getsize(path) == 0
        fh = open(path, 'a')
        if new_file:
            fh.write('\t'.join(header) + '\n')
        return fh

    fo = opened(a.files_out, ['set', 'file', 'sha256_old_stage_out', 'sha256_d9e0_stage_out', 'sha256_ours',
                              'sha256_merged', 'old_vs_d9e0', 'ours_vs_old', 'ours_vs_d9e0', 'ours_vs_merged'])
    ro = opened(a.rows_out, ['set', 'file', 'old_line', 'd9e0_line', 'our_line', 'pos', 'kind', 'old_val', 'd9e0_val',
                             'our_val', 'where', 'how', 'ctx'])
    ao = opened(a.agree_out, ['set', 'file', 'old_line', 'our_line', 'kind', 'stage_text', 'our_text'])
    nrow = 0
    agree = {'comment-only': 0, 'code': 0}
    for f in files:
        po, pn, pu, pm = (os.path.join(d, f) for d in (a.old_out, a.new_out, a.ours, a.merged))
        so, sn, su, smg = sha(po), sha(pn), sha(pu), sha(pm)
        fo.write('\t'.join([a.set, 'lib/' + f, so, sn, su, smg, eq_flag(so, sn), eq_flag(su, so), eq_flag(su, sn),
                            eq_flag(su, smg)]) + '\n')
        old, new = read_lines(po), read_lines(pn)
        ours = read_lines(pu) if su != '-' else []
        om, nm = comment_mask(old), comment_mask(new)
        um = comment_mask(ours) if ours else []
        o2n = align(old, new)
        o2u = align(old, ours) if ours else {}
        for i, ol in enumerate(old):
            if i not in o2n:
                ro.write('\t'.join([a.set, 'lib/' + f, str(i + 1), '-', '-', '-', 'line-unpaired', ol.strip()[:400],
                                    '-', '-', '-', '-', '-']) + '\n')
                nrow += 1
                continue
            j, how = o2n[i]
            nl = new[j]
            uj, uhow = o2u.get(i, (None, 'unpaired'))
            ul = ours[uj] if uj is not None else ''
            ulno = str(uj + 1) if uj is not None else '-'
            if ol == nl:
                if uj is not None and ul != ol:
                    kind = ('comment-only' if code_part(ul, um[uj]).strip() == code_part(ol, om[i]).strip()
                            else 'code')
                    agree[kind] += 1
                    ao.write('\t'.join([a.set, 'lib/' + f, str(i + 1), ulno, kind, ol.strip()[:300],
                                        ul.strip()[:300]]) + '\n')
                continue
            ot, nt = tokens(ol), tokens(nl)
            if norm(ol) == norm(nl) and len(ot) == len(nt):
                ut = tokens(ul) if uj is not None else []
                cache = {}
                for k, ((tv, ts), (nv, _)) in enumerate(zip(ot, nt)):
                    if tv == nv:
                        continue
                    if uj is not None:
                        uv, uw = token_in(ut, ul, k, ol, ot, cache)
                    else:
                        uv, uw = '-', 'no-line'
                    where = 'comment' if in_comment(om[i], ts) else 'code'
                    ctx = norm(ol[max(0, ts - 60):ts]) + '<<' + tv + '>>' + norm(ol[ts + len(tv):ts + len(tv) + 30])
                    ro.write('\t'.join([a.set, 'lib/' + f, str(i + 1), str(j + 1), ulno, str(k), 'token', tv, nv, uv,
                                        where, uw + ':' + uhow, ctx.replace('\t', ' ')]) + '\n')
                    nrow += 1
            else:
                where = 'comment' if code_part(ol, om[i]).strip() == code_part(nl, nm[j]).strip() else 'code'
                ro.write('\t'.join([a.set, 'lib/' + f, str(i + 1), str(j + 1), ulno, '-', 'text', ol.strip()[:400],
                                    nl.strip()[:400], ul.strip()[:400] if uj is not None else '-', where,
                                    how + ':' + uhow, '-']) + '\n')
                nrow += 1
    print(f'{a.set}: files {len(files)}, rows {nrow}, old=new lines where ours differs: {agree}', file=sys.stderr)


if __name__ == '__main__':
    main()
