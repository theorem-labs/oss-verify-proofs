#!/usr/bin/env python3
"""Rewrite stale address numerals inside COMMENTS of proof files from the image's own symbol table.

    fix_comment_numerals.py TABLE ROOT --twins DIR [--check]

TABLE rows (tab-separated, '#' lines skipped): <file under ROOT> <line> <old numeral> <symbol> <twin file> <twin sha256>
The twin file name is read under DIR (the unstripped images; outside git, pinned here by sha256). For each row the
tool reads the twin (its sha256 must equal the row's), finds the FUNC symbol <symbol> (exactly one start address),
checks that <old numeral> occurs on <line> inside a Rocq comment and nowhere in the line's code, and replaces it there
by the symbol's start address. It prints one line per row: file:line old -> new (symbol, twin sha256). --check only
verifies and prints. Exit 1 on any refusal; nothing is written then."""
import hashlib, os, re, struct, sys


def func_starts(path):
    b = open(path, 'rb').read()
    assert b[:4] == b'\x7fELF' and b[4] == 2 and b[5] == 1
    shoff, = struct.unpack_from('<Q', b, 0x28)
    shentsize, shnum = struct.unpack_from('<HH', b, 0x3a)
    sh = [struct.unpack_from('<IIQQQQIIQQ', b, shoff + i * shentsize) for i in range(shnum)]
    out = {}
    for (_, typ, _, _, off, size, link, _, _, _) in sh:
        if typ != 2:
            continue
        stroff = sh[link][4]
        for k in range(size // 24):
            st_name, st_info, _, st_shndx, st_value, _ = struct.unpack_from('<IBBHQQ', b, off + 24 * k)
            if st_shndx and (st_info & 15) == 2:
                e = b.index(b'\0', stroff + st_name)
                out.setdefault(b[stroff + st_name:e].decode('latin-1'), set()).add(st_value)
    return out, hashlib.sha256(b).hexdigest()


def comment_spans(text):
    """[start, end) offsets of every (* ... *) comment (nested), outside string literals."""
    spans, i, depth, start, instr = [], 0, 0, 0, False
    while i < len(text):
        if depth == 0 and text[i] == '"':
            instr = not instr
        elif not instr and text.startswith('(*', i):
            if depth == 0:
                start = i
            depth += 1
            i += 2
            continue
        elif not instr and depth and text.startswith('*)', i):
            depth -= 1
            i += 2
            if depth == 0:
                spans.append((start, i))
            continue
        i += 1
    return spans


def main():
    table, root = sys.argv[1], sys.argv[2]
    check = '--check' in sys.argv[3:]
    tdir = sys.argv[sys.argv.index('--twins') + 1]
    rows = [l.rstrip('\n').split('\t') for l in open(table) if l.strip() and not l.startswith('#')]
    twins, edits, bad = {}, {}, []
    for f, line, old, sym, twin, tsha in rows:
        if twin not in twins:
            twins[twin] = func_starts(os.path.join(tdir, twin))
        starts, sha = twins[twin]
        if sha != tsha:
            bad.append('%s: twin sha256 %s != %s' % (twin, sha, tsha))
            continue
        addrs = starts.get(sym, set())
        if len(addrs) != 1:
            bad.append('%s:%s: symbol %s has %d start addresses' % (f, line, sym, len(addrs)))
            continue
        new = '0x%x' % next(iter(addrs))
        path = root + '/' + f
        text = edits.get(path) or open(path, encoding='utf-8').read()
        lines = text.split('\n')
        n = int(line)
        lo = sum(len(x) + 1 for x in lines[:n - 1])
        hi = lo + len(lines[n - 1])
        hits = [m.start() + lo for m in re.finditer(r'(?<![0-9a-fA-Fx])%s(?![0-9a-fA-F])' % re.escape(old), lines[n - 1])]
        spans = comment_spans(text)
        inside = [h for h in hits if any(a <= h < b for a, b in spans)]
        if not hits or len(inside) != len(hits):
            bad.append('%s:%s: %s occurs %d times, %d inside a comment' % (f, line, old, len(hits), len(inside)))
            continue
        for h in sorted(inside, reverse=True):
            text = text[:h] + new + text[h + len(old):]
        edits[path] = text
        print('%s:%s %s -> %s (%s, twin sha256 %s)' % (f, line, old, new, sym, sha[:12]))
    if bad:
        print('\n'.join('REFUSED ' + b for b in bad))
        sys.exit(1)
    if not check:
        for path, text in edits.items():
            open(path, 'w', encoding='utf-8').write(text)


if __name__ == '__main__':
    main()
