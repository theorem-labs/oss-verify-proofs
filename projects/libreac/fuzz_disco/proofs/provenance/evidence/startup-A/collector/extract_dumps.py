#!/usr/bin/env python3
"""extract_dumps.py LOG OUT MARKER... [--split BYTES] -- the values of a collector build log that the start-up tools
read, without the rest of the log.

The start-up collector is a Rocq driver: building it prints each dump as `MARKER = 0`, `     : Z`, `     = <value>`,
`     : <type>`. hsform.py reads the JSDUMP (pass 1), HSDUMPHOLES and HSDUMP (pass 2) dumps, and it finds a pass by the
build's `ROCQ compile <dir>/<pass>.v` line. OUT keeps, in log order, every `ROCQ compile` line and, for each MARKER, its
dump from the `MARKER = 0` line to its type line. Before it cuts, it removes the timing lines the build splices into the
printed terms (`proofs/... .vo (real: ...)`), as hsform.py does when it reads a log. Every other line (build commands,
timings, warnings, the other prints) is left out. The first line of OUT names the log's sha256 and size.

A printed value longer than 64 KiB (HSDUMP: 50 hand-off states) is written one element of its outer list per line: the
space after each `;` that separates two elements of the outer list becomes a line break (the log's own line breaks
stay). hsform.py reads every run of white space as one space, so it reads the same terms. With --split, OUT is written
as OUT.1, OUT.2, ... of at most BYTES bytes each, cut at line breaks; `cat OUT.1 OUT.2 ...` gives OUT.
"""
import hashlib
import re
import sys

TIMING = re.compile(r'proofs/\S+\.vo \(real: [^)]*\)\n')
LONG = 1 << 16


def reflow(value):
    """the lines of a printed value `     = [...]` (one or more lines), with a line break after each `;` that separates
    two elements of its outer list"""
    text = '\n'.join(value)
    out, depth, start = [], 0, 0
    for k in range(text.index('['), len(text)):
        c = text[k]
        if c in '[({':
            depth += 1
        elif c in '])}':
            depth -= 1
        elif c == ';' and depth == 1 and text[k + 1:k + 2] == ' ':
            out.append(text[start:k + 1])
            start = k + 2
    out.append(text[start:])
    return '\n'.join(out).split('\n')


def main():
    args = sys.argv[1:]
    split = None
    if '--split' in args:
        k = args.index('--split')
        split = int(args[k + 1])
        del args[k:k + 2]
    if len(args) < 3:
        sys.exit('usage: extract_dumps.py LOG OUT MARKER... [--split BYTES]')
    log, out, markers = args[0], args[1], args[2:]
    raw = open(log, 'rb').read()
    lines = TIMING.sub('', raw.decode('utf-8', errors='replace')).split('\n')
    keep = [l.startswith('ROCQ compile ') for l in lines]
    values = {}                                       # first line of a dump's value -> the index of its type line
    for mk in markers:
        starts = [i for i, l in enumerate(lines) if l == '%s = 0' % mk]
        if len(starts) != 1:
            sys.exit('extract_dumps: %s: %d `%s = 0` lines (one expected)' % (log, len(starts), mk))
        i = starts[0]
        if lines[i + 1] != '     : Z' or not lines[i + 2].startswith('     = '):
            sys.exit('extract_dumps: %s: the dump %s has not the printed form `: Z` then `= ...`' % (log, mk))
        j = i + 3
        while j < len(lines) and not lines[j].startswith('     : '):
            j += 1
        if j == len(lines):
            sys.exit('extract_dumps: %s: the dump %s has no type line' % (log, mk))
        for k in range(i, j + 1):
            keep[k] = True
        values[i + 2] = j
    body, k = [], 0
    while k < len(lines):
        if k in values and sum(len(x) for x in lines[k:values[k]]) > LONG and lines[k].startswith('     = ['):
            body += reflow(lines[k:values[k]])
            k = values[k]
            continue
        if keep[k]:
            body.append(lines[k])
        k += 1
    head = '# extract_dumps.py of a collector log (sha256 %s, %d bytes): its ROCQ compile lines and the dumps %s' % (
        hashlib.sha256(raw).hexdigest(), len(raw), ', '.join(markers))
    text = [x + '\n' for x in [head] + body]
    if split is None:
        open(out, 'w').write(''.join(text))
        print('extract_dumps: %s -> %s (%d lines)' % (log, out, len(text)))
        return
    parts, cur = [], ''
    for x in text:
        if len(x.encode()) > split:
            sys.exit('extract_dumps: a line of %d bytes is longer than --split %d' % (len(x.encode()), split))
        if len((cur + x).encode()) > split:
            parts.append(cur)
            cur = ''
        cur += x
    parts.append(cur)
    for n, p in enumerate(parts, 1):
        open('%s.%d' % (out, n), 'w').write(p)
    print('extract_dumps: %s -> %s.1 .. %s.%d (%d lines)' % (log, out, out, len(parts), len(text)))


if __name__ == '__main__':
    main()
