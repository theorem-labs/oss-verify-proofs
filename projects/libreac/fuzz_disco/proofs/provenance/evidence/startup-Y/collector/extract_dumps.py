#!/usr/bin/env python3
"""extract_dumps.py [--part-bytes N] LOG OUT MARKER [MARKER ...] -- the per-value extract of a start-up collector log.

The collector prints each of its results as a Rocq `Compute` answer: a line `<MARKER> = 0`, a type line, then
`     = <value>` and a closing `     : <type>` line. hsform.py reads only those answers (`dump_list`, `holes_of`);
everything else in the log is build output. This script keeps, for each MARKER in the order the log holds them, the
text from the line `<MARKER> = 0` through the end of the first `     : ` line that follows the value. It first cuts the
`FILE.vo (real: ...)` lines that a timed build can splice into a long printed term, exactly as hsform.py's readlog does,
so the extract is what hsform.py parses. A header comment line names the log's sha256 and size.

hsform.py reads the extract in place of the log and gives the same output bytes (run.sh).
With --part-bytes N the extract is written as OUT.00, OUT.01, ... instead, each at most N bytes and cut only at a line
end; `cat OUT.??` gives the one-file extract back (the repository's file-size cap is 5 MiB)."""
import hashlib, re, sys

TIMING = re.compile(r'proofs/\S+\.vo \(real: [^)]*\)\n')


def block(s, marker):
    i = s.index('\n%s = 0\n' % marker) + 1
    v = s.index('\n     = ', i)
    c = s.index('\n     : ', v + 1)
    e = s.index('\n', c + 1) + 1
    return i, s[i:e]


def main():
    args = sys.argv[1:]
    part = None
    if args[:1] == ['--part-bytes']:
        part, args = int(args[1]), args[2:]
    log, out, markers = args[0], args[1], args[2:]
    raw = open(log, 'rb').read()
    s = TIMING.sub('', raw.decode('utf-8', errors='replace'))
    blocks = sorted(block(s, m) for m in markers)
    head = '(* extract of a collector log: sha256 %s, %d bytes; markers %s *)\n' % (
        hashlib.sha256(raw).hexdigest(), len(raw), ' '.join(markers))
    text = head + ''.join(b for _, b in blocks)
    if part is None:
        open(out, 'w').write(text)
        return
    data, k, n = text.encode('utf-8'), 0, 0
    while k < len(data):
        e = data.rfind(b'\n', k, k + part) + 1 if len(data) - k > part else len(data)
        assert e > k, 'a line longer than --part-bytes'
        open('%s.%02d' % (out, n), 'wb').write(data[k:e])
        k, n = e, n + 1


main()
