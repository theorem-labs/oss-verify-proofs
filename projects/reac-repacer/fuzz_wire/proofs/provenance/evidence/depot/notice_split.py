#!/usr/bin/env python3
"""notice_split.py LIB_A FILE.v... [--apply] -- put our port's notice outside the donor's multi-line notice.

In each FILE (relative to LIB_A), line 3 opens the donor's `(* Modified by Theorem Labs, ...` notice and does not close
it, and line 4 is OUR port's one-line notice `(* Modified by Theorem Labs, ...: copied from proofs/libreac/fuzz_knock/...
*)`, a whole comment inside the donor's. The run moves line 4, byte-unchanged, to the line directly after the line that
closes line 3's comment, so each notice is its own comment, in the same order (the donor's first, then ours).
It REFUSES (exit 1, nothing written) unless, for every file:
  - line 3 opens a comment that line 3 does not close, and line 4 is a complete comment starting `(* Modified by`;
  - after the move, the line count is the same, lines 1-2 (Copyright / SPDX) are byte-identical, the moved line is
    byte-identical, and every other line keeps its bytes and its order;
  - the file's token stream with comments stripped (nested `(* *)`, strings kept) is equal before and after.
Without --apply it prints, per file, the closing line and the checks.

notice_split.py --embedded LIB_A FILE.v... [--apply] -- the second mode: line 3 of FILE is our `(* Modified by Theorem
Labs, YYYY-MM: new file, written by ...` notice, and the same comment runs on into the file's documentation, so the
notice's end cannot be read. The notice becomes its own one-line comment and the documentation a second comment
directly after it, the same cut as image B's twins:
  (1) line 3 has `: ` after `written by `: the notice is line 3 up to that FIRST `: ` (the attribution), closed with
      ` *)`; the rest of line 3, after the `: `, opens the second comment as `(* ` + rest;
  (2) line 3 has no `: ` after `written by ` (the attribution runs on into line 4): the WHOLE of line 3 is the notice,
      closed with ` *)`, and a bare `(*` line opens the second comment before line 4.
Every other line is byte-unchanged and the comment-stripped token stream is equal; a line 3 that is already a closed
one-line notice is left as it is (a second run changes nothing); a file whose line 3 is not that notice is refused."""
import sys


def strip(t):
    o, d, i, s = [], 0, 0, False
    while i < len(t):
        if not s and t.startswith('(*', i):
            d += 1; i += 2; continue
        if not s and d and t.startswith('*)', i):
            d -= 1; i += 2; continue
        if d == 0:
            if t[i] == '"':
                s = not s
            o.append(t[i])
        i += 1
    return ''.join(o)


def depth_after(lines, upto, start=0):
    """the comment depth after lines[start:upto] (0-based, upto exclusive)"""
    d, s = 0, False
    t = '\n'.join(lines[start:upto])
    i = 0
    while i < len(t):
        if not s and t.startswith('(*', i):
            d += 1; i += 2; continue
        if not s and d and t.startswith('*)', i):
            d -= 1; i += 2; continue
        if d == 0 and t[i] == '"':
            s = not s
        i += 1
    return d


def split(t):
    L = t.split('\n')
    if not L[2].startswith('(* Modified by') or depth_after(L, 3, 2) != 1:
        raise ValueError('line 3 does not open an unclosed notice')
    if not (L[3].startswith('(* Modified by') and depth_after([L[3]], 1) == 0 and L[3].rstrip().endswith('*)')):
        raise ValueError('line 4 is not a whole one-line notice')
    rest = [L[2]] + L[4:]
    close = next((k for k in range(1, len(rest) + 1) if depth_after(rest, k) == 0), None)
    if close is None:
        raise ValueError("line 3's comment never closes")
    # rest[0] is line 3; rest[j] (j >= 1) is line j + 4 (1-based). The closing line is rest[close - 1].
    close_line = 3 if close == 1 else close + 3
    new = L[:3] + L[4:close_line] + [L[3]] + L[close_line:]
    return '\n'.join(new), close_line


def check(old, new, close_line):
    a, b = old.split('\n'), new.split('\n')
    errs = []
    if len(a) != len(b):
        errs.append('line count %d -> %d' % (len(a), len(b)))
    if a[:2] != b[:2]:
        errs.append('lines 1-2 changed')
    if b[close_line - 1] != a[3]:
        errs.append('the moved line is not byte-identical')
    if [x for i, x in enumerate(a) if i != 3] != [x for i, x in enumerate(b) if i != close_line - 1]:
        errs.append('another line changed or moved')
    if strip(old).split() != strip(new).split():
        errs.append('the comment-stripped token stream differs')
    return errs


def selftest():
    old = ('(* Copyright *)\n(* SPDX *)\n(* Modified by X: donor notice,\n(* Modified by Y: our notice. *)\n'
           '   more donor text *)\nDefinition a := 1.\n')
    new, c = split(old)
    assert c == 5 and new.split('\n')[4] == '(* Modified by Y: our notice. *)' and not check(old, new, c), (new, c)
    bad = old.replace('Definition a := 1.', 'Definition a := 2.')
    assert check(old, bad, c), 'a code change must be seen'
    try:
        split('(* C *)\n(* S *)\n(* Modified by X: closed. *)\n(* Modified by Y: ours. *)\n')
        raise AssertionError('a closed line 3 must be refused')
    except ValueError:
        pass
    print('notice_split: self-test 3 cases OK')


def split_embedded(t):
    """(new text, mode) for the --embedded cut; mode 0 = line 3 already a closed one-line notice (unchanged)"""
    L = t.split('\n')
    l3 = L[2] if len(L) > 2 else ''
    if not (l3.startswith('(* Modified by Theorem Labs, ') and 'written by ' in l3):
        raise ValueError('line 3 is not our `(* Modified by Theorem Labs, ... written by` notice')
    if depth_after([l3], 1) == 0 and l3.rstrip().endswith('*)'):
        return t, 0
    if depth_after([l3], 1) != 1:
        raise ValueError('line 3 does not open exactly one unclosed comment')
    w = l3.index('written by ') + len('written by ')
    k = l3.find(': ', w)
    if k >= 0:
        new = L[:2] + [l3[:k] + ' *)', '(* ' + l3[k + 2:]] + L[3:]
        return '\n'.join(new), 1
    new = L[:2] + [l3 + ' *)', '(*'] + L[3:]
    return '\n'.join(new), 2


def check_embedded(old, new, mode):
    a, b = old.split('\n'), new.split('\n')
    errs = []
    if mode and (a[:2] != b[:2] or a[3:] != b[4:] or len(b) != len(a) + 1):
        errs.append('a line other than line 3 changed')
    if strip(old).split() != strip(new).split():
        errs.append('the comment-stripped token stream differs')
    if mode and split_embedded(new)[1] != 0:
        errs.append('a second run would change the file')
    return errs


def selftest_embedded():
    n1 = ('(* C *)\n(* S *)\n(* Modified by Theorem Labs, 2026-10: new file, written by a lane L1 (K) for M: the\n'
          '   documentation of f. *)\nDefinition f := 1.\n')
    w1, m1 = split_embedded(n1)
    assert m1 == 1 and w1.split('\n')[2:4] == ['(* Modified by Theorem Labs, 2026-10: new file, written by a lane L1 (K) '
                                               'for M *)', '(* the'] and not check_embedded(n1, w1, m1), w1
    n2 = ('(* C *)\n(* S *)\n(* Modified by Theorem Labs, 2026-10: new file, written by a lane L2 for the\n'
          '   chain: the documentation of g. *)\nDefinition g := 2.\n')
    w2, m2 = split_embedded(n2)
    assert m2 == 2 and w2.split('\n')[2:5] == ['(* Modified by Theorem Labs, 2026-10: new file, written by a lane L2 for '
                                               'the *)', '(*', '   chain: the documentation of g. *)'] \
        and not check_embedded(n2, w2, m2), w2
    assert split_embedded(w1) == (w1, 0) and split_embedded(w2) == (w2, 0)
    try:
        split_embedded('(* C *)\n(* S *)\n(* some other comment\n *)\n')
        raise AssertionError('a line 3 that is not the notice must be refused')
    except ValueError:
        pass
    print('notice_split --embedded: self-test 4 cases OK')


def main():
    if sys.argv[1:2] == ['--embedded']:
        return main_embedded(sys.argv[2:])
    selftest()
    lib = sys.argv[1]
    apply = '--apply' in sys.argv[2:]
    files = [f for f in sys.argv[2:] if f != '--apply']
    out, bad = {}, []
    for f in files:
        old = open('%s/%s' % (lib, f), encoding='utf-8').read()
        try:
            new, c = split(old)
        except ValueError as e:
            bad.append('%s: %s' % (f, e)); continue
        errs = check(old, new, c)
        print('%s: line 4 moves after line %d (the close of line 3\'s comment); %s' % (
            f, c, 'checks OK' if not errs else '; '.join(errs)))
        if errs:
            bad.append(f)
        out[f] = new
    if bad:
        sys.exit('notice_split: REFUSED, nothing written: %s' % '; '.join(bad))
    if apply:
        for f, new in out.items():
            open('%s/%s' % (lib, f), 'w', encoding='utf-8').write(new)
        print('notice_split: %d file(s) written' % len(out))


def main_embedded(args):
    selftest_embedded()
    lib = args[0]
    apply = '--apply' in args[1:]
    files = [f for f in args[1:] if f != '--apply']
    out, bad = {}, []
    for f in files:
        old = open('%s/%s' % (lib, f), encoding='utf-8').read()
        try:
            new, mode = split_embedded(old)
        except ValueError as e:
            bad.append('%s: %s' % (f, e)); continue
        errs = check_embedded(old, new, mode)
        print('%s: %s; %s' % (f, {0: 'line 3 is already a closed notice: unchanged',
                                  1: 'cut (1): the notice is line 3 up to its first `: ` after `written by`',
                                  2: 'cut (2): the whole of line 3 is the notice, a bare `(*` line opens the rest'}[mode],
                              'checks OK' if not errs else '; '.join(errs)))
        if errs:
            bad.append(f)
        out[f] = new
    if bad:
        sys.exit('notice_split --embedded: REFUSED, nothing written: %s' % '; '.join(bad))
    if apply:
        for f, new in out.items():
            open('%s/%s' % (lib, f), 'w', encoding='utf-8').write(new)
        print('notice_split --embedded: %d file(s) written' % len(out))


if __name__ == '__main__':
    main()
