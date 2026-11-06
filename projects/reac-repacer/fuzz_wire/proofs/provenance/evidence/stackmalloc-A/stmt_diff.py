#!/usr/bin/env python3
"""stmt_diff.py BEFORE.v AFTER.v -- the statements of a Rocq file before and after a proof-body change, compared byte
for byte. The text is read with comments removed (nested `(* *)`, strings kept) and cut into sentences at a `.` that
ends a sentence (followed by whitespace or the end of the text). A STATEMENT is a sentence that opens with a
declaration keyword (Lemma, Theorem, Corollary, Proposition, Fact, Remark, Example, Definition, Fixpoint,
CoFixpoint, Inductive, Record, Structure, Class, Instance, Let, Ltac, Notation, Hypothesis, Variable, Context,
Section, End, Module, Local, Global, #[...]) or a vernacular (From, Require, Import, Export, Open, Set, Unset,
Arguments, Opaque, Transparent, Hint): everything a proof-body change must not touch. Every other sentence is a proof
step. Prints the counts and every statement that differs (exit 1 if any does); the statements are compared as BYTES
(whitespace included) and, apart from that, as token streams (whitespace collapsed), so a re-wrapped line is shown
as `whitespace only`."""
import re
import sys

KW = re.compile(r'^(?:#\[[^\]]*\]\s*)?(?:Local\s+|Global\s+|Program\s+)?(?:Lemma|Theorem|Corollary|Proposition|Fact|Remark|'
                r'Example|Definition|Fixpoint|CoFixpoint|Inductive|Record|Structure|Class|Instance|Let|Ltac|Notation|'
                r'Hypothesis|Hypotheses|Variable|Variables|Context|Section|End|Module|From|Require|Import|Export|Open|'
                r'Close|Set|Unset|Arguments|Opaque|Transparent|Hint|Existing|Coercion|Infix|Declare)\b')


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


def sentences(t):
    out, start = [], 0
    for m in re.finditer(r'\.(?=\s|$)', t):
        out.append(t[start:m.end()].strip('\n'))
        start = m.end()
    return [s for s in (x.strip() for x in out) if s]


def statements(path):
    ss = sentences(strip(open(path, encoding='utf-8').read()))
    return [s for s in ss if KW.match(s)], len(ss)


def main():
    a, na = statements(sys.argv[1])
    b, nb = statements(sys.argv[2])
    diffs = []
    for i in range(max(len(a), len(b))):
        x = a[i] if i < len(a) else None
        y = b[i] if i < len(b) else None
        if x != y:
            ws = x is not None and y is not None and x.split() == y.split()
            diffs.append((i, ws, x, y))
    print('stmt_diff: %s: %d sentences, %d statements; %s: %d sentences, %d statements; statements that differ: %d '
          '(whitespace only: %d)' % (sys.argv[1], na, len(a), sys.argv[2], nb, len(b), len(diffs),
                                      sum(1 for d in diffs if d[1])))
    for i, ws, x, y in diffs:
        print('  statement %d: %s\n    before: %s\n    after:  %s' % (i + 1, 'whitespace only' if ws else 'TEXT DIFFERS',
                                                               (x or '-')[:200].replace('\n', '\\n'),
                                                               (y or '-')[:200].replace('\n', '\\n')))
    sys.exit(1 if diffs else 0)


if __name__ == '__main__':
    main()
