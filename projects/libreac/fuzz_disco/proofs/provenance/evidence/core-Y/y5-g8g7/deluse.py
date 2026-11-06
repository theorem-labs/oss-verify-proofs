#!/usr/bin/env python3
"""deluse.py -- delete a refused definition and every use of it, the way fuzz_grant's A/AE2k.v was hand-adapted.

port_core.py writes `port_core_refused_<hex>` wherever the donor value has no counterpart in the target binary
(for A/AE2k.v: work-grant-D/review.tsv rows "code-no-counterpart" and "data-no-rule").  The marked file does not
compile: `The reference port_core_refused_41950 was not found`.  For a value the target plainly does not hold,
the release rule is not an --override row but deletion: the definition goes, and every use of it goes with it.

What proofs/libreac/fuzz_grant/lib/A/AE2k.v did to work-grant-D/stage-out/A/AE2k.v (stage-out line numbers):

  definitions removed -- the body held a marker
    12  FF_pc_wrap_fopen  := port_core_refused_41950   (fuzz_grant.asan has no fopen/fclose trampoline)
    14  FF_pc_wrap_fclose := port_core_refused_41958
    17  FF_real_fopen     := port_core_refused_93540   (it has no fopen/fclose body either)
    19  FF_real_fclose    := port_core_refused_92ee4
    31  A_RWA     := port_core_refused_20124           (it writes no file: no path, mode, "rwa" or trailer string)
    32  A_WB      := port_core_refused_20e60
    33  A_TRAILER := port_core_refused_20ea0
    34  A_PATH    := port_core_refused_20e00
  uses deleted
    49  tfib_icells: the elements `(FF_got_fclose, FF_real_fclose)` and `(FF_got_fopen, FF_real_fopen)`.  Each
        names a removed definition, so the whole list element goes, with one `; ` separator, and the list stays
        well formed; the four surviving rows keep their order.
  uses set to 0
    52  tfib_K := mkASink ... A_PATH A_WB A_RWA A_TRAILER ...  ->  ... 0 0 0 0 ...  The four sink string fields
        become 0: mkASink's positional arguments are the record's fields, and 0 is asink_syms' "this build holds
        no such string" (fuzz_grant's own line 38 comment says so, and asink_strs is never stated for it).
  grant did two more things that no marker calls for, so this file leaves them to the owner
    22  FF_got_fopen := 0x9e618 and 24 FF_got_fclose := 0x9e620: the GOT cells of the two absent functions.  They
        carry no marker (review.tsv calls stage lines 21/23 "data-DIFFERS"), so they survive here.
    49/52  grant also added `tfib_owned` and passed it as mkASink's 17th argument; that is new text, not a use.

The rule this file implements: a `Definition N ... .` whose body holds one of the marker tokens to resolve is
deleted, and then every use of N:
  * in a Coq list -- `[a; b; ...]`, or a `::` chain -- the whole element that mentions N is removed together with
    one separator, so a first element, a last element and a one-element list all stay well formed;
  * as the value of a record field (`f := N` inside `{| ... |}`) or as a positional argument of a record
    constructor (`mkR ... N ...`), N becomes `0`;
  * anything else is left as it stands and reported as 'cannot delete use of N at line L: <text>'.
Every deletion takes text out of a line and never takes a line out, so the line count does not change and every
line number of the run (review.tsv, required.tsv, a compiler message) still names the same line.  A comment that
stands above a deleted definition is not part of its sentence and stays.

    deluse.py MARKED_FILE MODEL_FILE   # applies it to MARKED_FILE and reports what still differs from MODEL_FILE
"""
import re, sys
from collections import namedtuple

MARKER = re.compile(r"port_core_refused_[0-9a-fA-F]+")
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")
NUMERAL = re.compile(r"0[xX][0-9a-fA-F]+|\d+")
CONSTRUCTOR = re.compile(r"mk[A-Z_][A-Za-z0-9_']*")  # Coq's record-constructor convention: mkASink
OPENERS = ('{|', '(', '[', '{')
CLOSERS = ('|}', ')', ']', '}')
OPS = ('::', ':=', ';', ',', ':', '.', '|', '=')

Tok = namedtuple('Tok', 'kind text start end')


def tokenize(text):
    """every token of a Coq file: comment, string, open, close, op, ident (qualified dots included), num, other."""
    toks, i, n = [], 0, len(text)
    while i < n:
        c = text[i]
        if c.isspace():
            i += 1
            continue
        if text.startswith('(*', i):
            d, j = 1, i + 2
            while j < n and d:
                if text.startswith('(*', j):
                    d, j = d + 1, j + 2
                elif text.startswith('*)', j):
                    d, j = d - 1, j + 2
                else:
                    j += 1
            toks.append(Tok('comment', text[i:j], i, j))
            i = j
            continue
        if c == '"':
            j = text.find('"', i + 1)
            j = n if j < 0 else j + 1
            toks.append(Tok('string', text[i:j], i, j))
            i = j
            continue
        hit = next((o for o in OPENERS if text.startswith(o, i)), None)
        if hit:
            toks.append(Tok('open', hit, i, i + len(hit)))
            i += len(hit)
            continue
        hit = next((o for o in CLOSERS if text.startswith(o, i)), None)
        if hit:
            toks.append(Tok('close', hit, i, i + len(hit)))
            i += len(hit)
            continue
        m = NUMERAL.match(text, i)
        if m:
            toks.append(Tok('num', m.group(0), i, m.end()))
            i = m.end()
            continue
        m = IDENT.match(text, i)
        if m:
            toks.append(Tok('ident', m.group(0), i, m.end()))
            i = m.end()
            continue
        hit = next((o for o in OPS if text.startswith(o, i)), None) or c
        toks.append(Tok('op', hit, i, i + len(hit)))
        i += len(hit)
    return toks


def group_structure(toks):
    """parent[i]: the opener token that encloses token i (-1 at top level); close[i]: an opener's closer."""
    parent, close, stack = [-1] * len(toks), [-1] * len(toks), []
    for i, t in enumerate(toks):
        if t.kind == 'open':
            parent[i] = stack[-1] if stack else -1
            stack.append(i)
            continue
        if t.kind == 'close' and stack:
            close[stack.pop()] = i
        parent[i] = stack[-1] if stack else -1
    return parent, close


def sentences(toks, parent):
    """(first, last) token index of every Coq sentence; `last` is its terminating `.`; comments stay outside."""
    out, start = [], None
    for i, t in enumerate(toks):
        if t.kind == 'comment':
            continue
        if start is None:
            start = i
        if t.kind == 'op' and t.text == '.' and parent[i] == -1:
            out.append((start, i))
            start = None
    if start is not None:
        out.append((start, len(toks) - 1))
    return out


def sentence_head(toks, parent, a, b):
    """(keyword, defined name) of a sentence, both read at its top level, so `#[export] Instance X` works."""
    kw = name = None
    for i in range(a, b + 1):
        if toks[i].kind == 'ident' and parent[i] == -1:
            if kw is None:
                kw = toks[i].text
            else:
                name = toks[i].text
                break
    return kw, name


def body_range(toks, parent, a, b):
    """the tokens after a sentence's top-level `:=`, terminator excluded; the whole sentence when it has none."""
    end = b - 1 if toks[b].kind == 'op' and toks[b].text == '.' else b
    for i in range(a, end + 1):
        if parent[i] == -1 and toks[i].kind == 'op' and toks[i].text == ':=':
            return i + 1, end
    return a, end


def split_items(toks, parent, owner, a, b, sep):
    """split token range [a, b] at the separators that belong to `owner` directly: (items, separators)."""
    seps = [i for i in range(a, b + 1)
            if parent[i] == owner and toks[i].kind == 'op' and toks[i].text == sep]
    items, lo = [], a
    for s in seps:
        items.append((lo, s - 1))
        lo = s + 1
    items.append((lo, b))
    return items, seps


def children(toks, parent, owner, a, b):
    """the direct children of a level: a token of the level itself, or the opener standing for a whole group."""
    return [i for i in range(a, b + 1) if parent[i] == owner and toks[i].kind != 'comment']


def _line_of(text, pos):
    return text.count('\n', 0, pos) + 1


def _line_text(text, pos):
    s = text.rfind('\n', 0, pos) + 1
    e = text.find('\n', pos)
    return text[s:len(text) if e < 0 else e].strip()


def delete_with_uses(text, refused):
    """Delete every `Definition N ... .` whose body holds a token of `refused`, then every use of each N.

    A use inside a Coq list loses its whole element, a use that is a record field's value becomes 0, and any
    other use is returned in the second value as 'cannot delete use of N at line L: <text>'.  Text is removed
    from within lines only: the returned text has exactly as many lines as `text`.
    """
    toks = tokenize(text)
    parent, close = group_structure(toks)
    marker = re.compile(r"\b(?:%s)\b" % '|'.join(re.escape(r) for r in sorted(refused))) if refused else None
    cut = [False] * len(text)      # a character the result drops ('\n' is never dropped)
    put = {}                       # character position -> text the result puts in front of it
    problems = []

    def drop(s, e):
        for i in range(s, e):
            if text[i] != '\n':
                cut[i] = True

    def drop_item(s, e):
        """drop a list element and tidy the whitespace its separator leaves behind."""
        while e < len(text) and text[e] in ' \t':
            e += 1
        if e >= len(text) or text[e] == '\n':
            while s > 0 and text[s - 1] in ' \t':
                s -= 1
        drop(s, e)

    def zero(s, e):
        drop(s, e)
        put[s] = '0'

    # 1. the definitions whose body holds a marker to resolve
    gone, spans = {}, []
    for a, b in sentences(toks, parent):
        kw, name = sentence_head(toks, parent, a, b)
        if kw != 'Definition' or not name or not marker:
            continue
        s, e = toks[a].start, toks[b].end
        if marker.search(text[s:e]):
            gone[name] = _line_of(text, s)
            spans.append((s, e))
            drop(s, e)

    # 2. every use of a deleted name, outside the deleted definitions themselves
    for t, tok in enumerate(toks):
        if tok.kind != 'ident' or tok.text not in gone:
            continue
        if any(s <= tok.start < e for s, e in spans):
            continue
        what = classify_use(toks, parent, close, t)
        if what is None:
            problems.append('cannot delete use of %s at line %d: %s'
                            % (tok.text, _line_of(text, tok.start), _line_text(text, tok.start)))
        elif what[0] == 'item':
            drop_item(what[1], what[2])
        else:
            zero(what[1], what[2])

    out = []
    for i, c in enumerate(text):
        if i in put:
            out.append(put[i])
        out.append(('\n' if c == '\n' else '') if cut[i] else c)
    return ''.join(out), problems


def classify_use(toks, parent, close, t):
    """What to do with the use at token `t`: ('item', s, e) to drop a list element, ('zero', s, e) to put 0
    in its place, or None when no rule fits.  Levels are walked from the innermost group outwards, so a use in a
    tuple inside a list drops the tuple, not just the name."""
    chain, g = [], parent[t]
    while g != -1:
        chain.append(g)
        g = parent[g]
    for owner in chain + [-1]:
        if owner == -1:
            sa, sb = sentence_of(toks, parent, t)
            if sa is None:
                return None
            a, b = body_range(toks, parent, sa, sb)
        else:
            a, b = owner + 1, close[owner] - 1
            if close[owner] < 0:
                a, b = owner + 1, len(toks) - 1
        if b < a:
            return None
        here = toks[owner].text if owner != -1 else ''

        if here in ('[', '{|'):
            items, seps = split_items(toks, parent, owner, a, b, ';')
            k = item_of(items, t)
            if k is None:
                return None
            if here == '{|':
                return record_field(toks, parent, owner, items[k], t)
            return list_element(toks, items, seps, k)

        items, seps = split_items(toks, parent, owner, a, b, '::')
        if len(items) > 1:
            k = item_of(items, t)
            if k is not None:
                return list_element(toks, items, seps, k)

        kids = children(toks, parent, owner, a, b)
        if (len(kids) > 1 and toks[kids[0]].kind == 'ident' and CONSTRUCTOR.fullmatch(toks[kids[0]].text)
                and not any(toks[i].kind == 'op' for i in kids)):
            if t in kids[1:]:
                return ('zero', toks[t].start, toks[t].end)
            return None
    return None


def sentence_of(toks, parent, t):
    for a, b in sentences(toks, parent):
        if a <= t <= b:
            return a, b
    return None, None


def item_of(items, t):
    for k, (lo, hi) in enumerate(items):
        if lo <= t <= hi:
            return k
    return None


def list_element(toks, items, seps, k):
    """drop element k with one separator, so the list stays well formed whether it is first, last or alone."""
    lo, hi = items[k]
    if hi < lo:
        return None
    if len(items) == 1:
        return ('item', toks[lo].start, toks[hi].end)
    if k < len(items) - 1:
        return ('item', toks[lo].start, toks[seps[k]].end)
    return ('item', toks[seps[k - 1]].start, toks[hi].end)


def record_field(toks, parent, owner, item, t):
    """`f := N` becomes `f := 0`; a field whose value is more than the name alone is left to the caller."""
    lo, hi = item
    for i in range(lo, hi + 1):
        if parent[i] == owner and toks[i].kind == 'op' and toks[i].text == ':=':
            value = children(toks, parent, owner, i + 1, hi)
            if value == [t]:
                return ('zero', toks[t].start, toks[t].end)
            return None
    return None


def defined_names(text):
    """name -> line, for every Definition/Instance/Lemma the file states, in the order it states them."""
    toks = tokenize(text)
    parent, _ = group_structure(toks)
    out = {}
    for a, b in sentences(toks, parent):
        kw, name = sentence_head(toks, parent, a, b)
        if kw in ('Definition', 'Instance', 'Lemma', 'Theorem', 'Fixpoint', 'Axiom', 'Parameter') and name:
            out[name] = _line_of(text, toks[a].start)
    return out


def list_elements(text):
    """name -> the elements of a definition whose body is one Coq list, each with its whitespace collapsed."""
    toks = tokenize(text)
    parent, close = group_structure(toks)
    out = {}
    for a, b in sentences(toks, parent):
        kw, name = sentence_head(toks, parent, a, b)
        if kw != 'Definition' or not name:
            continue
        ba, bb = body_range(toks, parent, a, b)
        if ba > bb or toks[ba].kind != 'open' or toks[ba].text != '[' or close[ba] != bb:
            continue
        items, _ = split_items(toks, parent, ba, ba + 1, bb - 1, ';')
        out[name] = [' '.join(text[toks[lo].start:toks[hi].end].split()) for lo, hi in items if lo <= hi]
    return out


def main(argv):
    if len(argv) != 3:
        sys.exit('usage: deluse.py MARKED_FILE MODEL_FILE')
    marked, model = argv[1], argv[2]
    with open(marked) as f:
        text = f.read()
    with open(model) as f:
        want = f.read()
    refused = set(MARKER.findall(text))
    print('%s: %d marker token(s): %s' % (marked, len(refused), ', '.join(sorted(refused)) or '-'))
    out, problems = delete_with_uses(text, refused)
    left = MARKER.findall(out)
    print('markers left: %d%s' % (len(left), '' if not left else ' (' + ', '.join(sorted(set(left))) + ')'))
    print('lines: %d in, %d out' % (text.count('\n'), out.count('\n')))
    print('cannot delete: %d' % len(problems))
    for p in problems:
        print('  ' + p)

    got_names, want_names = defined_names(out), defined_names(want)
    extra = [n for n in got_names if n not in want_names]
    missing = [n for n in want_names if n not in got_names]
    print('defined names vs %s:' % model)
    print('  only in the result: %s' % (', '.join('%s (line %d)' % (n, got_names[n]) for n in extra) or '-'))
    print('  only in the model:  %s' % (', '.join('%s (line %d)' % (n, want_names[n]) for n in missing) or '-'))
    got_lists, want_lists = list_elements(out), list_elements(want)
    print('list elements:')
    for name in sorted(set(got_lists) | set(want_lists)):
        g, w = got_lists.get(name), want_lists.get(name)
        if g is None or w is None:
            print('  %s: only in %s (%d element(s))' % (name, 'the result' if w is None else 'the model',
                                                        len(g if w is None else w)))
        elif g == w:
            print('  %s: same, %d element(s)' % (name, len(g)))
        else:
            print('  %s: only in the result: %s' % (name, ' | '.join(x for x in g if x not in w) or '-'))
            print('  %s: only in the model:  %s' % (name, ' | '.join(x for x in w if x not in g) or '-'))
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
