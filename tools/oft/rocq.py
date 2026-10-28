"""Rocq source as the tools read it: its comments (nested) and string literals, lexed the way Rocq lexes them."""
import re

_SPECIAL = re.compile(r'\(\*|\*\)|"')
_BLANK = re.compile(r"[^\n]")
# Rocq's blanks: space, tab, line feed and carriage return.  A run of them outside a string literal is one space in the
# code; any other character, a form feed included, is kept.
_WHITE = re.compile(r"[ \t\n\r]+")
_BLANKS = " \t\n\r"


def tokens(text):
    """(kind, piece, in_comment) for each piece of text, in order.  kind is "open" or "close" for a comment's
    brackets, "string" for a string literal ("" inside one is a quote), and "text" for anything else.  Rocq lexes
    string literals inside comments too, so a "*)" in one does not close its comment.  An unclosed comment or string
    runs to the end of the text."""
    i, depth, n = 0, 0, len(text)
    while i < n:
        m = _SPECIAL.search(text, i)
        j = m.start() if m else n
        if j > i:
            yield "text", text[i:j], depth > 0
        if m is None:
            return
        tok = m.group()
        if tok == "(*":
            depth += 1
            yield "open", tok, True
            i = j + 2
        elif tok == "*)":
            yield ("close", tok, True) if depth else ("text", tok, False)
            depth = max(depth - 1, 0)
            i = j + 2
        else:
            k = j + 1
            while True:
                k = text.find('"', k)
                if k < 0:
                    k = n
                    break
                if not text.startswith('""', k):
                    k += 1
                    break
                k += 2
            yield "string", text[j:k], depth > 0
            i = k


def strip(text, comments=True, strings=True):
    """Text with string literals blanked unless strings=False, and comments (nested) too unless comments=False;
    lines and offsets kept."""
    return "".join(_BLANK.sub(" ", piece) if (strings and kind == "string") or (comments and inside) else piece
                   for kind, piece, inside in tokens(text))


def code(text):
    """The code of a Rocq file: each comment taken as one space, each run of blanks outside a string literal as one
    space, none at either end, and every string literal as it is.  Two files with the same code differ only in their
    comments and their layout.

    Rocq opens a comment at a `(*` only where a token starts: a declared token such as `tok(*` takes the `(*` into
    itself.  So a comment counts as one only when its `(*` starts the text or follows a blank or the end of another
    comment; any other is kept as code, which can make a fingerprint change more often, never less.  text must be
    read without newline translation, so that a carriage return in a string literal is kept."""
    parts, run = [], []
    depth, kept = 0, False
    for kind, piece, _inside in tokens(text):
        if kind == "open" and depth == 0:
            # what precedes the `(*` here: a blank, nothing, or the one space a stripped comment left
            kept = (run[-1] if run else parts[-1] if parts else " ")[-1] not in _BLANKS
        if kind == "open":
            depth += 1
        elif kind == "close":
            depth -= 1
        if (depth > 0 or kind == "close") and not kept:
            run.append(" ")
        elif kind == "string":
            parts += [_WHITE.sub(" ", "".join(run)), piece]
            run = []
        else:
            run.append(piece)
        if depth == 0:
            kept = False
    parts.append(_WHITE.sub(" ", "".join(run)))
    parts[0] = parts[0].lstrip(" ")
    parts[-1] = parts[-1].rstrip(" ")
    return "".join(parts)
