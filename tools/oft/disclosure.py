"""What no file a release keeps may disclose, and the search for it.

A release leaves out what facts.hold holds back: a project held whole (by a finding, or `release: private`), the
statements open findings of an enrolled project hold back, and every finding that holds its project back.  No file the
release keeps may name any of them or carry a holding finding's evidence, whole or in part.  `needles` builds what to
look for, `found` judges one file and `search` judges every file the cut keeps or writes.

What it catches is a closed list (frozen on 2026-10-26: findings/ never
ships, a held project is removed or cut to a held page, and every release pull request is reviewed, so this check is a
safety net for the common accident, not the protection).  A copy of a holding finding's evidence is caught

1. whole, or any part of WINDOW or more long characters, or a whole short unit (a hunk's lines, its added text or its
   removed text, an input's printable payload run of PAYLOAD_MIN or more characters);
2. with changes of white space, line endings, case or Unicode normal form;
3. in UTF-8, UTF-16 or UTF-32;
4. through HTML character references, percent escapes (which keep their bytes), and the backslash escapes of C,
   Python, JSON and YAML, octal and YAML's `\\0`, `\\a`, `\\e` and `\\_` among them;
5. with the line prefixes of Markdown quoting and code comments;
6. as hex in the layouts of `xxd -p` and `xxd` (with item 5's marks on each line, too), and as a C array of bytes
   (`xxd -i`, Python's hex(), or decimal items);
7. by an input's exact bytes or its SHA-256.

Each item applies on its own: a combination of items is out of scope, and so is
everything else: word and colour diffs, quoted-printable, a `+` for a blank in a URL query, the layouts of `od` and
`hexdump`, per-line decorations (`cat -n`, `cat -A`, `git blame`, `git grep`), base64 (YAML's `!!binary` among them),
and anything retyped or paraphrased.

Each reading of a file's bytes (UTF-8, and UTF-16 and UTF-32 from every offset) is decoded: HTML character references,
percent escapes and backslash escapes (JSON's `\\uXXXX` among them) to a bounded fixed point, by a decoder that never
raises, then NFKC-normalised and case-folded.  A backslash before an octal digit is read as C and Python read it (one
octal escape), and, when an input holds a NUL before an octal digit, also as YAML reads `\\0` then (_yaml_nul).
Evidence is compared in three forms:

- The long form (canonical): only the alphanumeric characters (`str.isalnum`), which removes every comment prefix,
  quote, doubled quote, punctuation, white space, zero-width character and soft hyphen.  Long evidence is matched in
  windows: every run of WINDOW long characters of it is a key of one hash table, except a run made only of
  OUTCOME_WORDS (build names, outcomes, connectives, digits), which every counterexample note writes, and a run of
  fewer than MIN_DISTINCT different characters, which is chance text (one repeated character, `0000`, `abab`).  A
  16-character index of the windows is probed every 17 positions of a file's long text and each probe hit is checked
  against the windows around it, so every WINDOW-character copy is found, the search is linear in the file, and it does
  no work per window.
- The punctuation form: each line without the marks a copy puts at its ends (_LINE_START, _LINE_END: diff's `+`, `-`,
  `<` and `>`, a reply quote's `>`, a table's `|`, a comment's `#`, `//`, `*`, `;` or `(* *)`, a string's quotes), then
  without white space, with a run of one quote read as one.  A backslash before a line break keeps the break here, so
  each line of a continued line keeps its marks.  Short evidence, whose punctuation the long form would drop
  (`$(join a,b)` is `joinab` there), counts whole in it: a substring of PAYLOAD_MIN characters or more, whatever its
  characters.  It counts in the plain form too, the text without white space alone, so a copy rewrapped or folded by
  YAML's writer, whose new line may begin with a character a mark would take (`(*t`), counts.
- The bytes a file spells, one byte per character below U+0100: its own; what each decoding round reads; what each
  decoder alone reads (_alone: the backslash escapes, a backslash before a line break joining the lines and the blanks
  after it as YAML's writer folds a string; the character references; the percent escapes, one byte each), so that no
  decoder reads the bytes another wrote; with `\\0` before an octal digit read as YAML reads it (a NUL and the
  digit), when an input holds that byte pair; each of these with adjacent string literals joined and with a C array's
  `0xNN` and `0xN` items decoded, and as it is; and the bytes of its `xxd` and `xxd -p` lines and of its decimal arrays
  (in brackets or braces).  An input's exact bytes and its WINDOW-byte runs (of MIN_DISTINCT different bytes) are
  matched there, so Python's repr, a C string of `\\x` or octal escapes, YAML's escapes and this repository's YAML
  writer, a percent-escaped copy, and `xxd`, `xxd -p` and `xxd -i` of an input count.

The evidence of a finding that holds its project back is: its summary, whole and sentence by sentence, and each patch's
subject and the sentences of its commit message, in windows; for each hunk, its lines in diff order (context
included), its removed text and its added text, whole, the windows of its removed text and of its added text, and the
windows of its new side that upstream text does not hold (_new_side_windows); and for each input that is more than the
driver's header, its bytes and byte windows, its SHA-256, the windows of its hex, and each printable run of its
payload, whole (from PAYLOAD_MIN characters) and in windows.  A digest, recorded or computed, counts by its name and the
windows of its hex.

Names (slugs, patch file names, digests, held fuzz targets and statements) count only at a name boundary, in the
file's path and text with escapes decoded, case folded, every dash read as `_`, each path resolved, and each line break
and each blank beside a `/` deleted.  A name followed by a source or header suffix (`openssl/x509.h`) is a file name.
"""
import codecs
import collections
import hashlib
import html.entities
import os
import posixpath
import re
import stat
import unicodedata
import urllib.parse

from . import facts, lint, names, paths, urls

# the shortest run of long characters that counts as a copy of evidence
WINDOW = 32
# the shortest whole unit, in characters of the punctuation form, that counts as a copy of evidence: an input's
# printable payload run, and a hunk's lines, removed text or added text
PAYLOAD_MIN = 8
# the fewest distinct characters (or bytes) that make a window evidence; smaller runs are chance text.
# A whole unit counts whatever its characters
MIN_DISTINCT = 8
# the most decoding rounds: each round that changes the text shortens it, and text people and tools write reaches its
# fixed point in two or three, so the bound only stops a crafted nest of escapes from costing a round per character
DECODE_ROUNDS = 8
# the SHA-256 of empty output, in every finding record and in this repository's own tools, which reveals nothing
EMPTY_SHA256 = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
# where a fuzz target's own files live: a file under one of these may name a statement of it without its project
UNIT_DIRS = ("proofs", "projects", "counterexamples", "patches")
# what every counterexample note and finding summary writes about a run: build names, outcomes, articles, connectives
# and numbers.  A window made only of these words says what the statements already say (`the plain and ubsan builds
# exit 0, the control ...` is in public counterexample notes), so it is no evidence; a window with one other word is.
OUTCOME_WORDS = frozenset("""
    plain ubsan asan build builds binary binaries harness run runs ran input inputs control controls payload
    abort aborts aborted exit exits exited status code signal sigabrt sigsegv sigbus sigill sigfpe crash crashes
    crashed halt halts halted hang hangs hung timeout timeouts trap traps trapped fail fails failed pass passes passed
    stdout stderr output outputs same different differ differs agree agrees disagree disagrees normal normally
    the a an and or but while both all each every other its their it this that with without on of in to for from by
    is are was were be been does do did not no only also then so as at one two three four once twice
""".split())

# a name needle: its form, what an error calls it, whether it is relative (no count after a `/`), and the
# (path prefixes, Rocq modules) of the files it counts in, or None for every file
Name = collections.namedtuple("Name", "text label relative scope")
Exact = collections.namedtuple("Exact", "data label")
# names: [Name]; exact: [Exact]; windows: {long window: {label}}; whole: {(punctuation-form unit, its plain form):
# {label}}; byte_windows: {WINDOW-byte run: {label}}.  needles() completes them (_complete): whole becomes
# [(unit, plain, its long form, {label})], grams and byte_grams index the windows by their _GRAM-long runs, which
# `found` probes every _STRIDE positions before it looks a window up (so every WINDOW-long copy is found), and
# nul_digit says whether an input holds a NUL before an octal digit, the one byte pair YAML's writer and a C reader
# spell otherwise
Needles = collections.namedtuple("Needles", "names exact windows whole byte_windows grams byte_grams nul_digit")
_GRAM = 16
_STRIDE = WINDOW - _GRAM + 1

_BOMS = ((codecs.BOM_UTF32_LE, "utf-32-le"), (codecs.BOM_UTF32_BE, "utf-32-be"), (codecs.BOM_UTF8, "utf-8"),
         (codecs.BOM_UTF16_LE, "utf-16-le"), (codecs.BOM_UTF16_BE, "utf-16-be"))
_WIDE = (("utf-16-le", 2), ("utf-16-be", 2), ("utf-32-le", 4), ("utf-32-be", 4))
# every dash a reader takes for `-` but `-` itself, the soft hyphen among them
_DASHES = "\u00ad\u2010\u2011\u2012\u2013\u2014\u2015\u2212"
_IDENT = frozenset("abcdefghijklmnopqrstuvwxyz0123456789_")
_SOURCE_SUFFIXES = frozenset(("c", "h", "cc", "cpp", "cxx", "hpp", "hh", "inc", "ipp", "hxx"))
_SUFFIX = re.compile(r"[a-z0-9]+")
_NOT_ALNUM = re.compile(r"[\W_]+")
_ASCII_NOT_ALNUM = bytes(c for c in range(128) if not chr(c).isalnum())
_FORMAT = re.compile("[\u0600-\u0605\u061c\u06dd\u070f\u180e\u200b-\u200f\u202a-\u202e\u2060-\u2064"
                     "\u2066-\u206f\ufeff\ufff9-\ufffb]")
_ESCAPES = (r"u[dD][89abAB][0-9a-fA-F]{2}\\u[dD][c-fC-F][0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|U[0-9a-fA-F]{8}"
            r"|x[0-9a-fA-F]{2}|\r?\n[ \t]*")
# a backslash escape, as C and Python read it (octal: `\012` is one escape) and as YAML reads it (`\0` is a NUL, and
# the digits after it are text)
_BACKSLASH = {True: re.compile(r"\\(%s|[0-7]{1,3}|.)" % _ESCAPES, re.S),
              False: re.compile(r"\\(%s|.)" % _ESCAPES, re.S)}
# where YAML's writer and a C reader read a string's bytes otherwise: `\0` before an octal digit, which YAML reads as
# a NUL and the digit (it writes no other escape that looks octal)
_YAML_NUL = re.compile(r"\\0[0-7]")
_NUL_DIGIT = re.compile(rb"\x00[0-7]")
# a percent escape
_PERCENT = re.compile(r"%[0-9a-fA-F]{2}")
# the one-letter escapes of C, Python, JSON and YAML that stand for a control, space or line character
_CONTROL = {"n": "\n", "r": "\r", "t": "\t", "f": "\f", "v": "\v", "b": "\b", "0": "\0", "a": "\a", "e": "\x1b",
            "_": "\xa0", "N": "\x85", "L": "\u2028", "P": "\u2029"}
# the marks a copy puts at the start of a line (diff's `+`, `-`, `<` and `>`, a reply quote's `>`, a table's `|`, a
# comment's `#`, `//`, `*`, `;` or `(*`, a string's quotes) and at its end (a table's `|`, a comment's `*/` or `*)`, a
# string's quotes), with white space
_LINE_START = " \t\f\v+-<>|#/*;(\"'`"
_LINE_END = " \t\f\v|*/)\"'`"
_WHITE = re.compile(r"\s+")
_QUOTE_RUN = re.compile(r"(['\"])\1+")
# an item of a C array of bytes: `0xNN` (`xxd -i`) or `0xN` (Python's hex()), with its comma and the white space around
# it
_HEX_ITEM = re.compile(r"0[xX]([0-9a-fA-F]{1,2})(?![0-9a-fA-F])(?:\s*,\s*)?")
# a C array or a list of bytes in decimal (`{72, 101, 108, 108}`, json.dumps of a list of bytes): four items or more
# after the bracket or brace that opens it
_DECIMAL_ITEMS = re.compile(r"[\[{]\s*((?:[0-9]{1,3}\s*,\s*){3,}[0-9]{1,3})(?![\w.])")
_DIGITS = re.compile(r"\d+")
# a backslash that ends a line of a string, after a quote on that line: C and Python continue a string so, and YAML's
# writer folds one
_QUOTED_BREAK = re.compile(r"[\"'][^\"'\n]*\\\r?\n")
# a line of `xxd`, after the marks a copy puts at its start (item 5's: a quote's `>`, a table's `|`, a comment's `#`,
# `//`, `*`, `;`, `--`, `/*` or `(*`): the offset, the bytes as groups of hex digits one blank apart, then the two
# blanks before the text column (or the line's end).  Matched in "\n" + text, so the search looks for line breaks alone
_XXD_LINE = re.compile(r"\n[ \t>|#/*;(-]*[0-9a-fA-F]{4,16}:((?: [0-9a-fA-F]{2,8})+)(?=  |[ \t\r]*(?:\n|\Z))")
# a line of `xxd -p`, between the marks a copy puts at its start and its end (a comment's `*/` or `*)`): hex digits
# alone, two to a byte (in "\n" + text too).  The blanks before an end mark are in one optional group with it, so no
# two blank runs stand side by side and a long run of blanks is read in linear time
_PLAIN_HEX_LINE = re.compile(r"\n[ \t>|#/*;(-]*((?:[0-9a-fA-F]{2})+)(?:[ \t]*(?:\*/|\*\)))?[ \t\r]*(?=\n|\Z)")
# the end of a string literal, a line break, and the start of the next (C, Python): a reader joins them.  Only blanks
# before the line break, so a long run of blank lines is read once
_STRING_GLUE = re.compile(r"[\"'][ \t]*\r?\n\s*[bBuUlLrR]?[\"']")
_WRAP_SLASH = re.compile(r"(?<!\s)\s+(?=/)|(?<=/)\s+")
_WORD = re.compile(r"[^\W_]+")
_HUNK = re.compile(r"@@ -\d+(?:,(\d+))? \+\d+(?:,(\d+))? @@")
_STEPPED = re.compile(r"(?<![^\s()\[\]<>\"'`])[^\s()\[\]<>\"'`]*?(?://|/\.|\./)[^\s()\[\]<>\"'`]*")
_SENTENCE = re.compile(r"(?<=[.!?])\s+")


def _code_point(code):
    """The character of code, or U+FFFD when it is no character."""
    return chr(code) if code <= 0x10ffff and not 0xd800 <= code <= 0xdfff else "\ufffd"


def _charref(match):
    """One HTML character reference (a urls.CHARREF match), read as html.unescape reads it, but a numeric one keeps
    its code point (html.unescape reads 128 to 159 as Windows-1252 does, which would lose the byte), and one too long
    for any code point (urls.reference_digits) stays as it is, so int() never reads a long run of digits."""
    s = match.group(1)
    numeric = urls.reference_digits(s)
    if numeric is not None:
        digits, base = numeric
        return match.group() if len(digits) > 7 else _code_point(int(digits, base))
    if s in html.entities.html5:
        return html.entities.html5[s]
    # a name without its `;` (`&ampx`): the longest name it begins with
    for k in range(len(s) - 1, 1, -1):
        if s[:k] in html.entities.html5:
            return html.entities.html5[s[:k]] + s[k:]
    return match.group()


def _escape(match, octal=True, join=False):
    """One backslash escape: a C, Python, JSON or YAML one (`\\n`, `\\t`, `\\f`, `\\v`, `\\b`, `\\a`, `\\e`, `\\0`,
    YAML's `\\_`, `\\N`, `\\L` and `\\P`, `\\uXXXX` with its surrogate pair, `\\UXXXXXXXX`, `\\xXX`, and, when octal,
    the octal escape of C and Python, `\\NNN`); a backslash before a line break, which joins the two lines (C, a shell,
    YAML): with join, the break and the blanks that begin the next line go, as YAML folds a string, and otherwise the
    break stays, so each line keeps the marks a copy puts at its ends; or a backslash before any other character,
    which a reader reads as that character (Markdown, a listing)."""
    s = match.group(1)
    if s[0] in "\r\n":
        return "" if join else "\n"
    if octal and "0" <= s[0] <= "7":
        return chr(int(s, 8))
    if len(s) == 1:
        return _CONTROL.get(s, s)
    if s[0] == "x":
        return chr(int(s[1:], 16))
    if s[0] == "u" and len(s) == 11:
        high, low = int(s[1:5], 16), int(s[7:11], 16)
        return chr(0x10000 + ((high - 0xd800) << 10) + low - 0xdc00)
    return _code_point(int(s[1:], 16))


def _unescaped(text, octal=True, join=False):
    """[text, then the text after each decoding round that changed it]: character references, percent escapes and
    backslash escapes (_escape, with octal and join), until nothing changes or DECODE_ROUNDS rounds have run.  No step
    raises."""
    pattern = _BACKSLASH[octal]

    def escape(match):
        return _escape(match, octal, join)
    out = [text]
    for _ in range(DECODE_ROUNDS):
        t = urls.CHARREF.sub(_charref, text) if "&" in text else text
        t = urllib.parse.unquote(t, errors="replace") if "%" in t else t
        t = pattern.sub(escape, t) if "\\" in t else t
        if t == text:
            break
        out.append(t)
        text = t
    return out


def _yaml_nul(text, steps, nul_digit):
    """The rounds of text (_unescaped) with `\\0` before an octal digit read as YAML reads it, a NUL and the digit,
    where C and Python read one octal escape: only when an input holds that byte pair (nul_digit; no other copy reads
    otherwise) and one of text's rounds (steps) holds such an escape; else None."""
    if nul_digit and any("\\" in s and _YAML_NUL.search(s) for s in steps):
        return _unescaped(text, octal=False)
    return None


def _alone(text, nul_digit):
    """text read by each decoder alone, so that none reads the bytes another one wrote (an input's `\\`, `&lt` or
    `%41`): its backslash escapes, as C and Python read them and, when _yaml_nul would, as YAML reads `\\0` before an
    octal digit, a backslash that ends a line of a string (_QUOTED_BREAK) joining the lines and the blanks after it (C
    and Python continue a string so, and YAML's writer folds one); its character references; and its percent escapes,
    one byte each.  A decoder that changes nothing adds no text."""
    out = []
    if "\\" in text:
        join = ("\\\n" in text or "\\\r\n" in text) and bool(_QUOTED_BREAK.search(text))
        for octal in (True, False) if nul_digit and _YAML_NUL.search(text) else (True,):
            out.append(_BACKSLASH[octal].sub(lambda m, octal=octal: _escape(m, octal, join), text))
    if "&" in text:
        out.append(urls.CHARREF.sub(_charref, text))
    if "%" in text and _PERCENT.search(text):
        out.append(urllib.parse.unquote(text, encoding="latin-1", errors="replace"))
    return [t for t in out if t != text]


def _normal(text):
    """text with its format characters (U+200B and the like) deleted, NFKC-normalised and case-folded.  ASCII text
    holds no format character and NFKC leaves it as it is, so it is only case-folded."""
    if text.isascii():
        return text.lower()
    return unicodedata.normalize("NFKC", _FORMAT.sub("", text)).casefold()


def _decoded(text):
    """text decoded to its fixed point (_unescaped) and normal (_normal)."""
    return _normal(_unescaped(text)[-1])


def _long(decoded):
    """decoded text in the long form: only its alphanumeric characters (ASCII text by bytes.translate, the same set)."""
    if decoded.isascii():
        return decoded.encode("ascii").translate(None, _ASCII_NOT_ALNUM).decode("ascii")
    return _NOT_ALNUM.sub("", decoded)


def _punct(decoded):
    """decoded text in the punctuation form: each line without the marks a copy puts at its ends, then without white
    space, and a run of one quote read as one (this repository's YAML writer doubles `'`)."""
    lines = "".join(line.lstrip(_LINE_START).rstrip(_LINE_END) for line in decoded.splitlines())
    return _QUOTE_RUN.sub(r"\1", _WHITE.sub("", lines))


def _plain(decoded):
    """decoded text without white space, and a run of one quote read as one: the punctuation form of a copy whose line
    breaks fall elsewhere (rewrapped, or folded by YAML's writer), where a line may begin with a character a mark would
    take (`(*t`)."""
    return _QUOTE_RUN.sub(r"\1", _WHITE.sub("", decoded))


def _name_text(decoded):
    """decoded text in the name form: every dash read as `_`.  One str.replace per dash scans in C; a translate table
    looks each character up."""
    decoded = decoded.replace("-", "_")
    if not decoded.isascii():
        for dash in _DASHES:
            decoded = decoded.replace(dash, "_")
    return decoded


def _unwrapped(text):
    """text with every line break, and each blank run beside a `/`, deleted: a reader reads a name through a line break,
    and `zlib / checksum_fuzzer` as one path.  `str.replace` consumes every line break in C; the regex runs only when
    a blank actually borders `/`, so ordinary proof whitespace is not scanned again."""
    text = text.replace("\r", "").replace("\n", "")
    return _WRAP_SLASH.sub("", text) if any(s in text for s in ("/ ", "/\t", " /", "\t/")) else text


def _readings(data):
    """Every text the bytes may be read as: by the byte order mark, if there is one; else UTF-8, and, when the bytes
    hold a NUL, UTF-16 and UTF-32 in both byte orders from each offset a character can start at.  No decoding fails:
    a byte or unit that is no text reads as U+FFFD, which no needle holds."""
    for bom, enc in _BOMS:
        if data.startswith(bom):
            out = [data[len(bom):].decode(enc, "replace")]
            return out if enc == "utf-8" else out + [data.decode("utf-8", "replace")]
    out = [data.decode("utf-8", "replace")]
    if b"\0" in data:
        for enc, width in _WIDE:
            for start in range(width):
                part = data[start:]
                out.append((part + b"\0" * (-len(part) % width)).decode(enc, "replace"))
    return out


def _hex_byte(match):
    return chr(int(match.group(1), 16))


def _dumped(text):
    """The bytes text spells as a hex dump (its `xxd` lines, and its `xxd -p` lines, each in order) and as decimal
    arrays of bytes, each a bytes value; none when it holds none of them."""
    out = []
    lined = "\n" + text
    for pattern in (_XXD_LINE, _PLAIN_HEX_LINE):
        lines = [h for h in (m.group(1).replace(" ", "") for m in pattern.finditer(lined)) if len(h) % 2 == 0]
        if lines:
            out.append(bytes.fromhex("".join(lines)))
    items = []
    for m in _DECIMAL_ITEMS.finditer(text):
        numbers = [int(n) for n in _DIGITS.findall(m.group(1))]
        if max(numbers) < 256:
            items += numbers
    return out + [bytes(items)] if items else out


def _byte_views(data, rounds, alone):
    """The bytes a reader reads a file as, one byte per character below U+0100 (any other reads as `?`): data itself;
    each decoding round of each reading after the first (rounds: each reading's _unescaped, and its _yaml_nul ones);
    each reading read by each decoder alone (alone: _alone); each of these with adjacent string literals joined (C,
    Python), and each of these and each reading with the `0xNN` and `0xN` items of a C array decoded, each kept as it
    is too, so that no step reads the bytes of an input that holds `0x41`, or a quote, a line break and a quote; and
    the hex dumps and decimal arrays of bytes (_dumped) of each reading as it is and as decoded."""
    out = {data}
    texts = {text for steps in rounds for text in steps[1:]} | set(alone)
    for text in texts:
        out.add(text.encode("latin-1", "replace"))
        if "\n" in text and ("\"" in text or "'" in text):
            out.add(_STRING_GLUE.sub("", text).encode("latin-1", "replace"))
    for text in texts | {steps[0] for steps in rounds}:
        if "0x" in text or "0X" in text:
            items = _HEX_ITEM.sub(_hex_byte, text)
            if items != text:
                out.add(items.encode("latin-1", "replace"))
    for text in {text for steps in rounds for text in (steps[0], steps[-1])}:
        out.update(_dumped(text))
    return out


def canonical(data):
    """data (bytes) in the canonical long form: each reading, decoded and kept to its alphanumeric characters, joined
    by NUL characters.  `found` compares its windows in exactly this text; #117 reads it too."""
    return "\0".join(_long(_decoded(t)) for t in _readings(data))


def _name(text, label, relative=False, scope=None):
    """A name needle for text."""
    return Name(_name_text(_decoded(text)), label, relative, scope)


def _window_table(words, label, prose=True, counted=None):
    """{window: {label}}: each WINDOW-character run of words joined that holds MIN_DISTINCT different characters, at
    each offset i for which counted(i) holds (every offset, when counted is None), and, for prose, that holds a
    character of a word of the finding's own (not in OUTCOME_WORDS, not digits)."""
    form = "".join(words)
    if len(form) < WINDOW:
        return {}
    own = None
    if prose:
        # own[i]: how many of the first i characters of form belong to a word of the finding's own
        own = [0]
        for w in words:
            base, mine = own[-1], not (w in OUTCOME_WORDS or w.isdigit())
            own.extend(base + k * mine for k in range(1, len(w) + 1))
    return {window: {label} for i in range(len(form) - WINDOW + 1) for window in (form[i:i + WINDOW],)
            if (own is None or own[i + WINDOW] > own[i]) and (counted is None or counted(i))
            and len(set(window)) >= MIN_DISTINCT}


def _windows(text, label, prose=True):
    """The windows (_window_table) of text's long form.  A hex or a digest is not prose: a low-complexity hex run is
    chance text too, but no outcome word is in it."""
    return _window_table(_WORD.findall(_decoded(text)), label, prose)


def _whole(into, text, label):
    """Add text's punctuation form and its plain form to into ({(unit, plain): {label}}) when the punctuation form has
    at least PAYLOAD_MIN characters.  text is read as followed by a line break, as a copy of it is: a backslash that
    ends its last line joins that line to the next one, in the copy as in the patch, and is not part of what the copy
    shows."""
    decoded = _decoded(text + "\n")
    unit = _punct(decoded)
    if len(unit) >= PAYLOAD_MIN:
        into.setdefault((unit, _plain(decoded)), set()).add(label)


def _grams(windows):
    """The probe index of windows: every _GRAM-long run of every window."""
    return frozenset(w[i:i + _GRAM] for w in windows for i in range(WINDOW - _GRAM + 1))


def _complete(out):
    """out with its whole units as [(unit, its plain form, its long form, {label})] and its probe indexes."""
    return out._replace(whole=[(unit, plain, _long(unit), frozenset(labels))
                               for (unit, plain), labels in sorted(out.whole.items())],
                        grams=_grams(out.windows), byte_grams=_grams(out.byte_windows),
                        nul_digit=any(_NUL_DIGIT.search(e.data) for e in out.exact))


def _merge(into, windows):
    for window, labels in windows.items():
        into.setdefault(window, set()).update(labels)


def _named(text, needle, relative):
    """Whether text holds needle at a name boundary (and, when relative, not after a `/`), not as the stem of a source
    or header file name."""
    i = text.find(needle)
    while i >= 0:
        j = i + len(needle)
        before, after = text[i - 1:i], text[j:j + 1]
        suffix = _SUFFIX.match(text, j + 1) if after == "." else None
        if before not in _IDENT and after not in _IDENT and not (relative and before == "/") \
                and not ("/" in needle and suffix and suffix.group() in _SOURCE_SUFFIXES):
            return True
        i = text.find(needle, i + 1)
    return False


def _resolved(text):
    """Each run a reader follows as a path that resolves to another one, resolved (`.`, `..`, `//`)."""
    return [r for r, run in ((posixpath.normpath(m.group()), m.group()) for m in _STEPPED.finditer(text)) if r != run]


def _window_hits(text, windows, grams):
    """The labels of every window of windows (indexed by grams) that text, a str or bytes, holds.  The index is looked
    up every _STRIDE positions: any WINDOW-long run of text that is a window holds a _GRAM-long run at one of those
    positions, and that run is in the index, so each probe hit is checked against the windows around it, and every
    copy of a window is found wherever it starts."""
    hits, checked, last = set(), set(), len(text) - WINDOW
    for i in range(0, len(text) - _GRAM + 1, _STRIDE):
        if text[i:i + _GRAM] in grams:
            for j in range(max(0, i - WINDOW + _GRAM), min(i, last) + 1):
                if j not in checked:
                    checked.add(j)
                    labels = windows.get(text[j:j + WINDOW])
                    if labels:
                        hits |= labels
    return hits


def found(rel, data, needles):
    """The labels of needles the file at rel, whose bytes are data, holds: a name in its path or text; an exact copy of
    an input or a patch, or a window of an input's bytes, in the bytes it spells; a window of evidence in its long form;
    or a whole unit of evidence in its punctuation form or its plain form, which are built only when the long form
    holds that unit's letters and digits (the long form of a text's punctuation form is its long form)."""
    readings = _readings(data)
    rounds = [_unescaped(t) for t in readings]
    rounds += [r for r in (_yaml_nul(t, steps, needles.nul_digit) for t, steps in zip(readings, rounds)) if r]
    decoded = [_normal(steps[-1]) for steps in rounds]
    hits = set()
    if needles.exact or needles.byte_windows:
        views = _byte_views(data, rounds, [text for t in readings for text in _alone(t, needles.nul_digit)])
        hits.update(e.label for e in needles.exact if any(e.data in v for v in views))
        if needles.byte_windows:
            for view in views:
                hits |= _window_hits(view, needles.byte_windows, needles.byte_grams)
    longs = [_long(t) for t in decoded]
    if needles.windows:
        for long in longs:
            hits |= _window_hits(long, needles.windows, needles.grams)
    wanted = [(unit, plain, labels) for unit, plain, letters, labels in needles.whole
              if any(letters in long for long in longs)]
    if wanted:
        puncts, plains = [_punct(t) for t in decoded], [_plain(t) for t in decoded]
        hits.update(label for unit, plain, labels in wanted
                    if any(unit in p for p in puncts) or any(plain in p for p in plains) for label in labels)
    named = [_name_text(t) for t in [_decoded(rel)] + decoded]
    unwrapped = [_unwrapped(t) for t in named]
    text = "\0".join(named + unwrapped)
    # resolving paths only matters where a held path's last segment is: normpath deletes characters, it adds none
    if any(n.text.rsplit("/", 1)[-1] in text for n in needles.names if "/" in n.text):
        text = "\0".join([text] + [r for t in unwrapped for r in _resolved(t)])
    scoped = {}
    for n in needles.names:
        if n.scope is not None:
            if n.scope not in scoped:
                prefixes, modules = n.scope
                scoped[n.scope] = rel.startswith(prefixes) or any(_named(text, m, False) for m in modules)
            if not scoped[n.scope]:
                continue
        if _named(text, n.text, n.relative):
            hits.add(n.label)
    return hits


def _search_one(root, needles, rel):
    """found for one regular checkout file: an item of the search's forked scan."""
    with open(os.path.join(root, rel), "rb") as fh:
        return found(rel, fh.read(), needles)


def search(root, needles, skip, writes):
    """[(path, label)]: each kept on-disk file or write that holds a needle.  With no needle (nothing held) it reads
    nothing.  The files are independent, so they are judged on lint's forked scanner, on every CPU this process may
    use; the output is sorted after, so it is deterministic.  A path at or under skip, an ignored/generated path, a link
    or a non-regular file is not read."""
    if not any((needles.names, needles.exact, needles.windows, needles.whole, needles.byte_windows)):
        return []
    skip = {s.rstrip("/") for s in skip}
    hits = [(rel, label) for rel, text in sorted(writes.items()) for label in found(rel, text.encode(), needles)]
    files = []
    for d, dirs, fs in os.walk(root):
        rd = os.path.relpath(d, root).replace(os.sep, "/")
        rd = "" if rd == "." else rd + "/"
        dirs[:] = [x for x in dirs if rd + x not in skip and not paths.ignored(rd + x)
                   and not os.path.islink(os.path.join(d, x))]
        for f in sorted(fs):
            rel, full = rd + f, os.path.join(d, f)
            if rel not in skip and not paths.ignored(rel) and not paths.is_gen(rel) \
                    and stat.S_ISREG(os.lstat(full).st_mode):
                files.append(rel)
    judged = lint.forked_map(lambda rel: _search_one(root, needles, rel), files, lint.default_jobs())
    for rel, labels in zip(files, judged):
        hits += [(rel, label) for label in labels]
    return sorted(set(hits))


def _patch_message(data):
    """(subject, body) of a `git format-patch` file: the subject without its `[PATCH n/m]`, and the message up to the
    diffstat's `---`.  From, Date, the diffstat and the signature are left out, so another envelope still matches."""
    text = data.decode("utf-8", "replace").replace("\r\n", "\n").split("\ndiff --git", 1)[0]
    head, _, body = text.partition("\n\n")
    subject = next((line[len("Subject:"):].strip() for line in head.splitlines()
                    if line.lower().startswith("subject:")), "")
    subject = re.sub(r"^\[[^\]]*\]\s*", "", subject)
    return subject, body.split("\n---\n", 1)[0] if subject else ""


def _hunks(data):
    """[[(mark, text)]]: the lines of each hunk of a patch, in diff order, each with its mark (` `, `-` or `+`) and
    without it, read for as many lines as the hunk's header counts (so a removed `-- ` line is not a file header)."""
    lines = re.split(r"\r?\n", data.decode("utf-8", "replace"))
    out, i = [], 0
    while i < len(lines):
        m = _HUNK.match(lines[i])
        i += 1
        if not m:
            continue
        old, new, hunk = int(m.group(1) or 1), int(m.group(2) or 1), []
        while i < len(lines) and (old > 0 or new > 0) and lines[i][:1] in ("", " ", "+", "-", "\\"):
            mark, text = lines[i][:1] or " ", lines[i][1:]
            i += 1
            if mark == "\\":
                continue
            hunk.append((mark, text))
            old -= mark != "+"
            new -= mark != "-"
        out.append(hunk)
    return out


def _new_side_windows(hunk, label):
    """The windows of a hunk's new side (its context and added lines, in file order) that upstream text does not hold:
    each holds a long character the change adds, or spans the place of one it removes.  In each run of changed lines
    the removed and the added long text lose their common prefix and suffix first, so text the change keeps (a line it
    moves under a new condition) does not count as added; a run whose two sides are the same long text adds nothing."""
    words, changes, run, n = [], [], None, 0
    for mark, text in hunk + [(" ", "")]:
        ws = _WORD.findall(_decoded(text))
        if mark == " " and run:
            start, removed, added = run
            limit = min(len(removed), len(added))
            p = 0
            while p < limit and removed[p] == added[p]:
                p += 1
            s = 0
            while s < limit - p and removed[-1 - s] == added[-1 - s]:
                s += 1
            if len(removed) > p + s or len(added) > p + s:
                changes.append((start + p, start + len(added) - s))
            run = None
        if mark != " ":
            run = run or [n, "", ""]
            if mark == "-":
                run[1] += "".join(ws)
                continue
            run[2] += "".join(ws)
        words += ws
        n += sum(map(len, ws))

    def counted(i):
        return any(i < b and a < i + WINDOW if b > a else i < a < i + WINDOW for a, b in changes)
    return _window_table(words, label, counted=counted) if changes else {}


def _patch_needles(out, rel, data):
    """Add to out the needles of the patch at rel, whose bytes are data: its bytes; its subject and the sentences of
    its commit message, in windows; and for each hunk, its lines in diff order, its removed text and its added text,
    whole, the windows of its removed text and of its added text, and the windows of its new side."""
    out.exact.append(Exact(data, "the bytes of " + rel))
    subject, body = _patch_message(data)
    _merge(out.windows, _windows(subject, "the subject of " + rel))
    for sentence in [body] + _SENTENCE.split(body):
        _merge(out.windows, _windows(sentence, "the commit message of " + rel))
    for k, hunk in enumerate(_hunks(data), 1):
        where = "hunk %d of %s" % (k, rel)
        removed = "\n".join(t for m, t in hunk if m == "-")
        added = "\n".join(t for m, t in hunk if m == "+")
        _whole(out.whole, "\n".join(t for _, t in hunk), "the lines of " + where)
        _whole(out.whole, removed, "removed lines of " + where)
        _whole(out.whole, added, "added lines of " + where)
        _merge(out.windows, _windows(removed, "removed lines of " + where))
        _merge(out.windows, _windows(added, "added lines of " + where))
        _merge(out.windows, _new_side_windows(hunk, "the patched lines of " + where))


def _digest(out, digest, label):
    """Add to out a digest's needles: its name, and the windows of its hex, so a digest broken over lines counts."""
    out.names.append(_name(digest, label))
    _merge(out.windows, _windows(digest, label, prose=False))


def _payload(data):
    """(the payload after the driver's header (2 + n + 4 bytes, as facts.driver_calls reads it), its runs of printable
    text): a reproducer of a text format may hold a byte the fuzzer put there, and a reader reads the text around it."""
    raw = data[2 + (int.from_bytes(data[:2], "little") & 0x7fff) + 4:]
    runs, run = [], []
    for c in raw.decode("utf-8", "replace"):
        if (c.isprintable() or c.isspace()) and c != "\ufffd":
            run.append(c)
        elif run:
            runs.append("".join(run))
            run = []
    return raw, runs + (["".join(run)] if run else [])


def _input_needles(out, rel, data):
    """Add to out the needles of the input at rel, whose bytes are data: none for the driver's header alone, which
    every counterexample input begins with and which says nothing of the bug; else its bytes and its byte windows, its
    SHA-256 (_digest), the windows of its hex, and each printable run of its payload, whole and in windows."""
    raw, runs = _payload(data)
    if not raw:
        return
    label = "the bytes of " + rel
    out.exact.append(Exact(data, label))
    for i in range(len(data) - WINDOW + 1):
        window = data[i:i + WINDOW]
        if len(set(window)) >= MIN_DISTINCT:
            out.byte_windows.setdefault(window, set()).add(label)
    sha = hashlib.sha256(data).hexdigest()
    _digest(out, sha, "%s, the SHA-256 of %s" % (sha, rel))
    _merge(out.windows, _windows(data.hex(), "the hex of " + rel, prose=False))
    for run in runs:
        _whole(out.whole, run, "the payload of " + rel)
        _merge(out.windows, _windows(run, "the payload of " + rel))


def _module(p, h):
    """The Rocq module of fuzz target p/h without its root: each `OssFuzzTheorems.<p>.<h>` holds it at a name boundary,
    and Rocq also resolves it, as in `From OssFuzzTheorems Require <p>.<h>.Statements`."""
    return "%s.%s" % (names.ident(p), names.ident(h))


def _finding_needles(tree, f, out):
    """Add to out the needles of finding f, which holds its project back.  Raises facts.BoundedFileError when one of
    its files cannot be read within its cap."""
    d = tree.path(f.path)
    patches = sorted(n for n in os.listdir(d) if n.endswith(".patch")) if os.path.isdir(d) else []
    out.names.append(_name(f.slug, "%s, the slug of finding %s" % (f.slug, f.path)))
    for n in sorted(set(patches) | ({f.data["patch"]} if f.data.get("patch") else set())):
        out.names.append(_name(n, "%s, a patch file name of finding %s" % (n, f.path)))
    digests = {run[k] for side in ("input", "control") for run in (f.data.get(side) or {}).values()
               for k in ("stdout_sha256", "stderr_sha256") if isinstance(run.get(k), str)} - {EMPTY_SHA256}
    for digest in sorted(digests):
        _digest(out, digest, "%s, a digest finding %s records" % (digest, f.path))
    summary, label = f.data["summary"], "the summary of finding " + f.path
    for text in [summary] + _SENTENCE.split(summary):
        _merge(out.windows, _windows(text, label))
    for n, cap, add in [(n, facts.FINDING_INPUT_CAP, _input_needles) for n in ("input.bin", "control.bin")] + \
            [(n, facts.FINDING_FILE_CAP, _patch_needles) for n in patches]:
        rel = "%s/%s" % (f.path, n)
        if not os.path.lexists(tree.path(rel)):
            continue
        try:
            data = facts.read_bounded(tree.path(rel), cap)
        except facts.BoundedFileError as e:
            raise facts.BoundedFileError("%s: %s" % (rel, e))
        if data:
            add(out, rel, data)


def needles(tree, hold):
    """The Needles of what hold (facts.hold of tree) leaves out of tree: empty when nothing is held.

    Names: each fuzz target of a project held whole, as <project>/<harness> and as its Rocq module; for each holding
    finding, its slug, every `*.patch` name in its directory, its recorded digests and its inputs' SHA-256; for each
    held statement, its id, its Rocq names without the root, <harness>/<statement> (relative), and, in a file about its
    fuzz target, <statement> and <statement>_holds (relative).  The evidence: _finding_needles."""
    out = Needles([], [], {}, {}, {}, None, None, False)
    for p in sorted(hold.whole):
        proj = tree.projects[p]
        for h in sorted(set(proj.harnesses) | {e["name"] for e in proj.entries()}):
            unit = "%s/%s" % (p, h)
            out.names.append(_name(unit, "%s, a fuzz target of held project %s" % (unit, p)))
            out.names.append(_name(_module(p, h), "%s, the Rocq module of held fuzz target %s"
                                   % (names.rocq_harness(p, h), unit)))
    for fs in facts.holding(tree).values():
        for f in fs:
            _finding_needles(tree, f, out)
    for sid in sorted(hold.ids):
        p, h, st = sid.split("/")
        module = _module(p, h)
        out.names.append(_name(sid, "%s, a statement an open finding of %s holds back" % (sid, p)))
        for text, full in (("%s.Statements.%s" % (module, st), "%s.Statements.%s" % (names.rocq_harness(p, h), st)),
                           ("%s.%s" % (module, st), "%s.%s" % (names.rocq_harness(p, h), st)),
                           ("Proofs.%s.%s" % (module, st), names.rocq_proof(p, h, st))):
            out.names.append(_name(text, "%s, the Rocq name of held statement %s" % (full, sid)))
        short = "%s/%s" % (h, st)
        out.names.append(_name(short, "%s, held statement %s without its project" % (short, sid), relative=True))
        scope = (tuple("%s/%s/%s/" % (top, p, h) for top in UNIT_DIRS) + ("notes/%s.md" % p,),
                 (_name_text(_decoded(module)),))
        for name in (st, st + "_holds"):
            out.names.append(_name(name, "%s, held statement %s in a file about its fuzz target" % (name, sid),
                                   True, scope))
    return _complete(out)
