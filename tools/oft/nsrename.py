"""oft rename-namespace: the Rocq namespace of a tree, in its plain text and in the stored proof encodings (OSSV-162).

The namespace and the opam stem come from release.yaml (`namespace`, `opam_stem`; the defaults of names.py when it
names none).  `rename_tree` renames both in every tracked file but the ones EXEMPT names and the shared generated files
(paths.is_shared), sets them in release.yaml, removes the opam files of the old stem and renders the generated files
again (`oft generate --skip-shared`).  `rename_paths` renames some files of one commit, for `oft port-branch`, and
`verify` compares a commit with the rename of another.  All three rename a file's text with `rename_text`:

  a file that holds neither the namespace nor `rocq-<stem>` is returned as it is, unread (a .v file whose compressed
  blobs hide the namespace in their decoded bytes is read, below);
  any file but a .v file takes the word rule (c) over its whole text;
  a .v file is read as Rocq lexes it (`literals`):
    (a) a literal of a stored encoding (below) is renamed by its codec, or left byte for byte when `skip_plain` says so;
    (b) any other literal that holds the namespace is renamed component by component when its whole body is a dotted
        name (`@?ident(.ident)*.?`); else the file is refused.  The codec alphabets exclude `.`, so such a literal
        cannot be encoded data, and a word rule inside any other literal could rename encoded data whose length byte
        (`chr(48 + n)`, one of `:;<=>?@` for 10-16 characters) is no word character;
    (c) outside literals, the namespace as a word, and `rocq-<stem>` before `-`, a blank, `"`, `)` or the end, which
        renames the opam names and never a schema tag (`oss-fuzz-theorems/...`) or an image name
        (`oss-fuzz-theorems-checker`).  A word has no letter, digit or `_` on either side; in a .v file no `'` after
        it either, nor primes before it that follow an identifier character (`x'Name` is one Rocq identifier), while
        in any other file a `'` is a quote (`f'Name.x'`, `-printf 'Name.%P'`).
  The result must hold neither the namespace nor `rocq-<stem>` anywhere.

A proof stores its terms in three encodings whose decoders live in the tree itself.  All three hold a global's module
path as length-prefixed text, so a text rename would leave the length bytes behind and corrupt every term:

  KReplay table   a concatenation of entries, each `<kind><ncomp>` then
                  `<len><ident>` per component (KReplay.v:67-92).  A stream
                  reaches an entry by its byte offset (KReplay.v:520, :561), so
                  an entry is renamed in place and padded back to its old
                  length.  The table is stored plain, or LZ-compressed behind
                  `KReplay.lz_vm` (KReplay.v:713).
  KReplay stream  the opcode stream of `KReplay.run1` and `run` (decode_ph,
                  KReplay.v:369-600).  It carries no internal offsets, so the
                  two inline-global opcodes (KReplay.v:556-559) are rewritten
                  and the stream may shrink.  `run1z` stores the same stream
                  LZ-compressed (KReplay.v:724).
  CDef table      directory and global records at the byte offsets the header
                  of each `zQ` stream names (CDef.v:170-225).  A record is
                  renamed in place and padded back, as above.

Gates, per file:

  before   every table and stream parses to its exact end and re-serialises
           byte-identically from what the parse decoded; every offset a CDef
           stream names is a record that re-serialises to itself.  CDef bytes
           no record covers are never read; those holding the old name are
           padded over by the rename.  A plain (not LZ) KReplay table or stream
           whose bytes do not hold the old name is neither parsed nor changed
           (`skip_plain`), and is listed as left unparsed.
  after    every blob written parses again, no decoded path component is the
           old namespace, and the old name occurs nowhere in its decoded bytes.

Every length and offset counts bytes: a blob is read as the UTF-8 bytes of its
literal, the bytes Rocq's string holds (`_codec_blobs`, `write_body`).

The LZ decoder is ported here (`lz_inflate`) with the step limits of the Rocq
one (448 outer, 448 inner, 448 scan: KReplay.v:696-710), so a blob this tool
accepts is one the Rocq VM also inflates whole.  Every blob written is inflated
again and compared with the text it was built from.
"""
import multiprocessing
import os
import re
import shutil
import subprocess
import sys
import tempfile

from . import facts, generate, layout, paths


# the name a tree whose release.yaml names no namespace has: names.NAMESPACE_DEFAULT
OLD_DEFAULT = "OssFuzzTheorems"
PAD = "~"

# `(`, `)`, `*` and `.` are in neither encoding's alphabet, and neither is `"`
# or the LZ escape `!`: the blobs sit in Rocq string literals.
_FORBIDDEN = '"()*.'

# The files the rename leaves alone (plan D9): the tools (they hold the default name and the fingerprint's fixed name),
# the history, the two documents that state the fingerprint's fixed name, the negative control of the old name, and
# each fuzz target's provenance evidence: logs, patches, scripts and dumps of runs made before the rename, which record
# what those runs read and printed (renamed, they would record runs that never happened, and their MANIFEST's sha256
# would no longer match), and which no build reads.  And dev/stream/, the stream's internal tools, which the release
# cut removes (release_tree.INTERNAL): some of its files already use the new name by design, and a compiled .glob there
# keeps the old one.  A path ending in `/` names a folder; a `*` stands for one path component.
EXEMPT = ("tools/", "CHANGELOG.md", "docs/versioning.md", "docs/statements.md", "tests/negative/old_namespace/",
          "projects/*/*/proofs/provenance/evidence/", "dev/stream/")


class Error(Exception):
    """A blob or a file this tool does not understand, or a tree it refuses; the caller reports it and stops."""


def _exempt_re(e):
    body = "[^/]+".join(re.escape(part) for part in e.split("*"))
    return re.compile(body if e.endswith("/") else body + r"\Z")


_EXEMPT_RE = tuple(_exempt_re(e) for e in EXEMPT)


def exempt(rel):
    """Whether the rename leaves rel, a path from the repository root, alone (EXEMPT)."""
    return any(r.match(rel) for r in _EXEMPT_RE)


def exclude_pathspecs():
    """git pathspecs that leave out every path of EXEMPT, for `git grep` and the like."""
    return [":(glob,exclude)" + (e + "**" if e.endswith("/") else e) for e in EXEMPT]


# --------------------------------------------------------------------------
# LZ (KReplay.v:640-724)
# --------------------------------------------------------------------------

LZ_FUEL = 448          # `n4096` = `unary 32` seven times over = 7 * 64 (KReplay.v:707)
LZ_MAX_LEN = 92        # the five-byte form: dval + 5, dval <= 87
LZ_MAX_DIST = 588544   # 75 * 7744 + 87 * 88 + 87 + 1
LZ_SHORT_DIST = 1056   # 11 * 88 + 87 + 1
LZ_HEADER = 4          # `lz_inflate` starts at offset 4 (KReplay.v:709)


def _dval(c):
    """A base-88 digit (KReplay.v:643-644)."""
    if c < 40:
        return c - 35
    if c < 46:
        return c - 38
    return c - 39


def _digit(d):
    """The character `_dval` maps back to `d`, avoiding `!`, `"`, `(`, `)`, `*` and `.`."""
    if d < 5:
        return chr(35 + d)
    if d < 8:
        return chr(38 + d)
    return chr(39 + d)


LZ_DIGITS = "".join(_digit(d) for d in range(88))


def _num88(v, width):
    out = []
    for _ in range(width):
        out.append(_digit(v % 88))
        v //= 88
    if v:
        raise Error("a value too large for %d base-88 digits" % width)
    return "".join(reversed(out))


def lz_inflate(z):
    """The Rocq `LZ.lz_inflate` (KReplay.v:708-710), with its step limits."""
    out = bytearray()
    data = z.encode("latin-1")
    n = len(data)
    i = LZ_HEADER
    outer = LZ_FUEL
    while outer > 0 and i < n:
        inner = LZ_FUEL
        while inner > 0 and i < n:
            if data[i] == 33:
                d1 = _dval(data[i + 1])
                d2 = _dval(data[i + 2])
                if d1 < 76:
                    dist = d1 * 7744 + d2 * 88 + _dval(data[i + 3]) + 1
                    ln = _dval(data[i + 4]) + 5
                    i += 5
                else:
                    dist = (d1 - 76) * 88 + d2 + 1
                    ln = _dval(data[i + 3]) + 4
                    i += 4
                if dist > len(out):
                    # the Rocq `getrange` reads nothing there and the VM inflates
                    # a shorter text; refuse such a blob rather than guess
                    raise Error("an LZ back-reference of distance %d at offset %d "
                                "reaches before the start of the output" % (dist, i))
                avail = dist if dist < ln else ln
                lo = len(out) - dist
                piece = bytes(out[lo:lo + avail])
                for _ in range(8):          # `expand 8` (KReplay.v:663-667)
                    if len(piece) >= ln:
                        break
                    piece += piece
                out += piece[:ln]
            else:
                k = i + 1
                limit = k + LZ_FUEL         # `scan` runs on the step's fuel
                while k < n and k < limit and data[k] != 33:
                    k += 1
                out += data[i:k]
                i = k
            inner -= 1
        outer -= 1
    if i < n:
        raise Error("the LZ step limit stops %d bytes before the end of the blob"
                    % (n - i))
    return out.decode("latin-1")


def _emit_match(dist, ln):
    if dist <= LZ_SHORT_DIST and ln <= 91:
        return ("!" + _digit(76 + (dist - 1) // 88) + _digit((dist - 1) % 88)
                + _digit(ln - 4))
    d = dist - 1
    return ("!" + _digit(d // 7744) + _digit(d // 88 % 88) + _digit(d % 88)
            + _digit(ln - 5))


def lz_deflate(s, header=None, candidates=16):
    """A blob that `lz_inflate` turns back into `s`.

    Greedy with one step of lookahead, over the nearest occurrences of each
    four-byte prefix.  The result is checked by inflating it, never trusted.
    """
    data = s.encode("latin-1")
    if 33 in data:
        raise Error("the text to compress holds '!', which the LZ format reserves")
    n = len(data)
    out = [_num88(n, LZ_HEADER) if header is None else header]
    lit = 0
    i = 0

    def best(at):
        """(length, distance) of the longest match at `at`, or (0, 0)."""
        if at + 4 > n:
            return 0, 0
        word = data[at:at + 4]
        lo = at - LZ_MAX_DIST
        if lo < 0:
            lo = 0
        end = at + 3
        blen, bdist = 0, 0
        cap = n - at
        if cap > LZ_MAX_LEN:
            cap = LZ_MAX_LEN
        for _ in range(candidates):
            j = data.rfind(word, lo, end)
            if j < 0:
                break
            end = j + 3
            ln = 4
            while ln < cap and data[j + ln] == data[at + ln]:
                ln += 1
            dist = at - j
            if ln > blen and (ln >= 5 or dist <= LZ_SHORT_DIST):
                blen, bdist = ln, dist
                if ln == cap:
                    break
        return blen, bdist

    while i < n:
        ln, dist = best(i)
        if ln:
            nln, ndist = best(i + 1)
            if nln > ln:
                ln, dist = 0, 0
        if ln:
            if dist > LZ_SHORT_DIST and ln < 5:
                ln = 0
            # the blob sits in a UTF-8 source file: a match may neither start
            # nor end inside a multi-byte character, or the literal beside it
            # would hold half a character
            elif 0x80 <= data[i] < 0xC0 or (i + ln < n and 0x80 <= data[i + ln] < 0xC0):
                ln = 0
        if ln:
            if lit < i:
                out.append(data[lit:i].decode("latin-1"))
            out.append(_emit_match(dist, ln))
            i += ln
            lit = i
        else:
            i += 1
    if lit < n:
        out.append(data[lit:n].decode("latin-1"))
    return "".join(out)


# --------------------------------------------------------------------------
# KReplay table (kr_global, KReplay.v:67-92)
# --------------------------------------------------------------------------

class KrEntry(object):
    """One global: `<kind><ncomp>(<len><ident>)*<tail>`."""

    __slots__ = ("start", "end", "kind", "comps", "tail")

    def __init__(self, start, end, kind, comps, tail):
        self.start = start
        self.end = end
        self.kind = kind
        self.comps = comps
        self.tail = tail

    def render(self):
        out = [self.kind, chr(48 + len(self.comps))]
        for c in self.comps:
            if len(c) > 79:
                raise Error("an identifier of %d characters does not fit a length byte"
                            % len(c))
            out.append(chr(48 + len(c)))
            out.append(c)
        out.append(self.tail)
        return "".join(out)


def kr_entry_at(tab, p):
    """The entry that starts at offset `p`."""
    try:
        kind = tab[p]
        k = ord(kind)
        ncomp = ord(tab[p + 1]) - 48
        if ncomp < 0:
            raise Error("a component count below zero at offset %d" % p)
        q = p + 2
        comps = []
        for _ in range(ncomp):
            ln = ord(tab[q]) - 48
            if ln < 0:
                raise Error("an identifier length below zero at offset %d" % q)
            comps.append(tab[q + 1:q + 1 + ln])
            q += ln + 1
            if q > len(tab):
                raise IndexError
        # a constant (`C`, and its section form `c`) has no inductive index pair
        tail = "" if (k - 32 if k >= 96 else k) == 67 else tab[q:q + 2]
        q += len(tail)
        if q > len(tab):
            raise IndexError
    except IndexError:
        raise Error("an entry at offset %d runs past the end of the table" % p)
    return KrEntry(p, q, kind, comps, tail)


def kr_parse_table(tab):
    """Every entry, in order; the table is exactly their concatenation."""
    out = []
    p = 0
    while p < len(tab):
        e = kr_entry_at(tab, p)
        if e.end <= p:
            raise Error("an entry of no length at offset %d" % p)
        out.append(e)
        p = e.end
    return out


# --------------------------------------------------------------------------
# KReplay stream (decode_ph, KReplay.v:369-600)
# --------------------------------------------------------------------------

def _b64(s, p, n):
    """`kr_num2`..`kr_num5` (KReplay.v:16-24)."""
    v = 0
    for k in range(n):
        v = (v << 6) + (ord(s[p + k]) - 48)
    return v


# opcode -> bytes consumed, for the opcodes of a fixed length (KReplay.v:391-532)
_KR_FIXED = {
    35: 2, 36: 3, 37: 3, 38: 4, 39: 2, 43: 3, 44: 3, 45: 4, 47: 3, 48: 4,
    49: 4, 50: 5, 51: 2, 52: 3, 53: 3, 54: 4, 55: 3, 56: 4, 57: 4, 58: 5,
    59: 3, 60: 4, 61: 4, 62: 5, 63: 4, 64: 5, 65: 5, 66: 6, 67: 2, 68: 2,
    69: 2, 70: 2, 71: 2, 72: 3, 73: 3, 74: 3, 75: 3, 76: 3, 77: 3, 78: 4,
    79: 2, 80: 2, 81: 3, 82: 2, 83: 3, 84: 1, 85: 1, 86: 2, 87: 2, 88: 3,
    89: 3, 90: 4, 91: 1, 92: 2, 93: 2, 94: 3, 95: 3, 96: 4, 97: 1, 98: 2,
    99: 3, 100: 1, 101: 1, 102: 2, 103: 5, 106: 3, 107: 4, 108: 3, 109: 4,
}

# the same, for the extended opcodes behind O112, from the sub-opcode's offset
# (KReplay.v:537-597)
_KR_EXT_FIXED = {
    35: 5, 36: 3, 37: 2, 38: 2, 39: 2, 43: 4, 45: 2, 49: 5, 50: 3, 51: 3,
    52: 1, 53: 1, 56: 1, 57: 1, 59: 2, 60: 5, 61: 2, 62: 3, 64: 12, 66: 5,
}

KR_END = 111        # the opcode that returns the term (KReplay.v:535-536)
KR_EXT = 112        # the escape to the extended opcodes (KReplay.v:537)


def _kr_case_end(s, p):
    """The end of a `Case` opcode whose argument bytes start at `p` (KReplay.v:279-322)."""
    npm = ord(s[p]) - 48
    pf = p + 1
    nn = ord(s[pf + npm]) - 48
    pa = pf + npm + 1
    prp = pa + 3 * nn
    nbr = _b64(s, prp + 2, 2)
    q = prp + 4
    for _ in range(nbr):
        q += 2 + 3 * (ord(s[q]) - 48)
    return q


def _kr_str_end(s, p):
    """The end of a string literal whose argument bytes start at `p` (KReplay.v:353-367)."""
    n = _b64(s, p, 3)
    q = p + 3
    for _ in range(n):
        if ord(s[q]) == 114:                # a run of raw characters
            q += 3 + _b64(s, q + 1, 2)
        else:
            q += 3                          # one hex-coded byte
    return q


def kr_parse_stream(s):
    """The stream as pieces: strings copied through, and `KrEntry` inline globals.

    Raises unless the stream ends exactly at its terminating opcode.
    """
    pieces = []
    plain = 0
    p = 0
    n = len(s)
    while True:
        if p >= n:
            raise Error("the stream ends with no terminating opcode")
        op = ord(s[p])
        if op == KR_END:
            p += 1
            break
        if op == KR_EXT:
            q = p + 1
            sub = ord(s[q])
            if sub in _KR_EXT_FIXED:
                p = q + _KR_EXT_FIXED[sub]
            elif sub == 44:                 # Var: a name of `n` characters
                p = q + (ord(s[q + 1]) - 48) + 2
            elif sub in (47, 48):           # an inline global, hard and soft
                e = kr_entry_at(s, q + 1)
                if plain < p:
                    pieces.append(s[plain:p])
                pieces.append(s[p:q + 1])
                pieces.append(e)
                plain = e.end
                p = e.end
                continue
            elif sub == 54:                 # kr_lsort (KReplay.v:183-222)
                np = ord(s[q + 3])
                p = q + 6 + (0 if np == 126 else np - 48)
            elif sub == 55:                 # kr_usort (KReplay.v:95-112)
                p = q + (ord(s[q + 1]) - 48) + 2
            elif sub == 58:                 # a long binder name
                p = q + _b64(s, q + 3, 2) + 5
            elif sub == 63:                 # kr_fix (KReplay.v:325-343)
                p = q + 3 + 5 * (ord(s[q + 1]) - 48)
            elif sub == 65:                 # kr_str
                p = _kr_str_end(s, q + 1)
            else:
                raise Error("an unknown extended opcode %d at offset %d" % (sub, p))
        elif op in _KR_FIXED:
            p += _KR_FIXED[op]
        elif op == 104:                     # a short binder name
            p += (ord(s[p + 2]) - 48) + 3
        elif op == 105:
            p += (ord(s[p + 3]) - 48) + 4
        elif op == 110:                     # kr_case
            p = _kr_case_end(s, p + 1)
        else:
            raise Error("an unknown opcode %d at offset %d" % (op, p))
        if p > n:
            raise Error("the opcode before offset %d runs past the end of the stream" % p)
    if p != n:
        raise Error("%d bytes follow the stream's terminating opcode" % (n - p))
    if plain < n:
        pieces.append(s[plain:n])
    return pieces


def kr_render_stream(pieces):
    return "".join(p if isinstance(p, str) else p.render() for p in pieces)


# --------------------------------------------------------------------------
# CDef table (CDef.v:18-37, :170-225)
# --------------------------------------------------------------------------

_CDEF_CLS = {}
for _i in range(10):
    _CDEF_CLS[48 + _i] = _i          # '0'-'9': a final digit
for _i in range(6):
    _CDEF_CLS[97 + _i] = 10 + _i     # 'a'-'f': a final digit
for _i in range(16):
    _CDEF_CLS[103 + _i] = 16 + _i    # 'g'-'v': a digit the next one follows


def cdef_num_at(t, o):
    """(end, value) of the number at offset `o` (`num_at`, CDef.v:27-34)."""
    acc = 0
    while True:
        v = _CDEF_CLS.get(ord(t[o]), 99)
        if v < 16:
            return o + 1, acc + v
        if v < 32:
            acc = (acc + v - 16) * 16
            o += 1
        else:
            raise Error("a number expected at offset %d" % o)


def cdef_num(v):
    """The encoding `cdef_num_at` reads back as `v`."""
    digits = []
    while v >= 16:
        digits.append(v % 16)
        v //= 16
    digits.append(v)
    digits.reverse()
    out = [chr(103 + d) for d in digits[:-1]]
    out.append("0123456789abcdef"[digits[-1]])
    return "".join(out)


def _cdef_ident(word, pieces, mark):
    """One identifier as stored: whole, or behind `mark` in the pieces it was read from."""
    if pieces is None or "".join(pieces) != word:
        return cdef_num(len(word)) + word
    return mark + cdef_num(len(pieces)) + "".join(cdef_num(len(p)) + p for p in pieces)


class CdefRecord(object):
    """A directory (`comps`) or a global (`diroff` and `name`) of a CDef table.

    `pieces` keeps, per identifier, the pieces it is stored in (None when it is
    stored whole), so that a record renders back to the bytes it was read from;
    an identifier the rename changed is written whole.
    """

    __slots__ = ("start", "end", "comps", "diroff", "name", "pieces")

    def __init__(self, start, end, comps=None, diroff=None, name=None, pieces=None):
        self.start = start
        self.end = end
        self.comps = comps
        self.diroff = diroff
        self.name = name
        self.pieces = pieces

    def render(self):
        if self.comps is not None:       # a piece-stored component starts with length 0
            return cdef_num(len(self.comps)) + "".join(
                _cdef_ident(c, p, "0")
                for c, p in zip(self.comps, self.pieces or [None] * len(self.comps)))
        return cdef_num(self.diroff) + _cdef_ident(self.name, self.pieces, "|")


def _cdef_pieces(t, o, k):
    """`k` length-prefixed pieces of one identifier (CDef.v:175-177, :196-198)."""
    out = []
    for _ in range(k):
        o, ln = cdef_num_at(t, o)
        out.append(t[o:o + ln])
        o += ln
    return o, out


def cdef_dir_at(t, o):
    """A directory record (`dir_at`, CDef.v:170-187)."""
    start = o
    o, ncomp = cdef_num_at(t, o)
    comps = []
    pieces = []
    for _ in range(ncomp):
        o, ln = cdef_num_at(t, o)
        if ln == 0:                         # stored in pieces (CDef.v:181-183)
            o, npieces = cdef_num_at(t, o)
            o, ps = _cdef_pieces(t, o, npieces)
            comps.append("".join(ps))
            pieces.append(ps)
        else:
            comps.append(t[o:o + ln])
            pieces.append(None)
            o += ln
    if o > len(t):
        raise Error("the directory at offset %d runs past the end of the table" % start)
    return CdefRecord(start, o, comps=comps, pieces=pieces)


def cdef_glob_at(t, o):
    """A global record (`glob_at`, CDef.v:190-206)."""
    start = o
    o, diroff = cdef_num_at(t, o)
    pieces = None
    if ord(t[o]) == 124:                    # '|': a name stored in pieces
        o, npieces = cdef_num_at(t, o + 1)
        o, pieces = _cdef_pieces(t, o, npieces)
        name = "".join(pieces)
    else:
        o, ln = cdef_num_at(t, o)
        name = t[o:o + ln]
        o += ln
    if o > len(t):
        raise Error("the global at offset %d runs past the end of the table" % start)
    return CdefRecord(start, o, diroff=diroff, name=name, pieces=pieces)


class _CdefTerms(object):
    """Where the CDef terms starting at an offset can end (`term`, CDef.v:93-166).

    The decoder reads a `Case` (tag `M`) with as many branches as its inductive
    has constructors, which only the environment knows, so a walk returns every
    end offset some branch count gives, and the caller requires the stream's end
    to be among them.  Every other tag reads a fixed shape.  A global index must
    be below the header's count, and a shared-term index below the number of
    shared terms read before it (CDef.v:113-114, :210-225).
    """

    def __init__(self, s, nglobs):
        self.s = s
        self.nglobs = nglobs
        self.memo = {}

    def num(self, o):
        try:
            return cdef_num_at(self.s, o)
        except IndexError:
            raise Error("a number runs past the end of a CDef stream")

    def glob(self, o):
        o, j = self.num(o)
        if j >= self.nglobs:
            raise Error("global index %d of a CDef stream names no header entry" % j)
        return o

    def name(self, o, required=False):
        o, ln = self.num(o)
        if ln == 0 and required:
            raise Error("a variable name expected at offset %d of a CDef stream" % o)
        if o + ln > len(self.s):
            raise Error("a name runs past the end of a CDef stream")
        return o + ln

    def seq(self, starts, k, shared):
        """The ends of `k` terms in a row after any of `starts`."""
        for _ in range(k):
            nxt = set()
            for o in starts:
                nxt |= self.term(o, shared)
            starts = nxt
        return starts

    def term(self, o, shared):
        key = (o, shared)
        hit = self.memo.get(key)
        if hit is not None:
            return hit
        self.memo[key] = frozenset()        # a term never contains itself
        try:
            ends = frozenset(self._term(o, shared))
        except Error:
            ends = frozenset()
        self.memo[key] = ends
        return ends

    def _term(self, o, shared):
        s = self.s
        if o >= len(s):
            return set()
        c = ord(s[o])
        o += 1
        if c in (36, 77, 74):                   # `$` global; `M` case; `J` projection
            o = self.glob(o)
            if c == 36:
                return {o}
            if c == 74:
                o = self.num(self.num(o)[0])[0]
                return self.term(o, shared)
            ends = self.seq({o}, 2, shared)     # return type, scrutinee
            reach = set(ends)
            frontier = set(ends)
            while frontier:                     # then any number of branches
                frontier = self.seq(frontier, 1, shared) - reach
                reach |= frontier
            return reach
        if c in (94, 73, 78):                   # `^` Rel, `I` uint63, `N` nat
            return {self.num(o)[0]}
        if c in (43, 35, 45):                   # `+`, `#`, `-`: a positive
            return {self.num(o)[0]}
        if c == 126:                            # `~` shared term
            o, j = self.num(o)
            if j >= shared:
                raise Error("shared index %d out of range" % j)
            return {o}
        if c == 64:                             # `@` application: n, head, n args
            o, n = self.num(o)
            return self.seq({o}, n + 1, shared)
        if c in (62, 92):                       # `>` Prod, `\` Lambda
            return self.seq({self.name(o)}, 2, shared)
        if c == 61:                             # `=` LetIn
            return self.seq({self.name(o)}, 3, shared)
        if c == 63:                             # `?` Var
            return {self.name(o, required=True)}
        if c in (80, 90, 83, 84):               # `P`, `Z`, `S`, `T`
            return {o}
        if c == 75:                             # `K` cast: kind, value, type
            if o >= len(s) or s[o] not in "dvn":
                raise Error("a cast kind expected")
            return self.seq({o + 1}, 2, shared)
        if c == 88:                             # `X` fixpoint
            o, cnt = self.num(o)
            o, _ = self.num(o)
            starts = {o}
            for _ in range(cnt):
                nxt = set()
                for q in starts:
                    q, _ = self.num(q)
                    nxt |= self.term(self.name(q), shared)
                starts = nxt
            return self.seq(starts, cnt, shared)
        raise Error("unknown tag %d" % c)


def cdef_parse_stream(s):
    """The table offsets a stream's header names (`header`, CDef.v:208-225).

    Raises unless the shared terms and the root term can end exactly at the
    end of the stream (`decode`, CDef.v:227-240).
    """
    # a CDef term walk recurses once per nested term (`_CdefTerms`); set here, so that importing this module (as
    # every `oft` command does) changes nothing
    sys.setrecursionlimit(max(sys.getrecursionlimit(), 100000))
    o, cg = cdef_num_at(s, 0)
    o, cs = cdef_num_at(s, o)
    offsets = []
    for _ in range(cg):
        if o >= len(s) or ord(s[o]) != 33:
            raise Error("'!' expected at offset %d of a CDef stream" % o)
        o, v = cdef_num_at(s, o + 1)
        offsets.append(v)
    walk = _CdefTerms(s, cg)
    starts = {o}
    for j in range(cs):
        nxt = set()
        for q in starts:
            if q < len(s) and ord(s[q]) == 38:
                nxt |= walk.term(q + 1, j)
        if not nxt:
            raise Error("'&' and a shared term expected in a CDef stream")
        starts = nxt
    if len(s) not in walk.seq(starts, 1, cs):
        raise Error("a CDef stream does not decode to its exact end")
    return offsets


# --------------------------------------------------------------------------
# the stored blobs of a .v file
# --------------------------------------------------------------------------

# the call, or the binding, that a blob literal belongs to.  A plain KReplay
# table is bound straight to its `kr_t_<unit> ()`; the LZ one goes through
# `KReplay.lz_vm` on the same line, and the later marker wins.  A stream kept
# in a side file (`<file>_blobs<k>.v`) is bound to its `kr_b_<nnn> ()` and
# passed to `run1` by that call.
#
# Only the KReplay of this tool: boost-beast/http_request has a `Common/KReplay.v`
# whose `run` and `runc` take two arrays and a stream of another format
# (Common/KReplay.v:272-313).  Its calls are told apart by their first argument,
# `[|`, and its globals are plain text that an ordinary rename owns.
_MARKERS = [
    ("KReplay.lz_vm", "kr_table_lz"),
    ("KReplay.run1z_chk", "kr_stream_lz"),
    ("KReplay.run1z", "kr_stream_lz"),
    ("KReplay.run1_chk", "kr_stream"),
    ("KReplay.run1", "kr_stream"),
    ("KReplay.run_chk", "kr_stream"),
    ("KReplay.run", "kr_stream"),
    ("CDef.cdeft", "cdef_table"),
]
_MARKER_RE = re.compile("|".join(
    [re.escape(m) + r"(?!\w)" for m, _ in _MARKERS]
    + [r"\bzQ\b", r"\bkr_t_\w*\s*\(\s*\)\s*:=", r"\bkr_b_\w*\s*\(\s*\)\s*:="]))
_KIND_OF = dict(_MARKERS)
KINDS = ("kr_table_lz", "kr_table", "kr_stream_lz", "kr_stream",
         "cdef_table", "cdef_stream")


def _kind_of(marker):
    if marker.startswith("kr_t_"):
        return "kr_table"
    if marker.startswith("kr_b_"):
        return "kr_stream"
    if marker == "zQ":
        return "cdef_stream"
    return _KIND_OF[marker]


def literals(text):
    """(start, end, kind) per string literal, `start` just after the opening quote.

    `kind` names the encoding of the call the literal is an argument of; it is
    "text" for an element of a `[...]` list (the section names of `run1`, and
    the plain dotted-name lists an ordinary text rename owns), and None for a
    literal that belongs to no call this tool knows.  A doubled quote inside a
    literal is one quote, as Rocq reads it (the body `resp 0 ""<path>""` is
    `resp 0 "<path>"`); no stored encoding holds one (_gate refuses such a blob).
    """
    out = []
    i = 0
    n = len(text)
    last = 0        # the end of the literal before this one
    since = 0       # the end of the last literal that was not a list element:
                    # the call's name sits before its `[...]` of section names
    # a `kr_b_<nnn> ()` side file holds KReplay streams only when it loads KReplay
    side_kr = _REQUIRES_KREPLAY.search(text) is not None
    while i < n:
        if text[i] != '"':
            i += 1
            continue
        j = text.find('"', i + 1)
        while j >= 0 and j + 1 < n and text[j + 1] == '"':
            j = text.find('"', j + 2)
        if j < 0:
            raise Error("an unterminated string literal at %d" % i)
        head = text[last:i].rstrip()
        if head.endswith("[") or head.endswith(";"):
            kind = "text"
        else:
            # only the sentence the literal is in: a call before the end of
            # an earlier sentence (`.` then a blank) owns none of its literals
            region = _SENTENCE_END.split(text[since:i])[-1]
            found = list(_MARKER_RE.finditer(region))
            kind = _kind_of(found[-1].group()) if found else None
            if kind is not None:
                marker = found[-1].group()
                rest = region[found[-1].end():].lstrip()
                if rest.startswith("[|"):
                    kind = None     # boost-beast's `Common/KReplay.run [| … |]`
                elif marker.startswith("kr_b_") and not side_kr:
                    kind = None     # another codec's side file (`Rpl` on ossv/candidates)
            since = j + 1
        out.append((i + 1, j, kind))
        last = j + 1
        i = j + 1
    return out


_SENTENCE_END = re.compile(r"\.\s")
_REQUIRES_KREPLAY = re.compile(r"\bRequire\b[^\n]*\bKReplay\b")


def write_body(body):
    """The source text of a blob whose bytes `body` holds (see `_codec_blobs`)."""
    try:
        return body.encode("latin-1").decode("utf-8")
    except UnicodeDecodeError:
        raise Error("a rewritten blob is not valid UTF-8, so Rocq cannot read it")


def _plain(kind, body):
    """The decoded bytes of a blob.

    The four bytes before an LZ blob are the length of what it inflates to, in
    base 88; nothing in the Rocq decoder reads them (KReplay.v:709), and this
    tool writes them back from the text it compressed.
    """
    if not kind.endswith("_lz"):
        return body
    plain = lz_inflate(body)
    head = 0
    for c in body[:LZ_HEADER]:
        head = head * 88 + _dval(ord(c))
    if head != len(plain):
        raise Error("an LZ header of %d before a blob that inflates to %d bytes"
                    % (head, len(plain)))
    return plain


def check_blob(kind, body):
    """Parse one blob and re-serialise it: (plain text, what the parse found).

    Raises unless the parse reaches the blob's exact end and the rendering of
    what it decoded is byte-identical to the blob.
    """
    plain = _plain(kind, body)
    if kind.startswith("kr_table"):
        entries = kr_parse_table(plain)
        if "".join(e.render() for e in entries) != plain:
            raise Error("a KReplay table does not re-serialise to itself")
        return plain, entries
    if kind.startswith("kr_stream"):
        pieces = kr_parse_stream(plain)
        if kr_render_stream(pieces) != plain:
            raise Error("a KReplay stream does not re-serialise to itself")
        return plain, pieces
    if kind == "cdef_stream":
        return plain, cdef_parse_stream(plain)
    return plain, None      # a CDef table is parsed from the offsets its streams name


def cdef_records(table, offsets):
    """Every record of a CDef table the globals at `offsets` reach."""
    globs = {}
    for o in offsets:
        if o not in globs:
            globs[o] = cdef_glob_at(table, o)
    out = dict(globs)
    for g in globs.values():
        if g.diroff in out:
            if out[g.diroff].comps is None:
                raise Error("offset %d of the table is read as a global and as a "
                            "directory" % g.diroff)
            continue
        out[g.diroff] = cdef_dir_at(table, g.diroff)
    return out


def coverage_gaps(table, records):
    """The byte ranges of `table` that no record covers."""
    gaps = []
    at = 0
    for start, end in sorted((r.start, r.end) for r in records.values()):
        if start > at:
            gaps.append((at, start))
        at = max(at, end)
    if at < len(table):
        gaps.append((at, len(table)))
    return gaps


# --------------------------------------------------------------------------
# the rename
# --------------------------------------------------------------------------

def _renamed(comps, old, new):
    """`comps` with a leading `old` replaced, and whether it was there."""
    if comps and comps[0] == old:
        return [new] + list(comps[1:]), True
    return list(comps), False


def kr_filler(gap):
    """Entries that fill `gap` bytes and that no offset names.

    A renamed entry is shorter than the one it replaces, and the bytes after it
    must stay a well-formed entry sequence: the decoder never reads them, but a
    table is parsed by walking it (`kr_parse_table`).  The filler is a constant
    whose one component is padding.  Two bytes is the shortest entry there is,
    so a gap of one byte cannot be filled.
    """
    out = []
    while gap:
        if gap == 1:
            raise Error("a gap of one byte: no KReplay entry is shorter than two. "
                        "Rename to a name the same length or at least two shorter.")
        if gap == 2:
            out.append("C0")
            gap = 0
        else:
            take = min(gap, 82)         # a component of at most 79 characters
            if gap - take == 1:
                take -= 1
            out.append("C1" + chr(48 + take - 3) + PAD * (take - 3))
            gap -= take
    return "".join(out)


def rename_blob(kind, body, old, new, stats):
    """One blob with every path whose first component is `old` renamed to `new`."""
    plain = _plain(kind, body)
    if kind.startswith("kr_table"):
        out = []
        for e in kr_parse_table(plain):
            comps, hit = _renamed(e.comps, old, new)
            if not hit:
                out.append(plain[e.start:e.end])
                continue
            e.comps = comps
            text = e.render()
            room = e.end - e.start
            if len(text) > room:
                raise Error("a renamed entry at %d grew from %d to %d bytes"
                            % (e.start, room, len(text)))
            out.append(text + kr_filler(room - len(text)))
            stats["entries"] += 1
        fresh = "".join(out)
        if len(fresh) != len(plain):
            raise Error("a renamed KReplay table changed length")
    elif kind.startswith("kr_stream"):
        pieces = kr_parse_stream(plain)
        for p in pieces:
            if isinstance(p, KrEntry):
                p.comps, hit = _renamed(p.comps, old, new)
                if hit:
                    stats["inline"] += 1
        fresh = kr_render_stream(pieces)
    else:
        raise Error("rename_blob does not take %s" % kind)
    if fresh == plain:
        return body
    if not kind.endswith("_lz"):
        return fresh
    out = lz_deflate(fresh)
    if lz_inflate(out) != fresh:
        raise Error("a re-compressed blob does not inflate to the text it was built from")
    stats["lz_before"] += len(body)
    stats["lz_after"] += len(out)
    return out


def rename_cdef_table(table, records, old, new, stats):
    """A CDef table with every directory whose first component is `old` renamed.

    Bytes that no record covers are never read: a table is reached only through
    the globals its file's streams name (CDef.v:208-219), and `zQ` is local to
    the file.  A run of them that holds `old` (left there when a proof stopped
    using a global) is overwritten with padding.
    """
    out = list(table)
    for a, b in coverage_gaps(table, records):
        if old in table[a:b]:
            out[a:b] = list(PAD * (b - a))
            stats["dead_cleared"] += b - a
    for r in sorted(records.values(), key=lambda r: r.start):
        if r.comps is None:
            continue
        comps, hit = _renamed(r.comps, old, new)
        if not hit:
            continue
        r.comps = comps
        text = r.render()
        room = r.end - r.start
        if len(text) > room:
            raise Error("a renamed directory at %d grew from %d to %d bytes"
                        % (r.start, room, len(text)))
        out[r.start:r.end] = list(text + PAD * (room - len(text)))
        stats["dirs"] += 1
    return "".join(out)


# the counts rename_blob and rename_cdef_table keep (rename_text reads none of them)
COUNTS = ("entries", "inline", "dirs", "dead_cleared", "lz_before", "lz_after")


def _zero():
    return dict((k, 0) for k in COUNTS)


def _old_in_paths(kind, parse, old):
    """How many decoded path components of one parsed blob are `old`."""
    if kind.startswith("kr_table"):
        return sum(c == old for e in parse for c in e.comps)
    if kind.startswith("kr_stream"):
        return sum(c == old for p in parse if isinstance(p, KrEntry) for c in p.comps)
    return 0


# --------------------------------------------------------------------------
# a file's text
# --------------------------------------------------------------------------

def _codec_blobs(text, lits):
    """[(literal index, start, end, kind, body)] of the literals of a stored encoding.

    `body` is the literal's bytes, one character per byte (UTF-8 encoded, then
    read as Latin-1): a Rocq string is a byte string, and every length and
    offset in the encodings counts bytes.  `write_body` turns it back.
    """
    return [(i, start, end, kind, text[start:end].encode("utf-8").decode("latin-1"))
            for i, (start, end, kind) in enumerate(lits) if kind in KINDS]


def skip_plain(kind, body, old):
    """Whether a blob is left byte for byte and unparsed: a plain (not LZ) KReplay table or stream whose bytes do not
    hold `old`.  The rename has nothing to change in it, and some such blobs are of a KReplay variant this parser does
    not read (leptonica's).  A CDef or LZ blob is always parsed: its bytes do not show what it decodes to."""
    return kind in ("kr_table", "kr_stream") and old not in body


# a literal of no stored encoding that rule (b) renames: a whole plain dotted name, as an Ltac2 name list holds
_DOTTED = re.compile(r"@?[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*\.?")
# the forms whose bytes can hide the old name: a compressed blob, and a CDef table, which may store a component in
# pieces
_HIDING_MARK = re.compile(r"KReplay\.(?:lz_vm|run1z)(?!\w)|CDef\.cdeft(?!\w)")


def _word(name, rocq=False):
    """The name as a word: no letter, digit or `_` on either side (`\\w`, Unicode letters among them: Rocq reads
    `αName` as one identifier).  In Rocq text (rocq) no `'` after it either: a prime continues an identifier (`Name'`
    is another one); one before it is _starts_a_word's to judge.  In any other text a `'` is a quote (`f'Name.x'` in
    Python, `-printf 'Name.%P'` in bash)."""
    return re.compile(r"(?<!\w)" + re.escape(name) + (r"(?![\w'])" if rocq else r"(?!\w)"))


def _starts_a_word(text, at):
    """Whether a name at `at` of Rocq text starts an identifier: primes right before it continue an identifier only
    after an identifier character (`x'Name` is one identifier; `ROOT='Name.x'`, in a comment, holds the name)."""
    k = at
    while k > 0 and text[k - 1] == "'":
        k -= 1
    return k == at or k == 0 or not (text[k - 1].isalnum() or text[k - 1] == "_")


def _stem(stem):
    return re.compile(r"rocq-" + re.escape(stem) + r"(?=[-\s\")]|$)")


def _line(text, at):
    return text.count("\n", 0, at) + 1


def _new_stats():
    return {"encoded": 0, "dotted": 0, "plain": 0, "decoded": 0, "unparsed": []}


class _Names(object):
    """The old and new namespace and opam stem, with the word rules (c) of both."""

    def __init__(self, old, new, old_stem, new_stem):
        self.old, self.new, self.old_stem, self.new_stem = old, new, old_stem, new_stem
        self.word, self.word_rocq = _word(old), _word(old, rocq=True)
        self.stem = _stem(old_stem)
        self.stem_text = "rocq-" + old_stem

    def named(self, text):
        return self.old in text or self.stem_text in text

    def rule_c(self, span, at, hits, rocq=False):
        """span with rule (c) applied, Rocq's identifiers when rocq; the offset (span's `at` plus its own) of each
        change goes to hits."""
        if self.old not in span and self.stem_text not in span:
            return span

        def word(m):
            if rocq and not _starts_a_word(span, m.start()):
                return m.group()
            hits.append(at + m.start())
            return self.new

        hits.extend(at + m.start() for m in self.stem.finditer(span))
        span = (self.word_rocq if rocq else self.word).sub(word, span)
        return self.stem.sub("rocq-" + self.new_stem, span)


def _dotted(body, old, new):
    """body with each component equal to old renamed, when body is a whole plain dotted name; else None."""
    if _DOTTED.fullmatch(body) is None:
        return None
    at = "@" if body.startswith("@") else ""
    core = body[len(at):]
    dot = "." if core.endswith(".") else ""
    comps = core[:len(core) - len(dot)].split(".")
    return at + ".".join(new if c == old else c for c in comps) + dot


def _gate(rel, text, blobs, old, stats):
    """The before-gate of one file's blobs: [(index, start, end, kind, body, plain, parse)] of the blobs it parsed, and
    the records of its CDef table ({} for none).  A blob `skip_plain` leaves goes to stats["unparsed"]."""
    parsed = []
    offsets = []
    table = None
    for i, start, end, kind, body in blobs:
        if skip_plain(kind, body, old):
            stats["unparsed"].append((kind, i))
            continue
        try:
            if '"' in body:     # a doubled quote in the source: one byte to Rocq, two here, so no length would hold
                raise Error("it holds a quote, which no stored encoding has")
            plain, parse = check_blob(kind, body)
        except Error as e:
            raise Error("%s:%d: literal %d (%s): %s" % (rel, _line(text, start), i, kind, e))
        parsed.append((i, start, end, kind, body, plain, parse))
        if kind == "cdef_table":
            if table is not None:
                raise Error("%s:%d: a second CDef table in one file" % (rel, _line(text, start)))
            table = plain
        elif kind == "cdef_stream":
            offsets.extend(parse)
    stats["decoded"] += len(parsed)
    records = {}
    if table is not None:
        try:
            records = cdef_records(table, offsets)
        except (Error, IndexError) as e:
            raise Error("%s: the CDef table: %s" % (rel, e))
        for r in records.values():
            if table[r.start:r.end] != r.render():
                raise Error("%s: the CDef record at %d does not re-serialise to itself" % (rel, r.start))
    elif offsets:
        raise Error("%s: a CDef stream with no table" % rel)
    return parsed, records, offsets


def _decoded_old(parsed, records, old):
    """Whether a parsed blob of a file holds old in its decoded bytes, or a CDef record as a component (a component
    stored in pieces is in no run of the bytes)."""
    return (any(old in p[5] for p in parsed)
            or any(r.comps and old in r.comps for r in records.values()))


def _after_gate(rel, kind, fresh, offsets, old):
    """A rewritten blob parses again and holds `old` nowhere, as a path component or in its decoded bytes."""
    plain, parse = check_blob(kind, fresh)
    if kind == "cdef_table":
        comps = [c for r in cdef_records(plain, offsets).values() if r.comps for c in r.comps]
        decoded = sum(c == old for c in comps)
    else:
        decoded = _old_in_paths(kind, parse, old)
    if decoded or old in plain:
        raise Error("%s: a rewritten %s blob still holds %s" % (rel, kind, old))


def _rename(rel, text, n, stats, gate=False):
    """`rename_text` with its counts in stats; with gate, every blob of a .v file is gated even when the text does not
    hold either name (rename_tree's before-gate)."""
    named = n.named(text)
    if not rel.endswith(".v"):
        if not named:
            return text
        hits = []
        fresh = n.rule_c(text, 0, hits)
        stats["plain"] += len({_line(text, h) for h in hits})
        return _finish(rel, fresh, n)
    if not named and not gate and _HIDING_MARK.search(text) is None:
        return text
    try:
        lits = literals(text)
    except Error as e:
        if not named:
            return text     # a file this tool cannot lex holds neither name in its text
        raise Error("%s: %s" % (rel, e))
    # a compressed blob, or a CDef component stored in pieces, can hold the old name that the text does not; a blob
    # that does not parse is refused, as rename_tree's before-gate refuses it
    parsed, records, offsets = _gate(rel, text, _codec_blobs(text, lits), n.old, stats)
    if not named and not _decoded_old(parsed, records, n.old):
        return text
    by_index = dict((p[0], p) for p in parsed)
    pieces = []
    hits = []
    at = 0
    for i, (start, end, kind) in enumerate(lits):
        pieces.append(n.rule_c(text[at:start], at, hits, rocq=True))
        body = text[start:end]
        if i in by_index:
            _i, _s, _e, _k, raw, plain, _parse = by_index[i]
            try:
                if kind == "cdef_stream":
                    fresh = raw
                elif kind == "cdef_table":
                    fresh = rename_cdef_table(plain, records, n.old, n.new, _zero())
                else:
                    fresh = rename_blob(kind, raw, n.old, n.new, _zero())
                if fresh != raw:
                    for bad in _FORBIDDEN:
                        if bad in fresh:
                            raise Error("a rewritten blob holds %r, which its alphabet excludes" % bad)
                    _after_gate(rel, kind, fresh, offsets, n.old)
                    body = write_body(fresh)
                    stats["encoded"] += 1
            except Error as e:
                raise Error("%s:%d: literal %d (%s): %s" % (rel, _line(text, start), i, kind, e))
        elif kind not in KINDS and n.old in body:
            renamed = _dotted(body, n.old, n.new)
            if renamed is None:
                raise Error("%s:%d: a string literal holds %s and is neither a dotted name nor a stored encoding "
                            "this tool knows: %r" % (rel, _line(text, start), n.old, body[:80]))
            body = renamed
            stats["dotted"] += 1
        pieces.append(body)
        at = end
    pieces.append(n.rule_c(text[at:], at, hits, rocq=True))
    stats["plain"] += len({_line(text, h) for h in hits})
    return _finish(rel, "".join(pieces), n)


def _finish(rel, fresh, n):
    for name in (n.old, n.stem_text):
        at = fresh.find(name)
        if at >= 0:
            raise Error("%s:%d: %s is still there after the rename: %r"
                        % (rel, _line(fresh, at), name, fresh[max(0, at - 20):at + len(name) + 20]))
    return fresh


def rename_text(rel, text, old, new, old_stem, new_stem):
    """The text of the file rel with the namespace old renamed to new and the opam stem old_stem to new_stem (the
    rules in this module's docstring).  Pure.  Raises Error naming rel and the line when it refuses the file."""
    return _rename(rel, text, _Names(old, new, old_stem, new_stem), _new_stats())


def _check_names(new, new_stem):
    if not new or not new.isascii() or re.fullmatch(r"[A-Z][A-Za-z0-9]*", new) is None:
        raise Error("a namespace is one ASCII Rocq identifier that starts with a capital letter: %r" % new)
    if not new_stem or re.fullmatch(r"[a-z][a-z0-9]*(-[a-z0-9]+)*", new_stem) is None:
        raise Error("an opam stem is lower-case words joined by '-': %r" % new_stem)


# --------------------------------------------------------------------------
# release.yaml
# --------------------------------------------------------------------------

def set_release_names(text, new, new_stem):
    """release.yaml's text with `namespace: new` and `opam_stem: new_stem` set: in place where the key is there, else
    after the top-level `date:` line."""
    for key, value in (("opam_stem", new_stem), ("namespace", new)):
        line = "%s: %s" % (key, value)
        rx = re.compile(r"(?m)^%s:.*$" % key)
        if rx.search(text):
            text = rx.sub(line, text, count=1)
            continue
        m = re.search(r"(?m)^date:.*$", text)
        if m is None:
            raise Error("release.yaml has no top-level date: line to set %s after" % key)
        text = text[:m.end()] + "\n" + line + text[m.end():]
    return text


# --------------------------------------------------------------------------
# blobs of a commit
# --------------------------------------------------------------------------

class _Blobs(object):
    """`git cat-file --batch` of one repository: the bytes of an object by id or by `commit:path`."""

    def __init__(self, repo):
        self.repo = repo
        self.proc = subprocess.Popen(["git", "-C", repo, "cat-file", "--batch"], stdin=subprocess.PIPE,
                                     stdout=subprocess.PIPE)

    def get(self, spec):
        self.proc.stdin.write(spec.encode("utf-8", "surrogateescape") + b"\n")
        self.proc.stdin.flush()
        head = self.proc.stdout.readline().split()
        if len(head) != 3:
            raise Error("git cannot read %s" % spec)
        data = self.proc.stdout.read(int(head[2]))
        self.proc.stdout.read(1)
        return data

    def close(self):
        self.proc.stdin.close()
        self.proc.wait()
        self.proc.stdout.close()


def _decode(rel, data, n):
    """data as text; None for bytes that hold neither name and are no UTF-8 text (they are left as they are)."""
    try:
        return data.decode("utf-8")
    except UnicodeDecodeError:
        if n.old.encode() in data or n.stem_text.encode() in data:
            raise Error("%s: holds %s and is not UTF-8 text" % (rel, n.old))
        return None


def rename_paths(repo, commit, rels, old, new, old_stem, new_stem):
    """{path: its bytes renamed} for each of rels, read from commit: rename_text of its blob, as rename_tree renames
    it.  A file the rename leaves alone (EXEMPT) or a shared generated file (paths.is_shared) keeps its bytes, and so
    do bytes that are no UTF-8 text and hold neither name.  Raises one Error that lists every refusal."""
    n = _Names(old, new, old_stem, new_stem)
    out = {}
    refused = []
    blobs = _Blobs(repo)
    try:
        for rel in rels:
            data = blobs.get("%s:%s" % (commit, rel))
            if exempt(rel) or paths.is_shared(rel):
                out[rel] = data
                continue
            try:
                text = _decode(rel, data, n)
                out[rel] = data if text is None else _rename(rel, text, n, _new_stats()).encode("utf-8")
            except Error as e:
                refused.append(str(e))
    finally:
        blobs.close()
    if refused:
        raise Error("\n".join(refused))
    return out


# --------------------------------------------------------------------------
# verify: a commit against the rename of another
# --------------------------------------------------------------------------

def _filler(e):
    """Whether a KReplay table entry is kr_filler's: a constant with no component, or one of padding alone."""
    return e.kind == "C" and not e.tail and (not e.comps or (len(e.comps) == 1 and not e.comps[0].strip(PAD)))


def _replaced(comps, old, new):
    """comps with a first component old replaced by new: what the rename makes of a decoded path, read here apart from
    the rename's own code (`_renamed`), so that verify does not take the rename's word for it."""
    return [new] + list(comps[1:]) if list(comps[:1]) == [old] else list(comps)


def _not_renamed(kind, a_body, b_body, offsets, old, new):
    """None when the blob b_body decodes to a_body's decoded value with each path whose first component is old
    starting with new instead, the filler (kr_filler's entries, `~` padding) aside on either side; else what differs.
    offsets: what A's CDef streams name."""
    try:
        aplain, aparse = check_blob(kind, a_body)
        bplain, bparse = check_blob(kind, b_body)
    except Error as e:
        return "does not parse: %s" % e
    if old in bplain:
        return "still holds %s" % old
    if kind.startswith("kr_table"):
        if len(bplain) != len(aplain):
            return "decodes to %d bytes, A's to %d: a stream's offsets would land elsewhere" % (len(bplain),
                                                                                               len(aplain))
        want = [(e.start, e.kind, _replaced(e.comps, old, new), e.tail) for e in aparse if not _filler(e)]
        got = [(e.start, e.kind, e.comps, e.tail) for e in bparse if not _filler(e)]
        return None if want == got else "its entries are not A's renamed"
    if kind.startswith("kr_stream"):
        want = "".join(p if isinstance(p, str) else
                       KrEntry(p.start, p.end, p.kind, _replaced(p.comps, old, new), p.tail).render() for p in aparse)
        return None if want == bplain else "decodes otherwise than A's renamed"
    if kind == "cdef_stream":
        return None if aplain == bplain else "differs from A's, and the rename leaves a CDef stream as it is"
    try:
        ar, br = cdef_records(aplain, offsets), cdef_records(bplain, offsets)
    except (Error, IndexError) as e:
        return "its records do not parse: %s" % e
    if len(bplain) != len(aplain):
        return "is %d bytes, A's %d: a stream's offsets would land elsewhere" % (len(bplain), len(aplain))
    want = {o: (None if r.comps is None else _replaced(r.comps, old, new), r.diroff, r.name) for o, r in ar.items()}
    if want != {o: (r.comps, r.diroff, r.name) for o, r in br.items()}:
        return "its records are not A's renamed"
    for lo, hi in coverage_gaps(bplain, br):
        if any(x != y and x != PAD for x, y in zip(bplain[lo:hi], aplain[lo:hi])):
            return "bytes no record covers differ from A's at %d-%d" % (lo, hi)
    return None


def _verify_v(rel, a_text, want, got, n):
    """(the problems of a .v file got, which holds stored encodings, against a_text, its blob at A, the encoded
    literals decoded).  Outside those literals got must be want, rename_text of a_text; each literal of a stored
    encoding must decode to A's own literal's decoded value renamed (_not_renamed), and one the rename leaves byte for
    byte (skip_plain of A's literal) must be A's."""
    try:
        al, wl, gl = literals(a_text), literals(want), literals(got)
    except Error as e:
        return ["%s: %s" % (rel, e)], 0
    if not [k for _s, _e, k in al] == [k for _s, _e, k in wl] == [k for _s, _e, k in gl]:
        return ["%s: its string literals are not the rename's" % rel], 0
    if _outside_codec(want, wl) != _outside_codec(got, gl):
        return ["%s: its text outside the stored encodings is not the rename's" % rel], 0
    ab, gb = _codec_blobs(a_text, al), _codec_blobs(got, gl)
    offsets = []
    try:
        for _i, _s, _e, kind, body in ab:
            if kind == "cdef_stream":
                offsets.extend(cdef_parse_stream(body))
    except Error as e:
        return ["%s: A's CDef stream does not parse: %s" % (rel, e)], 0
    problems = []
    decoded = 0
    for (i, _s, _e, kind, body), (_j, start, _f, _k, gbody) in zip(ab, gb):
        if skip_plain(kind, body, n.old):
            if gbody != body:
                problems.append("%s:%d: literal %d (%s) is one the rename leaves byte for byte, and it differs"
                                % (rel, _line(got, start), i, kind))
            continue
        decoded += 1
        why = _not_renamed(kind, body, gbody, offsets, n.old, n.new)
        if why:
            problems.append("%s:%d: literal %d (%s) %s" % (rel, _line(got, start), i, kind, why))
    return problems, decoded


def _outside_codec(text, lits):
    """text with the body of each literal of a stored encoding left out."""
    out, at = [], 0
    for s, e, k in lits:
        if k in KINDS:
            out.append(text[at:s])
            at = e
    out.append(text[at:])
    return "\0".join(out)


def _old_opam(rel, stem):
    m = re.fullmatch(r"projects/([^/]+)/rocq-(.+)\.opam", rel)
    return m is not None and m.group(2) == "%s-%s" % (stem, m.group(1))


_BLOBS = None   # the _Blobs of a worker of verify


def _verify_one(row):
    """(problems, 1 when compared with the rename else 0, encoded literals decoded) of one path in both commits."""
    global _BLOBS
    repo, n, a = _JOB
    if _BLOBS is None or _BLOBS.repo != repo:
        _BLOBS = _Blobs(repo)
    mode_a, mode_b, oid_a, oid_b, _status, rel = row
    problems = []
    if mode_a != mode_b:
        problems.append("%s: its mode changed from %s to %s" % (rel, mode_a, mode_b))
    if paths.is_shared(rel):
        return problems + ["%s: a shared generated file differs (the line's render writes it)" % rel], 0, 0
    if exempt(rel):
        return problems + ["%s: a file the rename leaves alone (nsrename.EXEMPT) differs" % rel], 0, 0
    got = _BLOBS.get(oid_b)
    if paths.is_gen(rel):
        if n.old.encode() in got or n.stem_text.encode() in got:
            problems.append("%s: a generated file that still holds %s or %s" % (rel, n.old, n.stem_text))
        return problems, 0, 0
    try:
        text = _decode(rel, _BLOBS.get(oid_a), n)
        if text is None:
            return problems + ["%s: no text, and it differs" % rel], 1, 0
        want = _rename(rel, text, n, _new_stats())
        if rel == "release.yaml":
            want = set_release_names(want, n.new, n.new_stem)
    except Error as e:
        return problems + ["%s: the rename refuses %s's blob: %s" % (rel, a, e)], 1, 0
    got_text = got.decode("utf-8", "surrogateescape")
    if rel.endswith(".v") and any(k in KINDS for _s, _e, k in _safe_literals(text)):
        more, d = _verify_v(rel, text, want, got_text, n)
        return problems + more, 1, d
    if got_text != want:
        problems.append("%s: is not the rename of %s's blob" % (rel, a))
    return problems, 1, 0


# what `oft generate --check` prints for a generated file that is not its rendering
_NOT_RENDERED = re.compile(r"^(\S.*): (missing|differs from its rendering|generated file that the facts no longer "
                           r"produce; remove it)$")


def _generated_problems(repo, b):
    """The generated files of commit b that b's own tools do not render as b holds them: `oft generate --check
    --skip-shared`, with b's tools and facts, in a temporary worktree of b (removed afterwards).  A file the rename
    writes and the generator also writes (dune-project's `(name <opam stem>)` is no word-rule rename) is judged by what
    the generator makes of the new names."""
    from . import port      # port imports this module
    with tempfile.TemporaryDirectory(prefix="oft-verify-") as d:
        wt = os.path.join(d, "b")
        added = subprocess.run(["git", "-C", repo, "worktree", "add", "-q", "--detach", wt, b], capture_output=True)
        if added.returncode != 0:
            raise Error("git worktree add %s: %s" % (b, added.stderr.decode(errors="replace").strip()))
        try:
            done = port._own_python(wt, ["-m", "oft", "--root", wt, "generate", "--check", "--skip-shared"])
        finally:
            subprocess.run(["git", "-C", repo, "worktree", "remove", "--force", wt], capture_output=True)
    if done.returncode == 0:
        return []
    lines = (done.stdout + done.stderr).decode("utf-8", "replace").splitlines()
    problems = ["%s: %s's own tools render it otherwise (oft generate --check --skip-shared: %s)" % (m.group(1), b,
                                                                                                   m.group(2))
                for m in map(_NOT_RENDERED.match, lines) if m]
    problems += ["%s's facts: %s" % (b, line[len("error: "):]) for line in lines if line.startswith("error: ")]
    return problems or ["oft generate --check --skip-shared fails in %s: %s" % (b, lines[-1] if lines else
                                                                               "exit %d" % done.returncode)]


def verify(repo, a, b, jobs=None):
    """The problems found when commit b is compared with the rename of commit a, by the names of each one's
    release.yaml (keys.release_names):
      - every path that differs: a shared generated file (paths.is_shared) or a file of EXEMPT never does;
        release.yaml must be a's with the new names set; a generated file (paths.is_gen) must hold neither old name;
        any other text must be rename_text of a's blob, except that in a .v file each literal of a stored encoding
        must decode to a's literal's decoded value with each path's first component old replaced (_not_renamed, which
        reads a apart from the rename's code), the filler `~` aside;
      - a path only in a or only in b: an opam file of the old stem and its counterpart of the new, or a generated
        file;
      - every generated file of b is what b's own tools render from b's facts (_generated_problems);
      - no file of b outside EXEMPT and the shared generated files holds the old namespace or `rocq-<old stem>`."""
    return _verify(repo, a, b, jobs)[0]


def _verify(repo, a, b, jobs=None):
    """verify's problems, the files compared and the encoded literals decoded."""
    global _BLOBS
    from . import keys
    old, old_stem = keys.release_names(repo, a)
    new, new_stem = keys.release_names(repo, b)
    n = _Names(old, new, old_stem, new_stem)
    problems = []
    if (old, old_stem) == (new, new_stem):
        problems.append("release.yaml names %s and %s at both commits: %s is no rename of %s" % (old, old_stem, b, a))
    raw = _git_lines(repo, "diff-tree", "-r", "--no-renames", a, b)
    rows = [tuple(meta.lstrip(":").split()) + (rel,) for meta, rel in zip(raw[0::2], raw[1::2]) if meta]
    only_a = {r[5] for r in rows if r[4] == "D"}
    only_b = {r[5] for r in rows if r[4] == "A"}
    for rel in sorted(only_a):
        twin = re.sub(r"/rocq-%s-" % re.escape(old_stem), "/rocq-%s-" % new_stem, rel)
        if not ((_old_opam(rel, old_stem) and twin in only_b) or paths.is_gen(rel)):
            problems.append("%s: only in %s" % (rel, a))
    for rel in sorted(only_b):
        twin = re.sub(r"/rocq-%s-" % re.escape(new_stem), "/rocq-%s-" % old_stem, rel)
        if not ((_old_opam(rel, new_stem) and twin in only_a) or paths.is_gen(rel)):
            problems.append("%s: only in %s" % (rel, b))
    both = [r for r in rows if r[4] not in ("A", "D")]
    compared = decoded = 0
    for more, c, d in _map(_verify_one, both, jobs or (os.cpu_count() or 1), (repo, n, a)):
        problems += more
        compared += c
        decoded += d
    if _BLOBS is not None:      # the one this process opened when it compared the paths itself
        _BLOBS.close()
        _BLOBS = None
    for rel in _grep(repo, b, ["-F", "-e", old, "-e", n.stem_text]):
        if not paths.is_shared(rel):
            problems.append("%s: still holds %s or %s in %s" % (rel, old, n.stem_text, b))
    # a file the rename left as it is may hide the name in a stored encoding, which no search of the bytes finds; the
    # search below is a wider net than _HIDING_MARK, which _hidden applies
    differ = {r[5] for r in rows}
    hiding = [rel for rel in _grep(repo, b, ["-E", "-e", r"KReplay\.(lz_vm|run1z)|CDef\.cdeft"], "*.v")
              if rel not in differ and not paths.is_shared(rel)]
    problems += [p for p in _map(_hidden_one, hiding, jobs or (os.cpu_count() or 1), (repo, n, b)) if p]
    if _BLOBS is not None:
        _BLOBS.close()
        _BLOBS = None
    problems += _generated_problems(repo, b)
    return problems, compared, decoded


def _grep(repo, commit, args, glob="."):
    """The paths of commit, outside EXEMPT, that `git grep ARGS` matches."""
    pathspec = ["--", glob] + exclude_pathspecs()
    done = subprocess.run(["git", "-C", repo, "grep", "-l", "-z"] + args + [commit] + pathspec, capture_output=True)
    if done.returncode not in (0, 1):
        raise Error("git grep: %s" % done.stderr.decode(errors="replace").strip())
    return [hit.split(":", 1)[1] for hit in done.stdout.decode("utf-8", "surrogateescape").split("\0") if hit]


def _safe_literals(text):
    try:
        return literals(text)
    except Error:
        return []


def verify_cli(repo, a, b, jobs=None, out=sys.stdout):
    """`oft rename-namespace --verify A B`: exit 0 only with no problem."""
    problems, compared, decoded = _verify(repo, a, b, jobs=jobs)
    for p in problems:
        print("problem: %s" % p, file=out)
    print("verify: %d file(s) compared, %d encoded literals decoded; %d problem(s)"
          % (compared, decoded, len(problems)), file=out)
    return 1 if problems else 0


# --------------------------------------------------------------------------
# a tree
# --------------------------------------------------------------------------

STAGED = ".nsrename-new"


def _git_lines(root, *args):
    done = subprocess.run(["git", "-C", root, *args, "-z"], capture_output=True)
    if done.returncode != 0:
        raise Error("git %s: %s" % (" ".join(args), done.stderr.decode(errors="replace").strip()))
    return [p for p in done.stdout.decode("utf-8", "surrogateescape").split("\0") if p]


_JOB = None     # what each worker of _map reads: the arguments the caller of _map gives it, set by _init


def _init(job):
    global _JOB
    _JOB = job


def _tree_one(rel):
    """(rel, counts, whether it was staged, whether it already holds the new name, the error or None) of one file."""
    root, n, new_rules, check, shared = _JOB
    stats = _new_stats()
    path = os.path.join(root, rel)
    try:
        if os.path.islink(path) or not os.path.isfile(path):
            return rel, stats, False, False, None
        with open(path, "rb") as fh:
            data = fh.read()
        text = _decode(rel, data, n)
        if text is None:
            return rel, stats, False, False, None
        holds_new = any(rx.search(text) for rx in new_rules)
        if shared:
            return rel, stats, False, holds_new, None
        fresh = _rename(rel, text, n, stats, gate=True)
        staged = fresh != text
        if staged and not check:
            with open(path + STAGED, "w", encoding="utf-8", newline="") as fh:
                fh.write(fresh)
            shutil.copymode(path, path + STAGED)    # tests/check.sh is run as ./tests/check.sh
        return rel, stats, staged, holds_new, None
    except Error as e:
        return rel, stats, False, False, str(e)
    except Exception as e:      # a decoder fault is a refusal too
        return rel, stats, False, False, "%s: %s: %s" % (rel, type(e).__name__, e)


def _map(fn, items, jobs, job):
    if jobs > 1 and len(items) > 64:
        with multiprocessing.get_context("fork").Pool(jobs, initializer=_init, initargs=(job,)) as pool:
            return list(pool.imap(fn, items, chunksize=32))
    _init(job)
    return [fn(rel) for rel in items]


def _hidden(rel, data, n):
    """The problem of a .v file whose stored encodings decode to the old name although its text does not hold it, or
    None (as _rename's probe reads it: a file it cannot lex holds no name in its text)."""
    if not rel.endswith(".v") or not _HIDING_MARK.search(data.decode("utf-8", "replace")):
        return None
    try:
        text = data.decode("utf-8")
        lits = literals(text)
    except (Error, UnicodeDecodeError):
        return None
    try:
        parsed, records, _offsets = _gate(rel, text, _codec_blobs(text, lits), n.old, _new_stats())
    except Error as e:
        return str(e)
    if _decoded_old(parsed, records, n.old):
        return "%s: a stored encoding still decodes to %s" % (rel, n.old)
    return None


def _after_one(rel):
    """The problem of one file after the rename, or None: it holds the old name or `rocq-<old stem>`, or a stored
    encoding of a .v file decodes to the old name (_hidden)."""
    root, n, _new, _check, _shared = _JOB
    path = os.path.join(root, rel)
    if os.path.islink(path) or not os.path.isfile(path):
        return None
    with open(path, "rb") as fh:
        data = fh.read()
    if n.old.encode() in data or n.stem_text.encode() in data:
        return "%s: still holds %s or %s" % (rel, n.old, n.stem_text)
    return _hidden(rel, data, n)


def _hidden_one(rel):
    """_hidden of rel's blob at commit b, for verify."""
    global _BLOBS
    repo, n, b = _JOB
    if _BLOBS is None or _BLOBS.repo != repo:
        _BLOBS = _Blobs(repo)
    return _hidden(rel, _BLOBS.get("%s:%s" % (b, rel)), n)


def rename_tree(root, new, new_stem, check=False, jobs=None, out=sys.stdout):
    """`oft rename-namespace --to NEW --opam-stem STEM` on root, a git checkout: rename its namespace and opam stem
    (release.yaml's, or the defaults) to new and new_stem in every tracked file but the ones EXEMPT names and the shared
    generated files, set both in release.yaml, remove the opam files of the old stem and render the generated files
    again (`oft generate --skip-shared`).  It refuses, and writes nothing, when release.yaml already names new, when a
    tracked path holds the old name or is not in the checkout (a sparse checkout would be half renamed), when a tracked
    file differs from HEAD, when a file outside EXEMPT already holds the new name or `rocq-<new stem>` (the rename must
    be one-to-one), or when any file fails the before-gate or the rename; every refusal is printed.  Then the
    after-gate: no file outside EXEMPT and the shared generated files holds the old name or `rocq-<old stem>`, and no
    stored encoding decodes to the old name.  With check it stops before writing.  Exit 0, or 1."""
    root = os.path.abspath(root)
    try:
        _check_names(new, new_stem)
        old, old_stem = facts.read_release_names(root)
        tracked = _git_lines(root, "ls-files")
        dirty = _git_lines(root, "status", "--porcelain", "--untracked-files=no")
    except Error as e:
        print("rename-namespace: %s" % e, file=out)
        return 1
    n = _Names(old, new, old_stem, new_stem)
    new_rules = (_word(new), _stem(new_stem))
    problems = []
    if new == old:
        problems.append("release.yaml already names the namespace %s" % new)
    problems += ["%s: a path that holds %s" % (rel, old) for rel in tracked if old in rel]
    missing = [rel for rel in tracked if not os.path.lexists(os.path.join(root, rel))]
    if missing:
        problems.append("%d tracked file(s) are not in this checkout (a sparse checkout, say), among them %s: the "
                        "rename runs on a whole checkout" % (len(missing), ", ".join(missing[:5])))
    if dirty:
        problems.append("%d tracked file(s) differ from HEAD, among them %s: commit or drop them first (the rename "
                        "removes files with git rm, and writes nothing unless every step can pass)"
                        % (len(dirty), ", ".join(line[3:] for line in dirty[:5])))
    opams = [rel for rel in tracked if _old_opam(rel, old_stem)]
    gone = set(opams)
    files = [rel for rel in tracked if not exempt(rel) and rel not in gone]
    hand = [rel for rel in files if not paths.is_shared(rel)]
    shared = [rel for rel in files if paths.is_shared(rel)]
    jobs = jobs or (os.cpu_count() or 1)
    results = (_map(_tree_one, hand, jobs, (root, n, new_rules, check, False))
               + _map(_tree_one, shared, jobs, (root, n, new_rules, check, True)))
    staged = []
    totals = _new_stats()
    unparsed = []
    for rel, stats, was_staged, holds_new, err in results:
        if err:
            problems.append(err)
        if holds_new:
            problems.append("%s: already holds %s or rocq-%s, so the rename would not be one-to-one"
                            % (rel, new, new_stem))
        if was_staged:
            staged.append(rel)
        for k in ("encoded", "dotted", "plain", "decoded"):
            totals[k] += stats[k]
        unparsed += [(rel, kind, i) for kind, i in stats["unparsed"]]
    for rel, kind, i in unparsed:
        print("unparsed %s %s %d" % (rel, kind, i), file=out)
    per_unit = {}
    for rel, _kind, _i in unparsed:
        unit = layout.unit_of(rel) or os.path.dirname(rel)
        per_unit[unit] = per_unit.get(unit, 0) + 1
    for unit in sorted(per_unit):
        print("unparsed in %s: %d blob(s)" % (unit, per_unit[unit]), file=out)

    def drop_staged():
        for rel in staged:
            try:
                os.remove(os.path.join(root, rel + STAGED))
            except OSError:
                pass

    if problems:
        drop_staged()
        for p in problems:
            print("refused %s" % p, file=out)
        print("rename-namespace: %d problem(s); nothing written" % len(problems), file=out)
        return 1
    summary = ("%d file(s) renamed (%d encoded literals, %d dotted-name literals, %d plain lines); %d blob(s) left "
               "unparsed (listed above); %d opam files renamed"
               % (len(staged), totals["encoded"], totals["dotted"], totals["plain"], len(unparsed), len(opams)))
    if check:
        print("rename-namespace --check: %s; 0 problem(s); nothing written" % summary, file=out)
        return 0
    for rel in staged:
        os.replace(os.path.join(root, rel + STAGED), os.path.join(root, rel))
    release = os.path.join(root, "release.yaml")
    with open(release, encoding="utf-8") as fh:
        text = fh.read()
    with open(release, "w", encoding="utf-8", newline="") as fh:
        fh.write(set_release_names(text, new, new_stem))
    if opams:
        subprocess.run(["git", "-C", root, "rm", "-q", "--pathspec-from-file=-", "--pathspec-file-nul"],
                       input="\0".join(opams).encode("utf-8", "surrogateescape"), check=True, capture_output=True)
    if generate.run(root, shared=False, out=out) != 0:
        print("rename-namespace: the generated files do not render after the rename; 1 problem(s)", file=out)
        return 1
    problems = ["%s: its opam file of the new stem was not rendered" % rel for rel in opams
                if not os.path.isfile(os.path.join(root, re.sub(r"/rocq-%s-" % re.escape(old_stem),
                                                                 "/rocq-%s-" % new_stem, rel)))]
    now = sorted(set(_git_lines(root, "ls-files"))
                 | set(_git_lines(root, "ls-files", "--others", "--exclude-standard")))
    scan = [rel for rel in now if not exempt(rel) and not paths.is_shared(rel)]
    problems += [p for p in _map(_after_one, scan, jobs, (root, n, new_rules, False, False)) if p]
    for p in problems:
        print("after the rename: %s" % p, file=out)
    if problems:
        print("rename-namespace: %d problem(s) after the rename" % len(problems), file=out)
        return 1
    print("rename-namespace: %s; 0 problem(s)" % summary, file=out)
    return 0
