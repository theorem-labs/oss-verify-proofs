#!/usr/bin/env python3
"""rolenames.py -- the one place that knows how a session name is written in a shipped file: it is not. A ruling is
cited by the ROLE that made it ("the unit owner's ruling"), and no shipped file holds a time of day (`untime`), so no
fact of a record depends on which session ruled or when in the day. Read-only; used by kitscrub.py (this record's
copies of another owner's tools), earlierscrub.py, scrub_out.py (the refusal over the committed copy) and mkdiffs.py
(which removed lines of a diff it may show).

A NAME is a session name of the session roster: a lowercase prefix, a dash and lowercase words (`h-...` a lane's worker,
`port-...` / `fmb-...` a lane, `c-...` an owner of a shared piece, `r-...` a stream's root, `g-...` a group). Matched
case-sensitively (so `C-string` and `EQUAL-mod-pcrel` are not names) and word-bounded as the scanner of record bounds
them, except that a name may follow a dash which itself starts a line or follows no letter, digit, `_`, `.` or `/`
(a diff's removed line `-<name> ...`, an option `--<name>`); a name inside a longer dashed token (`x-<name>`) is
still not a name.
`names(path)` reads the roster's column 1 (the names that carry a dash); with a roster at hand the rewrite and
the refusal cover every name in it and every STEM of one, and without one they cover the shapes above, which is what
the scanner blocks.
A STEM is a roster name without its role prefix, and each shorter tail of its dashed words (`h-<x>-<y>-<z>` gives
`<x>-<y>-<z>` and `<y>-<z>`), kept when it holds a digit or a dash and is STEM_MIN characters or longer, so that no
plain word is one: a session is often cited by its stem alone. `stems(names)` derives them from the roster, so this file
holds none, and gives each the role of the name it comes from; a stem that two names of different roles share has no
one role, and the rewrite refuses it (the refusal still finds it). A stem is bounded as a name is, and is not a stem
before `.<digit>` (a longer number). NOT_STEMS lists a stem that is a real kit or code term: it is never rewritten
or refused.

ROLE_OF gives the role, from the prefix and the first word -- never from a list of names, which would put the names
back into a shipped file:
    r-<x>             the unit owner        a `c-` name whose first word is libc: the libc owner
    c-<x>             the <x> owner         g-<x>                a group lane
    h-<x>-<y>, port-<x>, fmb-<x>            a lane
EXTRA adds a name that has no roster shape: the coordinating session of this lane, which is `this lane`; and every
agent name of the lists in the directory NAMES_DIR names (env.sh; each `names-*.txt` there, one name a line, outside
every slice): an agent whose name holds `Review` or `Read` is `a fresh reviewer`, any other `a helper session`, and a
name there with a lane shape keeps the role its shape gives. Every writer stops when NAMES_DIR is unset or names no
directory. This file holds no session name, and no word the scanner of record blocks, in any form: what it, or a
writer, must know of them is read at run time by `private(key)` from the file SCRUB_FORBIDDEN names (env.sh; outside
every slice), from NAMES_DIR and from ROSTER_TXT, and every writer stops when that file or a key of it is missing.
ROSTER_TXT (env.sh; the registry's frozen roster.txt, outside every slice) is a further roster: its `w` and `r` names
(in any case), `a` agent ids and `l` lane prefixes (as written; never an `n`, `p` or `m` entry, which is no name) are
names too, matched as whole tokens; an agent id gets the role of a NAMES_DIR agent, and one cited as `(<id>: x` or
`(<id>, x` is dropped with its separator, the claim kept. NOT_NAMES lists a roster entry that is an ordinary word
here (`lead`, the word this docstring uses). Every writer stops when ROSTER_TXT names no file.

RULES rewrite the forms these records use, in order, so that the sentence still reads (`keep_time=True` keeps the time,
for a writer that must tell the two rewrites apart; by default `untime` then drops it):
    `ruling <name> HH:MMZ`        -> `ruling of the unit owner`
    `the <name> rulings`          -> `the unit owner's rulings`
    `<name> HH:MMZ ruled`         -> `the unit owner ruled,`
    `<name> HH:MMZ's literal test,`-> `the literal test of the unit owner's ruling,`
    `<name> HH:MMZ keeps`         -> `the unit owner's ruling keeps`
    `<name> HH:MMZ);`             -> `the unit owner's ruling);`
    `<name> confirmed`            -> `the unit owner confirmed`
    `<name>'s`                    -> `the unit owner's`
    `<name>`                      -> `the unit owner`
(`HH:MMZ` stands for a time of day in a source, here and in the comments below).
`untime(text)` drops every time of day (TIME_OF_DAY: `HH:MMZ`, `HH:MM:SSZ`, `HH:MxZ`, `HH:xxZ`; a date and a machine
stamp such as `20261031T214002Z` stay) with the punctuation that only served it: `(T)` goes whole, `(T: x` becomes
`(x`, `, T` and ` of T` and ` T` go, and every line keeps its place. `left_in(data)` lists a name a rule missed;
`times_in(data)` lists a time of day left; the writers refuse on both. `redact(text)` removes every name instead, for a
text that must not be reworded (a diff's removed line keeps its old bytes or none of them)."""
import functools, glob, os, re


def private(key):
    """the value of `key` in the file SCRUB_FORBIDDEN names (one `key<TAB>value` row each, `#` comments); exits when
    the file or the key is missing"""
    p = os.environ.get('SCRUB_FORBIDDEN', '')
    if not p or not os.path.isfile(p):
        raise SystemExit('rolenames: SCRUB_FORBIDDEN names no file (%r): refusing to run' % p)
    for line in open(p):
        if line[:1] != '#' and line.split('\t', 1)[0] == key:
            return line.rstrip('\n').split('\t', 1)[1]
    raise SystemExit('rolenames: %s has no %r row: refusing to run' % (p, key))


def private_rows(key):
    """every value of `key` in the file SCRUB_FORBIDDEN names, in order (none is an empty list)"""
    p = os.environ.get('SCRUB_FORBIDDEN', '')
    if not p or not os.path.isfile(p):
        raise SystemExit('rolenames: SCRUB_FORBIDDEN names no file (%r): refusing to run' % p)
    return [l.rstrip('\n').split('\t', 1)[1] for l in open(p) if l[:1] != '#' and l.split('\t', 1)[0] == key]


LEFT = r'(?<![A-Za-z0-9_./])(?<![A-Za-z0-9_./]-)'
RIGHT = r'(?![A-Za-z0-9_-])'
RIGHT_STEM = r'(?![A-Za-z0-9_-]|\.[0-9])'
STEM_MIN = 4
NOT_STEMS = frozenset()      # a stem that is a real kit or code term (none is known; see stems())
# the name shapes the scanner of record blocks, for a check with no roster at hand
SHAPES = (r'[cr]-[a-z]+(?:-[a-z0-9]+)*'
          r'|h-[a-z][a-z0-9]+(?:-[a-z0-9_]+)+'
          r'|port-(?!(?:built|commit|table|slot|license|prefix|hash)(?![a-z0-9_]))[a-z][a-z0-9]*(?:-[a-z0-9_]+)*'
          r'|fmb-[a-z0-9]+|g-[a-z][a-z0-9]*(?:-[a-z0-9]+)+')
EXTRA = dict([private('rolenames.EXTRA').split('\t')])


def _agents():
    """{agent name: its role} of every names-*.txt in NAMES_DIR"""
    d = os.environ.get('NAMES_DIR', '')
    if not d or not os.path.isdir(d):
        raise SystemExit('rolenames: NAMES_DIR names no directory (%r): refusing to run' % d)
    out = {}
    for f in sorted(glob.glob(os.path.join(d, 'names-*.txt'))):
        for l in open(f):
            n = l.strip()
            if n and not n.startswith('#'):
                out[n] = 'a fresh reviewer' if re.search(r'Review|Read', n) else 'a helper session'
    if not out: raise SystemExit('rolenames: NAMES_DIR %s holds no names-*.txt name: refusing to run' % d)
    return out


AGENTS = _agents()
for _n, _r in AGENTS.items():
    if not re.fullmatch(SHAPES, _n):     # a lane name of the lists keeps the role its shape gives (role_of)
        EXTRA.setdefault(_n, _r)


NOT_NAMES = frozenset({'lead'})   # roster entries that are ordinary words here (rolenames' own docstring uses `lead`)


def _roster_txt():
    """{name: its role} of the frozen roster ROSTER_TXT names (one `<kind> <name>` row each): `w` and `r` names (folded,
    matched in any case), `a` agent ids and `l` lane prefixes (as written); never an `n`, `p` or `m` entry (a module, a
    project word, a module-named file: no name). The role is the one its shape gives (role_of), and an agent id's is
    `a fresh reviewer` or `a helper session` as for NAMES_DIR"""
    p = os.environ.get('ROSTER_TXT', '')
    if not p or not os.path.isfile(p):
        raise SystemExit('rolenames: ROSTER_TXT names no file (%r): refusing to run' % p)
    kinds = {}
    for l in open(p):
        if l[:1] == '#' or not l.strip(): continue
        k, _, n = l.rstrip('\n').partition(' ')
        kinds.setdefault(k, set()).add(n)
    no = kinds.get('n', set()) | kinds.get('p', set()) | kinds.get('m', set())
    exact, folded = {}, {}
    for n in kinds.get('a', set()) - no:
        exact[n] = 'a fresh reviewer' if re.search(r'Review|Read', n) else 'a helper session'
    for n in kinds.get('l', set()) - no: exact.setdefault(n, 'a lane')
    nol = {x.lower() for x in no}
    for n in kinds.get('w', set()) | kinds.get('r', set()):
        if n.lower() not in nol: folded[n.lower()] = None
    return exact, folded


RT_EXACT, RT_FOLDED = _roster_txt()
TOKEN = re.compile(r'(?<![A-Za-z0-9_./-])[A-Za-z0-9](?:[A-Za-z0-9_.-]*[A-Za-z0-9])?(?![A-Za-z0-9_-])')


def _rt_name(tok):
    """(the roster.txt name, its role) when the whole token is one; else None"""
    if tok in NOT_NAMES or tok.lower() in NOT_NAMES: return None
    if tok in RT_EXACT: return tok, RT_EXACT[tok]
    if tok.lower() in RT_FOLDED: return tok, role_of(tok)
    return None


def _rt_sub(text, how, drop=True):
    """text with each roster.txt name replaced by how(name, role); with drop, an agent id cited as `(<id>: x` or
    `(<id>, x` is dropped with its separator and the claim kept (`(x`)"""
    out, last = [], 0
    for m in TOKEN.finditer(text):
        hit = _rt_name(m.group())
        if not hit: continue
        a, b = m.start(), m.end()
        if drop and hit[1] in ('a fresh reviewer', 'a helper session') and text[a - 1:a] == '(' \
                and text[b:b + 2] in (': ', ', '):
            out.append(text[last:a]); last = b + 2; continue
        out.append(text[last:a]); out.append(how(hit[0], hit[1])); last = b
    out.append(text[last:])
    return ''.join(out)


def rt_left_in(data):
    """every roster.txt name in bytes `data`: (offset, name)"""
    t = data.decode('utf-8', errors='replace')
    return [(m.start(), m.group()) for m in TOKEN.finditer(t) if _rt_name(m.group())]


TIME = r'[0-2][0-9]:[0-5x][0-9x]Z?Z?'
TIME_OF_DAY = r'(?<![0-9A-Za-z])[0-2]?[0-9]:[0-5x][0-9x](?::[0-5][0-9])?Z(?![A-Za-z0-9])'
GAP = r'(?P<g>\s+)'          # kept as it was: a citation may wrap, and a copy keeps every line in its place
SAID = r'ruled|confirmed|said'
VERBS = r'ruled|confirmed|commissioned|asks|wants|keeps|counts|measured|chose|ran|says|read'


def role_of(name):
    """the role to write instead of this session name"""
    if name in EXTRA: return EXTRA[name]
    pre, _, rest = name.partition('-')
    first = rest.split('-')[0]
    if pre == 'r': return 'the unit owner'
    if pre == 'c': return 'the libc owner' if first == 'libc' else 'the %s owner' % first
    if pre == 'g': return 'a group lane'
    return 'a lane'


@functools.lru_cache(maxsize=None)
def _stems(extra):
    """{stem: its role, or None when the names it comes from have different roles} of the names `extra` (a tuple)"""
    roles = {}
    for n in extra:
        w = n.split('-')
        for i in range(1, len(w)):
            s = '-'.join(w[i:])
            if len(s) >= STEM_MIN and re.search(r'[0-9-]', s) and s not in NOT_STEMS:
                roles.setdefault(s, set()).add(role_of(n))
    full = set(extra) | set(EXTRA)
    return {s: (next(iter(r)) if len(r) == 1 else None) for s, r in roles.items() if s not in full}


def stems(extra=()):
    """the stems of the names `extra` (a roster's column 1), each with the role of the name it comes from"""
    return dict(_stems(tuple(extra)))


@functools.lru_cache(maxsize=None)
def _pat(extra):
    alts = [SHAPES] + [re.escape(e) for e in sorted(set(list(extra) + list(EXTRA)), key=len, reverse=True)]
    pat = LEFT + '(?:(?:' + '|'.join(alts) + ')' + RIGHT
    st = sorted(_stems(extra), key=len, reverse=True)
    if st: pat += '|(?:' + '|'.join(re.escape(s) for s in st) + ')' + RIGHT_STEM
    return pat + ')'


def _name_pat(extra=()):
    return _pat(tuple(extra))


def untime(text):
    """text with every time of day dropped, with the punctuation that only served it; no line is added or removed"""
    T = TIME_OF_DAY
    for pat, rep in ((r'[ \t]*\(' + T + r'\)', ''),                       # `accepted (HH:MMZ).` -> `accepted.`
                     (r'\(' + T + r'[:,]?[ \t]*', '('),                    # `(HH:MMZ: ld ...` -> `(ld ...`
                     (r'[ \t]+of[ \t]+' + T, ''),                         # `ruling of HH:MMZ keeps` -> `ruling keeps`
                     (r',[ \t]*' + T, ''),                                # `ruling, HH:MMZ)` -> `ruling)`
                     (r',(\n[ \t]*(?:#[ \t]*)?)' + T + r'\)', r')\1'),      # `ruling,` / `HH:MMZ): x` -> `ruling)` / `: x`
                     (r',(\n[ \t]*(?:#[ \t]*)?)' + T + r'[ \t]*', r'\1'),  # the time wrapped onto the next line
                     (r'[ \t]+' + T, ''),                                 # `measured HH:MMZ:` -> `measured:`
                     (T + r'[ \t]*', '')):                                # anything left
        text = re.sub(pat, rep, text)
    return text


def times_in(data):
    """every time of day left in bytes `data`: (offset, the time)"""
    return [(m.start(), m.group().decode()) for m in re.finditer(TIME_OF_DAY.encode(), data)]


def rewrite(text, extra=(), keep_time=False):
    """text with every session name, and every stem of one, written as its role, and (unless keep_time) every time
    of day dropped. `extra`: further names (a roster's column 1), whose stems are rewritten too."""
    N = '(?P<n>%s)' % _name_pat(extra)
    T = '(?P<t>%s)' % TIME
    st = _stems(tuple(extra))
    def r(m):
        n = m.group('n')
        if n not in st: return role_of(n)
        if st[n] is None: raise ValueError('rolenames: a stem of names with different roles: %r' % n)
        return st[n]
    rules = [
        # a citation that already says "ruling": do not say it twice
        (r'\bruling' + GAP + N + r'\s+' + T, lambda m: 'ruling of %s,%s%s' % (r(m), m.group('g'), m.group('t'))),
        (r'\bthe' + GAP + N + r'\s+rulings', lambda m: "%s's%srulings" % (r(m), m.group('g'))),
        # the act of ruling, at that time
        (N + GAP + T + r'\s+(?P<v>' + SAID + r')\b',
         lambda m: '%s %s,%s%s,' % (r(m), m.group('v'), m.group('g'), m.group('t'))),
        # the time's own possessive: "<name> HH:MMZ's literal test," -> "the literal test of <role>'s ruling, HH:MMZ,"
        (N + GAP + T + r"'s\s+(?P<x>[a-z][a-z ]*?)(?=[,.;:)])",
         lambda m: "the %s of %s's ruling,%s%s" % (m.group('x'), r(m), m.group('g'), m.group('t'))),
        # a word follows the citation: "of <time>" keeps the sentence running
        (N + GAP + T + r'(?=\s+[a-z])', lambda m: "%s's ruling of%s%s" % (r(m), m.group('g'), m.group('t'))),
        # the citation ends here
        (N + GAP + T, lambda m: "%s's ruling,%s%s" % (r(m), m.group('g'), m.group('t'))),
        # a date instead of a time
        (N + GAP + r'(?P<d>20[0-9]{2}-[01][0-9]-[0-3][0-9])',
         lambda m: "%s's instruction of%s%s" % (r(m), m.group('g'), m.group('d'))),
        (N + GAP + r'(?P<v>' + VERBS + r')\b', lambda m: '%s%s%s' % (r(m), m.group('g'), m.group('v'))),
        (N + r"'s", lambda m: "%s's" % r(m)),
        (N, r),
    ]
    for pat, rep in rules:
        text = re.sub(pat, rep, text)
    text = _rt_sub(text, lambda n, role: role)          # the names of ROSTER_TXT (an agent id cited is dropped)
    return text if keep_time else untime(text)


def names(path):
    """the session names of a roster file: column 1, the names that carry a dash (`lead` and the other hyphen-less
    names are ordinary words)"""
    out = []
    for i, line in enumerate(open(path)):
        f = line.rstrip('\n').split('\t')
        if i and f and '-' in f[0]: out.append(f[0])
    return sorted(set(out), key=len, reverse=True)


def redact(text, extra=()):
    """text with every session name, and every stem of one, replaced by `<redacted>` and nothing reworded (`extra`: a
    roster's column 1)"""
    return _rt_sub(re.sub(_name_pat(extra), '<redacted>', text), lambda n, role: '<redacted>', drop=False)


def left_in(data, extra=()):
    """every session name left in bytes `data`: the shapes always, plus `extra` (a roster) and its stems when given,
    and every name of ROSTER_TXT"""
    rx = re.compile(_name_pat(extra).encode())
    return [(m.start(), m.group().decode(errors='replace')) for m in rx.finditer(data)] + rt_left_in(data)
