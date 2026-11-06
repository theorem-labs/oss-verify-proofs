#!/usr/bin/env python3
"""kitscrub.py -- the writer of this record's copies of the cmpkit 86da41d3ef68 files, and of jtcheck 226254f48c97 (from the
original sha256 226254f48c97; tools/DIFFS.md: the jtcheck of record for table verdicts, which supersedes the kit's jtcheck 8b0ea3862423; read with
`--from`). Read-only on KIT_DIR; writes OUT_DIR. The kit files hold host paths, session names and the registry's
branch name in their comments and in a few constants; the committed slice may hold none of these. So each copy is
the original file with exactly these changes:
  - a session's citation is dropped and its claim kept (CITE: `(<name>, x` -> `(x`, `<name>'s plant` -> `a plant`, a
    session's path or branch -> the claim it supports, in the forms of the first copies these records shipped), and the
    kit's plain word `lane` (its word for a work stream, no session's name) is reworded (`a record`) or dropped. CITE is a
    declared table of (file, the kit's text, its replacement) read at run time from SCRUB_FORBIDDEN, key
    `kitscrub.CITE` (its kit texts hold the names and paths, so this file cannot); each kit text must be found exactly
    once, and a replacement keeps the line count. After it, every remaining session name becomes its ROLE and every
    time of day is dropped (`rolenames.py`: `the unit owner's ruling`), so that no fact of the record depends on which
    session ruled or when; the tool registry's branch name becomes `the tool registry`. A copy that still holds a
    placeholder (PLACEHOLDER: a role or path placeholder a session's citation would leave) is refused, so a citation CITE does not cover
    stops the writer. A session name may only be rewritten inside a comment or a docstring: the copy's syntax tree,
    docstrings left out, must equal the tree before that rewrite (checked; the copy is refused otherwise);
  - in jtcheck.py, the README item each comment cites and the counts it gives, set to the package's own README and
    controls (JT_WORDS below: the escaping-base switch is README A5 and costs 48 -> 30 acceptances, 18 of 48
    tables, as controls/escmeas.out and esccost.out measure; the psABI is A1; no README item covers the FP-store
    sentence, so its label goes); each text must be found exactly once;
  - a code line that holds a path under the mnt root (repin_check.py's IMG / PIN, bytecmp's `base`, only read by those
    files' own `main`, which these records never run) reads that path from the environment instead, defaulting to
    empty: `os.environ.get('KIT_<FILE>_<KEY>', '')`;
  - every line keeps its place (no line is added or removed), so drvcmp's two block checks over repin_check.py
    lines 31-80 and 209-231 still read the same text;
  - the sha256 constants the kit uses to pin its own files are set to the copies: drvcmp's BC_SHA (bytecmp) and
    jtcheck's strictcmp3.py / drvcmp.py pins; drvcmp's CLASS_SHA / TARGETS_SHA are recomputed and must not change;
  - the docstring words on those pins say what they name (PIN_WORDS below): jtcheck's lists the kit originals and says
    that the pins are set to this record's copies; drvcmp's names the bytecmp it checks as this record's copy, by its
    sha256, of bytecmp 1480ca2faea0. Each such text must be found exactly once in the kit file, or the copy is refused.
The code logic is unchanged; tools/DIFFS.md (mkdiffs.py) gives each copy's whole diff against its original (for
jtcheck.py, the registry's file). The
patterns of the text removed (branch, registry, host paths) are read at run time from the file SCRUB_FORBIDDEN names
(rolenames.private), so that this file spells none of them in any form; it stops when that file is missing.
usage: kitscrub.py KIT_DIR OUT_DIR [--from FILE=PATH ...]   (FILE is read from PATH instead of KIT_DIR)"""
import ast, hashlib, importlib.util, os, re, sys

_spec = importlib.util.spec_from_file_location('rolenames', os.path.join(os.path.dirname(os.path.abspath(__file__)), 'rolenames.py'))
rolenames = importlib.util.module_from_spec(_spec); _spec.loader.exec_module(rolenames)

FILES = ['bytecmp-1480ca2faea0.py', 'repin_check.py', 'strictcmp3.py', 'closure_strict3.py', 'paircl.py', 'luiscan.py',
         'ambiscan.py', 'drvcmp.py', 'jtcheck.py']
# the patterns of the text removed are read from SCRUB_FORBIDDEN; the session names and their roles are rolenames.py's
BRANCH = re.compile(rolenames.private('kitscrub.BRANCH'))
REGISTRY = re.compile(rolenames.private('kitscrub.REGISTRY'))
HOMEP = re.compile(rolenames.private('kitscrub.HOMEP'))
MNTQ = re.compile(rolenames.private('kitscrub.MNTQ'))
FORBIDDEN = re.compile(rolenames.private('kitscrub.FORBIDDEN'), re.I)
REGWORD = re.compile(rolenames.private('kitscrub.REGWORD'), re.I)
def _unesc(x): return x.replace('\\n', '\n').replace('\\t', '\t').replace('\\\\', '\\')
CITE = [tuple(_unesc(v) for v in r.split('\t')) for r in rolenames.private_rows('kitscrub.CITE')]
PLACEHOLDER = re.compile(r"\ba lane\b|\blanes\b|\blane's\b|\bthis lane\b|<a lane path>|a lane branch|\bthe libc owner\b(?!'s ruling)")
# (the kit's text, its replacement) in jtcheck.py: the README item labels and counts its comments cite
JT_WORDS = [
    ("# STORED TO MEMORY: the bytes settle it, the refusal is ON and it costs nothing - of the 63 tables the",
     "# STORED TO MEMORY: the bytes settle it, the refusal is ON and it costs nothing - of the 48 tables the"),
    ("# and the refusal is OFF by default - it flags 24 of those 63 and would cost 32 of 89 acceptances on the",
     "# and the refusal is OFF by default - it flags 18 of those 48, and turning it on costs 48 -> 30 acceptances on the"),
    ("# record pairs (README A6, controls/escmeas.out and esccost.out).",
     "# record pairs (README A5, controls/escmeas.out and esccost.out)."),
    ("refuses here as it does at a write. The psABI assumption A3 does not cover a return address the bytes",
     "refuses here as it does at a write. The psABI assumption A1 does not cover a return address the bytes"),
    ("write one (README A3). The integer source is rs1 in all four.",
     "write one. The integer source is rs1 in all four."),
    ("register may be dead), so it refuses only when `args` is set (README A6). None when it never leaves.",
     "register may be dead), so it refuses only when `args` is set (README A5). None when it never leaves."),
]
# (file, the kit's text, its replacement): the docstring words on the kit's own sha pins, set to say what they pin.
# `{bc}` is the 12-character sha256 of this record's bytecmp copy. A replacement keeps its line (no newline).
PIN_WORDS = [
    ('jtcheck.py', "Loads the comparison kit beside it, checking each file's sha256:",
     "Loads the comparison kit beside it; named here are the kit originals, the pins below are set to this record's copies:"),
    ('drvcmp.py', '  - bytecmp 1480ca2faea0 (the tool registry tools/bytecmp/1480ca2faea0, version of record; file sha256 '
                  'checked below),',
     '  - copy {bc} of bytecmp 1480ca2faea0 (tool registry tools/bytecmp/1480ca2faea0, version of record; the copy\'s '
     'sha256 checked below),'),
]

def code_tree(text):
    """the syntax tree of a Python file with every docstring left out (module, class and function docstrings)"""
    t = ast.parse(text)
    for node in ast.walk(t):
        if isinstance(node, (ast.Module, ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef)) and node.body and \
                isinstance(node.body[0], ast.Expr) and isinstance(getattr(node.body[0], 'value', None), ast.Constant) and \
                isinstance(node.body[0].value.value, str):
            node.body = node.body[1:]
    return ast.dump(t)

def sha(b): return hashlib.sha256(b).hexdigest()

def scrub(name, text, roster=()):
    """the copy: the session names as their roles (over the whole text, so a citation that wraps keeps its line), then
    per line the branch, registry and host-path rules and the mnt paths read from the environment"""
    out = []; n = 0
    key = re.sub(r'[^A-Z0-9]', '_', name.split('.')[0].upper())
    for ln, (line, named) in enumerate(zip(text.split('\n'), rolenames.rewrite(text, roster).split('\n')), 1):
        new = named
        if MNTQ.search(new) and not new.lstrip().startswith('#'):
            k = [0]
            def env(m):
                k[0] += 1
                return "os.environ.get('KIT_%s_%d_%d', '')" % (key, ln, k[0])
            new = MNTQ.sub(env, new)
        new = BRANCH.sub('a lane branch', new)
        new = REGISTRY.sub('the tool registry', new)
        new = HOMEP.sub('<a lane path>', new)
        new = REGWORD.sub('registry', new)
        if new != line: n += 1
        out.append(new)
    return '\n'.join(out), n

def name_only(text, roster=()):
    """text with the session names written as their roles, the times of day dropped, and nothing else (for the
    syntax-tree check)"""
    return rolenames.rewrite(text, roster)


def main():
    kd, od = sys.argv[1], sys.argv[2]
    src = {f: os.path.join(kd, f) for f in FILES}
    rest = sys.argv[3:]
    while rest:
        if rest[0] != '--from' or len(rest) < 2 or rest[1].split('=', 1)[0] not in src:
            raise SystemExit('usage: kitscrub.py KIT_DIR OUT_DIR [--from FILE=PATH ...]')
        f, p = rest[1].split('=', 1); src[f] = p; rest = rest[2:]
    os.makedirs(od, exist_ok=True)
    texts, changed = {}, {}
    roster = rolenames.names(os.environ['ROSTER_TSV']) if os.environ.get('ROSTER_TSV') else ()
    for f in FILES:
        t = open(src[f]).read()
        if code_tree(name_only(t, roster)) != code_tree(t):
            raise SystemExit('kitscrub: %s holds a session name outside a comment or a docstring: refusing' % f)
        c = t
        for g, was, now in CITE:
            if g != f: continue
            if c.count(was) != 1 or was.count('\n') != now.count('\n'):
                raise SystemExit('kitscrub: %s: the CITE text %r is found %d times, or its replacement changes the line '
                                 'count: refusing' % (f, was[:40], c.count(was)))
            c = c.replace(was, now)
        if code_tree(c) != code_tree(t):
            raise SystemExit('kitscrub: %s: a CITE rewrite changed code: refusing' % f)
        if f == 'jtcheck.py':
            for was, now in JT_WORDS:
                if c.count(was) != 1:
                    raise SystemExit('kitscrub: jtcheck.py holds %d copies of %r, not 1: refusing' % (c.count(was), was[:40]))
                c = c.replace(was, now)
            if code_tree(c) != code_tree(t):
                raise SystemExit('kitscrub: jtcheck.py: a JT_WORDS rewrite changed code: refusing')
        texts[f], changed[f] = scrub(f, c, roster)
    # bytecmp and repin_check read os.environ now where they read a path: both already import os?
    for f in ('bytecmp-1480ca2faea0.py', 'repin_check.py'):
        t = texts[f]
        if "os.environ.get('KIT_" in t and not re.search(r'^import [^\n]*\bos\b', t, re.M):
            t = re.sub(r'^(import [^\n]*)$', r'\1, os', t, count=1, flags=re.M)
            texts[f] = t
    # the kit's own pins, set to the copies
    bc = sha(texts['bytecmp-1480ca2faea0.py'].encode())
    rl = texts['repin_check.py'].split('\n')
    cls = sha(('\n'.join(rl[30:80]) + '\n').encode()); tgt = sha(('\n'.join(rl[208:231]) + '\n').encode())
    d = texts['drvcmp.py']
    old = {k: re.search(r"^%s = '([0-9a-f]{64})'" % k, d, re.M).group(1) for k in ('BC_SHA', 'CLASS_SHA', 'TARGETS_SHA')}
    if (old['CLASS_SHA'], old['TARGETS_SHA']) != (cls, tgt):
        raise SystemExit('kitscrub: repin_check.py lines 31-80 / 209-231 changed (%s %s vs %s %s): refusing'
                         % (cls[:12], tgt[:12], old['CLASS_SHA'][:12], old['TARGETS_SHA'][:12]))
    d = d.replace("BC_SHA = '%s'" % old['BC_SHA'], "BC_SHA = '%s'" % bc)
    texts['drvcmp.py'] = d
    # the docstring words on the pins (drvcmp's before its sha256 is taken for jtcheck's pin)
    for f, was, now in PIN_WORDS:
        if texts[f].count(was) != 1:
            raise SystemExit('kitscrub: %s holds %d copies of the pin text %r, not 1: refusing' % (f, texts[f].count(was), was))
        texts[f] = texts[f].replace(was, now.format(bc=bc[:12]))
    j = texts['jtcheck.py']
    for f in ('strictcmp3.py', 'drvcmp.py'):
        m = re.search(r"\('%s', '([0-9a-f]{64})'\)" % re.escape(f), j)
        j = j.replace(m.group(0), "('%s', '%s')" % (f, sha(texts[f].encode())))
    texts['jtcheck.py'] = j
    for f in FILES:
        b = texts[f].encode()
        left = [m.group() for m in FORBIDDEN.finditer(texts[f])] + [n for _, n in rolenames.left_in(b, roster)] + \
               [t for _, t in rolenames.times_in(b)]
        if left: raise SystemExit('kitscrub: %s still holds %r' % (f, left[:3]))
        ph = [m.group() for m in PLACEHOLDER.finditer(texts[f])]
        if ph: raise SystemExit('kitscrub: %s holds the placeholder %r (a citation CITE does not cover): refusing' % (f, ph[:3]))
        p = os.path.join(od, f)
        open(p, 'wb').write(b); os.chmod(p, os.stat(src[f]).st_mode & 0o777)
        print('%s\t%s -> %s\t%d lines changed' % (f, sha(open(src[f], 'rb').read())[:12], sha(b)[:12],
                                                  sum(1 for a, c in zip(open(src[f]).read().split('\n'),
                                                                        texts[f].split('\n')) if a != c)))

if __name__ == '__main__':
    main()
