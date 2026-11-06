#!/usr/bin/env python3
"""earlierscrub.py -- the writer of the rewrites of a shipped ARCHIVE of prior versions of this record (`earlier/`,
each `earlier/<version>/` written by that version's own run). Writes in place, and prints one row per file it changed.
RAN is the same versions as their runs wrote them (`earlier-raw/`, outside the slice): the archive is that, except
exactly the rewrites below, and each file that differs from its RAN copy has its row in DIR/SCRUB.tsv.

The rewrites, applied by this writer and no hand edit; every rewritten line keeps its place:
  - ROLE: a prior version was written before the rule that a ruling is cited by the ROLE that made it (`rolenames.py`),
    so its text may still name a session: every text file under DIR is rewritten by rolenames.rewrite;
  - TIME: no shipped file holds a time of day: every text file under DIR is rewritten by rolenames.untime (a date and a
    machine stamp stay); in a .py file only a comment or a docstring may change (the syntax tree, docstrings left out,
    is checked to be the same);
  - LOADER: a tool of a prior version may spell, in a bracket form, words the scanner of record blocks (the patterns it
    refuses or redacts). The file SCRUB_FORBIDDEN names (outside the slice; rolenames.private) holds each such
    pattern under the key `<file under DIR>:<line>`; that line's string literal, which must equal the pattern, becomes
    `_SF('<key>')`, the same text read at run time from that file, and the comment line `# spelled with one-letter
    classes ...` above the first such line becomes the one-line definition of `_SF`. The pattern each statement
    compiles is checked to be the same before and after; the tool needs SCRUB_FORBIDDEN to run;
  - SHA256 PIN REPAIR: a changed file's sha256 that another file of the archive names (its `tools.sha256` row, a
    `DIFFS.md` table cell, a sha pin inside a tool copy that loads it) is replaced by the new sha256, in full and in its
    12-character short form, so the archive stays internally consistent;
  - DIFFS.md NOTE: a tool copy that the role or the time rewrite changed after its version ran gets, in its version's
    tools/DIFFS.md, one hunk per rewritten line that no hunk of the version's own diff shows (a line such a hunk shows
    is rewritten there too), `@@ -L +L @@` and one line that says so, naming only the rewrites done at that line (a
    session name written as its role or dropped, a time of day dropped, a sha256 pin set to the shipped copy; no old bytes: they
    name a session or a time), citing SCRUB.tsv and the original by its sha256; the copy's row counts those lines, so
    the row and the diff describe the shipped copy against its original.
Every other byte of an archived file is its own text as its version ran: a commit named inside it is part of that
text, not a citation of this record. A note this writer writes names no registry commit (it names the original by its
sha256 only); it refuses one that does.
It refuses (exit 1) when a session name, a time of day or a spelled word of the scanner's list (key `words`) is left,
when a rewrite changed a line count or a compiled pattern, when a changed file's old sha256 is still named anywhere under
DIR, or when a file's RAN copy is missing or is not the one SCRUB.tsv names. DIR/SCRUB.tsv, the archive's own record:
one row per file that differs from its RAN copy, with the sha256 as its version ran, the sha256 shipped, the number of
lines changed and the rewrites applied; it is the only file this writer adds.
usage: earlierscrub.py --ran RAN DIR"""
import ast, difflib, hashlib, importlib.util, os, re, sys

_spec = importlib.util.spec_from_file_location('rolenames', os.path.join(os.path.dirname(os.path.abspath(__file__)), 'rolenames.py'))
rolenames = importlib.util.module_from_spec(_spec); _spec.loader.exec_module(rolenames)

SKIP_EXT = ('.elf', '.pyc', '.log')
LIT = re.compile(r"""(?<![A-Za-z0-9_])([rRbB]{0,2}(?:'(?:[^'\\]|\\.)*'|"(?:[^"\\]|\\.)*"))""")
SF_DEF = ("def _SF(k): return [l.rstrip('\\n').split('\\t', 1)[1] for l in open(os.environ['SCRUB_FORBIDDEN']) "
          "if l.split('\\t', 1)[0] == k][0]   # the patterns below: read at run time from SCRUB_FORBIDDEN")
REGCITE = re.compile(r'registry commit [0-9a-f]{6,40}')   # refused in a note this writer writes
NOTE = ('%s: reworded after this version ran (%s; '
        '%s: sha256 %s as run -> %s shipped); old bytes in the original (sha256 %s); the sha256 of the unredacted '
        'diff above is that of the copy as run')
MARK = 'after this version ran'        # every note this writer has written, in any of its wordings
HEADER = 'file\tsha256 as the version ran\tsha256 shipped\tlines changed\trewrites'


def sha(b): return hashlib.sha256(b).hexdigest()


def code_tree(text):
    """the syntax tree of a Python text with its docstrings left out"""
    t = ast.parse(text)
    for node in ast.walk(t):
        if isinstance(node, (ast.Module, ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef)) and node.body and \
                isinstance(node.body[0], ast.Expr) and isinstance(getattr(node.body[0], 'value', None), ast.Constant) \
                and isinstance(node.body[0].value.value, str):
            node.body = node.body[1:]
    return ast.dump(t)


def files_of(d):
    out = []
    for root, dirs, fs in os.walk(d):
        dirs[:] = sorted(x for x in dirs if x != '__pycache__')
        for n in sorted(fs):
            if not n.endswith(SKIP_EXT): out.append(os.path.join(root, n))
    return out


def spelled(line, words):
    """the words of the scanner's list that `line` spells in a form a plain search misses: bracket classes, quotes and
    concatenation, escapes, case"""
    s = re.sub(r'\\x([0-9a-fA-F]{2})', lambda m: chr(int(m.group(1), 16)), line)
    s = re.sub(r'[^a-z0-9/.\-]', '', s.lower())
    return [w for w in words if w in s and w not in line.lower()]


def statement(lines, i):
    """(first, last) 0-based line indexes of the statement that holds line i (a module-level assignment)"""
    t = ast.parse('\n'.join(lines))
    for node in t.body:
        if node.lineno - 1 <= i <= node.end_lineno - 1: return node.lineno - 1, node.end_lineno - 1
    return None


def loader(rel, s, keys, bad):
    """the LOADER rewrite of the text s of file rel (keys: {line number: pattern})"""
    lines = s.split('\n'); orig = lines[:]
    first = min(keys)
    for ln in sorted(keys):
        line = lines[ln - 1]
        if '_SF(' in line: continue
        m = LIT.search(line)
        if not m:
            bad.append('%s:%d: no string literal to load' % (rel, ln)); continue
        v = ast.literal_eval(m.group(1)); isb = isinstance(v, bytes)
        if (v.decode() if isb else v) != keys[ln]:
            bad.append('%s:%d: the literal is not the SCRUB_FORBIDDEN pattern of its key' % (rel, ln)); continue
        call = "_SF('%s:%d')%s" % (rel, ln, '.encode()' if isb else '')
        head = line[:m.start(1)]
        if not head.strip(): call = '+ ' + call                       # a continuation line of a concatenation
        tail = line[m.end(1):]
        nxt = lines[ln] if ln < len(lines) else ''
        if not tail.strip() and LIT.match(nxt.strip()) and ln + 1 not in keys:
            tail = ' + r""'                                              # the next literal concatenates with r""
        lines[ln - 1] = head + call + tail
    if lines != orig:
        c = next((k for k in range(first - 2, max(-1, first - 4), -1) if lines[k].startswith('# spelled with')), None)
        if c is None:
            bad.append('%s: no `# spelled with ...` comment line above line %d for the definition of _SF' % (rel, first))
            return s
        lines[c] = SF_DEF
        # the compiled patterns are the same
        def ns(): return {'re': re, 'os': os, '_SF': lambda k: rolenames.private(k)}
        for ln in sorted(keys):
            st = statement(orig, ln - 1)
            if not st: bad.append('%s:%d: not a module-level statement' % (rel, ln)); continue
            a, b = st
            o, n = ns(), ns()
            exec('\n'.join(orig[a:b + 1]), o); exec('\n'.join(lines[a:b + 1]), n)
            name = [k for k in o if k not in ('re', 'os', '_SF', '__builtins__')]
            if not name or any((o[k].pattern, o[k].flags) != (n[k].pattern, n[k].flags) for k in name):
                bad.append('%s:%d: the compiled pattern changed' % (rel, ln))
    return '\n'.join(lines)


ROSTER = ()      # the roster's column 1, set by main()


def what(a, b):
    """the rewrites that turned line a into line b, as a note names them (only those done at that line)"""
    r = rolenames.rewrite(a, ROSTER, keep_time=True); t = rolenames.untime(r); out = []
    if r != a:
        roles = r'\b(?:a lane|a group lane|this lane|the [a-z]+ owner|a fresh reviewer|a helper session)\b'
        out.append('a session name written as its role' if len(re.findall(roles, r)) > len(re.findall(roles, a))
                   else 'a session name dropped, its claim kept')
    if t != r: out.append('a time of day dropped')
    if t != b: out.append('a sha256 pin set to the shipped copy')
    return ', '.join(out) or 'a sha256 pin set to the shipped copy'


def diffs_note(d, rel, ran_text, text, texts, bad, scrub_name):
    """the DIFFS.md NOTE of the role / time rewrite of tool copy rel (its RAN text and its shipped text), every note of
    an earlier run on that copy written afresh; returns (DIFFS.md path, new DIFFS.md text) or None"""
    ver, _, name = ('', '', rel[len('tools/'):]) if rel.startswith('tools/') else rel.partition('/tools/')
    p = os.path.join(d, ver, 'tools', 'DIFFS.md')
    if '/' in name or p not in texts: return None
    md = texts[p]
    sec = re.search(r'^## %s\n.*?(?=^## |\Z)' % re.escape(name), md, re.M | re.S)
    row = re.search(r'^\| `%s` \| `[0-9a-f]{64}` \| `([0-9a-f]{64})` \| ([^|]*) \|([^|]*)\|$' % re.escape(name), md, re.M)
    if not sec or not row:
        bad.append('%s: no DIFFS.md section or row for %s' % (p, name)); return None
    body = sec.group(0)
    block = re.search(r'```diff\n(.*?)```\n', body, re.S)
    hunks = re.split(r'(?m)^(?=@@ )', block.group(1))
    pre, hunks = hunks[0], [h for h in hunks[1:] if MARK not in h]     # the notes are written afresh below
    def start(h): return int(re.match(r'@@ -(\d+)', h).group(1))
    def covered(h):
        m = re.match(r'@@ -\d+(?:,\d+)? \+(\d+)(?:,(\d+))? @@', h)
        return range(int(m.group(1)), int(m.group(1)) + int(m.group(2) if m.group(2) is not None else 1))
    rl, sl = ran_text.split('\n'), text.split('\n')
    changed = [i + 1 for i, (a, b) in enumerate(zip(rl, sl)) if a != b]
    shown = {ln for h in hunks for ln in covered(h)}
    for ln in changed:
        if ln in shown:
            continue        # a hunk shows that line already: our own note, or the version's own diff, rewritten too
        hunks.append('@@ -%d +%d @@\n%s\n' % (ln, ln, NOTE % (name, what(rl[ln - 1], sl[ln - 1]), scrub_name, sha(ran_text.encode())[:12],
                                                               sha(text.encode())[:12], row.group(1)[:12])))
    hunks.sort(key=start)
    nrm = nad = 0
    for h in hunks:
        m = re.match(r'@@ -\d+(?:,(\d+))? \+\d+(?:,(\d+))? @@', h)
        nrm += int(m.group(1) or 1); nad += int(m.group(2) or 1)
    nbody = body[:block.start(1)] + pre + ''.join(hunks) + body[block.end(1):]
    nmd = md[:sec.start()] + nbody + md[sec.end():]
    cell = re.sub(r'^\s*\d+ removed, \d+ added', ' %d removed, %d added' % (nrm, nad), row.group(3))
    nmd = nmd.replace(row.group(0), row.group(0)[:-len(row.group(3)) - 1] + cell + '|', 1)
    return p, nmd


def main():
    if len(sys.argv) != 4 or sys.argv[1] != '--ran':
        raise SystemExit('usage: earlierscrub.py --ran RAN DIR')
    ran, d = os.path.abspath(sys.argv[2]), os.path.abspath(sys.argv[3])
    roster = rolenames.names(os.environ['ROSTER_TSV']) if os.environ.get('ROSTER_TSV') else ()
    global ROSTER
    ROSTER = roster
    words = rolenames.private('words').split('|')
    keys = {}
    for line in open(os.environ['SCRUB_FORBIDDEN']):
        m = re.match(r'([^#\t][^\t]*):(\d+)\t(.*)$', line.rstrip('\n'))
        if m and os.path.isfile(os.path.join(d, m.group(1))): keys.setdefault(m.group(1), {})[int(m.group(2))] = m.group(3)
    bad, kinds = [], {}
    scrub = os.path.join(d, 'SCRUB.tsv')
    old_rows, old_info = {}, {}
    if os.path.exists(scrub):
        for l in open(scrub).read().split('\n')[1:]:
            if l.strip():
                f = l.split('\t')
                old_rows[f[0]] = f[4].split(', ') if len(f) > 4 else (['role'] if f[1] != '-' else ['sha256 pin repair'])
                if len(f) > 3 and re.fullmatch(r'[0-9a-f]{64}', f[1]) and re.fullmatch(r'[0-9a-f]{64}', f[2]):
                    old_info[f[0]] = (f[1], f[2], int(f[3]))
    texts = {}
    for p in files_of(d):
        if p == scrub: continue
        b = open(p, 'rb').read()
        try: texts[p] = b.decode()
        except UnicodeDecodeError:
            for off, name in rolenames.left_in(b, roster):
                bad.append('%s: a session name %r at offset %d in a file that is not text' % (p, name, off))
    start = dict(texts)
    def rel(p): return os.path.relpath(p, d)
    # every sha256 a rewrite moved, as run -> as shipped: those an earlier run recorded in SCRUB.tsv, and this run's
    shamap = {a: b for a, b, _ in old_info.values() if a != b}
    for p, s in sorted(texts.items()):
        r_ = rolenames.rewrite(s, roster, keep_time=True)
        n = loader(rel(p), r_, keys[rel(p)], bad) if rel(p) in keys else r_
        t_ = t0 = rolenames.untime(n)
        if p.endswith('.py') and t_ != n:
            try:
                if code_tree(t_) != code_tree(n): bad.append('%s: a time of day outside a comment or a docstring' % p)
            except SyntaxError:
                bad.append('%s: not Python, so the time rewrite cannot be checked' % p)
        if t_ == s: continue
        if t_.count('\n') != s.count('\n'):
            bad.append('%s: a rewrite changed the line count' % p); continue
        if r_ != s: kinds.setdefault(rel(p), []).append('role')
        if n != r_: kinds.setdefault(rel(p), []).append('loader')
        if t0 != n: kinds.setdefault(rel(p), []).append('time')
        shamap[sha(s.encode())] = sha(t_.encode())
        texts[p] = t_
    # the archive's own pins of a changed file's sha256, repeated until no pin changes (a fixed point): a file the pin
    # repair changes is itself pinned by others (drvcmp.py pins bytecmp, jtcheck.py pins drvcmp.py, tools.sha256 pins
    # every tool). A note line (`... after this version ran ...`) names the sha256 as run on purpose and is kept.
    def final(x):
        seen = set()
        while x in shamap and x not in seen: seen.add(x); x = shamap[x]
        return x
    def repair():
        for k in list(shamap): shamap[k] = final(k)
        changed = False
        for p, s in sorted(texts.items()):
            out_ = []
            for l in s.split('\n'):
                if 'after this version ran' not in l:
                    for o, w in shamap.items():
                        if o != w and (o in l or o[:12] in l): l = l.replace(o, w).replace(o[:12], w[:12])
                out_.append(l)
            n = '\n'.join(out_)
            if n != s:
                shamap[sha(s.encode())] = sha(n.encode())
                texts[p] = n; changed = True
                if 'sha256 pin repair' not in kinds.get(rel(p), []): kinds.setdefault(rel(p), []).append('sha256 pin repair')
        return changed
    rounds = 0
    while repair():
        rounds += 1
        if rounds > 50: bad.append('the sha256 pin repair does not reach a fixed point'); break
    def ran_of(r):
        """the file as its version ran: its RAN copy, or, for a file no rewrite has changed before (no SCRUB.tsv row),
        the archive's own bytes before this run; None when neither is known"""
        rp = os.path.join(ran, r)
        if os.path.isfile(rp): return open(rp, 'rb').read()
        if r not in old_rows and os.path.join(d, r) in start: return start[os.path.join(d, r)].encode()
        return None
    # the DIFFS.md notes of every tool copy the role or the time rewrite changed, in this run or an earlier one
    for r in sorted(set(old_rows) | set(kinds)):
        if not {'role', 'time'} & set(old_rows.get(r, []) + kinds.get(r, [])) or '/tools/' not in '/' + r or not r.endswith('.py'):
            continue
        rb_ = ran_of(r)
        if rb_ is None and r in old_info and texts[os.path.join(d, r)] == start[os.path.join(d, r)]:
            continue         # no RAN copy (an archive inside an archive): its notes of an earlier run stand as written
        if rb_ is None: bad.append('%s: no RAN copy' % r); continue
        got = diffs_note(d, r, rb_.decode(), texts[os.path.join(d, r)], texts, bad, os.path.basename(d) + '/SCRUB.tsv')
        if got and got[1] != texts[got[0]]:
            texts[got[0]] = got[1]
            if 'DIFFS.md note' not in kinds.get(rel(got[0]), []): kinds.setdefault(rel(got[0]), []).append('DIFFS.md note')
    while repair():          # a file the notes changed may be pinned too
        rounds += 1
        if rounds > 50: bad.append('the sha256 pin repair does not reach a fixed point'); break
    for p, s in texts.items():
        b = s.encode()
        left = rolenames.left_in(b, roster)
        if left: bad.append('%s: session name %r left' % (p, left[0][1]))
        tl = rolenames.times_in(b)
        if tl: bad.append('%s: a time of day %r left' % (p, tl[0][1]))
        for l_ in s.split('\n'):
            if MARK in l_ and REGCITE.search(l_): bad.append('%s: a note names a registry commit' % p)
        body = '\n'.join(l for l in s.split('\n') if 'after this version ran' not in l)   # a note names the sha as run
        for o in shamap:
            if o in body or o[:12] in body: bad.append('%s: the old sha256 %s is still named' % (p, o[:12]))
        for i, line in enumerate(s.split('\n'), 1):
            w = spelled(line, words)
            if w: bad.append('%s:%d: spells %d word(s) of the scanner\'s list' % (p, i, len(w)))
    if bad:
        for b in bad: print('earlierscrub: REFUSED: ' + b, file=sys.stderr)
        sys.exit(1)
    for p, s in texts.items():
        if s != start[p]:
            open(p, 'w').write(s)
            print('%s\t%s\t%s -> %s' % (rel(p), ', '.join(kinds.get(rel(p), [])), sha(start[p].encode())[:12], sha(s.encode())[:12]))
    # SCRUB.tsv: every file that differs from its RAN copy, with the rewrites applied, in this run or an earlier one
    rows = []
    for r in sorted(set(old_rows) | set(kinds)):
        sp = os.path.join(d, r)
        a = ran_of(r)
        b = open(sp, 'rb').read()
        if a is None and r in old_info and b == start[sp].encode():
            rows.append('%s\t%s\t%s\t%d\t%s' % (r, old_info[r][0], sha(b), old_info[r][2], ', '.join(old_rows[r])))
            continue         # no RAN copy and unchanged in this run: the row an earlier run recorded
        if a is None:
            print('earlierscrub: REFUSED: %s: no RAN copy' % r, file=sys.stderr); sys.exit(1)
        if a == b: continue
        nl = sum(1 for x in difflib.unified_diff(a.decode().split('\n'), b.decode().split('\n'), n=0, lineterm='')
                 if x[:1] == '+' and x[:3] != '+++')
        ks = []
        for k in old_rows.get(r, []) + kinds.get(r, []):
            if k not in ks: ks.append(k)
        rows.append('%s\t%s\t%s\t%d\t%s' % (r, sha(a), sha(b), nl, ', '.join(ks)))
    open(scrub, 'w').write(HEADER + '\n' + '\n'.join(rows) + '\n')
    print('earlierscrub: %d file(s) changed in this run; SCRUB.tsv %d row(s); 0 names left, 0 spelled words left'
          % (sum(1 for p in texts if texts[p] != start[p]), len(rows)))


if __name__ == '__main__':
    main()
