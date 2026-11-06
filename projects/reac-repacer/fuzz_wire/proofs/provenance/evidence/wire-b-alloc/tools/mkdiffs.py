#!/usr/bin/env python3
"""mkdiffs.py -- the writer of TOOLS_DIR/DIFFS.md. Read-only on its inputs.

For every *.py in TOOLS_DIR it writes the copy's sha256 and its origin:
  - a copy given with --orig NAME ORIG_FILE: the original's sha256, its source (SOURCES below, by the original's
    sha256; an original with no recorded source is refused) and the unified diff original -> copy, with no context
    lines. A removed line is never reworded. A hunk whose only change is the rewrite of `rolenames.py` (session names
    written as roles, times of day dropped: its added lines are the lines of rolenames.rewrite over the whole original,
    as kitscrub.py writes them: a citation may wrap onto a line that the rewrite keeps) is shown as one line, `<copy>:
    ruling citations reworded by role and times of day dropped; old bytes in the tool registry (sha256 <the
    original's, 12 characters>)`, with the source text in place of `the tool registry` for an original that is not in
    the registry; so is each run of such line pairs in a hunk that has other changes too and whose removed lines name
    a session or hold a time of day. In every other removed line a host path, a branch name, a commit that is not
    released (COMMITS), a session name and a time of day are shown as <redacted> (REDACT and COMMITS below,
    rolenames.redact, rolenames.TIME_OF_DAY), and a removed line that
    names a session or holds a time in a hunk whose removed and added lines do not pair is refused. The sha256 of the
    unredacted diff is given too, so
    that a holder of the original can check the diff, and a `code compare` line says whether the syntax tree,
    docstrings left out, is the original's (a comment is in no tree), with the changed lines counted as comment
    (a comment line, or a code line whose code is kept and only its trailing comment changed), docstring or code;
  - a copy that is byte-equal to a recorded original: its source, "unchanged";
  - a script written for these records (OURS): no original.
Any other script is refused (exit 1), and so is a DIFFS.md that would still hold such text (FORBIDDEN below) or a
commit that is not released (COMMITS).
usage: mkdiffs.py TOOLS_DIR [--orig NAME ORIG_FILE]..."""
import argparse, ast, difflib, hashlib, importlib.util, io, os, re, sys, tokenize

_spec = importlib.util.spec_from_file_location('rolenames', os.path.join(os.path.dirname(os.path.abspath(__file__)), 'rolenames.py'))
rolenames = importlib.util.module_from_spec(_spec); _spec.loader.exec_module(rolenames)
SURVEY = 'image-B donor survey scripts (repacer/B-DONORS.md)'
REG = 'the tool registry'
KIT = 'cmpkit 86da41d3ef68 (the tool registry), '
SOURCES = {   # original sha256 -> source (each original is named by its sha256; no registry commit or path is cited)
    '1480ca2faea075e866800faab4e18aea5fb4a96dcea17ef1fe8981f1bdd0f98f':
        KIT + 'bytecmp-1480ca2faea0.py = bytecmp 1480ca2faea0 of ' + REG + ' (its lines 39-151 are insnflow '
        'a36c2b82eb44 of the same registry)',
    '4d70e90bc1fa4d70fe1ea53e0208593ee5e87ff53c3b80c8b767ffdff4eaa3a6':
        KIT + 'drvcmp.py: loader (bytecmp + repin_check Img / sx / targets / w_off), twins; no target pass',
    'e6883477399df80d35e1810dd93f2d5c85aa4d07cb16fbc887ad625851d98a66':
        KIT + 'repin_check.py: the shared class Img (lines 31-80) and sx / targets / w_off (209-231); `funcs` on strictcmp3',
    '65688e94214a74664ffa83a21c283412a64b81f8a7eaa40f970a91f4eb1319b7':
        KIT + 'strictcmp3.py: THE ONE compare (tcmp, tsame, lui_scan / rule 8, the combined verdict)',
    'a98d2b3e88574d09d4aee478ba4fed060a3c1577e2229f47affb116c3ccded4e':
        KIT + 'closure_strict3.py: by-name closure, one compare per X address, every differing target printed',
    '926a9a88afcdc233aa5cd0451a0a8965217e1e08dbc09ffb4e7e8c3bd61017e1':
        KIT + 'paircl.py: target-paired closure against a STRIPPED pin; every pair judged by strictcmp3.tcmp',
    '226254f48c97ba6db570f21d68591e7601d6970cd9f06683dc2ebe2874458dc7':
        "jtcheck 226254f48c97 (the tool registry), the jtcheck of record for table verdicts, which supersedes the "
        "kit's jtcheck 8b0ea3862423 (sha256 8b0ea3862423e3941fd9d70ccc9bcb89cfd89b824fa348140e168880c9745fb7): jump / "
        "string tables and initializers, each table's entry size and count proven on the CFG (Flow.prove) or refused; "
        'strictcmp3.tcmp per function',
    '9ae61e4a0e018677862566a53e3b9a6c0f1a89c9f71a9012bf1893f8ec93edad':
        KIT + 'luiscan.py: the rule-8 (lui) exposure scan per function',
    '9f61b4cee42207e6ae77f33c6ca2d9a9b8f938c38cff50b8c71c057b1e955d8d':
        KIT + 'ambiscan.py: did a by-name compare take the wrong copy of a duplicated name',
}
OURS = {'syms.py': 'symbol lookup',
        'rolenames.py': 'the one place that knows how a ruling is cited in a shipped file: by the role that made it, '
                        'never by a session name and with no time of day (used by kitscrub.py, scrub_out.py, '
                        'earlierscrub.py and this writer); it also reads, at run time, the private list SCRUB_FORBIDDEN (outside the slice) '
                        'that holds the text these writers refuse, redact or rewrite',
        'earlierscrub.py': "the writer of the rewrites of a shipped archive of a prior version (earlier/): the role "
                           "rewrite, the time-of-day rewrite, the forbidden-word loader, the sha256 pin repair and the "
                           "archive DIFFS.md notes of the role and time rewrites",
        'gates.py': 'the gate writer: one verdict file per unit gate (kit, lui, base, plants), each with its evidence '
                    'lines and its `GATE ... VERDICT:` line, and the two negative controls it runs first',
        'scrub_out.py': 'the one writer of the committed slice',
        'mkdiffs.py': 'the writer of this DIFFS.md',
        'kitscrub.py': "the writer of this record's copies of the 9 kit files (jtcheck.py: of jtcheck 226254f48c97) "
                       "(comment and docstring words, unused host-path constants, and the kit's own sha pins with the "
                       "docstring words on them, set to the copies)",
        'settle.py': "per-target settlement: TABLE / REFUSED / INDEXED / CSTR / RELSTR / INITIALIZER / NOT-PCREL (loads "
                     "strictcmp3 through jtcheck 226254f48c97, and uses its table / copy_len, with the table shape its "
                     "Flow.prove gives on both images: luitrace.table_proof2)",
        'handtable.py': "the hand settlement of a table jtcheck 226254f48c97 refuses, under this record's rule: entries, "
                        "dispatch, and the bound by a CFG walk, each on both images (parts (1)-(3) of that rule)",
        'dupcheck.py': 'duplicate-name check for every function compared by name (strictcmp3 cmp and closure_strict3)',
        'escape.py': 'second settlement pass for an escaping empty-string pointer: decoded escape sites, direct readers, the field reads from objscan.py, checked return-path words, and the equal window (support)',
        'objscan.py': 'whole-image scan of every load of an object field that an escaping pointer is stored into, each followed to its readers',
        'otherrows.py': 'the function names the kit reports as other (closure_strict3 + paircl)',
        'mkaccept.py': 'writes ACCEPTANCES.tsv: the kit verdict (unchanged) + settle rows + one LUI row per lui-in-section target + the plants',
        'luitrace.py': 'the hand trace of every lui value of every compared function (shapes a-g), with the settlement classes of the rulings',
        'cite_gen.py': 'reads the CITE table (parameter and return types and names) from the pinned compiler-rt source',
        'plants.py': 'the plants: (a) lui + lui -> add -> a store base and (c) lui -> divuw -> slli -> a store base, both caught as DIFFERS; (b) a lui argument re-pointed to a uptr parameter, refused',
        'luirows.py': "luiscan's exposed functions re-run on strictcmp3.tcmp by address (EXPOSED / RERUN rows)",
        'basescan.py': "shape (h): every load / store / AMO / jalr base of the compared set named as its full address in X and Y (roots in full); an address no symbol covers compared by its bytes or settled by jtcheck 226254f48c97's table rule"}
# the patterns of the text redacted and refused are read from the file SCRUB_FORBIDDEN names (rolenames.private), so
# that this file spells none of them in any form; the session names are rolenames.py's, and a removed line that names
# one shows <redacted> in its place or is not shown (`show`)
REDACT = re.compile(rolenames.private('mkdiffs.PATHS'), re.I)
FORBIDDEN = re.compile(rolenames.private('mkdiffs.FORBIDDEN'), re.I)
COMMITS = re.compile(rolenames.private('mkdiffs.COMMITS'))   # the commits not released that an original cites
LANE = re.compile(r"\blane(?:s|'s)?\b")   # the kit's plain word for a work stream (no session's name)


def sha(b):
    return hashlib.sha256(b).hexdigest()


def docspans(text):
    """the line numbers that a docstring of this Python file covers"""
    out = set()
    for node in ast.walk(ast.parse(text)):
        if isinstance(node, (ast.Module, ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef)) and node.body and \
                isinstance(node.body[0], ast.Expr) and isinstance(getattr(node.body[0], 'value', None), ast.Constant) \
                and isinstance(node.body[0].value.value, str):
            out |= set(range(node.body[0].lineno, node.body[0].end_lineno + 1))
    return out


def code_tree(text):
    """the syntax tree with every docstring left out (a comment is in no tree)"""
    t = ast.parse(text)
    for node in ast.walk(t):
        if isinstance(node, (ast.Module, ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef)) and node.body and \
                isinstance(node.body[0], ast.Expr) and isinstance(getattr(node.body[0], 'value', None), ast.Constant) \
                and isinstance(node.body[0].value.value, str):
            node.body = node.body[1:]
    return ast.dump(t)


def comment_cols(text):
    """{line number: the column where the comment that ends that line starts} of a Python file"""
    return {t.start[0]: t.start[1] for t in tokenize.generate_tokens(io.StringIO(text).readline)
            if t.type == tokenize.COMMENT}


def kinds(otext, ctext):
    """each changed line of the copy, as comment / docstring / code (by the original's own line numbering); a code
    line whose text before its trailing comment is unchanged is a comment change; each code line with what makes it
    code: a path now read from the environment, or a sha256 pin set to this record's copy of the file it pins"""
    ol, cl = otext.split('\n'), ctext.split('\n')
    ds = docspans(otext)
    oc, cc = comment_cols(otext), comment_cols(ctext)
    c = d = 0; code = []
    for i, (a, b) in enumerate(zip(ol, cl), 1):
        if a == b: continue
        if a.lstrip().startswith('#') and b.lstrip().startswith('#'): c += 1
        elif i in oc and i in cc and a[:oc[i]] == b[:cc[i]]: c += 1
        elif i in ds: d += 1
        else:
            code.append((i, 'a path read from the environment' if "os.environ.get('KIT_" in b else
                            'the `os` import that environment read needs' if b.startswith('import ') and
                            b == a + ', os' else
                            "a sha256 pin set to this record's copy of the file it pins" if re.search(r'[0-9a-f]{64}', b)
                            else 'UNEXPLAINED'))
    return c, d, len(code), code


def hunks(full):
    """the hunks of a unified diff with no context lines: (header, old start, new start, removed lines, added lines)"""
    out = []
    for ln in full[2:]:
        if ln.startswith('@@'):
            m = re.match(r'@@ -(\d+)(?:,\d+)? \+(\d+)(?:,\d+)? @@', ln)
            out.append((ln, int(m.group(1)), int(m.group(2)), [], []))
        else:
            out[-1][3 if ln[:1] == '-' else 4].append(ln)
    return out


def span(a, k):
    return '%d' % a if k == 1 else '%d,%d' % (a, k)


def show(n, full, named, roster, note, bad):
    """the diff as DIFFS.md shows it. A hunk whose added lines are the same lines of `named` (the original with only
    the role rewrite, as kitscrub.py writes it) is the one line `note`; in a hunk with any other change whose removed
    lines name a session, so is each run of line pairs whose added line is that line of `named`. Every other removed
    line is shown with a host path, a branch name, a commit that is not released (COMMITS) and a session name as
    <redacted>; it is never reworded."""
    def old(ln): return re.sub(rolenames.TIME_OF_DAY, '<redacted>',
                               rolenames.redact(COMMITS.sub('<redacted>', REDACT.sub('<redacted>', ln)), roster))
    def private_in(x): return rolenames.left_in(x.encode(), roster) or rolenames.times_in(x.encode())
    out = full[:2]
    for hd, a, c, rm, ad in hunks(full):
        k = len(rm)
        pairs = k == len(ad) and a == c
        cit = [pairs and ad[i][1:] == named[a - 1 + i] for i in range(k)]
        if pairs and all(cit):
            out.append(note)
            continue
        if not any(private_in(x) for x in rm):
            out += [hd] + [old(x) for x in rm] + ad
            continue
        if not pairs:
            bad.append('%s:%d: a hunk whose removed lines name a session or hold a time of day, and whose removed and '
                       'added lines do not pair' % (n, a))
            continue
        i = 0
        while i < k:
            j = i
            while j < k and cit[j] == cit[i]: j += 1
            if cit[i]:
                out.append(note)
            else:
                out += ['@@ -%s +%s @@\n' % (span(a + i, j - i), span(a + i, j - i))] + [old(x) for x in rm[i:j]] \
                    + ad[i:j]
            i = j
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('tools')
    ap.add_argument('--orig', nargs=2, action='append', default=[], metavar=('NAME', 'ORIG_FILE'))
    a = ap.parse_args()
    roster = rolenames.names(os.environ['ROSTER_TSV']) if os.environ.get('ROSTER_TSV') else ()
    orig = dict(a.orig)
    names = sorted(n for n in os.listdir(a.tools) if n.endswith('.py'))
    bad = [n for n in orig if n not in names]
    table, sections = [], []
    laneword, dropped = [], []   # the kit's plain word `lane` reworded; a README label dropped (line of the original)
    for n in names:
        cb = open(os.path.join(a.tools, n), 'rb').read(); cs = sha(cb)
        if n in orig:
            ob = open(orig[n], 'rb').read(); os_ = sha(ob)
            if os_ not in SOURCES:
                bad.append('%s: the original has no recorded source' % n); continue
            ol, cl = ob.decode().splitlines(True), cb.decode().splitlines(True)
            full = list(difflib.unified_diff(ol, cl, 'a/' + n, 'b/' + n, n=0))
            for hd, a0, c0, rm, ad in hunks(full):
                for i, x in enumerate(rm):
                    if LANE.search(x) and not (REDACT.search(x) or rolenames.left_in(x.encode(), roster)
                                               or rolenames.times_in(x.encode())):
                        laneword.append('%s:%d' % (n, a0 + i))
                    if len(ad) == len(rm) and re.search(r'\(README A\d+\)', x) and 'README' not in ad[i]:
                        dropped.append('%s:%d' % (n, a0 + i))
            named = rolenames.rewrite(ob.decode(), roster).splitlines(True)
            if len(named) != len(ol):
                bad.append('%s: the role rewrite of the original changed its line count' % n); continue
            src = SOURCES[os_]
            shown = show(n, full, named, roster, '%s: ruling citations reworded by role and times of day dropped; old '
                         'bytes in %s (sha256 %s)\n'
                         % (n, REG if REG in src else src, os_[:12]), bad)
            nrm = sum(1 for ln in full if ln[:1] == '-' and ln[:3] != '---')
            nad = sum(1 for ln in full if ln[:1] == '+' and ln[:3] != '+++')
            nc, nd, nk, kl = kinds(ob.decode(), cb.decode())
            same = code_tree(ob.decode()) == code_tree(cb.decode())
            if len(ol) != len(cl):
                bad.append('%s: the copy has %d lines, the original %d: every line must keep its place'
                           % (n, len(cl), len(ol)))
            for i, why in kl:
                if why == 'UNEXPLAINED':
                    bad.append('%s:%d: a changed code line that is neither a path read from the environment nor a '
                               'sha256 pin' % (n, i))
            code = ('the syntax tree with docstrings left out is EQUAL (a comment is in no tree): every changed line '
                    'is a comment or a docstring' if same and not nk else
                    'every changed code line is ' + '; '.join('line %d %s' % x for x in kl)
                    + ('; the tree is otherwise the original\'s' if not same else ''))
            table.append((n, cs, os_, SOURCES[os_], '%d removed, %d added (%d comment, %d docstring, %d code)' % (
                nrm, nad, nc, nd, nk)))
            sections.append('## %s\n\n- copy sha256 `%s`\n- original sha256 `%s`: %s\n- changed lines: %d comment, '
                            '%d docstring, %d code\n- code compare: %s\n- sha256 of the unredacted diff: '
                            '`%s`\n\n```diff\n%s```\n' % (n, cs, os_, SOURCES[os_], nc, nd, nk, code,
                                                          sha(''.join(full).encode()),
                                                          ''.join(x if x.endswith('\n') else x + '\n' for x in shown)))
        elif cs in SOURCES:
            table.append((n, cs, cs, SOURCES[cs], 'unchanged'))
        elif n in OURS:
            table.append((n, cs, '-', 'written for these records: ' + OURS[n], '-'))
        else:
            bad.append('%s: not a recorded original, not given with --orig, not written for these records' % n)
    text = ('# Tool copies: sources and changes\n\nWritten by mkdiffs.py. Each copy below is the script these records '
            'ran. A changed copy\'s diff against its original has no context lines and covers the whole change; a host '
            'path that a copy now reads from the environment defaults to empty. Every changed comment word is a host '
            'path, a branch name, a session\'s citation dropped with its claim kept (kitscrub.py CITE), the kit\'s plain '
            'word `lane` (its word for a work stream, no session\'s name) reworded or dropped (kitscrub.py CITE; at %s), '
            'a session name written as its role (`rolenames.py`), a time of day dropped, a README item label or count '
            'that jtcheck.py cites, set to its own package\'s README and controls, or dropped where no README item '
            'covers the sentence (kitscrub.py JT_WORDS; dropped at %s), or a docstring word on what a '
            'kit sha256 pin names (jtcheck.py, drvcmp.py: kitscrub.py PIN_WORDS), which the '
            % (', '.join(laneword) or 'no line', ', '.join(dropped) or 'no line') +
            '`code compare` line measures: the syntax tree, docstrings left out, is the original\'s. A removed line is '
            'never reworded: a hunk, or a run of lines of a hunk, whose only change is that rewrite is shown as one '
            'line, `<copy>: ruling citations reworded by role and times of day dropped; old bytes in ...`, which names '
            'the original by its sha256, and in every removed line shown a host path, a branch name, a commit that is not '
            'released, a session name and a time of day are `<redacted>`. '
            'The sha256 of the unredacted diff lets a holder of the original check each diff.\n\n'
            '| tool | copy sha256 | original sha256 | source | changed lines |\n|---|---|---|---|---|\n'
            + ''.join('| `%s` | `%s` | %s | %s | %s |\n' % (n, cs, ('`%s`' % os_) if os_ != '-' else '-', src, ch)
                      for n, cs, os_, src, ch in table)
            + '\n' + '\n'.join(sections))
    for m in FORBIDDEN.finditer(text):
        bad.append('DIFFS.md: forbidden text left at offset %d' % m.start())
    for off, name in rolenames.left_in(text.encode(), roster):
        bad.append('DIFFS.md: session name %r left at offset %d' % (name, off))
    for off, t in rolenames.times_in(text.encode()):
        bad.append('DIFFS.md: a time of day %r left at offset %d' % (t, off))
    for m in COMMITS.finditer(text):
        bad.append('DIFFS.md: a commit that is not released left at offset %d' % m.start())
    for m in re.finditer(r'registry commit [0-9a-f]{6,40}', text):
        bad.append('DIFFS.md: a registry commit cited at offset %d' % m.start())
    if bad:
        for b in bad:
            print('mkdiffs: REFUSED: ' + b, file=sys.stderr)
        sys.exit(1)
    open(os.path.join(a.tools, 'DIFFS.md'), 'w').write(text)
    print('mkdiffs: %d tools, %d changed copies' % (len(table), len(sections)))


if __name__ == '__main__':
    main()
