#!/usr/bin/env python3
"""inst_sites.py [--image A|B] LIB MEMBER... -- every instantiation site of the Section variables / binders that the
grown-layout class's DPT and BND members add (the class ruling's condition (1)).

LIB: the unit's lib directory (LIB/<side>/<F>). MEMBER: FILE:LINE:NAME:KIND, where KIND is
  section-var  NAME is a Section `Variable` (DPOST, or c0's ly' / md'): the script finds the Section that declares it,
               every lemma / definition of that Section whose text names NAME (they take NAME as an argument after
               `End`), and every use of those names in other files, with the argument the use passes in NAME's
               place when the use names its own variable (pass-through: the caller's Section variable of the same
               name) or the whole application otherwise;
  binder       NAME is a lemma / record binder (`(ly' : alayout)` ..): every use of the declaration at LINE in the
               same or another file (the binder is instantiated at each use; nothing is assumed).
At the end it lists, for section-var DPOST, every place where a DPOST-typed argument is BOUND to a term
(`set (DPOST := fun ..)`, `Let DPOST.. := fun ..`, a passed `(fun ly' W' md' z m => ..)`): the tops of the chain.
Prints one row per site: KIND MEMBER  FILE:LINE  TEXT.
"""
import os, re, sys

DECL = re.compile(r"^\s*(?:Local\s+|Global\s+)?(Lemma|Theorem|Corollary|Fact|Definition|Fixpoint|Record|Let|Abbreviation|"
                  r"Notation|Section|End|Variable|Variables|Hypothesis|Hypotheses|Context)\b\s*([^\s:(]*)")
BIND = re.compile(r"set \(DPOST\w* := fun|Let DPOST\w*\b[^:]*:[^=]*:= *fun|\(fun (?:ly'|ly2|l) (?:W'|W2) (?:md'|md2|md'') z m =>")


def main():
    args = sys.argv[1:]
    side = 'A'
    if args[:1] == ['--image']:
        side, args = args[1], args[2:]
    if len(args) < 2:
        sys.exit(__doc__)
    lib, members = args[0], args[1:]
    d = os.path.join(lib, side)
    files = sorted(f for f in os.listdir(d) if f.endswith('.v'))
    text = {f: open(os.path.join(d, f), encoding='utf-8').read().split('\n') for f in files}
    for m in members:
        f, ln, name, kind = m.split(':')
        ln = int(ln)
        mod = f[:-2]
        t = text[f]
        if kind == 'section-var':
            # the enclosing Section: last `Section` before ln whose `End` is after ln
            stack = []
            sec = None
            for i, l in enumerate(t):
                mm = DECL.match(l)
                if not mm:
                    continue
                if mm.group(1) == 'Section':
                    stack.append((mm.group(2).rstrip('.'), i + 1))
                elif mm.group(1) == 'End' and stack:
                    s = stack.pop()
                    if s[1] <= ln <= i + 1:
                        sec = (s[0], s[1], i + 1)
                        break
            if not sec:
                print('section-var\t%s\t%s:%d\tNO SECTION FOUND' % (m, f, ln))
                continue
            names = []
            cur = None
            for i in range(sec[1], sec[2]):
                mm = DECL.match(t[i])
                if mm and mm.group(1) in ('Lemma', 'Theorem', 'Corollary', 'Fact', 'Definition', 'Fixpoint', 'Record', 'Let'):
                    cur = (mm.group(2), mm.group(1))
                if cur and cur[1] != 'Let' and re.search(r"(?<![\w'])%s(?![\w'])" % re.escape(name), t[i]) and (not names or names[-1] != cur[0]):
                    names.append(cur[0])
            print('section-var\t%s\t%s:%d-%d\tSection %s: %d declarations take %s after End: %s'
                  % (m, f, sec[1], sec[2], sec[0], len(names), name, ' '.join(names)))
            if not names:
                continue
            use = re.compile(r"@?\b%s\.(?:%s)(?![\w'])" % (re.escape(mod), '|'.join(re.escape(n) for n in names)))
            own_re = re.compile(r"(?<![\w'])%s(?![\w'])" % re.escape(name))
            for g in files:
                if g == f or (mod + '.') not in '\n'.join(text[g]):
                    continue
                for i, l in enumerate(text[g]):
                    if mod + '.' not in l:
                        continue
                    for u in use.finditer(l):
                        seg = l[u.start():u.start() + 400]
                        print('section-var\t%s\t%s:%d\t%s\t%s' % (m, g, i + 1, 'passes its own %s' % name if own_re.search(seg)
                                                                 else 'application', seg[:300]))
        elif kind == 'binder':
            mm = None
            for i in range(ln - 1, -1, -1):
                mm = DECL.match(t[i])
                if mm and mm.group(1) not in ('Variable', 'Variables', 'Hypothesis', 'Hypotheses'):
                    break
            dn = mm.group(2) if mm else '?'
            print('binder\t%s\t%s:%d\tdeclaration %s %s' % (m, f, ln, mm.group(1) if mm else '?', dn))
            for g in files:
                for i, l in enumerate(text[g]):
                    if g == f and i + 1 == ln:
                        continue
                    for u in re.finditer(r"(?:@?\b%s\.)?(?<![\w'.])%s(?![\w'])" % (re.escape(mod), re.escape(dn)), l):
                        if g != f and not l[u.start():].startswith((mod + '.', '@' + mod + '.')):
                            continue
                        print('binder\t%s\t%s:%d\tuse\t%s' % (m, g, i + 1, l[max(0, u.start() - 40):u.start() + 220]))
                        break
    for g in files:
        for i, l in enumerate(text[g]):
            for u in BIND.finditer(l):
                print('bound\tDPOST\t%s:%d\t%s' % (g, i + 1, l[u.start():u.start() + 220]))


if __name__ == '__main__':
    main()
