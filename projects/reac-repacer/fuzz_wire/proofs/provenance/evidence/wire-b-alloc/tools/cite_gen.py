#!/usr/bin/env python3
"""cite_gen.py -- the CITE table luitrace.py classifies with: the TYPE and NAME of each parameter that a lui-derived
value reaches, and the RETURN TYPE of each function that returns one, read from the PINNED SOURCE. Read-only.

Why the source and not the DWARF: both images are built without DWARF parameters (84 CUs, 5512 DW_TAG_subprogram, 134
DW_TAG_formal_parameter, 12 DW_TAG_member in fuzz_uci.asan-ubsan), so no parameter name or struct field can be cited
from the image. The source is the compiler-rt of `Alpine clang version 20.1.8` (.comment of both images, Linker: LLD
20.1.8), i.e. llvm-project llvmorg-20.1.8, fetched into SRC_DIR with the repository path as the file name (`/` -> `_`).

What is cited, for each (callee, aK) and each function of the given luitrace outputs:
  * the callee's unqualified name is searched as a DECLARATION `Name(` in the source files (a line whose parameter list
    parses, each entry holding a type and a name, or `...`);
  * the parameter COUNT must equal the count the MANGLED name carries (demangled by libstdc++, a member's implicit
    `this` counted as a0), so the register -> parameter map is checked against the image's own symbol;
  * the entry at that register gives `arg<TAB>mangled callee<TAB>aK<TAB>type<TAB>name<TAB>file:line `decl``;
  * the text before the name of the declaration gives `ret<TAB>mangled name<TAB>-<TAB>type<TAB><TAB>file:line`.
A callee that is not found, whose list does not parse, or whose count does not match gives NO row (its rows stay NOT
CERTIFIED). Where several declarations match, the first by file name order is taken and the row says how many matched.
usage: cite_gen.py SRC_DIR LUITRACE_TSV [LUITRACE_TSV ...] > cite.tsv"""
import os, re, sys, importlib.util
HERE = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location('luitrace', os.path.join(HERE, 'luitrace.py'))
lt = importlib.util.module_from_spec(_spec); _spec.loader.exec_module(lt)

KEYWORDS = {'return', 'if', 'while', 'for', 'switch', 'sizeof', 'new', 'delete', 'else', 'do', 'case', 'typedef'}

def params_at(lines, i, col):
    """the text between the '(' at lines[i][col] and its matching ')', over at most 12 lines"""
    depth = 0; out = ''
    for j in range(i, min(len(lines), i + 12)):
        s = lines[j][col:] if j == i else lines[j]
        for ch in s:
            if ch == '(':
                depth += 1
                if depth == 1: continue
            elif ch == ')':
                depth -= 1
                if depth == 0: return out
            if depth >= 1: out += ch
        out += ' '
    return None

TYPE_OK = re.compile(r'^[A-Za-z_][\w:<>,*&\s\[\]]*$')

def entry(decl):
    """(type, name) of one declaration entry, or None when it does not read as `TYPE NAME`"""
    d = re.sub(r'\s*=.*$', '', decl).strip()
    if d in ('void', ''): return None
    if d == '...': return ('...', '...')
    m = re.match(r'^(.*?)([A-Za-z_]\w*)\s*(\[\s*\d*\s*\])?$', d)
    if not m or not m.group(1).strip(): return None
    typ = m.group(1).strip() + (' []' if m.group(3) else '')
    nm = m.group(2)
    if nm in KEYWORDS or re.match(r'^(unsigned|signed|const|struct|class|long|short|int|char|void)$', nm): return None
    core = re.sub(r'\b(const|volatile|struct|class|enum|unsigned|signed|register)\b', ' ', typ)
    if not TYPE_OK.match(typ.strip()) or '->' in typ or '.' in typ or '(' in typ or '"' in typ: return None
    if not core.strip(): return None
    return (typ, nm)

def compatible(dmt, typ):
    """does the source type agree with the type the MANGLED name carries? (a typedef hides a pointer-sized integer, so
    a mangled integer may be a uptr in the source; nothing else may disagree)"""
    d, s = lt.dm_kind(dmt), lt.src_kind(typ)
    return d == s or (d == 'int' and s == 'uptr')

def scope_ok(lines, i, quals):
    """every qualifier the mangled name carries (namespace, then class) must be declared in the file before the hit"""
    for q in quals:
        pat = re.compile(r'\b(class|struct|namespace)\s+%s\b' % re.escape(q))
        if not any(pat.search(l) for l in lines[:i + 1]): return False
    return True

def find_decls(files, nm, want, want_var, dmts=None, quals=()):
    """[(file, line, [(type, name)], return type)] declarations of nm with the wanted parameter count, every parameter
    type agreeing with the mangled name's, declared in the scope the mangled name gives; headers first"""
    hits = []
    for fname, lines in sorted(files.items(), key=lambda kv: (not kv[0].endswith('.h'), kv[0])):
        for i, line in enumerate(lines):
            for m in re.finditer(r'(?<![\w.>])%s\s*\(' % re.escape(nm), line):
                before = line[:m.start()].rstrip()
                if before.endswith(('return', '=', '.', '->', 'if', 'while', '&&', '||', ',', '(')): continue
                if before.endswith('#define') or line.lstrip().startswith(('//', '*', '#')): continue
                pl = params_at(lines, i, m.end() - 1)
                if pl is None: continue
                raw = [x.strip() for x in lt.split_params(pl)]
                if len(raw) == 1 and raw[0] in ('void', ''): raw = []
                es = [entry(x) for x in raw]
                if any(e is None for e in es): continue
                var = any(e[0] == '...' for e in es)
                named = [e for e in es if e[0] != '...']
                if len(named) != want or var != want_var: continue
                if dmts is not None and (len(dmts) != len(named) or
                                         not all(compatible(d, t) for d, (t, _) in zip(dmts, named))): continue
                if not scope_ok(lines, i, quals): continue
                rt = re.sub(r'^(static|inline|virtual|explicit|constexpr|extern "C"|extern|ALWAYS_INLINE|SANITIZER_INTERFACE_ATTRIBUTE|INLINE|NOINLINE|__attribute__\(\(.*?\)\))\s+', '',
                            before.strip()).strip()
                rt = re.sub(r'^.*;\s*', '', rt)
                hits.append((fname, i + 1, named, rt))
    return hits

def path_of(fname):
    for pre, real in (('sanitizer_common_', 'sanitizer_common/'), ('asan_', 'asan/'), ('lsan_', 'lsan/'),
                      ('interception_', 'interception/'), ('ubsan_', 'ubsan/')):
        if fname.startswith(pre): return real + fname[len(pre):]
    return fname

def main():
    src = sys.argv[1]
    files = {f: open(os.path.join(src, f), encoding='utf-8', errors='replace').read().split('\n')
             for f in sorted(os.listdir(src)) if f.endswith(('.h', '.cpp', '.c', '.inc'))}
    need_arg = {}; need_ret = set()
    for p in sys.argv[2:]:
        for l in open(p):
            f = l.rstrip('\n').split('\t')
            if f[0] != 'ROW' or len(f) < 6 or f[5] != 'NOT CERTIFIED': continue
            kind = f[3].split(' ')[1] if ' ' in f[3] else ''
            if kind == 'arg':
                m = re.match(r'(\S+) (?:parameter )?(a\d)\b', f[6])
                if m: need_arg.setdefault(m.group(1), set()).add(m.group(2))
            elif kind == 'ret':
                need_ret.add(f[1])
    print('# kind\tname\tregister\ttype\tname / meaning\tcitation (llvm-project llvmorg-20.1.8, compiler-rt/lib/<path>, '
          'or musl 1.2.5)')
    def lookup(mangled):
        """(file, line, [(type, name)], return type, how many declarations matched, member?) or None"""
        pt = lt.prototype(mangled)
        if not pt or not mangled.startswith('_Z'): return None
        ps, var, ev = pt
        member = ps[:1] == ['this']
        d = lt.demangle(mangled.split('/')[0].split('{')[0])
        if not d: return None
        head = d[:d.rfind('(')] if '(' in d else d
        base = head
        while True:
            nxt = re.sub(r'<[^<>]*>', '', base)
            if nxt == base: break
            base = nxt
        parts = base.split('::')
        nm = parts[-1].strip()
        quals = [q.strip() for q in parts[:-1] if re.match(r'^\w+$', q.strip())]
        if not nm or nm.startswith('~') or not re.match(r'^\w+$', nm): return None
        dmts = ps[1:] if member else ps
        hits = find_decls(files, nm, len(dmts), var, dmts, quals)
        if not hits: return None
        return hits[0][0], hits[0][1], hits[0][2], hits[0][3], len(hits), member
    for callee in sorted(need_arg):
        h = lookup(callee)
        if h is None: continue
        fname, ln, named, rt, nhit, member = h
        many = '' if nhit == 1 else ' (%d declarations match; the first by header, then file name)' % nhit
        for k in sorted(need_arg[callee]):
            idx = int(k[1:]) - (1 if member else 0)
            if idx < 0:
                print('arg\t%s\t%s\tthis *\tthis\t%s:%d (the implicit object parameter)%s' % (callee, k, path_of(fname), ln, many))
                continue
            if idx >= len(named): continue
            typ, pnm = named[idx]
            print('arg\t%s\t%s\t%s\t%s\t%s:%d `%s %s`%s' % (callee, k, typ, pnm, path_of(fname), ln, typ, pnm, many))
    for fn in sorted(need_ret):
        h = lookup(fn)
        if h is None: continue
        fname, ln, named, rt, nhit, member = h
        if not rt: continue
        print('ret\t%s\t-\t%s\t\t%s:%d `%s ...(...)`%s' % (fn, rt, path_of(fname), ln, rt,
                                                           '' if nhit == 1 else ' (%d declarations match)' % nhit))

if __name__ == '__main__':
    main()
