"""twinlist.py -- what the drivers of this directory share: the twin symbol listing, and running a tool unchanged.

The tools are not shipped here: run.sh takes the directory that holds them (TOOLS, in the layout tools.sha256
names) and checks every file's sha256 before it runs anything; it passes the directory in STARTUP_TOOLS. Each tool read
the unstripped twin of the pinned image or names a host path as a constant; the twin is not shipped, and
twin/fuzz_disco.asan.syms carries the symbol facts the tools read (twin_symbols.py: `ADDRESS SIZE TYPE NAME` lines in
.symtab order, `#` header lines; it refuses a twin in which a symbol that is not STT_FUNC gets one of the letters
t/T/w/W, so those letters are exactly the functions). A driver imports the tool as a module from TOOLS, replaces the one
function or constant the run needs (the listing in place of the twin, an input in place of a host path), and then runs
the tool's own `__main__` block.
"""
import ast
import importlib
import os
import re
import sys

TWIN_RE = re.compile(r'^# symbols of the unstripped twin sha256 ([0-9a-f]{64})', re.M)
PIN_RE = re.compile(r'^# the pinned image is sha256 ([0-9a-f]{64})', re.M)


def tools_dir():
    """the directory of the tools (STARTUP_TOOLS, set by run.sh)"""
    d = os.environ.get('STARTUP_TOOLS')
    if not d or not os.path.isdir(d):
        raise SystemExit('twinlist: STARTUP_TOOLS does not name the directory of the tools (run.sh sets it)')
    return os.path.abspath(d)


def is_listing(path):
    """True for a twin symbol listing (text), False for an ELF"""
    with open(path, 'rb') as f:
        return f.read(4) != b'\x7fELF'


def header(path):
    """(twin sha256, pinned image sha256) the listing's header names; ValueError when it names either not"""
    txt = open(path).read()
    t, p = TWIN_RE.search(txt), PIN_RE.search(txt)
    if not t or not p:
        raise ValueError('%s: not a twin symbol listing (no twin / pinned-image sha256 in its header)' % path)
    return t.group(1), p.group(1)


def rows(path):
    """[(value, size, type letter, name)] of the listing, in its (.symtab) order"""
    out = []
    for line in open(path):
        f = line.split()
        if len(f) == 4 and not line.startswith('#'):
            out.append((int(f[0], 16), int(f[1], 16), f[2], f[3]))
    return out


def load(subdir, name):
    """import the tool `name` from TOOLS/subdir (that directory first on sys.path, as when the tool runs as a script)"""
    d = os.path.join(tools_dir(), subdir)
    if d not in sys.path:
        sys.path.insert(0, d)
    mod = importlib.import_module(name)
    if os.path.dirname(os.path.abspath(mod.__file__)) != d:
        raise SystemExit('twinlist: %s was imported from %s, not from %s' % (name, mod.__file__, d))
    return mod


def run_main(mod, argv):
    """run the tool's own `if __name__ == '__main__':` block in its module namespace, with sys.argv[1:] = argv"""
    tree = ast.parse(open(mod.__file__).read(), mod.__file__)
    blocks = [n for n in tree.body if isinstance(n, ast.If) and ast.unparse(n.test) in
              ("__name__ == '__main__'", '__name__ == "__main__"')]
    if len(blocks) != 1:
        raise SystemExit('twinlist: %s has %d __main__ blocks, expected 1' % (mod.__file__, len(blocks)))
    sys.argv = [mod.__file__] + list(argv)
    exec(compile(ast.Module(body=blocks[0].body, type_ignores=[]), mod.__file__, 'exec'), mod.__dict__)
