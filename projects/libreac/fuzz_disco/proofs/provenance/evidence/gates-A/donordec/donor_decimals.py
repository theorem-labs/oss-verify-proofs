#!/usr/bin/env python3
"""donor_decimals.py -- find DECIMAL integer literals in a ported proof tree that are a DONOR (cgif) address but not the
same object's address in the TARGET image.

A literal v (decimal, 65536 <= v < 0x600000, outside comments, not part of an identifier, not after 0x) is a HIT when
cgif's image has a symbol N covering v at offset o (v = N + o) and the target image does not place N + o at v
(N absent from the target, or target(N) + o != v).

Symbols: the target's from its symbol source (an unstripped twin of the pin, given as ELF:SYMS); cgif's (stripped pins)
recovered by port_addr_check 5033540ba83b's `recover` (the frozen kit directory given by --kit), cached in --cache.

This version takes every path as an argument; the rows it writes are the rows of the earlier version (sha256
e7d879e2ed9c...) on the same inputs. Usage:

  donor_decimals.py --git GIT --kit KITDIR --donors-from DIR --cache DIR \\
      --cgif-image BUILD=ELF [...] [--target-image BUILD=ELF:SYMS ...] \\
      --tree NAME=REF[:ROOT][@BASE] [--tree ...] --target {disco|cgif} [--subdirs A,Reusable,U] [--plant FILE] --out OUT.tsv

BUILD is asan / asan-ubsan / ubsan (the image of a file follows its directory: lib/A asan, lib/U ubsan, lib/Reusable/Y*
and lib/Y asan-ubsan, any other file both asan images). A file whose build has no image given is a refusal (exit 2).
"""
import argparse, hashlib, importlib, os, re, subprocess, sys

KIT_SHA = '5033540ba83b'
LO, HI = 65536, 0x600000
DEC = re.compile(r"(?<![\w.'])(\d+)(?![\w.'])")
DECL = re.compile(r"\b(Definition|Lemma|Theorem|Corollary|Fact|Hypothesis|Hypotheses|Variable|Context|Instance|"
                  r"Notation|Let|Fixpoint|Record|Inductive|Abbreviation|Ltac)\s+([A-Za-z_][\w']*)")

P = None                # the kit's port_addr_check module (set by setup())
strip_comments = None   # the kit's scan_literals.strip_comments
CFG = {}


def setup(a):
    """Import the frozen kit from a.kit and keep every path argument; refuses a kit of another version."""
    global P, strip_comments
    kp = os.path.join(a.kit, 'port_addr_check.py')
    sha = hashlib.sha256(open(kp, 'rb').read()).hexdigest()
    if not sha.startswith(KIT_SHA):
        sys.exit(f'donor_decimals: REFUSED: {kp} is port_addr_check {sha[:12]}, not {KIT_SHA}')
    sys.path.insert(0, a.kit)
    P = importlib.import_module('port_addr_check')
    strip_comments = importlib.import_module('scan_literals').strip_comments
    CFG.update(git=a.git, donors_from=a.donors_from, cache=a.cache,
               donor_builds=a.donor_builds.split(','), donor_projects=a.donor_projects.split(','),
               cgif=dict(x.split('=', 1) for x in a.cgif_image),
               target={b: tuple(s.split(':', 1)) for b, s in (x.split('=', 1) for x in a.target_image)})
    print(f'# kit port_addr_check {sha}', file=sys.stderr)


def git(*a):
    return subprocess.run(['git', '-C', CFG['git'], *a], capture_output=True, text=True, check=True).stdout


def load_donors():
    out = []
    for e, d in donor_specs():
        out.append(P.Image(e, d, key=os.path.basename(e)))
    return out


def donor_specs():
    return P.find_donors(CFG['donors_from'], CFG['donor_builds'], CFG['donor_projects'])


def cgif_image(build):
    if build not in CFG['cgif']:
        sys.exit(f'donor_decimals: REFUSED: no --cgif-image {build}=ELF, and a scanned file needs it')
    S = P.Image(CFG['cgif'][build], None, key=f'cgif.{build}')
    if not S.syms:
        P.attach_recovery(S, donor_specs(), load_donors, CFG['cache'], log=lambda m: print(m, file=sys.stderr))
    return S


def target_image(target, build):
    if target == 'cgif':
        return cgif_image(build)
    if build not in CFG['target']:
        sys.exit(f'donor_decimals: REFUSED: no --target-image {build}=ELF:SYMS, and a scanned file needs it')
    e, d = CFG['target'][build]
    return P.Image(e, d, key=f'disco.{build}')


def build_of(path):
    rel = path.split('/lib/', 1)[1]
    if rel.startswith('A/'):
        return ['asan']
    if rel.startswith('U/'):
        return ['ubsan']
    if rel.startswith('Reusable/Y') or rel.startswith('Y/') or (rel.startswith('Y') and '/' not in rel):
        return ['asan-ubsan']
    return ['asan', 'asan-ubsan']


def cover(I, v):
    """(names, start, size) of I's symbol covering v, smallest first."""
    best = None
    for a, sz, ns, t, ev in I.syms:
        if a <= v < a + max(sz, 1) and ns:
            if best is None or sz < best[2]:
                best = (tuple(ns), a, sz)
    return best


def scan(files, target, out_rows, tree_name):
    imgs = {}
    for path, text in files:
        for b in build_of(path):
            if b not in imgs:
                imgs[b] = (cgif_image(b), target_image(target, b))
            C, T = imgs[b]
            body = strip_comments(text)
            lines = body.split('\n')
            for ln, line in enumerate(lines, 1):
                for m in DEC.finditer(line):
                    if line[max(0, m.start() - 2):m.start()].lower() == '0x':
                        continue
                    v = int(m.group(1))
                    if not (LO <= v < HI):
                        continue
                    c = cover(C, v)
                    if not c:
                        continue
                    names, cs, csz = c
                    off = v - cs
                    cands = [a + off for n in names for a, sz in T.byname.get(P.norm_name(n), [])]
                    if v in cands:
                        continue
                    tc = cover(T, v)
                    if tc and {P.norm_name(x) for x in tc[0]} & {P.norm_name(x) for x in names} and v - tc[1] == off:
                        continue
                    tv = min(cands, key=lambda x: abs(x - v)) if cands else None
                    decl = None
                    for k in range(ln - 1, -1, -1):
                        d = DECL.search(lines[k])
                        if d:
                            decl = f'{d.group(1)} {d.group(2)}'
                            break
                    out_rows.append(dict(tree=tree_name, image=b, file=path, line=ln, value=v, hexv=hex(v),
                                         cgif=f'{names[0]}+{off:#x}', cgif_size=csz,
                                         target_same=(hex(tv) if tv is not None else 'absent'),
                                         target_at_v=(f'{tc[0][0]}+{v - tc[1]:#x}' if tc else '-'),
                                         decl=decl or '-', text=line.strip()[:160]))


def tree_files(ref, subdirs, only_changed_vs=None):
    files = []
    for sd in subdirs:
        names = git('ls-tree', '-r', '--name-only', ref, '--', sd).split()
        if only_changed_vs:
            changed = set(git('diff', '--name-only', only_changed_vs, ref, '--', sd).split())
            names = [n for n in names if n in changed]
        for n in names:
            if n.endswith('.v'):
                files.append((n, git('show', f'{ref}:{n}')))
    return files


def add_image_args(ap):
    """The path arguments donor_decimals.py and funnel.py share."""
    ap.add_argument('--git', required=True, help='git dir for the --tree refs')
    ap.add_argument('--kit', required=True, help='directory of the frozen port_addr_check 5033540ba83b kit '
                    '(port_addr_check.py, scan_literals.py, cfgpair.py)')
    ap.add_argument('--donors-from', required=True, help='root of the symbolised donor images (<project>/<build>/<target> '
                    'with <target>.debug beside it) that cgif symbol recovery matches against')
    ap.add_argument('--donor-builds', default='asan,asan-ubsan,plain,ubsan')
    ap.add_argument('--donor-projects', default='omx-clap-core,plugin-hostd,libreac')
    ap.add_argument('--cache', required=True, help='recovery cache directory (written)')
    ap.add_argument('--cgif-image', action='append', default=[], metavar='BUILD=ELF', help="cgif's stripped pin")
    ap.add_argument('--target-image', action='append', default=[], metavar='BUILD=ELF:SYMS',
                    help='the target pin and its symbol source (unstripped twin); needed for --target disco')


def main():
    ap = argparse.ArgumentParser()
    add_image_args(ap)
    ap.add_argument('--tree', action='append', required=True, help='NAME=REF[:ROOT][@BASE] (BASE: only files changed vs it)')
    ap.add_argument('--target', default='disco', choices=['disco', 'cgif'])
    ap.add_argument('--subdirs', default='A,Reusable,U')
    ap.add_argument('--plant', help='local .v file scanned as an extra file under lib/A/')
    ap.add_argument('--out', required=True)
    a = ap.parse_args()
    setup(a)
    rows = []
    for t in a.tree:
        name, spec = t.split('=', 1)
        base = None
        if '@' in spec:
            spec, base = spec.split('@', 1)
        ref, root = (spec.split(':', 1) + ['proofs/libreac/fuzz_disco/lib'])[:2]
        subs = [f'{root}/{s}' for s in a.subdirs.split(',')]
        fl = tree_files(ref, subs, base)
        print(f'# {name}: {ref} {root}: {len(fl)} files', file=sys.stderr)
        scan(fl, a.target, rows, name)
    if a.plant:
        scan([('plant/lib/A/' + os.path.basename(a.plant), open(a.plant).read())], a.target, rows, 'plant')
    cols = ['tree', 'image', 'file', 'line', 'value', 'hexv', 'cgif', 'cgif_size', 'target_same', 'target_at_v', 'decl', 'text']
    with open(a.out, 'w') as f:
        f.write('\t'.join(cols) + '\n')
        for r in rows:
            f.write('\t'.join(str(r[c]) for c in cols) + '\n')
    print(f'# rows {len(rows)}', file=sys.stderr)


if __name__ == '__main__':
    main()
