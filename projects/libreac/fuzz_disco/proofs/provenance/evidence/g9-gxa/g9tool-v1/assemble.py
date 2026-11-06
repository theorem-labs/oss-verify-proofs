#!/usr/bin/env python3
"""Write the relocated fuzz_disco text of one fm route file, header line and numeral table included.

  python3 assemble.py disco-A|disco-Y <fm lib/A path without .v> --pred-dir DIR --table-dir DIR [--wt WORKTREE]
                      [--allow-stop] [--out FILE]

Reads fm 3e35620c52e text from the hub git, the predict table <pred dir>/<target>/<path>.tsv (run predict.sh first),
writes <WT>/proofs/libreac/fuzz_disco/lib/{A|B}/<path>.v and <table dir>/<target>/<path>.table, and prints every
Require'd disco module that is not in the worktree yet.
New version of the first G9 tool version's assemble.py (sha256 6e1c1063d31e871344af08eb533f5a9bd9c97ceb7dffafec263c6ec9ac2ddd4a):
the fm branch name of line 1 is the environment variable FM_BRANCH, the predict and table directories are --pred-dir
and --table-dir, the piece files PIECES_DIR (optional: group names in messages only), instead of constants or paths
beside the script.
"""
import os, re, sys, csv, glob, collections, argparse
TOOLDIR = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, TOOLDIR)
import reloc, numerals

TOOL = '0767e70e074a'
SHA = reloc.SRC_REF
# the name of the fm branch that holds the source commits, as line 1 writes it before the commit
FM_BRANCH = os.environ.get('FM_BRANCH') or sys.exit('assemble.py: set FM_BRANCH (the fm branch name of line 1)')
PIECES = os.environ.get('PIECES_DIR')


def groups_of_files():
    """fm path (A/...) -> group name, from the P0 piece files (none when PIECES_DIR is not set)."""
    out = {}
    for md in glob.glob(os.path.join(PIECES, 'P*-*-*.md')) if PIECES else ():
        g = os.path.basename(md)[:-3]
        for line in open(md):
            m = re.match(r'\|\s*\d+\s*\|\s*`(A/[^`]+)\.v`', line)
            if m:
                out.setdefault(m.group(1)[2:], []).append(g)
    return out


def required_modules(text):
    """Disco modules a relocated text Requires (From ... Require ..., Require <path>.)."""
    mods = []
    lines = text.split('\n')
    i = 0
    while i < len(lines):
        s = lines[i]
        if (s.startswith('From ') and ' Require' in s) or s.startswith('Require '):
            stmt = [s]
            while not stmt[-1].rstrip().endswith('.') and i + 1 < len(lines):
                i += 1
                stmt.append(lines[i])
            j = ' '.join(x.strip() for x in stmt)
            m = re.match(r'From\s+([A-Za-z0-9_.]+)\s+Require\s+(?:Import\s+|Export\s+)?(.*)\.$', j)
            if m and m.group(1).startswith(reloc.DSTPFX):
                mods += [m.group(1)[len(reloc.DSTPFX):] + '.' + n for n in m.group(2).split()]
            m = re.match(r'Require\s+(?:Import\s+|Export\s+)?(.*)\.$', j)
            if m and not j.startswith('From '):
                mods += [n[len(reloc.DSTPFX):] for n in m.group(1).split() if n.startswith(reloc.DSTPFX)]
        i += 1
    return mods


def module_status(wt, mods):
    """For each disco module that is not a file in the worktree: pending route file (group) or MISSING."""
    routes = None
    out = []
    for dm in sorted(set(mods)):
        if os.path.exists(os.path.join(wt, reloc.DST_UNIT, dm.replace('.', '/') + '.v')):
            continue
        routes = routes if routes is not None else groups_of_files()
        rel = dm.split('.', 2)[2] if dm.startswith(('lib.A.', 'lib.B.')) else None
        fm = rel.replace('.', '/') if rel else None
        if fm and fm in routes:
            out.append((dm, 'pending: fm A/%s.v, group %s' % (fm, ' / '.join(sorted(routes[fm])))))
        else:
            out.append((dm, 'MISSING'))
    return out


def others(tsv, stem, target):
    """Rows of the predict table that give no relocated value (the tool did not key them, no HAND pick)."""
    rows = []
    with open(tsv) as fh:
        for r in csv.DictReader(fh, delimiter='\t'):
            if r['verdict'] == 'MAPS' and r['expected']:
                continue
            if target in numerals.HAND.get((stem, r['src_value']), {}):
                continue
            rows.append(r)
    return rows


def header(target, f, text, kept, gaps, left=()):
    cfg = reloc.TARGETS[target]
    applied = [k for k in kept if k[4] in ('applied', 'propagated')]
    hand = sorted({(k[1], k[2]) for k in kept if k[4] == 'hand'})
    symkeys = {k[1] for k in kept if k[4] == 'sym-key'}
    lines = text.split('\n')
    symkeys |= {r['src_value'] for r in left
                if re.search(r'sym\s+(?:[A-Za-z0-9_]+\s+)?' + re.escape(r['src_value']) + r'\b',
                             lines[int(r['src_line']) - 1])}
    symkeys = sorted(symkeys)
    h = ('(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/%s.v (%s %s); '
         'relocated to libreac/%s by g9/tool (reloc.py target %s): module paths changed; %d address numerals moved '
         '(port_addr_check %s predict, fm.asan -> %s, symbol + offset; table g9/tool/tables/%s/%s.table)'
         % (f, FM_BRANCH, SHA, cfg['image'], target, len(applied), TOOL, cfg['image'], target, f))
    if hand:
        h += '; by hand (numerals.py HAND, reason in the table): %s' % ', '.join('%s -> %s' % p for p in hand)
    if symkeys:
        h += '; GXA symbol keys kept (%s)' % ', '.join(symkeys)
    ren = []
    if re.search(r'\bRT_IImgA\b', text):
        ren.append('record RT_IImgA -> %s' % ', '.join('%s %s.%s' % (n, m, d) for n, m, d in cfg['record']
                                                     if re.search(r'\b%s\b' % n, text)))
    for a, b in reloc.COMMON_IDENT:
        if re.search(r'\b%s\b' % a, text):
            ren.append('%s -> %s' % (a, b))
    core = sorted(a for a in cfg['core'] if re.search(r'\b%s\b' % a, text))
    if core:
        ren.append('A-core -> Y-core (lib.Reusable): ' + ', '.join('%s->%s' % (a, reloc.YCORE[a]) for a in core))
    if ren:
        h += '; names: ' + '; '.join(ren)
    if gaps:
        h += '; hand checks: ' + '; '.join(gaps)
    return h + '. *)'


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('target', choices=sorted(reloc.TARGETS))
    ap.add_argument('file', help='fm path under lib/A, without .v (e.g. FMsnprintfImg, Bz/A/I_ikit)')
    ap.add_argument('--wt', default=os.environ.get('WT', os.getcwd()))
    ap.add_argument('--allow-stop', action='store_true', help='write the file even if it names a STOP module')
    ap.add_argument('--out', help='write here instead of the worktree path')
    ap.add_argument('--pred-dir', default=os.environ.get('PRED_DIR'), help='predict tables (default $PRED_DIR)')
    ap.add_argument('--table-dir', default=os.environ.get('TABLE_DIR'),
                    help='where <target>/<path>.table is written (default $TABLE_DIR)')
    a = ap.parse_args()
    if not a.pred_dir or not a.table_dir:
        sys.exit('assemble.py: give --pred-dir and --table-dir (or PRED_DIR and TABLE_DIR)')
    f = a.file[:-2] if a.file.endswith('.v') else a.file
    mod = f.replace('/', '.')
    reloc.set_target(a.target)
    cfg = reloc.TARGETS[a.target]
    if mod in reloc.COMMON or mod in cfg['rename'] or mod in reloc.STOP:
        sys.exit('%s: not relocated by this tool (disco has it as %s)' % (f, reloc.COMMON.get(mod) or cfg['rename'].get(mod)
                                                                        or reloc.STOP.get(mod)))
    if mod in reloc.NEUTRAL and a.target != 'disco-A':
        print('%s: class (a), one copy at lib/A/%s.v serves both images; relocate it with disco-A' % (f, f))
        return
    destdir = 'lib/A' if mod in reloc.NEUTRAL else cfg['pathdir']
    dest = a.out or os.path.join(a.wt, reloc.DST_UNIT, destdir, f + '.v')
    text = reloc.fm_text(f)
    tsv = os.path.join(a.pred_dir, a.target, f + '.tsv')
    if not os.path.exists(tsv):
        sys.exit('%s: no predict table %s; run ./predict.sh %s %s' % (f, tsv, a.target, f))
    subs, kept = numerals.build(tsv, text, os.path.basename(f), a.target)
    probe = reloc.relocate(text, subs, '')
    stops = {k: v for k, v in reloc.NOTES.items() if v.startswith('STOP')}
    if stops and not a.allow_stop:
        for k, v in stops.items():
            print('%s: names %s: %s' % (f, k, v), file=sys.stderr)
        sys.exit(3)
    status = module_status(a.wt, required_modules(probe))
    left = others(tsv, os.path.basename(f), a.target)
    gaps = ['%s %s' % (k, v) for k, v in stops.items()]
    out = reloc.relocate(text, subs, header(a.target, f, text, kept, gaps, left))
    os.makedirs(os.path.dirname(dest), exist_ok=True)
    open(dest, 'w').write(out)
    tdir = os.path.join(a.table_dir, a.target, os.path.dirname(f))
    os.makedirs(tdir, exist_ok=True)
    with open(os.path.join(a.table_dir, a.target, f + '.table'), 'w') as fh:
        fh.write('how\tfm file:line\tfm value\tdisco value\twhy\n')
        for ln, val, exp, res, how in sorted(kept, key=lambda k: (k[0], k[1])):
            fh.write('%s\t%s:%d\t%s\t%s\t%s\n' % (how, f + '.v', ln, val, exp, res if how == 'hand' else res.split(';')[0]))
        lines = text.split('\n')
        for r in left:
            v = str(int(r['src_value'], 16)) if r['kind'] == 'dec' else r['src_value']
            why = r['src_res'] or r['note']
            how = 'NOT-KEYED ' + r['verdict']
            if re.search(r'sym\s+(?:[A-Za-z0-9_]+\s+)?' + re.escape(v) + r'\b', lines[int(r['src_line']) - 1]):
                how += ' sym-key'
                why = 'GXA symbol key, kept: disco lib/CJ/RL/I/IImg{A,B}.v KV rows map it; ' + why
            fh.write('%s\t%s:%s\t%s\t%s\t%s\n' % (how, f + '.v', r['src_line'], v,
                                                r['expected'] or 'fm value kept', why))
    c = collections.Counter(k[4] for k in kept)
    nk = collections.Counter(r['verdict'] for r in left)
    print('%s -> %s' % (f, os.path.relpath(dest, a.wt)))
    print('  numerals: %s; not keyed: %s' % (dict(c), dict(nk)))
    for dm, why in status:
        print('  Require %s: %s' % (dm, why))
    for k, v in reloc.NOTES.items():
        print('  %s %s: %s' % (v.split(':')[0], k, v.split(':', 1)[1].strip()))


if __name__ == '__main__':
    main()
