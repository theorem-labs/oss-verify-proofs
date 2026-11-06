#!/usr/bin/env python3
"""Write the relocated fuzz_disco text of one fm route file, header line and numeral table included.

  python3 assemble.py disco-A|disco-Y <fm lib/A path without .v> --pred-dir DIR --table-dir DIR [--wt WORKTREE]
                      [--allow-stop] [--out FILE] [--dry-run] [--src-ref REF] [--not-keyed FILE]

Reads fm 3e35620c52e text from the hub git, the predict table <pred dir>/<target>/<path>.tsv (run predict.sh first),
writes <WT>/proofs/libreac/fuzz_disco/lib/{A|B}/<path>.v and <table dir>/<target>/<path>.table (each by rename, never
half written), and prints every Require'd disco module that is not in the worktree yet.  Exit 3: a STOP module; 4: a
refused numeral (same-name rule, recorded in the --not-keyed table when given), a P0 numerals.tsv disagreement or a
code-range count (a hand decides; --allow-stop writes the file with fm's value kept and the items in the header); 5: the
predict table is empty, partial or changed, or a substitution did not happen (re-run predict; never overridden).
New version of the G9 tool's assemble.py of record (sha256 3f12587966378062db389ac913a27490c4a2c724799e0030870278da0afbb276):
the fm branch name of line 1 is the environment variable FM_BRANCH, the table directory is --table-dir, the predict
directory --pred-dir (or PRED_DIR), the refused-numeral table --not-keyed (none by default), the piece files PIECES_DIR
(optional: group names in messages only), instead of constants or paths beside the script.
"""
import os, re, sys, csv, glob, fcntl, subprocess, collections, argparse
TOOLDIR = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, TOOLDIR)
import reloc, numerals

TOOL = '0767e70e074a'
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


def others(rows, path, target):
    """Rows of the predict table that give no relocated value (the tool did not key them, no HAND pick)."""
    out = []
    for r in rows:
        if r['verdict'] == 'MAPS' and r['expected']:
            continue
        h = numerals.by_hand(path, r['src_value'], target)
        if h and h[0] != numerals.KEEP:
            continue
        out.append(r)
    return out


def table_problems(rows, raw, summary, ref):
    """Why a predict table cannot be trusted (empty, partial, not matching its own summary, or predicted from another
    fm commit than `ref`), else []."""
    if not raw.strip():
        return ['the table is empty']
    if not os.path.exists(summary):
        return ['no %s beside the table' % os.path.basename(summary)]
    s = open(summary).read()
    m = re.search(r'^# files (?:read|paired) \d+; numerals (\d+)', s, re.M)
    if not m:
        return ['%s has no "numerals N" line (predict failed or is still running)' % os.path.basename(summary)]
    if int(m.group(1)) != len(rows):
        return ['the table has %d rows but its summary counts %d numerals: a partial table' % (len(rows), int(m.group(1)))]
    r = re.search(r'^# src-ref (\S+)', s, re.M)
    tref = r.group(1) if r else '3e35620c52e'     # a table predicted before --src-ref existed read the first route
    if commit_of(tref) != commit_of(ref):
        return ['the table was predicted from fm %s, not --src-ref %s' % (tref, ref)]
    return []

def commit_of(ref):
    """Full sha of an fm commit name (abbreviated shas compare equal to the full one)."""
    return subprocess.run(['git', '-C', reloc.HUB, 'rev-parse', '--verify', '-q', ref + '^{commit}'], capture_output=True,
                          text=True, env=dict(os.environ, GIT_NO_LAZY_FETCH='1')).stdout.strip() or ref


CONSTANTS = re.compile(r'^\s*(?:#\[[^\]]*\]\s*)?(?:Local\s+|Global\s+|Program\s+)*(?:Definition|Fixpoint|CoFixpoint|Lemma|'
                       r'Theorem|Corollary|Fact|Remark|Example|Proposition|Inductive|CoInductive|Record|Structure|Class|'
                       r'Instance|Axiom|Parameter|Variable|Hypothesis|Function|Let|Module|Notation)\b', re.M)


def per_image_requires(wt, probe):
    """For a class (a) text: the lib/A modules it Requires that each image has separately and that define constants
    (a Definition, Lemma, ... in the code of the lib/B copy, or of a per-image route file); tactic-only ones are fine."""
    out = []
    for dm in sorted(set(required_modules(probe))):
        rel = dm[6:]
        if not dm.startswith('lib.A.') or rel in reloc.NEUTRAL:
            continue
        twin = os.path.join(wt, reloc.DST_UNIT, 'lib', 'B', rel.replace('.', '/') + '.v')
        if os.path.exists(twin):
            src = open(twin).read()
        elif rel in reloc.fm_modules():
            src = reloc.fm_text(rel.replace('.', '/'))          # a route file each image relocates separately
        else:
            continue                                            # one copy, shared by both images
        if CONSTANTS.search(reloc.code_text(src)):
            out.append('%s defines constants and each image has its own copy' % dm)
    return out


def residual(out, kept):
    """Applied fm values still in the output code (outside KEY positions): a substitution that did not happen."""
    made = [k for k in kept if k[4] in ('applied', 'propagated', 'hand')]
    news = {k[2] for k in made}
    code = reloc.code_text(out).split('\n')
    bad = []
    for v in sorted({k[1] for k in made} - news):    # a value that is also a new value cannot be told apart
        at = [i for i, l in enumerate(code[1:], 2) if reloc.numeral_re(v).search(l) and not numerals.key_position(l, v)]
        if at:
            bad.append('fm value %s is still in the output code at line %s' % (v, ','.join(map(str, at))))
    return bad


def unapplied(rows, kept):
    """MAPS rows that should move a value but none moved or was refused: the table and the run disagree."""
    done = {k[4] for k in kept}
    movable = {(int(k[0]), k[1]) for k in kept if k[4] in ('applied', 'refused')}
    maps = [r for r in rows if r['verdict'] == 'MAPS' and r['expected']]
    if maps and movable == set() and not done & {'sym-key', 'kept-by-hand', 'same-value', 'hand', 'ident'}:
        return ['%d MAPS rows, 0 applied' % len(maps)]
    return []


def write_atomic(path, text):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    tmp = '%s.%d.tmp' % (path, os.getpid())
    with open(tmp, 'w') as fh:
        fh.write(text)
    os.replace(tmp, path)


def record_not_keyed(path, target, f, refused):
    """Add the refused numerals to the NOT-KEYED table at path (one row per target, file:line, value), under a lock."""
    groups = ' / '.join(sorted(groups_of_files().get(f, ['-'])))
    new = ['%s\t%s\t%s.v:%d\t%s\tREFUSED (predicted %s)\tMAPS\tSTOP, same-name rule: %s; a hand decides' % (
        target, groups, f, ln, val, exp, why[len('REFUSED: '):]) for ln, val, exp, why, _ in refused]
    with open(path + '.lock', 'a+') as lk:
        fcntl.flock(lk, fcntl.LOCK_EX)
        cur = open(path).read().rstrip('\n').split('\n') if os.path.exists(path) else []
        key = lambda l: tuple(l.split('\t')[i] for i in (0, 2, 3))
        have = {key(l) for l in cur[1:]}
        add = [l for l in new if key(l) not in have]
        if add:
            write_atomic(path, '\n'.join(cur + add) + '\n')


def header(target, f, text, kept, gaps, left=()):
    cfg = reloc.TARGETS[target]
    code = reloc.code_text(text)
    applied = [k for k in kept if k[4] in ('applied', 'propagated')]
    hand = sorted({(k[1], k[2]) for k in kept if k[4] == 'hand'})
    symkeys = {k[1] for k in kept if k[4] == 'sym-key'}
    lines = code.split('\n')
    symkeys |= {r['src_value'] for r in left if numerals.key_position(lines[int(r['src_line']) - 1], r['src_value'])}
    symkeys = sorted(symkeys)
    h = ('(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/%s.v (%s %s); '
         'relocated to libreac/%s by g9/tool (reloc.py target %s): module paths changed; %d address numerals moved '
         '(port_addr_check %s predict, fm.asan -> %s, symbol + offset; table g9/tool/tables/%s/%s.table)'
         % (f, FM_BRANCH, reloc.SRC_REF, cfg['image'], target, len(applied), TOOL, cfg['image'], target, f))
    if hand:
        h += '; by hand (numerals.py BY_HAND, reason in the table): %s' % ', '.join('%s -> %s' % p for p in hand)
    if symkeys:
        h += '; GXA symbol keys kept (%s)' % ', '.join(symkeys)
    ren = []
    if re.search(r'\bRT_IImgA\b', code):
        ren.append('record RT_IImgA -> %s' % ', '.join('%s %s.%s' % (n, m, d) for n, m, d in cfg['record']
                                                     if re.search(r'\b%s\b' % n, code)))
    for a, b in reloc.COMMON_IDENT:
        if re.search(r'\b%s\b' % a, code):
            ren.append('%s -> %s' % (a, b))
    core = sorted(a for a in cfg['core'] if re.search(r'\b%s\b' % a, code))
    if core:
        ren.append('A-core -> Y-core (lib.Reusable): ' + ', '.join('%s->%s' % (a, reloc.YCORE[a]) for a in core))
    if ren:
        h += '; names: ' + '; '.join(ren)
    if reloc.ZIFY_FLAG.search(code):
        h += '; zify flag override made Local'
    if reloc.IMG_NAMES.search(code):
        h += '; YImgTop zify_pre_hook added after the last Require'
    if gaps:
        h += '; hand checks: ' + '; '.join(gaps)
    return h + '. *)'


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('target', choices=sorted(reloc.TARGETS))
    ap.add_argument('file', help='fm path under lib/A, without .v (e.g. FMsnprintfImg, Bz/A/I_ikit)')
    ap.add_argument('--wt', default=os.environ.get('WT', os.getcwd()))
    ap.add_argument('--allow-stop', action='store_true',
                    help='write the file despite STOP modules, refused numerals (fm value kept), P0 disagreements or '
                         'range counts; each one is listed in the header')
    ap.add_argument('--out', help='write here instead of the worktree path')
    ap.add_argument('--pred-dir', default=os.environ.get('PRED_DIR'), help='predict tables (default $PRED_DIR)')
    ap.add_argument('--table-dir', default=os.environ.get('TABLE_DIR'),
                    help='where <target>/<path>.table is written (default $TABLE_DIR)')
    ap.add_argument('--not-keyed', help='the NOT-KEYED table refused numerals are added to (default: none)')
    ap.add_argument('--dry-run', action='store_true', help='run every check, write nothing (no .v, table, NOT-KEYED)')
    ap.add_argument('--src-ref', default=reloc.DEFAULT_SRC_REF,
                    help='fm commit to read the route file from (default %s; R9 rows: 0ddf65fd8cc)' % reloc.DEFAULT_SRC_REF)
    a = ap.parse_args()
    if not a.pred_dir or not (a.table_dir or a.dry_run):
        sys.exit('assemble.py: give --pred-dir and --table-dir (or PRED_DIR and TABLE_DIR)')
    reloc.set_src_ref(a.src_ref)
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
    again = './predict.sh %s%s %s' % ('' if a.src_ref == reloc.DEFAULT_SRC_REF else '--src-ref %s ' % a.src_ref, a.target, f)
    if not os.path.exists(tsv):
        sys.exit('%s: no predict table %s; run %s' % (f, tsv, again))
    rows, raw = numerals.read_table(tsv)
    bad = table_problems(rows, raw, tsv[:-4] + '.summary', a.src_ref)
    if bad:
        sys.stderr.write('%s: REFUSED, predict table %s: %s; re-run %s\n' % (f, tsv, bad[0], again))
        sys.exit(5)
    subs, kept = numerals.build(rows, text, f, a.target)
    probe = reloc.relocate(text, subs, '')
    stops = {k: v for k, v in reloc.NOTES.items() if v.startswith('STOP')}
    if mod in reloc.NEUTRAL:
        per = per_image_requires(a.wt, probe)
        if per:
            stops['class (a)'] = 'STOP: one copy cannot serve both images: ' + '; '.join(per) + '; relocate it per image'
    refused = [k for k in kept if k[4] == 'refused']
    holds = ['line %d %s refused (predicted %s): %s' % (ln, v, e, why[len('REFUSED: '):]) for ln, v, e, why, _ in refused]
    holds += ['P0 numerals.tsv: ' + m for m in numerals.p0_check(f, a.target, text, kept)]
    holds += ['code range: ' + m for m in numerals.range_check(text, subs, kept, a.target)]
    status = module_status(a.wt, required_modules(probe))
    left = others(rows, f, a.target)
    gaps = ['%s %s' % (k, v) for k, v in stops.items()] + holds
    out = reloc.relocate(text, subs, header(a.target, f, text, kept, gaps, left))
    broken = residual(out, kept) + unapplied(rows, kept)
    if numerals.read_table(tsv)[1] != raw:
        broken.append('the predict table changed while assembling')
    if refused and not a.dry_run and a.not_keyed:
        record_not_keyed(a.not_keyed, a.target, f, refused)
    for m in broken:
        sys.stderr.write('%s: REFUSED, %s\n' % (f, m))
    for k, v in stops.items():
        sys.stderr.write('%s: names %s: %s\n' % (f, k, v))
    for m in holds:
        sys.stderr.write('%s: STOP, %s\n' % (f, m))
    if broken:
        sys.exit(5)
    if (stops or holds) and not a.allow_stop:
        sys.exit(3 if stops else 4)
    if a.dry_run:
        print('%s: %s, checks pass (dry run, nothing written)' % (f, a.target))
        return
    write_atomic(dest, out)
    lines = reloc.code_text(text).split('\n')
    table = ['how\tfm file:line (fm %s)\tfm value\tdisco value\twhy' % reloc.SRC_REF]
    for ln, val, exp, res, how in sorted(kept, key=lambda k: (k[0], k[1])):
        table.append('%s\t%s:%d\t%s\t%s\t%s' % (how, f + '.v', ln, val, exp, res if how in ('hand', 'refused') else res.split(';')[0]))
    for r in left:
        v = str(int(r['src_value'], 16)) if r['kind'] == 'dec' else r['src_value']
        why = r['src_res'] or r['note']
        how = 'NOT-KEYED ' + r['verdict']
        if numerals.key_position(lines[int(r['src_line']) - 1], v):
            how += ' sym-key'
            why = 'GXA symbol key, kept: disco lib/CJ/RL/I/IImg{A,B}.v KV rows map it; ' + why
        table.append('%s\t%s:%s\t%s\t%s\t%s' % (how, f + '.v', r['src_line'], v, r['expected'] or 'fm value kept', why))
    write_atomic(os.path.join(a.table_dir, a.target, f + '.table'), '\n'.join(table) + '\n')
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
