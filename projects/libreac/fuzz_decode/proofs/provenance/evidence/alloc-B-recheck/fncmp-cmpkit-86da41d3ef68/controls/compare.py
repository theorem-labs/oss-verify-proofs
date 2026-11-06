#!/usr/bin/env python3
"""compare.py -- the kit 86da41d3ef68's own controls, as run here, against the outputs the kit registered (its controls/):
  negctl.out           vs controls/repin-negctl.out          byte for byte
  OUT/SUMMARY.tsv      vs controls/SUMMARY.tsv               per row: the seven verdict columns (plant, family, tool, sha12,
                                                             version, baseline verdict, planted verdict) exactly; the
                                                             evidence column after the directory paths are normalized
  OUT/planted.sha256   vs controls/planted.sha256            after the path normalization
  OUT/raw/             vs controls/suite-raw.tar.xz           every raw output file, after the path normalization
The path normalization replaces the five directories a run chooses (the planted-copy directory, the output directory, the
kit copy, the 4bbd3a74be89 kit copy and the cross-check directory) of THIS run and of the registered run by the same labels.
usage: compare.py RUN_DIR (holding kitrun/ oldkit/ xchk/ planted/ suite-out/ negctl.out) REG_RUN_ROOT (the registered
run's directory: the prefix of its planted/, controls/suite-out-kit3, kit4bbd/, kit3/, xchk/)"""
import collections, io, os, sys, tarfile

RUN, REG = (os.path.abspath(x) for x in sys.argv[1:3])
KC = os.path.join(RUN, 'kitrun', 'controls')
P = [(RUN + '/planted', '<planted>'), (RUN + '/suite-out', '<out>'), (RUN + '/kitrun', '<kit>'), (RUN + '/oldkit', '<oldkit>'),
     (RUN + '/xchk', '<xchk>'), (REG + '/planted', '<planted>'), (REG + '/controls/suite-out-kit3', '<out>'),
     (REG + '/kit4bbd', '<oldkit>'), (REG + '/kit3', '<kit>'), (REG + '/xchk', '<xchk>')]


def norm(s):
    for a, b in P:
        s = s.replace(a, b)
    return s


def main():
    out = []
    a, b = open(os.path.join(RUN, 'negctl.out'), 'rb').read(), open(os.path.join(KC, 'repin-negctl.out'), 'rb').read()
    out.append('negctl.py: negctl.out vs controls/repin-negctl.out: %s' % ('IDENTICAL' if a == b else 'DIFFERENT'))
    ra = [l.rstrip('\n').split('\t') for l in open(os.path.join(RUN, 'suite-out', 'SUMMARY.tsv'))]
    rb = [l.rstrip('\n').split('\t') for l in open(os.path.join(KC, 'SUMMARY.tsv'))]
    v7 = sum(x[:7] != y[:7] for x, y in zip(ra, rb))
    ev = [(x[0], x[2], len(x[7]), norm(x[7]), norm(y[7])) for x, y in zip(ra, rb) if norm(x[7]) != norm(y[7])]
    out.append('suite.py SUMMARY.tsv: rows %d / %d registered; rows whose seven verdict columns differ: %d; rows whose evidence '
               'differs after the path normalization: %d' % (len(ra), len(rb), v7, len(ev)))
    in_path = lambda s, k: s[s.rfind(' ', 0, k) + 1:][:1] == os.sep    # position k lies in a token that starts with '/'
    for p, t, n, x, y in ev:
        k = next((i for i in range(min(len(x), len(y))) if x[i] != y[i]), min(len(x), len(y)))
        how = ('the shorter is a prefix of the longer (the cut falls later in the run whose paths are shorter)'
               if k == min(len(x), len(y)) else 'they first differ inside a directory path the cut left unnormalizable'
               if in_path(x, k) and in_path(y, k) else 'they DIFFER')
        out.append('  %s %s: the evidence is cut at %d characters in both runs; normalized, %s: ..%s | ..%s' % (
            p, t, n, how, x[max(0, k - 50):k + 15], y[max(0, k - 50):k + 15]))
    pa = norm(open(os.path.join(RUN, 'suite-out', 'planted.sha256')).read())
    pb = norm(open(os.path.join(KC, 'planted.sha256')).read())
    out.append('suite.py planted.sha256: %d lines; %s after the path normalization' % (
        pa.count('\n'), 'IDENTICAL' if pa == pb else 'DIFFERENT'))
    reg = {}
    with tarfile.open(os.path.join(KC, 'suite-raw.tar.xz')) as t:
        for m in t.getmembers():
            if m.isfile() and '/raw/' in m.name:
                reg[m.name.split('/raw/', 1)[1]] = t.extractfile(m).read().decode('utf-8', 'replace')
    mine = os.path.join(RUN, 'suite-out', 'raw')
    fs = {os.path.relpath(os.path.join(d, f), mine) for d, _, ff in os.walk(mine) for f in ff}
    diff = [f for f in sorted(fs & set(reg)) if norm(open(os.path.join(mine, f), errors='replace').read()) != norm(reg[f])]
    out.append('suite.py raw outputs: %d files here, %d registered; only here %d, only registered %d; differing after the path '
               'normalization: %d' % (len(fs), len(reg), len(fs - set(reg)), len(set(reg) - fs), len(diff)))
    cells = collections.Counter(r[6] for r in ra[1:] if r[4].startswith('NEW'))
    out.append('kit-version (NEW) cells: %d: %s' % (sum(cells.values()), dict(cells.most_common())))
    print('\n'.join(out))


if __name__ == '__main__':
    main()
