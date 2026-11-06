#!/usr/bin/env python3
"""mk_results.py RUNLOG GATES.md [CTLLOG ...] -- writes the `## Gate run of record` section of GATES.md FROM the log of a
run_gates.sh run (and the logs of the runner's CTL control runs), so no result in that section is typed by hand. The
section lies between two marker lines; it is replaced as a whole, or inserted before the `## Gate table` heading when
it is not there yet. From RUNLOG it reads: the runner's RUN line (its sha256, the gates, the sha256 of each input file),
the G0 snapshot lines, the GD.expect lines GD echoes, every RESULT line, the runner's SUMMARY line, the runner's own
`run_gates.sh exit status: N` line and the wrapper's `WRAPPER run_gates.sh exit status N; wall N s` line. It refuses
(exit 1, GATES.md unchanged) when one of those lines is missing, when the runner's and the wrapper's exit status differ,
or when its own count of RESULT lines differs from the runner's SUMMARY.
  python3 mk_results.py W/logs/run.vNfull.out W/GATES-wireB.md W/logs/run.vNctl.fail.out W/logs/run.vNctl.ok.out"""
import hashlib
import os
import re
import sys

BEGIN = '<!-- BEGIN gate run of record: written by gates/mk_results.py from the run log; change the run, not this text -->'
END = '<!-- END gate run of record -->'
RES = re.compile(r'^RESULT (.*) rc=(\S+) \(want (\d+)\) (OK|UNEXPECTED)$')


def sha(p):
    return hashlib.sha256(open(p, 'rb').read()).hexdigest()


def one(rx, lines, what, path):
    hits = [m for m in (re.search(rx, line) for line in lines) if m]
    if len(hits) != 1:
        sys.exit('mk_results: REFUSED: %s: %d line(s) for %s, 1 needed' % (path, len(hits), what))
    return hits[0]


def run(path):
    lines = open(path).read().split('\n')
    r = {'path': path, 'lines': lines}
    r['run'] = one(r'^RUN run_gates\.sh sha256 ([0-9a-f]{64}); gates: ([^;]*); AF0M_A sha256 ([^;]*); AD1G_PATCHED sha256 '
                   r'([^;]*); GD\.expect sha256 ([^;]*); trunk clone HEAD ([0-9a-f]{40})$', lines, 'the RUN line', path)
    r['own'] = int(one(r'^run_gates\.sh exit status: (\d+)$', lines, "the runner's exit status", path).group(1))
    w = one(r'^WRAPPER run_gates\.sh exit status (\d+); wall (\d+) s$', lines, "the wrapper's exit status", path)
    r['wrap'], r['wall'] = int(w.group(1)), int(w.group(2))
    if r['own'] != r['wrap']:
        sys.exit('mk_results: REFUSED: %s: the runner says exit status %d, the wrapper saw %d' % (path, r['own'], r['wrap']))
    s = one(r'^SUMMARY: RESULT lines (\d+) in this run\'s logs \(([^)]*)\); OK \(rc = the stated want\) (\d+); '
            r'UNEXPECTED or no want stated (\d+)$', lines, 'the SUMMARY line', path)
    r['n'], r['logs'], r['ok'], r['bad'] = int(s.group(1)), s.group(2), int(s.group(3)), int(s.group(4))
    r['res'] = [l for l in lines if l.startswith('RESULT ')]
    r['rows'] = [RES.match(l) for l in r['res']]
    nok = sum(1 for m in r['rows'] if m and m.group(4) == 'OK')
    if len(r['res']) != r['n'] or nok != r['ok']:
        sys.exit('mk_results: REFUSED: %s: %d RESULT lines / %d OK here, the SUMMARY says %d / %d'
                 % (path, len(r['res']), nok, r['n'], r['ok']))
    return r


def cell(t):
    return t.replace('|', '\\|').replace('`', "'")


def main():
    if len(sys.argv) < 3:
        sys.exit(__doc__)
    runlog, gates, ctl = sys.argv[1], sys.argv[2], sys.argv[3:]
    r = run(runlog)
    m = r['run']
    L = r['lines']
    g0 = [l for l in L if l.startswith('G0 snapshot: ') or l.startswith('G0 snapshot vs lib/B of the trunk clone')]
    i = next((k for k, l in enumerate(L) if l.startswith('=== GD.expect ')), None)
    gdx = []
    if i is not None:
        for l in L[i + 1:]:
            if not l.startswith('  '):
                break
            gdx.append(l.strip())
    nz = [x for x in r['rows'] if x and x.group(3) != '0']
    out = ['## Gate run of record', '', BEGIN,
           'Written by `gates/mk_results.py` (sha256 %s) from `logs/%s` (sha256 %s).'
           % (sha(__file__)[:12], os.path.basename(runlog), sha(runlog)[:12]), '',
           '- Runner: `gates/run_gates.sh` sha256 %s; gates run: `%s`.' % (m.group(1), m.group(2)),
           "- Inputs: image A's AF0m (AF0M_A) sha256 %s; the B core's YD1g (AD1G_PATCHED) sha256 %s; `gates/GD.expect` "
           'sha256 %s; trunk clone HEAD %s.' % (m.group(3), m.group(4), m.group(5), m.group(6))]
    out += ['- `%s`' % l.rstrip() for l in g0]
    out += ['- **Exit status %d**: the runner\'s own (1 when a RESULT line of the run is UNEXPECTED or states no want); '
            'the wrapper saw %d; wall %d s.' % (r['own'], r['wrap'], r['wall']),
            '- RESULT lines: %d (in %s); OK %d; UNEXPECTED or no want stated %d. Steps whose wanted rc is not 0: %d (each '
            'a control or a known result; its label says which).' % (r['n'], r['logs'], r['ok'], r['bad'], len(nz))]
    for c in ctl:
        cr = run(c)
        bad = [x.group(1) for x in cr['rows'] if x and x.group(4) == 'UNEXPECTED']
        out.append('- Runner control `logs/%s` (`%s`): exit status %d; RESULT lines %d, OK %d, UNEXPECTED %d%s.'
                   % (os.path.basename(c), cr['run'].group(2), cr['own'], cr['n'], cr['ok'], cr['bad'],
                      (': ' + ', '.join('`%s`' % b for b in bad)) if bad else ''))
    if gdx:
        out += ['- GD expectations, as GD read them from `gates/GD.expect`:', '']
        out += ['    ' + l for l in gdx]
    out += ['', '| # | step | rc | want | verdict |', '|---|---|---|---|---|']
    for k, (l, x) in enumerate(zip(r['res'], r['rows']), 1):
        if x:
            out.append('| %d | %s | %s | %s | %s |' % (k, cell(x.group(1)), x.group(2), x.group(3),
                                                     x.group(4) if x.group(4) == 'OK' else '**UNEXPECTED**'))
        else:
            out.append('| %d | %s | - | - | **no want stated** |' % (k, cell(l[len('RESULT '):])))
    out += [END, '']
    t = open(gates).read()
    if BEGIN in t and END in t:
        a, b = t.index(BEGIN), t.index(END) + len(END)
        a = t.rindex('## Gate run of record', 0, a)
        t = t[:a] + '\n'.join(out).rstrip('\n') + t[b:]
    else:
        a = t.index('\n## Gate table\n') + 1
        t = t[:a] + '\n'.join(out) + '\n' + t[a:]
    open(gates, 'w').write(t)
    print('mk_results: %s: section written from %s (%d RESULT lines, exit status %d, %d control log(s))'
          % (gates, runlog, r['n'], r['own'], len(ctl)))


main()
