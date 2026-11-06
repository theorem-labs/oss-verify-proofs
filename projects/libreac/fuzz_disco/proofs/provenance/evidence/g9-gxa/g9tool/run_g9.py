#!/usr/bin/env python3
"""Re-run the G9 relocation of every shipped file the tool wrote, and compare each output with the shipped bytes.

  run_g9.py SHIPPED_REF OUT [--jobs-ref REF] [--clean-room COMMIT ...] [--jobs N]

SHIPPED_REF: the commit of the tree every output is compared with (its proofs/libreac/fuzz_disco/lib). --jobs-ref: the
tree the job list is read from (default SHIPPED_REF): every lib file whose line 1 there is the G9 tool's header gives
the fm path, the fm commit and the target; a header with `hand checks:` was written with --allow-stop. --clean-room
COMMIT: a commit that wrote tool-written files anew from their statements; each job file it changed must be, at
SHIPPED_REF, the blob that commit wrote, and its row says so in the how column, with whether every distinct address
literal (>= 0x10000) of its code is in the tool's code. Environment (as predict.sh, numerals.py and assemble.py read
it): HUB, PAC_DIR, FM_IMAGE / FM_DEBUG, A_IMAGE / A_DEBUG, Y_IMAGE / Y_DEBUG, P0_NUMERALS, FM_BRANCH. Every child runs
with PYTHONHASHSEED=0 (the checker's notes list aliases in set order).

Steps: the lib tree of SHIPPED_REF is unpacked into OUT/wt (assemble reads the Require'd modules there); predict.sh
runs once per (fm commit, target) into OUT/pred/<commit>; the fixed tool (this directory) assembles every job into
OUT/v/fixed/<shipped path>; a job of fm 3e35620c52e whose output differs is assembled again with the first tool version
(../g9tool-v1) into OUT/v/first/<shipped path>. Writes:
  OUT/g9-rerun.tsv          one row per shipped file: which version reproduces it byte for byte, else how it differs;
  OUT/g9-table-disco-A.tsv, OUT/g9-table-disco-Y.tsv   the per-numeral tables of the version that reproduced each
                            file (the fixed one where none did), one table per target with the shipped file as the first
                            column.
"""
import argparse
import collections
import concurrent.futures
import hashlib
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
V1 = os.path.join(os.path.dirname(HERE), 'g9tool-v1')
LIB = 'proofs/libreac/fuzz_disco/lib'
HEAD = re.compile(r'^\(\* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/(?P<f>.+?)\.v \(\S+ (?P<ref>[0-9a-f]+)\); '
                  r'relocated to libreac/\S+ by g9/tool \(reloc\.py target (?P<t>disco-[AY])\)')
FIRST_REF = '3e35620c52e'
HUB = os.environ.get('HUB') or sys.exit('run_g9.py: set HUB')
sys.path.insert(0, HERE)
import reloc                                   # noqa: E402  (code_text only)


def git(*a, data=None):
    return subprocess.run(['git', '-C', HUB, *a], input=data, capture_output=True, check=True,
                          env=dict(os.environ, GIT_NO_LAZY_FETCH='1')).stdout


def shipped_files(ref):
    paths = [p for p in git('ls-tree', '-r', '--name-only', ref, '--', LIB + '/').decode().split('\n') if p.endswith('.v')]
    out = git('cat-file', '--batch', data=''.join('%s:%s\n' % (ref, p) for p in paths).encode())
    blobs, i = {}, 0
    for p in paths:
        j = out.index(b'\n', i)
        size = int(out[i:j].split()[2])
        blobs[p] = out[j + 1:j + 1 + size]
        i = j + 1 + size + 1
    return blobs


def jobs_of(blobs):
    jobs = []
    for p, b in sorted(blobs.items()):
        line1 = b.split(b'\n', 1)[0].decode('utf-8', 'replace')
        m = HEAD.match(line1)
        if m:
            jobs.append(dict(path=p, f=m.group('f'), ref=m.group('ref'), target=m.group('t'),
                             allow='; hand checks: ' in line1, data=b))
    return jobs


def run(cmd, env):
    r = subprocess.run(cmd, capture_output=True, text=True, env=env)
    return r.returncode, r.stdout + r.stderr


REQ = re.compile(r'From\s+([A-Za-z0-9_.]+)\s+Require\s+(Import\s+|Export\s+)?([^.]*(?:\.[A-Za-z0-9_]+)*)\s*\.(?=\s|$)')


def norm_requires(code):
    """code with every From ... Require statement replaced by the sorted set of (path, kind, name) it Requires"""
    reqs = set()

    def take(m):
        for n in m.group(3).split():
            reqs.add((m.group(1), (m.group(2) or '').strip(), n))
        return ' '
    rest = REQ.sub(take, code)
    return sorted(reqs), ' '.join(rest.split())


def literals(code):
    return collections.Counter(x.lower() for x in re.findall(r'0x[0-9a-fA-F]+', code) if int(x, 16) >= 0x10000)


def differs(shipped, out):
    """how the shipped text differs from the tool's: (class, every shipped address literal in the tool's code?)"""
    a, b = reloc.code_text(shipped.decode()), reloc.code_text(out.decode())
    lits = 'yes' if not literals(a) - literals(b) else 'no'
    if a.split() == b.split():
        return 'comments or white space only', lits
    if norm_requires(a) == norm_requires(b):
        return 'Require statements grouped differently only', lits
    return 'code differs (a step after the tool)', lits


def clean_room(commits, shipped_ref, jobs):
    """{job path: commit} for the job files each clean-room commit changed; each must be, at shipped_ref, the blob
    that commit wrote (else a later change is not covered and the run stops)"""
    out = {}
    paths = {j['path'] for j in jobs}
    for c in commits:
        full = git('rev-parse', '--verify', c + '^{commit}').decode().strip()
        for p in git('diff-tree', '--no-commit-id', '-r', '--name-only', full).decode().split():
            if p not in paths:
                continue
            if git('rev-parse', '%s:%s' % (full, p)) != git('rev-parse', '%s:%s' % (shipped_ref, p)):
                sys.exit('run_g9.py: %s at %s is not the blob %s wrote' % (p, shipped_ref, full[:12]))
            out[p] = full
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('shipped_ref')
    ap.add_argument('out')
    ap.add_argument('--jobs-ref')
    ap.add_argument('--clean-room', action='append', default=[])
    ap.add_argument('--jobs', type=int, default=6)
    a = ap.parse_args()
    O = os.path.abspath(a.out)
    env = dict(os.environ, PYTHONHASHSEED='0', GIT_NO_LAZY_FETCH='1', PYTHONDONTWRITEBYTECODE='1')
    blobs = shipped_files(a.shipped_ref)
    jobs = jobs_of(shipped_files(a.jobs_ref) if a.jobs_ref else blobs)
    for j in jobs:
        j['data'] = blobs.get(j['path']) or sys.exit('run_g9.py: %s is not in %s' % (j['path'], a.shipped_ref))
    restated = clean_room(a.clean_room, a.shipped_ref, jobs)
    print('jobs: %d files carry the G9 header in %s; %d restated clean-room' % (
        len(jobs), a.jobs_ref or a.shipped_ref, len(restated)))
    wt = os.path.join(O, 'wt')
    if not os.path.isdir(os.path.join(wt, LIB)):
        os.makedirs(wt, exist_ok=True)
        tar = git('archive', a.shipped_ref, LIB)
        subprocess.run(['tar', '-x', '-C', wt], input=tar, check=True)
    groups = collections.defaultdict(list)
    for j in jobs:
        groups[(j['ref'], j['target'])].append(j['f'])
    for (ref, t), fs in sorted(groups.items()):
        rc, log = run(['bash', os.path.join(HERE, 'predict.sh'), '--src-ref', ref, t] + sorted(set(fs)),
                      dict(env, PRED_DIR=os.path.join(O, 'pred', ref)))
        print('predict %s %s: %d files, rc %d' % (ref, t, len(set(fs)), rc))
        if rc:
            sys.exit(log[-4000:])

    def assemble(j, version):
        tool = HERE if version == 'fixed' else V1
        out = os.path.join(O, 'v', version, j['path'])
        os.makedirs(os.path.dirname(out), exist_ok=True)
        cmd = [sys.executable, os.path.join(tool, 'assemble.py'), j['target'], j['f'], '--pred-dir',
               os.path.join(O, 'pred', j['ref']), '--table-dir', os.path.join(O, 'tables', version, j['ref']),
               '--wt', wt, '--out', out] + (['--src-ref', j['ref']] if version == 'fixed' else [])
        if j['allow']:
            cmd.append('--allow-stop')
        if os.path.exists(out):
            os.remove(out)
        rc, log = run(cmd, env)
        if rc in (3, 4) and not j['allow']:
            # the shipped header lists no hand check, so it was not written by this run: write the tool's text anyway
            # (--allow-stop) to say how the shipped file differs from it
            rc2, log2 = run(cmd + ['--allow-stop'], env)
            log = '%s; with --allow-stop for the comparison: rc %d' % (log.strip().split('\n')[-1][:200], rc2)
        data = open(out, 'rb').read() if os.path.exists(out) else None
        return rc, data, log

    with concurrent.futures.ThreadPoolExecutor(a.jobs) as ex:
        fixed = list(ex.map(lambda j: assemble(j, 'fixed'), jobs))
        again = [j for j, (rc, d, _) in zip(jobs, fixed) if d != j['data'] and j['ref'] == FIRST_REF]
        first = dict(zip([j['path'] for j in again], ex.map(lambda j: assemble(j, 'first'), again)))
    rows = ['shipped file\ttarget\tfm ref\tallow-stop\tfixed tool rc\tfixed tool output = shipped\t'
            'first version output = shipped\treproduced by\thow the shipped file differs from the fixed output\t'
            'every shipped address literal (>= 0x10000, code) in the fixed output\tshipped sha256\tre-run sha256']
    tables = collections.defaultdict(list)
    for j, (rc, d, log) in zip(jobs, fixed):
        f1 = first.get(j['path'])
        eq0, eq1 = d == j['data'], bool(f1 and f1[1] == j['data'])
        by = 'fixed' if eq0 else 'first' if eq1 else 'none'
        how, lits = differs(j['data'], d) if by == 'none' and d is not None else ('', '')
        if by == 'none' and d is not None and j['path'] in restated:
            sa, sb = (set(literals(reloc.code_text(x.decode()))) for x in (j['data'], d))
            lits = 'yes' if sa <= sb else 'no'
            how = ('clean-room restatement %s: proof text not tool output; every distinct address literal >= 0x10000 '
                   'of the shipped code in the tool output: %s' % (restated[j['path']][:12], lits))
        if rc in (3, 4) and not j['allow']:
            how = '%s; the tool stops without --allow-stop (rc %d): %s' % (how, rc, log)
        if d is None:
            how = 'no output (rc %d): %s' % (rc, log.strip().split('\n')[-1][:200])
        got = d if by != 'first' else f1[1]
        rows.append('\t'.join([j['path'], j['target'], j['ref'], 'yes' if j['allow'] else 'no', str(rc),
                               'yes' if eq0 else 'no', ('yes' if eq1 else 'no') if f1 else '-', by, how, lits,
                               hashlib.sha256(j['data']).hexdigest(),
                               hashlib.sha256(got).hexdigest() if got is not None else '-']))
        version = 'first' if by == 'first' else 'fixed'
        tpath = os.path.join(O, 'tables', version, j['ref'], j['target'], j['f'] + '.table')
        if os.path.exists(tpath):
            for line in open(tpath).read().rstrip('\n').split('\n')[1:]:
                tables[j['target']].append('%s\t%s\t%s\t%s' % (j['path'], j['ref'], version, line))
    with open(os.path.join(O, 'g9-rerun.tsv'), 'w') as fh:
        fh.write('\n'.join(rows) + '\n')
    for t in ('disco-A', 'disco-Y'):
        with open(os.path.join(O, 'g9-table-%s.tsv' % t), 'w') as fh:
            fh.write('shipped file\tfm ref\ttool version\thow\tfm file:line\tfm value\tdisco value\twhy\n')
            fh.write(''.join(l + '\n' for l in tables[t]))
    c = collections.Counter(r.split('\t')[7] for r in rows[1:])
    print('reproduced byte for byte: fixed %d, first version %d, none %d (of %d)' % (
        c['fixed'], c['first'], c['none'], len(jobs)))


if __name__ == '__main__':
    main()
