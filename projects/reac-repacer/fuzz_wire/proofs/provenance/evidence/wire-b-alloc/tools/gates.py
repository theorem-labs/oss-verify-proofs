#!/usr/bin/env python3
"""gates.py DIR UNIT -- the gate writer of a <unit>-b-alloc record: it reads the outputs this run wrote in DIR and
writes one verdict file per gate into DIR: gate-kit.txt, gate-lui.txt, gate-base.txt, gate-plants.txt, and
gate-controls.txt, the two negative controls. Read-only on every input. run.sh calls it after the last measurement
and before scrub_out.py, so the verdict files ship in the slice.

Each gate file holds its evidence lines -- the counts it read, and every failing line -- and its LAST line is exactly

    GATE <unit>-b-alloc-<kit|lui|base|plants> VERDICT: PASS|FAIL head <40-hex> inputs <text>

where <40-hex> is the head the gate ran against (the environment value GATE_HEAD when it is set: env.sh sets it to
the commit the slice is staged on; else the git HEAD of the worktree DIR lies in; gates.py refuses when it has
neither) and <text> names the tool of record of that gate and its sha256, read from tools.sha256.

The PASS rules:
  kit     each of the 4 roots.tsv rows against grant B (pair U:G) reads EQUAL or EQUAL-mod-pcrel with target-differ 0,
          AND every kit-reported closure row (ROW) and differing target (ACCEPT) of ACCEPTANCES.tsv is SETTLED-EQUAL,
          or is left UNSETTLED / NOT SETTLED by the kit settlement and carried by a hand-trace LUI line of the same
          function and word, which is the NOT CERTIFIED: REAL 0 reading, or by a handtable.out VERDICT of the same
          function and word that reads SETTLED-BY-HAND (a table jtcheck 226254f48c97 refuses, settled by hand under
          the record's rule: parts (1)-(3) by handtable.py; part (4), a non-writer's read, is RECORD.md's), AND no data
          line and no handtable.out VERDICT reads DIFFERS.
  lui     no luitrace.tsv row reads DIFFERS.
  base    basescan.tsv's TOTAL line has DIFFERS 0 (an absent field is 0, and the verdict classes must then sum to the
          base count, so a difference cannot hide in a missing field), and no row reads DIFFERS.
  plants  every planted control of plants.out reads CAUGHT or REFUSED; of the De Bruijn settlement control, the planted
          copy (ctl-settle-debruijn-planted.tsv) reads NOT SETTLED and the untouched baseline
          (ctl-settle-debruijn-untouched.tsv) SETTLED-EQUAL; and the dispatch-size control
          (ctl-settle-slli3-planted.tsv: a dispatch's `slli 2` set to `slli 3` in a copy of X) has no TABLE row read
          with 4-byte entries: its table is read with 8-byte entries or it does not settle; and of the five
          hand-settlement controls (each a copy of one image with one word of parseCIE or of its table changed),
          ctl-handtable-bound.out (a second definition of the table limit in an arm after the guard) reads NOT SETTLED
          because the bound differs, ctl-handtable-zarm.out (a larger second limit in a jump-table arm),
          ctl-handtable-jump.out (a jump into the dispatch block) and ctl-handtable-entries.out (the limit raised by
          one) read NOT SETTLED, and ctl-handtable-slot.out (one slot of Y's table re-pointed) reads DIFFERS.

The controls, run on copies in a scratch directory and written to gate-controls.txt: one roots.tsv row set to
DIFFERENT must make kit FAIL, and one plant verdict set to EQUAL must make plants FAIL. A control that does not fail
makes gates.py refuse (exit 1), so a gate that cannot fail never ships a PASS.
usage: gates.py DIR UNIT [--out DIR]"""
import os, re, shutil, subprocess, sys, tempfile

GATES = ('kit', 'lui', 'base', 'plants')
ROOTS = ('__interceptor_trampoline_malloc', '___interceptor_malloc', '__interceptor_trampoline_free',
         '___interceptor_free')
OK_ROOT = ('EQUAL', 'EQUAL-mod-pcrel')


def rows(path, sep='\t'):
    with open(path) as f:
        return [l.rstrip('\n').split(sep) for l in f if l.rstrip('\n')]


def head_of(d):
    """the 40-hex head this gate ran against: GATE_HEAD when the environment sets it (a run outside a worktree, and
    the value a reproduction of this slice carries), else the git HEAD of the worktree DIR lies in, else None"""
    h = os.environ.get('GATE_HEAD', '').strip()
    if re.fullmatch(r'[0-9a-f]{40}', h):
        return h
    try:
        r = subprocess.run(['git', '-C', d, 'rev-parse', 'HEAD'], capture_output=True, text=True)
        if r.returncode == 0 and re.fullmatch(r'[0-9a-f]{40}', r.stdout.strip()):
            return r.stdout.strip()
    except OSError:
        pass
    return None


def shas(d):
    out = {}
    p = os.path.join(d, 'tools.sha256')
    if os.path.exists(p):
        for l in rows(p, None):
            if len(l) == 2: out[l[1]] = l[0][:12]
    return out


def gate_kit(d, ev):
    bad = []
    rt = [r for r in rows(os.path.join(d, 'roots.tsv')) if len(r) > 11 and r[1] == 'U:G']
    ev.append('roots.tsv: %d rows for the pair U:G' % len(rt))
    seen = set()
    for r in rt:
        ev.append('  %s %s target-differ %s' % (r[0], r[6], r[11]))
        seen.add(r[0])
        if r[6] not in OK_ROOT or r[11] != '0':
            bad.append('roots.tsv: %s reads %s with target-differ %s' % (r[0], r[6], r[11]))
    for n in ROOTS:
        if n not in seen: bad.append('roots.tsv: no U:G row for the root %s' % n)
    acc = [r for r in rows(os.path.join(d, 'ACCEPTANCES.tsv')) if not r[0].startswith('#')]
    rowl = [r for r in acc if r[0] == 'ROW']
    accl = [r for r in acc if r[0] == 'ACCEPT' and r[1] != 'function']
    luil = [r for r in acc if r[0] == 'LUI']
    lui_at = {(r[1], r[2].lstrip('+')) for r in luil}
    ev.append('ACCEPTANCES.tsv: %d closure rows, %d target pairs, %d hand-trace rows' % (len(rowl), len(accl), len(luil)))
    ev.append('  closure rows: %d SETTLED-EQUAL, %d left to the hand traces'
              % (sum(1 for r in rowl if r[-1] == 'ROW SETTLED-EQUAL'), sum(1 for r in rowl if r[-1] == 'ROW NOT SETTLED')))
    ev.append('  target pairs: %d SETTLED-EQUAL, %d left to the hand traces'
              % (sum(1 for r in accl if r[-1] == 'SETTLED-EQUAL'), sum(1 for r in accl if r[-1] == 'UNSETTLED')))
    for r in rowl:
        if r[-1] not in ('ROW SETTLED-EQUAL', 'ROW NOT SETTLED'):
            bad.append('ACCEPTANCES.tsv ROW %s reads %s' % (r[1], r[-1]))
    carried = handed = 0
    hand = {(r[1], r[2].lstrip('+')): r[3] for r in rows(os.path.join(d, 'handtable.out')) if r[0] == 'VERDICT'}
    for r in accl:
        if r[-1] == 'SETTLED-EQUAL': continue
        if r[-1] != 'UNSETTLED':
            bad.append('ACCEPTANCES.tsv ACCEPT %s %s reads %s' % (r[1], r[2], r[-1])); continue
        if (r[1], r[2].lstrip('+')) in lui_at: carried += 1
        elif hand.get((r[1], r[2].lstrip('+')), '').startswith('SETTLED-BY-HAND'): handed += 1
        else: bad.append('ACCEPTANCES.tsv: the target %s %s is UNSETTLED and has no hand-trace LUI row and no hand '
                         'table settlement' % (r[1], r[2]))
    ev.append('  every target left unsettled has a LUI row (%d) or a hand table settlement in handtable.out under this '
              'record\'s rule, parts (1)-(3): entries, dispatch, bound (%d), of %d'
              % (carried, handed, sum(1 for r in accl if r[-1] == 'UNSETTLED')))
    for (fn, off), v in sorted(hand.items()):
        ev.append('  handtable.out %s +%s: %s' % (fn, off, v[:60]))
        if v.startswith('DIFFERS'): bad.append('handtable.out: %s +%s reads %s' % (fn, off, v))
    for r in luil:
        if 'DIFFERS' in '\t'.join(r): bad.append('ACCEPTANCES.tsv LUI %s %s reads DIFFERS' % (r[1], r[2]))
    nd = sum(1 for r in acc if 'DIFFERS' in '\t'.join(r))
    ev.append('  data lines reading DIFFERS: %d (the comment header, which quotes the plant verdicts, is not a data line)' % nd)
    if nd: bad.append('ACCEPTANCES.tsv: %d data line(s) read DIFFERS' % nd)
    return bad


def gate_lui(d, ev):
    bad = []
    rs = [r for r in rows(os.path.join(d, 'luitrace.tsv')) if not r[0].startswith('#')]
    diff = [r for r in rs if 'DIFFERS' in '\t'.join(r)]
    ev.append('luitrace.tsv: %d rows, %d reading DIFFERS' % (len(rs), len(diff)))
    for r in diff[:20]: bad.append('luitrace.tsv: %s' % '\t'.join(r)[:200])
    if len(diff) > 20: bad.append('luitrace.tsv: %d further rows read DIFFERS' % (len(diff) - 20))
    return bad


def gate_base(d, ev):
    bad = []
    rs = rows(os.path.join(d, 'basescan.tsv'))
    tot = [r for r in rs if r[0] == 'TOTAL']
    if len(tot) != 1:
        return ['basescan.tsv: %d TOTAL lines' % len(tot)]
    t = {}
    for f in tot[0][1:]:
        m = re.fullmatch(r'(.+) (\d+)', f)
        if m: t[m.group(1)] = int(m.group(2))
    cls = ['bases EQUAL', 'bases EQUAL+BYTES', 'bases EQUAL+INDEX', 'bases EQUAL+TABLE', 'bases NOT CERTIFIED',
           'bases DIFFERS']
    s = sum(t.get(k, 0) for k in cls)
    ev.append('basescan.tsv TOTAL: bases %d; %s' % (t.get('bases', -1), ', '.join('%s %d' % (k, t.get(k, 0)) for k in cls)))
    ev.append('  the verdict classes sum to %d, the base count is %d' % (s, t.get('bases', -1)))
    if t.get('bases DIFFERS', 0): bad.append('basescan.tsv TOTAL: bases DIFFERS %d' % t['bases DIFFERS'])
    if s != t.get('bases', -1):
        bad.append('basescan.tsv TOTAL: the verdict classes sum to %d, not to the base count %d' % (s, t.get('bases', -1)))
    diff = [r for r in rs if r[0] in ('BASE', 'ROOTBASE') and 'DIFFERS' in '\t'.join(r)]
    ev.append('  rows reading DIFFERS: %d' % len(diff))
    for r in diff[:20]: bad.append('basescan.tsv: %s' % '\t'.join(r)[:200])
    return bad


def gate_plants(d, ev):
    bad = []
    pl = rows(os.path.join(d, 'plants.out'))
    v = [r for r in pl if r[0].endswith('-VERDICT')]
    ev.append('plants.out: %d planted controls' % len(v))
    for r in v:
        ev.append('  %s %s' % (r[0], r[1]))
        if not r[1].startswith(('CAUGHT', 'REFUSED')):
            bad.append('plants.out: %s reads %s' % (r[0], r[1]))
    if not v: bad.append('plants.out: no planted control')
    for name, want in (('ctl-settle-debruijn-untouched.tsv', 'ROW SETTLED-EQUAL'),
                       ('ctl-settle-debruijn-planted.tsv', 'ROW NOT SETTLED')):
        rs = [r for r in rows(os.path.join(d, name)) if r[0] == 'ROW']
        got = rs[0][-1] if rs else '(no ROW line)'
        ev.append('  %s: %s' % (name, got))
        if got != want:
            bad.append('%s: reads %s, not %s' % (name, got, want))
    name = 'ctl-settle-slli3-planted.tsv'
    acc = [r for r in rows(os.path.join(d, name)) if r[0] == 'ACCEPT' and r[1] != 'function']
    if not acc: bad.append('%s: no ACCEPT row' % name)
    for r in acc:
        m = re.search(r'table\(\): [a-z]+(\d+)-', r[7]) if r[6] == 'TABLE' else None
        size = int(m.group(1)) if m else None
        ev.append('  %s: %s %s: %s' % (name, r[2], r[6], 'read with %d-byte entries' % size if size else
                                       'not settled as a table (refused)'))
        if r[6] == 'TABLE' and size != 8:
            bad.append('%s: %s settles as a table with %s-byte entries, not 8' % (name, r[2], size))
    # each control must fail for its own reason (handtable.py's words), not only fail
    slot47 = r'NOT SETTLED \(X: slot 47 targets 0x[0-9a-f]+, not a word of the function\)'
    for name, want in (('ctl-handtable-bound.out', r'NOT SETTLED \(the bound differs between X and Y\)'),
                       ('ctl-handtable-zarm.out', slot47),
                       ('ctl-handtable-jump.out', r"NOT SETTLED \(X: the block word \+0x264 has predecessors \['\+0x248', "),
                       ('ctl-handtable-entries.out', slot47),
                       ('ctl-handtable-slot.out', r'DIFFERS \(1 entries\)')):
        hv = [r for r in rows(os.path.join(d, name)) if r[0] == 'VERDICT']
        ev.append('  %s: %s' % (name, hv[0][3][:100] if hv else '(no VERDICT line)'))
        if not hv or not re.match(want, hv[0][3]):
            bad.append('%s: reads %s, not the reason %s' % (name, hv[0][3][:80] if hv else '(no VERDICT line)', want))
    return bad


RUN = {'kit': gate_kit, 'lui': gate_lui, 'base': gate_base, 'plants': gate_plants}


def inputs_text(d):
    s = shas(d)
    def t(n): return '%s %s' % (n, s.get(n, '(no tools.sha256 row)'))
    return {'kit': 'cmpkit 86da41d3ef68: %s (roots.tsv); %s, %s and %s (ACCEPTANCES.tsv, jtcheck 226254f48c97: %s); %s '
                   '(handtable.out)' % (t('strictcmp3.py'), t('settle.py'), t('luitrace.py'), t('mkaccept.py'),
                                        t('jtcheck.py'), t('handtable.py')),
            'lui': '%s (luitrace.tsv)' % t('luitrace.py'),
            'base': '%s (basescan.tsv)' % t('basescan.py'),
            'plants': '%s (plants.out); %s (ctl-settle-*.tsv); %s (ctl-handtable-*.out)'
                      % (t('plants.py'), t('settle.py'), t('handtable.py'))}


def write_gates(d, unit, head, out):
    """every gate over the outputs in d; writes out/gate-<name>.txt; returns {name: PASS|FAIL}"""
    txt = inputs_text(d)
    verdict = {}
    for g in GATES:
        ev = []
        bad = RUN[g](d, ev)
        verdict[g] = 'FAIL' if bad else 'PASS'
        body = ev + (['', 'FAILING:'] + bad if bad else [])
        line = 'GATE %s-b-alloc-%s VERDICT: %s head %s inputs %s' % (unit, g, verdict[g], head, txt[g])
        with open(os.path.join(out, 'gate-%s.txt' % g), 'w') as f:
            f.write('\n'.join(body + [line]) + '\n')
    return verdict


def controls(d, unit, head, out):
    """the two negative controls, on copies: a changed root row must fail kit, a changed plant verdict must fail
    plants"""
    lines, bad = [], []
    for name, files, edit in (
            ('one roots.tsv row set to DIFFERENT', ('roots.tsv',),
             lambda s: s.replace('\tEQUAL-mod-pcrel\t', '\tDIFFERENT\t', 1)),
            ('one plant verdict set to EQUAL', ('plants.out',),
             lambda s: re.sub(r'(-VERDICT\t)(CAUGHT|REFUSED)[^\n]*', r'\1EQUAL', s, count=1))):
        with tempfile.TemporaryDirectory() as t:
            for n in os.listdir(d):
                p = os.path.join(d, n)
                if os.path.isfile(p): shutil.copy2(p, os.path.join(t, n))
            for n in files:
                s = open(os.path.join(t, n)).read()
                new = edit(s)
                if new == s: bad.append('control %r changed nothing in %s' % (name, n))
                open(os.path.join(t, n), 'w').write(new)
            v = write_gates(t, unit, head, t)
            want = 'kit' if 'roots' in files[0] else 'plants'
            lines.append('control: %s -> %s' % (name, ', '.join('%s %s' % (g, v[g]) for g in GATES)))
            for g in GATES:
                tail = open(os.path.join(t, 'gate-%s.txt' % g)).read().rstrip('\n').split('\n')
                if g == want:
                    k = tail.index('FAILING:') if 'FAILING:' in tail else len(tail) - 1
                    lines += ['  ' + x for x in tail[k:-1]][:5]
                    lines.append('  ' + tail[-1])
            if v[want] != 'FAIL': bad.append('control %r left %s at %s: a gate that cannot fail' % (name, want, v[want]))
    with open(os.path.join(out, 'gate-controls.txt'), 'w') as f:
        f.write('The two negative controls of this run, each on a copy of the outputs in a scratch directory: the gate\n'
                'named must read FAIL, or gates.py refuses and no verdict file is written.\n\n' + '\n'.join(lines) + '\n')
    return bad


def main():
    d = os.path.abspath(sys.argv[1]); unit = sys.argv[2]
    out = os.path.abspath(sys.argv[sys.argv.index('--out') + 1]) if '--out' in sys.argv else d
    os.makedirs(out, exist_ok=True)
    if unit.startswith('fuzz_'): unit = unit[len('fuzz_'):]
    head = head_of(d)
    if not head:
        raise SystemExit('gates.py: no git HEAD for %s and no 40-hex GATE_HEAD in the environment: refusing' % d)
    bad = controls(d, unit, head, out)
    if bad:
        for b in bad: print('gates.py: REFUSED: ' + b, file=sys.stderr)
        sys.exit(1)
    v = write_gates(d, unit, head, out)
    for g in GATES:
        print(open(os.path.join(out, 'gate-%s.txt' % g)).read().rstrip('\n').split('\n')[-1])
    if any(x == 'FAIL' for x in v.values()):
        sys.exit(2)


if __name__ == '__main__':
    main()
