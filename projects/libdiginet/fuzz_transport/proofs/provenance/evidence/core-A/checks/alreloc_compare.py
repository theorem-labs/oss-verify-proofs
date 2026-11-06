#!/usr/bin/env python3
"""Position-paired comparison of port_core's relocated numerals with alreloc's per-numeral report
(libdiginet/fuzz_transport image-A core). Kind: measurement; it proves no function. Copied unchanged in method from
libdiginet/fuzz_decode's record (alreloc_compare.py, sha256 e6d5a5dd551b; internal record).

  alreloc_compare.py --hub HUB --ref REF --src-lib proofs/libreac/fuzz_grant/lib --stage STAGE --stage-out STAGE_OUT
                     --report-a DIR --report-r DIR [--report-r-prefix A/] [--rename OLD=NEW ...] --out-dir OUT

Inputs
  --hub / --ref / --src-lib  the donor text: git show REF:SRC_LIB/<file> in the hub (read only)
  --stage       port_core's WORK/stage (donor text as port_core staged it: module paths renamed, same lines);
                checked to hold the donor's numerals on every line
  --stage-out   the relocated text; every .v file under it is compared
  --report-a    alreloc's --report tree for the lib/A files (<dir>/<file>.tsv)
  --report-r    alreloc's --report tree for the Reusable files, run at a fixture path: report file
                <dir>/<prefix><file>.tsv, rows named <prefix><file> (--report-r-prefix, default A/)
  --rename      the identifier renames port_core applied (whole identifiers), so its lines pair with the donor's
Pairing
  A numeral is a token (?<![\\w])(0x[0-9a-fA-F]+|\\d+)(?![\\w]). A donor line pairs with a stage-out line when their
  skeletons (renames applied, every numeral replaced by #) match in difflib's alignment of the two files; the
  numerals of a paired line pair by index. A donor line with no partner (a line port_core's patches replaced) is
  not-covered; a stage-out line with no donor partner (the header line port_core adds, lines its patches add) gives
  `added` positions. alreloc's value at a position is its report row for that line and token (rows of one token on
  one line are taken in order; a single identity row covers every occurrence), else the donor's token (no row: no
  rule of alreloc's changed it).
Classes (values compared as integers)
  agree             both moved the numeral, to the same value, and alreloc did not flag it
  both-kept         both kept the donor's value, and alreloc did not flag it
  disagree          the values differ: kind both-moved (to different values), alreloc-only (alreloc moved it,
                    port_core kept it) or portcore-only (port_core moved it, alreloc kept it by one of its rules)
  alreloc-unmapped  alreloc flagged it (UNMAPPED, *-UNSURE, `left:` unexamined, or a file-level TWIN-MISMATCH /
                    AMBIGUOUS-MODEL-CONSTANT naming it): alreloc gives no value of its own
  alreloc-refused   alreloc wrote no report for the file (every position of it)
  not-covered       the donor line has no paired stage-out line (port_core patched it)
  added             a stage-out numeral on a line with no donor partner (no donor value, no alreloc value)
Outputs (OUT)
  counts.tsv      class, kind, count (and the sum)
  positions.tsv   one row per numeral position: file, donor line, stage-out line, token index, donor, port_core,
                  alreloc, class, kind, alreloc rule, alreloc's source / unit locations, column (in the donor line,
                  or in the stage-out line for `added`)
"""
import argparse, collections, difflib, os, re, subprocess, sys

TOK = re.compile(r'(?<![\w])(0x[0-9a-fA-F]+|\d+)(?![\w])')
FLAG_RULES = ('UNMAPPED', 'DECIMAL-UNSURE', 'INSN-UNSURE', 'DERIVED-UNSURE', 'OFFSET-UNSURE', 'LISTING-UNSURE',
              'BOUND-UNSURE', 'ADDR-UNSURE', 'left:')
CLASSES = ('agree', 'both-kept', 'disagree', 'alreloc-unmapped', 'alreloc-refused', 'not-covered', 'added')
COLS = ['file', 'donor_line', 'out_line', 'tok', 'donor', 'port_core', 'alreloc', 'class', 'kind', 'alreloc_rule',
        'alreloc_src_loc', 'alreloc_unit_loc', 'column']


def val(t):
    return int(t, 16) if t[:2].lower() == '0x' else int(t)


def tree_files(d):
    out = []
    for root, _, fs in os.walk(d):
        out += [os.path.relpath(os.path.join(root, f), d) for f in fs if f.endswith('.v')]
    return sorted(out)


def load_report(path, prefix):
    hdr, rows = [], []
    for l in open(path).read().split('\n'):
        if not l:
            continue
        if l.startswith('#') or l.startswith('file:line\t'):
            hdr.append(l)
            continue
        p = l.split('\t')
        fl, ln = p[0].rsplit(':', 1)
        rows.append(dict(file=fl[len(prefix):] if prefix and fl.startswith(prefix) else fl, line=int(ln), old=p[1],
                         new=p[2], rule=p[3], oldloc=p[4], newloc=p[5]))
    return hdr, rows


def header_flags(hdr):
    """{(line, value): kind} of the file-level flags alreloc's report header names"""
    out = {}
    for h in hdr:
        m = re.match(r'# AMBIGUOUS-MODEL-CONSTANT (\S+):(\d+) (\S+) -> ', h)
        if m:
            out[(int(m.group(2)), val(m.group(3)))] = 'AMBIGUOUS-MODEL-CONSTANT'
        m = re.match(r'# TWIN-MISMATCH (\S+) (0x[0-9a-f]+): hex at line (.*?); decimal (\d+) at line (.*?) \(one value', h)
        if m:
            v = val(m.group(2))
            for part in (m.group(3), m.group(5)):
                for q in part.split(','):
                    out.setdefault((int(q.strip().split()[0]), v), 'TWIN-MISMATCH')
    return out


def main():
    ap = argparse.ArgumentParser()
    for k in ('hub', 'ref', 'src-lib', 'stage', 'stage-out', 'report-a', 'report-r', 'out-dir'):
        ap.add_argument('--' + k, required=True)
    ap.add_argument('--report-r-prefix', default='A/')
    ap.add_argument('--rename', action='append', default=[])
    a = ap.parse_args()
    renames = [x.split('=', 1) for x in a.rename]

    def skel(l):
        for o, n in renames:
            l = re.sub(r"(?<![\w'])%s(?![\w'])" % re.escape(o), n, l)
        return TOK.sub('#', l)

    files = tree_files(a.stage_out)
    counts = collections.Counter()
    out, problems = [], []
    for f in files:
        r_ = subprocess.run(['git', '-C', a.hub, 'show', '%s:%s/%s' % (a.ref, a.src_lib, f)], capture_output=True,
                            text=True)
        if r_.returncode:
            problems.append('%s: no donor file at %s:%s' % (f, a.ref[:12], a.src_lib))
            continue
        don = r_.stdout.split('\n')
        st = open(os.path.join(a.stage, f)).read().split('\n')
        so = open(os.path.join(a.stage_out, f)).read().split('\n')
        if len(st) != len(don) or any(TOK.findall(x) != TOK.findall(y) for x, y in zip(don, st)):
            problems.append('%s: the staged text does not hold the donor\'s numerals line by line' % f)
            continue
        sm = difflib.SequenceMatcher(None, [skel(x) for x in st], [skel(x) for x in so], autojunk=False)
        pm = {}
        for tag, i1, i2, j1, j2 in sm.get_opcodes():
            if tag == 'equal':
                for k in range(i2 - i1):
                    pm[i1 + k] = j1 + k
        rdir, pre = (a.report_a, '') if f.startswith('A/') else (a.report_r, a.report_r_prefix)
        rp = os.path.join(rdir, pre + f + '.tsv')
        refused = not os.path.isfile(rp)
        hdr, rows = ([], []) if refused else load_report(rp, pre)
        hflag = header_flags(hdr)
        byl = collections.defaultdict(list)
        for x in rows:
            byl[x['line']].append(x)
        for i, l in enumerate(don):
            ln = i + 1
            dt = [(m.start(), m.group(1)) for m in TOK.finditer(l)]
            if not dt:
                if byl.get(ln):
                    problems.append('%s:%d: alreloc rows on a line without numerals' % (f, ln))
                continue
            occ = collections.defaultdict(list)
            for k, (c, t) in enumerate(dt):
                occ[t].append(k)
            arow = [None] * len(dt)
            used = collections.defaultdict(list)
            for x in byl.get(ln, []):
                used[x['old']].append(x)
            for t, rs in used.items():
                ks = occ.get(t, [])
                if len(rs) == len(ks):
                    for k, x in zip(ks, rs):
                        arow[k] = x
                elif ks and len(rs) < len(ks) and all(x['new'] == x['old'] for x in rs):
                    for k in ks:
                        arow[k] = rs[0]
                else:
                    problems.append('%s:%d: token %s: %d occurrences, %d alreloc rows' % (f, ln, t, len(ks), len(rs)))
            oi = pm.get(i)
            ot = TOK.findall(so[oi]) if oi is not None else None
            for k, (c, t) in enumerate(dt):
                x = arow[k]
                pc = ot[k] if ot is not None else None
                al = x['new'] if x else t
                kind = ''
                if pc is None:
                    cls, kind = 'not-covered', 'patched line'
                elif refused:
                    cls, kind, al = 'alreloc-refused', 'no alreloc report for the file', '-'
                elif x is not None and x['rule'].startswith(FLAG_RULES):
                    cls, kind = 'alreloc-unmapped', x['rule'].split(' (')[0].split(':')[0]
                elif (ln, val(t)) in hflag:
                    cls, kind = 'alreloc-unmapped', hflag[(ln, val(t))]
                elif val(pc) == val(al):
                    cls = 'both-kept' if val(pc) == val(t) else 'agree'
                elif val(pc) == val(t):
                    cls, kind = 'disagree', 'alreloc-only'
                elif val(al) == val(t):
                    cls, kind = 'disagree', 'portcore-only'
                else:
                    cls, kind = 'disagree', 'both-moved'
                counts[(cls, kind)] += 1
                out.append([f, str(ln), str(oi + 1) if oi is not None else '-', str(k), t,
                            pc if pc is not None else '-', al, cls, kind, x['rule'] if x else '-',
                            x['oldloc'] if x else '-', x['newloc'] if x else '-', str(c)])
        # stage-out lines with no donor partner: the header line port_core adds and the lines its patches add
        partnered = set(pm.values())
        for j, l in enumerate(so):
            if j in partnered:
                continue
            for k, m in enumerate(TOK.finditer(l)):
                counts[('added', 'no donor line')] += 1
                out.append([f, '-', str(j + 1), str(k), '-', m.group(1), '-', 'added', 'no donor line', '-', '-', '-',
                            str(m.start())])
    if problems:
        sys.exit('alreloc_compare.py: ' + '\nalreloc_compare.py: '.join(problems))
    os.makedirs(a.out_dir, exist_ok=True)
    with open(os.path.join(a.out_dir, 'counts.tsv'), 'w') as fh:
        fh.write('class\tkind\tcount\n')
        for (c, k), n in sorted(counts.items(), key=lambda x: (CLASSES.index(x[0][0]), x[0][1])):
            fh.write('%s\t%s\t%d\n' % (c, k or '-', n))
        fh.write('total\t-\t%d\n' % sum(counts.values()))
    with open(os.path.join(a.out_dir, 'positions.tsv'), 'w') as fh:
        fh.write('\t'.join(COLS) + '\n')
        for r in out:
            fh.write('\t'.join(s.replace('\t', ' ') for s in r) + '\n')
    by = collections.Counter()
    for (c, k), n in counts.items():
        by[c] += n
    print('alreloc_compare.py: %d files, %d numeral positions: %s' % (
        len(files), sum(counts.values()), ', '.join('%s %d' % (c, by[c]) for c in CLASSES)))


if __name__ == '__main__':
    main()
