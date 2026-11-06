"""map_rows.py GA KA CLASSES_A TAKES_A MERGES_A GB KB CLASSES_B FILE_B... -- image A's consumer decisions (the image-A core's step 2 on
lib/A) carried to the image-B twins by line CONTENT.

GA / KA: the image-A pair the image-A core classified (GA/A/<F> the unit's relocated grant text, KA/A/<F> knock's text relocated
onto fuzz_wire.asan); CLASSES_A: the image-A core's consumer-classes.tsv; TAKES_A: the image-A core's takes.tsv (the --take rows; a row of kind
MERGE carries its `--merge 'F:H:OLD=NEW'` in its last column, read as a merge row); MERGES_A: the image-A core's hand --merge rows
not in its takes.tsv (file, hunk, OLD, NEW, count). GB / KB: the image-B pair (GB/B/<Y> lib/B of the unit, KB/B/<Y>
knock's lib/AU twin relocated onto fuzz_wire.asan-ubsan); CLASSES_B: depot_classify.py --consumer --sub B over that pair.
FILE_B: the lib/B files, Y<x>.v (the twin of A<x>.v). $AMODS: a file naming the unit's lib/A modules (one per line);
with the file names of GA/A and KA/A they are the A<x> names the comparison maps to Y<x>.

Lines are compared with comments removed and the image taken out: every numeral -> #, the lib/A module names -> their
lib/B twins (A<x> -> Y<x>), lib.A -> lib.B, B's own `lib.B Require YImgTop` -> `lib.Reusable Require YImgTop`, the image
module AsanUbsan -> Asan. B's grant lines are aligned with A's grant lines and B's knock lines with A's knock lines
(difflib, equal runs only). Each B hunk (depot_classify.py's numbering) is then decided by the A hunks its aligned lines
fall in:
  take   every such A hunk was TAKEN by the image-A core (class depot / layout-grow, a --take row, a --merge row): taken on B by
         class when B's class is depot / layout-grow, else by a --take row;
  keep   every such A hunk was kept (a B class depot / layout-grow hunk is then a row `B class, A kept`: depot_apply.py
         takes it by class; measured here: each such hunk is one Require run joining A's kept AWalkFw0 line and A's
         taken KnBlockExt line, so with the AWalkFw0 rule below its text is A's);
  mixed  both: listed, taken (the same Require runs);
  B-only no line of the hunk falls in an A hunk (B's own difference): B's class decides.
An A taken hunk none of whose knock lines (for a deletion: grant lines) is in a hunk B takes is listed (`A taken, not on
B`). A --merge row's OLD is knock text, placed on the taken B hunk whose knock lines hold it; a NEW that is
text of A's grant lines of the hunk is grant's text, so on B each of its numerals becomes the numeral at the same place of
the aligned B grant line (a numeral that pairs with two B values refuses). Any other NEW is kept as written only when
every numeral in it is held by the A file and kept unchanged by every aligned B line (a plain constant); a numeral the
A file does not hold, or one the alignment maps to a different B value, refuses, because the A decisions and the A
pair (GA / KA) must come from the same image-A record. The A rule
for AWalkFw0 (a hunk taken by class or row whose knock lines name AWalkFw0 and whose grant lines do not: --merge
F:H:AWalkFw0=AB1v) is applied on B as AWalkFw0=YB1v. Prints rows-B.tsv on stdout and writes the depot_apply.py arguments
to $ROWS_ARGS."""
import difflib, os, re, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from depot_classify import norm_lines

NUM = re.compile(r"(?<![A-Za-z0-9_'])(?:0x[0-9a-fA-F]+|\d+)(?![0-9A-Za-z_])")
# text a shipped record must not carry: worker and lane names (a one-letter role, a hyphen and a name, or a box or dec
# number), working-branch refs, session ids, host paths. The same pattern is in record.sh.
REFUSE = re.compile(r"(?<![A-Za-z0-9_])(?:[hcr]-[a-z][a-z0-9]*(?:-[a-z0-9]+)*|box-\d+|dec-\d+)(?![A-Za-z0-9_])"
                    r"|\bcold/|\b01a1[0-9a-f]{4}-[0-9a-f]{4}-|/(?:home|mnt|tmp|dev/shm)/")


def table(p):
    t = {}
    for line in open(p).read().splitlines()[1:]:
        q = line.split('\t')
        if len(q) >= 7 and q[1].isdigit():
            t[(q[0], int(q[1]))] = q[2]
    return t


def pair(gp, kp):
    gl, kl = [l for _, l in norm_lines(open(gp).read())], [l for _, l in norm_lines(open(kp).read())]
    gh, kh, ops = [0] * len(gl), [0] * len(kl), []
    for tag, i1, i2, j1, j2 in difflib.SequenceMatcher(None, gl, kl, autojunk=False).get_opcodes():
        if tag != 'equal':
            ops.append((i1, i2, j1, j2))
            for i in range(i1, i2):
                gh[i] = len(ops)
            for j in range(j1, j2):
                kh[j] = len(ops)
    return gl, kl, gh, kh, ops


def align(a, b):
    m = {}
    for tag, i1, i2, j1, j2 in difflib.SequenceMatcher(None, a, b, autojunk=False).get_opcodes():
        if tag == 'equal':
            for k in range(i2 - i1):
                m[j1 + k] = i1 + k
    return m


def main():
    ga, ka, ca, ta, ma, gb, kb, cb = sys.argv[1:9]
    files = sys.argv[9:]
    amods = {f[:-2] for d in (os.path.join(ga, 'A'), os.path.join(ka, 'A')) for f in os.listdir(d) if f.endswith('.v')}
    amods |= set(open(os.environ['AMODS']).read().split())
    amod = re.compile(r'\b(%s)\b' % '|'.join(sorted(amods, key=len, reverse=True)))

    def norm_a(s):
        s = s.replace('.lib.A ', '.lib.B ').replace('.lib.A.', '.lib.B.')
        s = amod.sub(lambda m: m.group(1) if m.group(1) == 'AWalkFw0' else 'Y' + m.group(1)[1:], s)
        return NUM.sub('#', s)

    def norm_b(s):
        s = re.sub(r'\.lib\.B Require YImgTop\.', '.lib.Reusable Require YImgTop.', s)
        return NUM.sub('#', re.sub(r'\bAsanUbsan\b', 'Asan', s))

    cla, clb = table(ca), table(cb)
    tka = [l.split('\t') for l in open(ta).read().splitlines()[1:]]
    takes = {(q[0], int(q[1])) for q in tka if len(q) > 1 and q[1].isdigit()}
    merges = {}
    for line in open(ma).read().splitlines()[1:]:
        f, h, old, new, n = line.split('\t')
        merges.setdefault((f, int(h)), []).append((old, new, int(n)))
    for q in tka:
        if len(q) > 6 and q[2].startswith('MERGE'):
            spec = re.search(r"--merge '([^']*)'", q[6])
            if not spec:
                sys.exit('map_rows: MERGE row %s:%s has no --merge command' % (q[0], q[1]))
            f, h, s = spec.group(1).split(':', 2)
            n = re.match(r'^(.*)#(\d+)$', s)
            s, n = (n.group(1), int(n.group(2))) if n else (s, 1)
            old, new = s.split('=', 1)
            if (old, new, n) not in merges.get((f, int(h)), []):
                merges.setdefault((f, int(h)), []).append((old, new, n))
    rows, args, cnt = [], [], {}
    for fb in files:
        fa = 'A' + fb[1:]
        ag, ak, agh, akh, aops = pair(os.path.join(ga, 'A', fa), os.path.join(ka, 'A', fa))
        bg, bk, bgh, bkh, bops = pair(os.path.join(gb, 'B', fb), os.path.join(kb, 'B', fb))
        gmap = align([norm_a(l) for l in ag], [norm_b(l) for l in bg])
        kmap = align([norm_a(l) for l in ak], [norm_b(l) for l in bk])

        def took(h):
            return cla.get((fa, h)) in ('depot', 'layout-grow') or (fa, h) in takes or (fa, h) in merges
        covered, placed, tk, tg = set(), set(), set(), set()
        for j, (i1, i2, j1, j2) in enumerate(bops, 1):
            hs = {agh[gmap[i]] for i in range(i1, i2) if i in gmap} | {akh[kmap[k]] for k in range(j1, j2) if k in kmap}
            hs.discard(0)
            st, sk = sorted(h for h in hs if took(h)), sorted(h for h in hs if not took(h))
            c = clb.get((fb, j))
            auto = c in ('depot', 'layout-grow')
            kind = 'take' if st and not sk else 'keep' if sk and not st else 'mixed' if st else 'B-only'
            take = kind in ('take', 'mixed') or (kind == 'B-only' and auto)
            what = []
            if take and not auto:
                args += ['--take', '%s:%d' % (fb, j)]
                what.append('--take')
            elif take:
                what.append('class ' + c)
            elif auto:
                what.append('class %s, A kept' % c)
            else:
                what.append('kept')
            eff = take or auto
            if eff:
                covered.update(st)
                tk.update(norm_b(l) for l in bk[j1:j2])
                tg.update(norm_b(l) for l in bg[i1:i2])
            for h in st:
                for old, new, n in merges.get((fa, h), []):
                    if old not in '\n'.join(bk[j1:j2]):
                        continue
                    placed.add((fa, h, old))
                    ai1, ai2 = aops[h - 1][:2]
                    if new in '\n'.join(ag[ai1:ai2]):
                        nmap = {}
                        for i in range(i1, i2):
                            if i in gmap and ai1 <= gmap[i] < ai2:
                                for x, y in zip(NUM.findall(ag[gmap[i]]), NUM.findall(bg[i])):
                                    nmap.setdefault(x, set()).add(y)
                        amb = [x for x in NUM.findall(new) if len(nmap.get(x, ())) != 1]
                        if amb:
                            sys.exit('map_rows: %s:%d (A %s:%d) merge NEW %r: numerals %s pair with no single B value'
                                     % (fb, j, fa, h, new, amb))
                        new = NUM.sub(lambda m: next(iter(nmap[m.group(0)])), new)
                    elif NUM.search(new):
                        # the A decision's NEW text is not in this run's A grant hunk, so its numerals are not paired
                        # with B there. A numeral the A file holds and every aligned B line keeps unchanged (a plain
                        # constant) is safe to carry. A numeral the A file does not hold at all came from another
                        # A pair (another image), and one the alignment maps to a different B value is image-relative:
                        # carrying either verbatim would write another image's value. Refuse those.
                        fmap = {}
                        for i in range(len(bg)):
                            if i in gmap:
                                for x, y in zip(NUM.findall(ag[gmap[i]]), NUM.findall(bg[i])):
                                    fmap.setdefault(x, set()).add(y)
                        anum = set(x for l in ag for x in NUM.findall(l))
                        bad = [x for x in NUM.findall(new) if x not in anum or fmap.get(x, {x}) != {x}]
                        if bad:
                            sys.exit('map_rows: %s:%d (A %s:%d) merge NEW %r is not in the A grant hunk of GA, and its '
                                     'numerals %s are foreign to GA or change between the images: the A decisions '
                                     '(TAKES_A / MERGES_A) and the A pair (GA / KA) must come from the same image-A record'
                                     % (fb, j, fa, h, new, bad))
                    spec = '%s=%s' % (old, new) + ('#%d' % n if n != 1 else '')
                    args += ['--merge', '%s:%d:%s' % (fb, j, spec)]
                    what.append('--merge ' + spec)
            if eff and 'AWalkFw0' in ' '.join(bk[j1:j2]) and 'AWalkFw0' not in ' '.join(bg[i1:i2]):
                args += ['--merge', '%s:%d:AWalkFw0=YB1v' % (fb, j)]
                what.append('--merge AWalkFw0=YB1v (A rule)')
            cnt[kind] = cnt.get(kind, 0) + 1
            if kind != 'keep' or auto:
                rows.append((fb, str(j), c or '-', kind, ' '.join('%d%s' % (h, '' if took(h) else 'k') for h in sorted(hs)) or '-',
                             '; '.join(what), ' | '.join(bk[j1:j2])[:200] or '(delete) ' + ' | '.join(bg[i1:i2])[:180]))
        for h in range(1, len(aops) + 1):
            ai1, ai2, aj1, aj2 = aops[h - 1]
            if h not in covered and (all(norm_a(l) in tk for l in ak[aj1:aj2]) if aj2 > aj1
                                     else all(norm_a(l) in tg for l in ag[ai1:ai2])):
                covered.add(h)
            if took(h) and h not in covered:
                cnt['A taken, not on B'] = cnt.get('A taken, not on B', 0) + 1
                rows.append((fb, '-', cla.get((fa, h), '-'), 'A taken, not on B', str(h), '-',
                             ' | '.join(ak[aj1:aj2])[:200] or '(delete) ' + ' | '.join(ag[ai1:ai2])[:180]))
            for old, new, n in merges.get((fa, h), []):
                if (fa, h, old) not in placed:
                    cnt['A merge not placed'] = cnt.get('A merge not placed', 0) + 1
                    rows.append((fb, '-', '-', 'A merge not placed', str(h), '%s=%s' % (old, new), '-'))
    # fail closed: the table and the arguments carry text copied from the inputs (hunk lines, --merge specs), so a
    # worker or lane name, a working-branch name, a session id or a host path that arrives through an input is refused
    # here, before anything is written, whatever file it came from
    bad = [(n, m.group(0)) for n, s in enumerate(['\t'.join(r) for r in rows] + args, 1) for m in [REFUSE.search(s)] if m]
    if bad:
        for n, w in bad[:10]:
            print('map_rows: REFUSED output item %d carries %r (worker / lane / branch / session / host text)' % (n, w),
                  file=sys.stderr)
        sys.exit(3)
    print('file\tB hunk\tB class\tdecision\tA hunks (k = kept by the image-A core)\tdepot_apply\tB knock lines')
    for r in rows:
        print('\t'.join(r))
    open(os.environ['ROWS_ARGS'], 'w').write('\n'.join(args) + '\n')
    print('map_rows: %s; %d --take, %d --merge' % (', '.join('%s %d' % kv for kv in sorted(cnt.items())),
                                                    args.count('--take'), args.count('--merge')), file=sys.stderr)


if __name__ == '__main__':
    main()
