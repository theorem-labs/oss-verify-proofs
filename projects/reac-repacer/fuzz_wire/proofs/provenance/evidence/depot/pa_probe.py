#!/usr/bin/env python3
"""pa_probe.py make LIB LIB_NS OUTDIR FILE...  |  pa_probe.py read OUTDIR > TSV  |  pa_probe.py diff A.tsv B.tsv

Print Assumptions of every Theorem / Lemma / Corollary / Fact of the named lib/A files, read by Rocq.
make: for each FILE (e.g. AF0w.v), OUTDIR/P<F>.v = `From <LIB_NS>.A Require <F>.` then, for every theorem name the
file declares (Section-closed names included; `Local` ones skipped, they are not visible), a marker line and
`Print Assumptions <F>.<name>.`. Compile each probe against the built lib (run-flag-probe.sh, with PROJ / LIB set for
the tree), one compile per probe.
read: one row per theorem: file, name, the sorted axiom list (`Closed under the global context` = none), and the
flags SECTION-VARIABLE / ADMITTED (`Admitted` shows as an axiom named after a lemma of the lib) / PARAMETER.
diff: compares two read tables by (file, name): rows present in one only, and rows whose axiom lists differ."""
import os, re, sys

DECL = re.compile(r"^\s*(?:#\[[^\]]*\]\s*)?(Local\s+)?(?:Theorem|Lemma|Corollary|Fact|Proposition)\s+([A-Za-z_][\w']*)", re.M)


def make(lib, ns, out, files):
    os.makedirs(out, exist_ok=True)
    for f in files:
        t = open(os.path.join(lib, 'A', f), encoding='utf-8').read()
        mod = f[:-2]
        names = [m.group(2) for m in DECL.finditer(t) if not m.group(1)]
        seen, lines = set(), ['From %s.A Require %s.' % (ns, mod), 'Set Printing Width 4000.']
        for n in names:
            if n in seen:
                continue
            seen.add(n)
            lines += ['Goal True. idtac "PA-BEGIN %s". exact I. Qed.' % n, 'Print Assumptions %s.%s.' % (mod, n)]
        lines.append('Goal True. idtac "PA-END". exact I. Qed.')
        open(os.path.join(out, 'P' + f), 'w').write('\n'.join(lines) + '\n')
    print('pa_probe make: %d probe(s)' % len(files))


def read(out):
    print('file\ttheorem\taxioms\tflags')
    for f in sorted(os.listdir(out)):
        if not (f.startswith('P') and f.endswith('.out')):
            continue
        t = open(os.path.join(out, f), errors='replace').read()
        rc = (re.findall(r'^rc=(\d+)', t, flags=re.M) or ['?'])[-1]
        parts = re.split(r'^PA-BEGIN (\S+)\n', t, flags=re.M)
        for i in range(1, len(parts), 2):
            name, body = parts[i], parts[i + 1].split('PA-BEGIN')[0].split('PA-END')[0]
            body = re.sub(r'^rc=\d+\s*$', '', body, flags=re.M)
            ax, flags = [], set()
            if 'Closed under the global context' in body:
                state = 'closed'
            elif re.search(r'^Axioms:\s*$', body, flags=re.M) or re.search(r'^Section Variables:\s*$', body, flags=re.M):
                state = 'axioms'
                cur = None
                for line in body.split('\n'):
                    h = re.match(r'^(Axioms|Section Variables):\s*$', line)
                    if h:
                        cur = h.group(1)
                        continue
                    m = re.match(r'^([A-Za-z_][\w.\']*)\s*:', line)
                    if m and cur:
                        ax.append(('SECVAR ' if cur == 'Section Variables' else '') + m.group(1))
                        if cur == 'Section Variables':
                            flags.add('SECTION-VARIABLE')
                        elif '.Proofs.' in m.group(1):
                            flags.add('ADMITTED-OR-PARAMETER')
            else:
                # no Print Assumptions output for this theorem (the compile stopped: timeout / error): NOT closed
                state = 'NO-OUTPUT'
                flags.add('NO-OUTPUT (compile rc=%s)' % rc)
            if 'Error' in body:
                flags.add('ERROR')
            ax = sorted(set(ax))
            shown = {'closed': 'closed', 'axioms': ' '.join(ax), 'NO-OUTPUT': 'NO-OUTPUT'}[state]
            print('%s\t%s\t%s\t%s' % (f[1:-4] + '.v', name, shown, ' '.join(sorted(flags)) or '-'))
        seen = set(parts[1::2])
        probe = os.path.join(out, f[:-4] + '.v')
        if os.path.exists(probe):
            for name in re.findall(r'idtac "PA-BEGIN (\S+)"', open(probe).read()):
                if name not in seen:
                    print('%s\t%s\tNO-OUTPUT\tNO-OUTPUT (never reached; compile rc=%s)' % (f[1:-4] + '.v', name, rc))


def diff(a, b):
    def load(p):
        return {(l.split('\t')[0], l.split('\t')[1]): l.split('\t')[2:] for l in open(p).read().splitlines()[1:] if l.strip()}
    A, B = load(a), load(b)
    only_a = sorted(set(A) - set(B))
    only_b = sorted(set(B) - set(A))
    dif = sorted(k for k in set(A) & set(B) if A[k][0] != B[k][0])
    print('pa diff: %d in both, %d only in %s, %d only in %s, %d differ' % (len(set(A) & set(B)), len(only_a), a, len(only_b), b, len(dif)))
    for k in only_a:
        print('ONLY-A\t%s\t%s\t%s' % (k[0], k[1], A[k][0]))
    for k in only_b:
        print('ONLY-B\t%s\t%s\t%s' % (k[0], k[1], B[k][0]))
    for k in dif:
        print('DIFFER\t%s\t%s\tA: %s\tB: %s' % (k[0], k[1], A[k][0], B[k][0]))


if __name__ == '__main__':
    a = sys.argv[1:]
    if a[:1] == ['make'] and len(a) >= 5:
        make(a[1], a[2], a[3], a[4:])
    elif a[:1] == ['read'] and len(a) == 2:
        read(a[1])
    elif a[:1] == ['diff'] and len(a) == 3:
        diff(a[1], a[2])
    else:
        sys.exit(__doc__)
