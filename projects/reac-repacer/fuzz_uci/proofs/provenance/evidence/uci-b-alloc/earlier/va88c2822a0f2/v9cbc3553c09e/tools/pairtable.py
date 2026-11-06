#!/usr/bin/env python3
"""pairtable.py -- run paircl.py (unchanged, via runpy) and write one TSV row per function it paired. Read-only.

paircl.py pairs X (unstripped) functions with addresses of the STRIPPED donor Y by the call targets alone. This wrapper
adds, per pair: the cmp counts of the bytecmp that drvcmp.py loads (verdict, pcrel, real, unmeasured) on X's bytes vs Y's bytes at the
paired address; the donor's symbol name at that address, read from Y's unstripped twin YU (whose PT_LOAD bytes equal Y's,
see twins.out), and whether it equals X's name; and repin_check 9cbc3553c09e's tcmp (symbolic target pass, X vs YU at
the same address): target-differ count.
usage: pairtable.py X_ELF Y_STRIPPED Y_UNSTRIPPED NAME ADDR OUT_TSV     (paircl's own output goes to stdout)"""
import sys, os, runpy, importlib.util
HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location('drvcmp', os.path.join(HERE, 'drvcmp.py'))
dc = importlib.util.module_from_spec(spec); spec.loader.exec_module(dc)
xp, yp, yup, name, addr, out = sys.argv[1:7]
sys.argv = [os.path.join(HERE, 'paircl.py'), xp, yp, name, addr]
g = runpy.run_path(os.path.join(HERE, 'paircl.py'), run_name='__main__')
pair, starts, X, Y = g['pair'], g['starts'], g['X'], g['Y']
bad = {b[1]: b[3] for b in g['bad']}
I = {'X': X, 'YU': dc.Img(yup)}
ystarts = {}
for v, z, n, t in I['YU'].syms:
    if t == 'STT_FUNC' and z > 0:
        ystarts.setdefault(v, []).append((n, z))
tot = {'pcrel': 0, 'real': 0, 'unmeasured': 0, 'tdiff': 0, 'namemis': 0, 'sizemis': 0}
with open(out, 'w') as f:
    f.write('# X %s %s; Y %s %s; YU %s %s; root %s Y %s\n' % (xp, dc.sha(xp)[:12], yp, dc.sha(yp)[:12], yup,
            dc.sha(yup)[:12], name, addr))
    f.write('fn\tX addr\tY addr\tsize\tY name (YU)\tname eq\tY size (YU)\tbytecmp verdict\tpcrel\treal\tunmeasured\t'
            'tcmp target-differ (X vs YU)\tpaircl row\n')
    for xa in sorted(pair):
        ya = pair[xa]; n, z = starts[xa][0]
        bx, by = X.rd(xa, z), Y.rd(ya, z)
        v, c = dc.bc_cmp(bx, by) if by is not None else ('Y bytes missing', None)
        yn = ystarts.get(ya, [('-', 0)])
        ynames = {e[0] for e in yn}; ysz = yn[0][1]
        eq = n in ynames
        _, _, _, diff = dc.tcmp(I, 'X', xa, 'YU', ya, z)
        if c:
            tot['pcrel'] += c[0]; tot['real'] += c[1]; tot['unmeasured'] += c[2]
        tot['tdiff'] += 1 if diff else 0; tot['namemis'] += 0 if eq else 1; tot['sizemis'] += 0 if ysz == z else 1
        f.write('%s\t%#x\t%#x\t%d\t%s\t%s\t%d\t%s\t%s\t%s\t%s\t%d\t%s\n' % (
            n, xa, ya, z, '/'.join(sorted(ynames)), 'yes' if eq else 'NO', ysz, v, c[0] if c else '', c[1] if c else '',
            c[2] if c else '', len(diff), bad.get(xa, 'ok')))
    f.write('# pairs %d; real words total %d; pcrel %d; unmeasured %d; functions with tcmp target-differ %d; '
            'name mismatches %d; size mismatches %d; paircl other %d; conflicts %d\n'
            % (len(pair), tot['real'], tot['pcrel'], tot['unmeasured'], tot['tdiff'], tot['namemis'], tot['sizemis'],
               len(g['bad']), len(g['conflicts'])))
print('# pairtable: pairs %d; real %d; tcmp target-differ functions %d; name mismatches %d; size mismatches %d'
      % (len(pair), tot['real'], tot['tdiff'], tot['namemis'], tot['sizemis']))
