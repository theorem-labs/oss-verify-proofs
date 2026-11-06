#!/usr/bin/env python3
"""paircl.py -- compare a function of image X (with symbols) and its whole direct-call closure against a STRIPPED image Y,
pairing functions by the call targets themselves (read-only).

Start: X function NAME (a name exactly one sized STT_FUNC address carries, NAME{file} for one copy of a name several copies
carry - the kit's qualified name, strictcmp3.qname -, or 0x<address> of a sized STT_FUNC; any other NAME is REFUSED, rc 2,
with every candidate listed), Y at the address ADDR (from the donor's released file). Each X function in the
closure is compared with the Y code at its paired address, over X's size, by the comparison kit's ONE compare,
strictcmp3.py's tcmp (bytecmp cmp: verdict, pc-relative count, real differences; then every pc-relative and lui-built
target pair judged by its target rule). Y's names come from its unstripped twin YU_ELF and every byte read is Y's own (the two must
have the same PT_LOAD layout). A function counts EQUAL / EQUAL-mod-pcrel only with no target difference; a row's printed
verdict is the combined one (strictcmp3.verdict: DIFFERENT-target / UNMEASURED-target when a target differs), followed by
`(words-only ...)`; every acceptance tcmp makes that is not a name is printed as closure_strict3.py prints it (ACCEPT lines, and the CSTR
row per C-string acceptance: function, pair, word offset, addr1, addr2, length, hex, repr). The i-th pc-relative target
of X is paired with the i-th of Y; a target pair tcmp did not report that starts an X function (directly, or as the
value of a .got cell) adds the pair (X target, Y target) to the work list. A pair seen twice with different partners is
reported (the pairing must be one-to-one). A reported target pair is never paired (fail closed).
Every function row that is not EQUAL says `printed M of N targets`: N differing targets, of which the first M are printed
inline (TARGET lines; M = 2, or all with --full). EVERY differing target of every row is written to a TSV file named in
the header (--targets-out FILE; default ./paircl-targets-<X sha12>-<X root>-<ADDR>.tsv); a row with M < N says so
(`TRUNCATED: ... NOT PRINTED`). Every pairing conflict is printed.
usage: paircl.py X_ELF Y_ELF NAME ADDR YU_ELF [--full] [--targets-out FILE]"""
import sys, os, importlib.util
from elftools.elf.elffile import ELFFile
HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location('strictcmp3', os.path.join(HERE, 'strictcmp3.py'))
s2 = importlib.util.module_from_spec(spec); spec.loader.exec_module(s2)   # s2: the kit's compare module (now strictcmp3)
targets, bc_words, tcmp = s2.targets, s2.bc_words, s2.tcmp

argv = sys.argv[1:]; FULL = '--full' in argv; argv = [x for x in argv if x != '--full']; TOUT = None
if '--targets-out' in argv:
    k = argv.index('--targets-out'); TOUT = argv[k + 1]; del argv[k:k + 2]
if len(argv) != 5: sys.exit(__doc__.split('usage: ')[1])
xp, yp, name, yaddr, yup = argv
X = s2.Img(xp); ya = int(yaddr, 16)
Y = s2.Img(yup)   # Y's unstripped twin YU_ELF: its symbols name Y's targets; its PT_LOAD bytes become Y's below
YP = [(g['p_vaddr'], g['p_filesz'], g['p_memsz'], g.data()) for g in ELFFile(open(yp, 'rb')).iter_segments()
      if g['p_type'] == 'PT_LOAD']
if [x[:3] for x in YP] != [(v, fz, mz) for (v, fz, d), mz in zip(Y.segs, Y.mzs)]:
    sys.exit('paircl: Y_ELF and YU_ELF have different PT_LOAD layouts')
Y.segs = [(v, fz, d) for v, fz, mz, d in YP]
I = {'X': X, 'Y': Y}
def held(Im, a):
    d = Im.rd(a, 8)
    return None if d is None else int.from_bytes(d, 'little')
starts = {}
for v, z, n, t in X.syms:
    if t == 'STT_FUNC' and z > 0:
        starts.setdefault(v, []).append((n, z))
def root(I, spec):
    """(addr, size) of the X root, or REFUSE (rc 2): a 0x<address> must start a sized STT_FUNC; a NAME must be carried by
    exactly one sized STT_FUNC address; NAME{file} selects the copy whose kit-qualified name (strictcmp2.qname) is spec."""
    if spec.startswith('0x'):
        c = sorted({(v, z) for v, z, n, t in I.syms if v == int(spec, 16) and t == 'STT_FUNC' and z > 0})
    else:
        nm = spec.split('{')[0]
        c = sorted({(v, z) for v, z, t in I.byname.get(nm, []) if t == 'STT_FUNC' and z > 0})
        if '{' in spec: c = [(v, z) for v, z in c if s2.qname(I, nm, v) == spec]
    if len(c) == 1: return c[0]
    nm = spec.split('{')[0]
    cand = [] if spec.startswith('0x') else sorted({(v, z) for v, z, t in I.byname.get(nm, []) if t == 'STT_FUNC' and z > 0})
    print('paircl: REFUSED root %s: %s' % (spec, 'no sized STT_FUNC matches' if not c else '%d sized STT_FUNC copies match' % len(c))
          + ''.join('\n  %s @%#x size %d' % (s2.qname(I, nm, v) or nm + ' (the file does not make this copy unique)', v, z)
                    for v, z in cand) + ('\n  give NAME{file} or 0x<address>' if len(cand) > 1 else ''), file=sys.stderr)
    sys.exit(2)
xs = root(X, name)
TOUT = TOUT or 'paircl-targets-%s-%#x-%#x.tsv' % (s2.sha(xp)[:12], xs[0], ya)
print('# X %s sha256 %s; Y %s sha256 %s; YU %s sha256 %s; root %s X %#x Y %#x size %d; every differing target: %s'
      % (xp, s2.sha(xp)[:12], yp, s2.sha(yp)[:12], yup, s2.sha(yup)[:12], name, xs[0], ya, xs[1], os.path.abspath(TOUT)))
pair = {xs[0]: ya}; rev = {ya: xs[0]}; work = [xs[0]]; bad = []; nfun = 0; nrow = {'EQUAL': 0, 'EQUAL-mod-pcrel': 0}
conflicts = []; acc = []
while work:
    xa = work.pop(); yb = pair[xa]; n, z = starts[xa][0]; nfun += 1
    bx, by = X.rd(xa, z), Y.rd(yb, z)
    if by is None:
        bad.append((n, xa, yb, 'Y bytes missing')); continue
    fb = []
    v, c, t3, diff = tcmp(I, 'X', xa, 'Y', yb, z, fb); vw = v
    if v not in ('EQUAL', 'EQUAL-mod-pcrel') and c: v = '%s (pcrel %d real %d unmeasured %d)' % (v, c[0], c[1], c[2])
    if fb: acc.append((n, xa, yb, fb))
    if c is not None:   # the words align: pair the call targets tcmp did not report
        tx, ty = targets(xa, bx), targets(yb, by); w = bc_words(bx); reported = {int(d[0], 16) for d in diff}
        for i in sorted(set(tx) & set(ty)):
            if w[i][0] in reported: continue
            ax, ay = tx[i][1], ty[i][1]
            if X.sec(ax) == Y.sec(ay) == '.got': ax, ay = held(X, ax), held(Y, ay)
            if ax in starts:
                if ax in pair:
                    if pair[ax] != ay: conflicts.append((starts[ax][0][0], hex(ax), hex(pair[ax]), hex(ay)))
                elif ay in rev and rev[ay] != ax:
                    conflicts.append(('Y target taken', hex(ax), hex(ay)))
                elif not (xa <= ax < xa + z):
                    pair[ax] = ay; rev[ay] = ax; work.append(ax)
    label = v if not diff else '%s target-diff %d (words-only %s)' % (s2.verdict(vw, diff), len(diff), v)
    if v in nrow and not diff: nrow[v] += 1
    else: bad.append((n, xa, yb, label, diff))
print('closure %d functions paired; EQUAL %d; EQUAL-mod-pcrel (targets paired) %d; other %d; pairing conflicts %d'
      % (nfun, nrow['EQUAL'], nrow['EQUAL-mod-pcrel'], len(bad), len(conflicts)))
NP = None if FULL else 2
with open(TOUT, 'w') as tf:
    tf.write('fn\tX addr\tY addr\tword offset\tX target\tY target\tkind\tinfo\n')
    for b in bad:
        d = b[4] if len(b) > 4 else []
        for e in d: tf.write('%s\t%#x\t%#x\t%s\t%s\t%s\t%s\t%r\n' % (b[0], b[1], b[2], e[0], e[1], e[2], e[3], e[4]))
        m = len(d) if NP is None else min(NP, len(d))
        print('  ', b[0][:80], hex(b[1]), hex(b[2]), b[3], '; printed %d of %d targets' % (m, len(d))
              + ('' if m == len(d) else ' -- TRUNCATED: %d MORE DIFFERING TARGETS NOT PRINTED (all in %s, or run with --full)'
                 % (len(d) - m, TOUT)))
        for e in d[:m]: print('      TARGET %s %s | %s %s %r' % e[:5])
for c in conflicts: print('  CONFLICT', c)
for n, xa, yb, fb in acc:
    t = s2.fb_text(fb)
    if t: print('   ACCEPT %s @%#x/%#x: %s' % (n, xa, yb, t))
    for r in s2.cstr_rows(n, 'X:Y', fb): print(r)
