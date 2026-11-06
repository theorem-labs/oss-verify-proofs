#!/usr/bin/env python3
"""paircl.py -- compare a function of image X (with symbols) and its whole direct-call closure against a STRIPPED image Y,
pairing functions by the call targets themselves (read-only).

Start: X function NAME at its symbol, Y at the address ADDR (from the donor's released file). Each X function in the
closure is compared with the Y code at its paired address, over X's size, by the comparison kit's ONE compare,
strictcmp2.py's tcmp (bytecmp cmp: verdict, pc-relative count, real differences; then every pc-relative target pair
judged by its target rule). Y's names come from its unstripped twin YU_ELF and every byte read is Y's own (the two must
have the same PT_LOAD layout). A function counts EQUAL / EQUAL-mod-pcrel only with no target difference; every
acceptance tcmp makes that is not a name is printed as closure_strict2.py prints it (ACCEPT lines, and strictcmp2's CSTR
row per C-string acceptance: function, pair, word offset, addr1, addr2, length, hex, repr). The i-th pc-relative target
of X is paired with the i-th of Y; a target pair tcmp did not report that starts an X function (directly, or as the
value of a .got cell) adds the pair (X target, Y target) to the work list. A pair seen twice with different partners is
reported (the pairing must be one-to-one). A reported target pair is never paired (fail closed).
usage: paircl.py X_ELF Y_ELF NAME ADDR YU_ELF"""
import sys, os, importlib.util
from elftools.elf.elffile import ELFFile
HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location('strictcmp2', os.path.join(HERE, 'strictcmp2.py'))
s2 = importlib.util.module_from_spec(spec); spec.loader.exec_module(s2)
targets, bc_words, tcmp = s2.targets, s2.bc_words, s2.tcmp

X = s2.Img(sys.argv[1]); name = sys.argv[3]; ya = int(sys.argv[4], 16)
Y = s2.Img(sys.argv[5])   # Y's unstripped twin YU_ELF: its symbols name Y's targets; its PT_LOAD bytes become Y's below
YP = [(g['p_vaddr'], g['p_filesz'], g['p_memsz'], g.data()) for g in ELFFile(open(sys.argv[2], 'rb')).iter_segments()
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
xs = X.fsym(name)
print('# X %s sha256 %s; Y %s sha256 %s; YU %s sha256 %s; root %s X %#x Y %#x size %d' % (sys.argv[1], s2.sha(sys.argv[1])[:12],
      sys.argv[2], s2.sha(sys.argv[2])[:12], sys.argv[5], s2.sha(sys.argv[5])[:12], name, xs[0], ya, xs[1]))
pair = {xs[0]: ya}; rev = {ya: xs[0]}; work = [xs[0]]; bad = []; nfun = 0; nrow = {'EQUAL': 0, 'EQUAL-mod-pcrel': 0}
conflicts = []; acc = []
while work:
    xa = work.pop(); yb = pair[xa]; n, z = starts[xa][0]; nfun += 1
    bx, by = X.rd(xa, z), Y.rd(yb, z)
    if by is None:
        bad.append((n, xa, yb, 'Y bytes missing')); continue
    fb = []
    v, c, t3, diff = tcmp(I, 'X', xa, 'Y', yb, z, fb)
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
    label = v if not diff else '%s target-diff %d' % (v, len(diff))
    if v in nrow and not diff: nrow[v] += 1
    else: bad.append((n, xa, yb, label, diff[:2]))
print('closure %d functions paired; EQUAL %d; EQUAL-mod-pcrel (targets paired) %d; other %d; pairing conflicts %d'
      % (nfun, nrow['EQUAL'], nrow['EQUAL-mod-pcrel'], len(bad), len(conflicts)))
for b in bad: print('  ', b[0][:80], hex(b[1]), hex(b[2]), b[3], b[4] if len(b) > 4 else '')
for c in conflicts[:10]: print('  CONFLICT', c)
for n, xa, yb, fb in acc:
    t = s2.fb_text(fb)
    if t: print('   ACCEPT %s @%#x/%#x: %s' % (n, xa, yb, t))
    for r in s2.cstr_rows(n, 'X:Y', fb): print(r)
