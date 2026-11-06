#!/usr/bin/env python3
"""paircl.py -- compare a function of image X (with symbols) and its whole direct-call closure against a STRIPPED image Y,
pairing functions by the call targets themselves (read-only).

Start: X function NAME at its symbol, Y at the address ADDR (from the donor's released file). Each X function in the
closure is compared with the Y code at its paired address, over X's size: bytecmp 7daa0e2a03d9's words + cmp (verdict,
pc-relative count, real differences), and repin_check 9cbc3553c09e's targets() on both sides. The i-th pc-relative
target of X is paired with the i-th of Y; a target that starts an X function adds the pair (X target, Y target) to the
work list. A pair seen twice with different partners is reported (the pairing must be one-to-one). Data targets are
compared by their 8 bytes (or the string at a .rodata target).
usage: paircl.py X_ELF Y_ELF NAME ADDR"""
import sys, os, importlib.util
from elftools.elf.elffile import ELFFile
HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location('drvcmp', os.path.join(HERE, 'drvcmp.py'))
dc = importlib.util.module_from_spec(spec); spec.loader.exec_module(dc)
targets, bc_words, bc_cmp = dc._g['targets'], dc.bc_words, dc.bc_cmp

class Raw:
    def __init__(s, p):
        s.e = ELFFile(open(p, 'rb'))
        s.segs = [(g['p_vaddr'], g['p_filesz'], g.data()) for g in s.e.iter_segments() if g['p_type'] == 'PT_LOAD']
        s.secs = [(x.name, x['sh_addr'], x['sh_size']) for x in s.e.iter_sections() if x['sh_addr'] > 0]
    def rd(s, a, n):
        for v, z, d in s.segs:
            if v <= a and a + n <= v + z:
                return d[a - v:a - v + n]
        return None
    def sec(s, a):
        for n, v, z in s.secs:
            if v <= a < v + z:
                return n
        return None

X = dc.Img(sys.argv[1]); Y = Raw(sys.argv[2]); name = sys.argv[3]; ya = int(sys.argv[4], 16)
starts = {}
for v, z, n, t in X.syms:
    if t == 'STT_FUNC' and z > 0:
        starts.setdefault(v, []).append((n, z))
xs = X.fsym(name)
print('# X %s sha256 %s; Y %s sha256 %s; root %s X %#x Y %#x size %d' % (sys.argv[1], dc.sha(sys.argv[1])[:12], sys.argv[2],
      dc.sha(sys.argv[2])[:12], name, xs[0], ya, xs[1]))
pair = {xs[0]: ya}; rev = {ya: xs[0]}; work = [xs[0]]; bad = []; nfun = 0; nrow = {'EQUAL': 0, 'EQUAL-mod-pcrel': 0}
conflicts = []
while work:
    xa = work.pop(); yb = pair[xa]; n, z = starts[xa][0]; nfun += 1
    bx, by = X.rd(xa, z), Y.rd(yb, z)
    if by is None:
        bad.append((n, xa, yb, 'Y bytes missing')); continue
    r = bc_cmp(bx, by)
    v = r[0]
    if v not in ('EQUAL', 'EQUAL-mod-pcrel') and r[1]: v = '%s (pcrel %d real %d unmeasured %d)' % (v, r[1][0], r[1][1], r[1][2])
    tx, ty = targets(xa, bx), targets(yb, by)
    kx, ky = sorted(tx), sorted(ty)
    diff = []
    if kx != ky:
        diff.append(('target word positions differ', len(kx), len(ky)))
    for i in kx:
        if i not in ty: continue
        ax, ay = tx[i][1], ty[i][1]
        sx_, sy_ = X.sec(ax), Y.sec(ay)
        if sx_ != sy_:
            diff.append((hex(i * 4), 'section', sx_, sy_)); continue
        if ax in starts:
            if ax in pair:
                if pair[ax] != ay: conflicts.append((starts[ax][0][0], hex(ax), hex(pair[ax]), hex(ay)))
            elif ay in rev and rev[ay] != ax:
                conflicts.append(('Y target taken', hex(ax), hex(ay)))
            elif not (xa <= ax < xa + z):
                pair[ax] = ay; rev[ay] = ax; work.append(ax)
        elif sx_ in ('.rodata',):
            a1, a2 = X.rd(ax, 64) or b'', Y.rd(ay, 64) or b''
            s1, s2 = a1.split(b'\0')[0], a2.split(b'\0')[0]
            isstr = len(s1) >= 2 and all(32 <= c < 127 or c in (9, 10) for c in s1)
            same = (s1 == s2) if isstr else (a1[:8] == a2[:8])
            if not same: diff.append((hex(i * 4), 'rodata string' if isstr else 'rodata 8 bytes', a1[:16], a2[:16]))
        elif sx_ in ('.got', '.data', '.data.rel.ro'):
            pass  # cells: content is the image's own data / pointers
    label = v if not diff else '%s target-diff %d' % (v, len(diff))
    if v in nrow and not diff: nrow[v] += 1
    else: bad.append((n, xa, yb, label, diff[:2]))
print('closure %d functions paired; EQUAL %d; EQUAL-mod-pcrel (targets paired) %d; other %d; pairing conflicts %d'
      % (nfun, nrow['EQUAL'], nrow['EQUAL-mod-pcrel'], len(bad), len(conflicts)))
for b in bad: print('  ', b[0][:80], hex(b[1]), hex(b[2]), b[3], b[4] if len(b) > 4 else '')
for c in conflicts[:10]: print('  CONFLICT', c)
