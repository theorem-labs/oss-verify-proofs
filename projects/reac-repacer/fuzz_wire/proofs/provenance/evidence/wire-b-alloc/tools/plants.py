#!/usr/bin/env python3
"""plants.py -- the two controls the ruling asks for (the unit owner's ruling), each of which the hand trace must REFUSE:
  (a) a lui value that forms a STORE BASE through `add`. Two lui values that lie in NO section of either image
      (0x700000 and -0x600000, so rule 8 of cmpkit 86da41d3ef68 reads each as a plain constant and bytecmp compares it
      raw) are added into a .bss address (0x100000) that names a DIFFERENT offset in the two images; a store uses it as
      its base. The same four words are written at the same offset of the same function in BOTH copies, so the images
      stay byte-equal there: only the meaning of the address differs. luitrace must report DIFFERS (full address X vs Y);
      the kit, which does not follow `add`, is expected to stay EQUAL (its fail-open class).
  (b) a lui value passed as a CALL ARGUMENT to a `uptr` ADDRESS parameter. A call site whose row the hand trace settles
      as (i) CALL ARGUMENT is re-pointed, in both copies, to a function whose cited parameter at that register is a uptr
      (or pointer) that is an address, not a count or a length (each copy to its own image's copy of that function, so
      the meaning is the same on both sides). the unit owner's ruling keeps uptr address parameters NOT CERTIFIED, so the row
      must stop settling.
  (c) the plant (a) store base, reached only through divuw and a shift (PLANT_C): it must come out DIFFERS, which shows
      the trace follows a value through those ops (the re-reviews, 2026-10-31).
Read-only on the images; the copies are written under OUT_DIR.
usage: plants.py X_ELF Y_ELF OUT_DIR ROOT1,ROOT2,... CITE_TSV BASELINE_LUITRACE_TSV"""
import os, re, shutil, subprocess, sys, importlib.util
HERE = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location('luitrace', os.path.join(HERE, 'luitrace.py'))
lt = importlib.util.module_from_spec(_spec); _spec.loader.exec_module(lt)
s3 = lt.s3

# plant (c): lui t0,0x700 ; li t1,14 ; divuw t0,t0,t1 ; slli t0,t0,1 ; sd zero,0(t0) -- a lui value that reaches a store
# base only through divuw and a shift (0x700000 / 14 = 0x80000, << 1 = 0x100000); 0x700000 lies in no section
PLANT_C = [0x007002B7, 0x00E00313, 0x0262D2BB, 0x00129293, 0x0002B023]
PLANT_C_TEXT = ['lui t0,0x700', 'li t1,14', 'divuw t0,t0,t1', 'slli t0,t0,1', 'sd zero,0(t0)']
PLANT_C_SUM = 0x100000
# plant (a): lui t0,0x700 ; lui t1,0xffa00 ; add t0,t0,t1 ; sd zero,0(t0)
PLANT_A = [0x007002B7, 0xFFA00337, 0x006282B3, 0x0002B023]
PLANT_A_TEXT = ['lui t0,0x700', 'lui t1,0xffa00', 'add t0,t0,t1', 'sd zero,0(t0)']
PLANT_A_SUM = 0x100000
def foff(path, a):
    from elftools.elf.elffile import ELFFile
    for g in ELFFile(open(path, 'rb')).iter_segments():
        if g['p_type'] == 'PT_LOAD' and g['p_vaddr'] <= a < g['p_vaddr'] + g['p_filesz']:
            return a - g['p_vaddr'] + g['p_offset']
    return None

def patch(path, addr, words):
    with open(path, 'r+b') as f:
        for k, w in enumerate(words):
            o = foff(path, addr + 4 * k)
            if o is None: raise SystemExit('address %#x is in no PT_LOAD of %s' % (addr + 4 * k, path))
            f.seek(o); f.write(w.to_bytes(4, 'little'))

def jal(frm, to, rd=1):
    d = to - frm
    if not -(1 << 20) <= d < (1 << 20): return None
    i = d & 0x1FFFFE
    return (((i >> 20) & 1) << 31) | (((i >> 1) & 0x3FF) << 21) | (((i >> 11) & 1) << 20) | \
           (((i >> 12) & 0xFF) << 12) | (rd << 7) | 0x6F

def compared(X, Y, roots):
    """{X address: (name, size, Y address)} for the functions the record compares (luitrace's own walk)"""
    def starts(Im):
        st = {}
        for v, z, n, t in Im.syms:
            if t == 'STT_FUNC' and z > 0: st.setdefault(v, []).append((n, z))
        return st
    SX, SY = starts(X), starts(Y)
    def refs(Im, st, a, z):
        b = s3.frd(Im, a, z); out = {}
        if b is None: return out
        for i, (kind, ta) in s3.targets(a, b).items():
            if Im.sec(ta) == '.got':
                c = s3.frd(Im, ta, 8); ta = int.from_bytes(c, 'little') if c else -1
            if ta in st and not (a <= ta < a + z): out[i] = ta
        return out
    yof = {}; seen = set(); work = []
    for r in roots:
        cx, cy = s3.fcopies(X, r), s3.fcopies(Y, r)
        yof[cx[0][0]] = cy[0][0]; seen.add(cx[0][0]); work.append(cx[0][0])
    while work:
        a = work.pop(); z = SX[a][0][1]; ya = yof.get(a)
        ry = refs(Y, SY, ya, z) if ya is not None and SY.get(ya, [(None, -1)])[0][1] == z else {}
        for i, t in refs(X, SX, a, z).items():
            if t not in yof and i in ry: yof[t] = ry[i]
            if t not in seen: seen.add(t); work.append(t)
    out = {}
    for a in sorted(seen):
        nx, zx = sorted(SX[a])[0]
        ya = yof.get(a)
        if ya is not None and SY.get(ya, [(None, -1)])[0][1] == zx:
            out[a] = (s3.qname(X, nx, a) or nx, zx, ya)
    return out

def run_trace(xp, yp, roots, cite, only, out):
    cmd = [sys.executable, os.path.join(HERE, 'luitrace.py'), xp, yp, ','.join(roots), cite, '--only', only]
    r = subprocess.run(cmd, capture_output=True, text=True)
    open(out, 'w').write(r.stdout)
    if r.returncode: sys.stderr.write(r.stderr[-2000:])
    return [l.split('\t') for l in r.stdout.splitlines()]

def run_kit(xp, yp, fn, out):
    cmd = [sys.executable, os.path.join(HERE, 'strictcmp3.py'), 'cmp', fn, 'A=' + xp, 'B=' + yp, 'A:B']
    r = subprocess.run(cmd, capture_output=True, text=True)
    open(out, 'w').write(r.stdout + r.stderr)
    for l in r.stdout.splitlines():
        f = l.split('\t')
        if len(f) > 6 and f[1] == 'A:B': return f
    return None

def main():
    xp, yp, outd, roots, cite, base = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4].split(','), sys.argv[5], sys.argv[6]
    os.makedirs(outd, exist_ok=True)
    X, Y = s3.Img(xp), s3.Img(yp)
    cs = compared(X, Y, roots)
    print('#\tX %s sha256 %s\tY %s sha256 %s\tcompared functions %d' % (
        os.path.basename(xp), s3.sha(xp)[:12], os.path.basename(yp), s3.sha(yp)[:12], len(cs)))

    # ---- plant (a): a store base built by `add` from two lui values -------------------------------------------------
    site = None
    for a, (nm, z, ya) in sorted(cs.items()):
        if z < 10 * 4 or '{' in nm: continue
        b = s3.frd(X, a, z); by = s3.frd(Y, ya, z)
        if b is None or by is None or any(n == 2 for o, x, n in s3.bc_words(b)) or any(n == 2 for o, x, n in s3.bc_words(by)):
            continue
        site = (a, nm, z, ya); break
    if site is None: raise SystemExit('no function to plant in')
    a, nm, z, ya = site
    off = 4 * 4                                   # after the prologue words, inside the function on every path
    xa, ya_ = os.path.join(outd, 'plant-a-X.elf'), os.path.join(outd, 'plant-a-Y.elf')
    shutil.copy2(xp, xa); shutil.copy2(yp, ya_); os.chmod(xa, 0o644); os.chmod(ya_, 0o644)
    patch(xa, a + off, PLANT_A); patch(ya_, ya + off, PLANT_A)
    print('PLANT-A\t%s\t+%#x\t%s\tthe sum %#x is %s in X and %s in Y' % (
        nm, off, ' ; '.join(PLANT_A_TEXT), PLANT_A_SUM, s3.qres(X, PLANT_A_SUM), s3.qres(Y, PLANT_A_SUM)))
    rows = run_trace(xa, ya_, roots, cite, nm, os.path.join(outd, 'plant_a_luitrace.out'))
    mine = [r for r in rows if r[0] == 'ROW' and r[2] == '+%#x' % off]
    for r in mine: print('PLANT-A-ROW\t%s\t%s\t%s' % (r[3], r[5], r[6][:160]))
    print('PLANT-A-VERDICT\t%s' % ('CAUGHT: ' + '; '.join(sorted({r[5] for r in mine if r[5] == 'DIFFERS'}))
                                   if any(r[5] == 'DIFFERS' for r in mine) else
                                   'NOT CAUGHT: ' + '; '.join(sorted({r[5] for r in mine})) if mine else 'NOT CAUGHT: no row'))
    k = run_kit(xa, ya_, nm, os.path.join(outd, 'plant_a_kit.out'))
    print('PLANT-A-KIT\t%s\tverdict %s\ttarget-differ %s\t(the kit of record on the planted pair)' % (
        nm, k[6] if k else '?', k[11] if k and len(k) > 11 else '?'))

    # ---- plant (c): the same store base reached only through divuw and a shift ------------------------------------
    xc, yc = os.path.join(outd, 'plant-c-X.elf'), os.path.join(outd, 'plant-c-Y.elf')
    shutil.copy2(xp, xc); shutil.copy2(yp, yc); os.chmod(xc, 0o644); os.chmod(yc, 0o644)
    patch(xc, a + off, PLANT_C); patch(yc, ya + off, PLANT_C)
    print('PLANT-C\t%s\t+%#x\t%s\tthe value %#x is %s in X and %s in Y' % (
        nm, off, ' ; '.join(PLANT_C_TEXT), PLANT_C_SUM, s3.qres(X, PLANT_C_SUM), s3.qres(Y, PLANT_C_SUM)))
    rows = run_trace(xc, yc, roots, cite, nm, os.path.join(outd, 'plant_c_luitrace.out'))
    mine = [r for r in rows if r[0] == 'ROW' and r[2] == '+%#x' % off]
    for r in mine: print('PLANT-C-ROW\t%s\t%s\t%s' % (r[3], r[5], r[6][:160]))
    print('PLANT-C-VERDICT\t%s' % ('CAUGHT: DIFFERS' if any(r[5] == 'DIFFERS' for r in mine) else
                                   'NOT CAUGHT: ' + '; '.join(sorted({r[5] for r in mine})) if mine else 'NOT CAUGHT: no row'))
    k = run_kit(xc, yc, nm, os.path.join(outd, 'plant_c_kit.out'))
    print('PLANT-C-KIT\t%s\tverdict %s\ttarget-differ %s\t(the kit of record on the planted pair)' % (
        nm, k[6] if k else '?', k[11] if k and len(k) > 11 else '?'))

    # ---- plant (b): a lui call argument to a uptr ADDRESS parameter -------------------------------------------------
    # a row the hand trace settles as (i) is re-pointed to a function whose CITED parameter at that register is a uptr
    # (or a pointer) that is an address, not a count or a length: the unit owner's ruling keeps uptr ADDRESS parameters NOT
    # CERTIFIED, so the row must stop settling.
    addr_param = {}                                   # callee -> {register: (type, name, citation)}
    for p in (cite, os.path.join(os.path.dirname(cite), 'cite-extra.tsv')):
        if not os.path.exists(p): continue
        for l in open(p):
            f = l.rstrip('\n').split('\t')
            if len(f) < 6 or f[0] != 'arg': continue
            if lt.src_kind(f[3]) in ('uptr', 'ptr') and not lt.means_count(f[4]) and f[4] != 'this':
                addr_param.setdefault(f[1], {})[f[2]] = (f[3], f[4], f[5])
    settled = [l.rstrip('\n').split('\t') for l in open(base)]
    settled = [r for r in settled if r[0] == 'ROW' and r[5].startswith('(i) ')]
    if not settled: raise SystemExit('no settled CALL ARGUMENT row in the baseline')
    pick = None
    for kind in ('uptr', 'ptr'):                      # a uptr address parameter first; a pointer only if none fits
      for cand in sorted(settled, key=lambda r: (r[1], r[2], r[3])):
        fname, luipc, pc = cand[1], cand[2], cand[3].split(' ')[0]
        reg = cand[4]
        fas = [k for k, v in cs.items() if v[0] == fname]
        if not fas: continue
        fa = fas[0]; fya = cs[fa][2]; wpc = int(pc[1:], 16)
        for cn in sorted(addr_param):
            if reg not in addr_param[cn] or lt.src_kind(addr_param[cn][reg][0]) != kind: continue
            cx, cy = s3.fcopies(X, cn), s3.fcopies(Y, cn)
            if len(cx) != 1 or len(cy) != 1: continue
            wx, wy = jal(fa + wpc, cx[0][0]), jal(fya + wpc, cy[0][0])
            if wx is None or wy is None: continue
            pick = (cand, fname, luipc, pc, reg, fa, fya, wpc, cn, cx[0][0], cy[0][0], wx, wy); break
        if pick: break
      if pick: break
    if pick is None: raise SystemExit('no settled row that a uptr-address callee in jal range can take')
    cand, fname, luipc, pc, reg, fa, fya, wpc, cn, cxa, cya, wx, wy = pick
    xb, yb = os.path.join(outd, 'plant-b-X.elf'), os.path.join(outd, 'plant-b-Y.elf')
    shutil.copy2(xp, xb); shutil.copy2(yp, yb); os.chmod(xb, 0o644); os.chmod(yb, 0o644)
    patch(xb, fa + wpc, [wx]); patch(yb, fya + wpc, [wy])
    t_, n_, c_ = addr_param[cn][reg]
    print('PLANT-B\t%s\t%s\tthe call at %s is re-pointed to %s (X %#x, Y %#x), whose parameter %s is `%s %s` (an address) [%s]'
          % (fname, luipc, pc, cn, cxa, cya, reg, t_, n_, c_))
    rows = run_trace(xb, yb, roots, cite, fname, os.path.join(outd, 'plant_b_luitrace.out'))
    mine = [r for r in rows if r[0] == 'ROW' and r[2] == luipc and r[3].startswith(pc + ' arg') and r[4] == reg]
    for r in mine: print('PLANT-B-ROW\t%s\t%s\t%s' % (r[3], r[5], r[6][:160]))
    before = [r for r in settled if r[1] == fname and r[2] == luipc and r[3].startswith(pc + ' arg') and r[4] == reg]
    print('PLANT-B-BEFORE\t%s' % '; '.join('%s %s' % (r[3], r[5]) for r in before))
    ok = mine and all(r[5] == 'NOT CERTIFIED' for r in mine)
    print('PLANT-B-VERDICT\t%s' % ('REFUSED: ' + '; '.join(sorted({r[5] for r in mine})) if ok else
                                   'NOT REFUSED: ' + '; '.join(sorted({r[5] for r in mine})) if mine else 'no row'))
    k = run_kit(xb, yb, fname, os.path.join(outd, 'plant_b_kit.out'))
    print('PLANT-B-KIT\t%s\tverdict %s\ttarget-differ %s' % (fname, k[6] if k else '?', k[11] if k and len(k) > 11 else '?'))

if __name__ == '__main__':
    main()
