#!/usr/bin/env python3
"""measure_gcut.py AD2J AD2F AD1X ASAN_GLOBALS_TSV [AD1Y] -- the values the transport image-A G hunks carry, measured.

AD2J  the start-up region list (lib/A/AD2j.v of the target lib: IMG_REGIONS, mkRegion base lo hi wlo whi)
AD2F  the core's A/AD2f.v (stage-out text: STDOUT_LO/HI, SOBUF_LO/HI, A_INITFLAG; the counts port_core wrote)
AD1X  the core's A/AD1x.v (stage-out text: F_STDERR_LO/HI; the IMG_XL count port_core wrote)
ASAN_GLOBALS_TSV  output of asan_globals.py on the unstripped twin (beg, size, size_with_redzone, name)
AD1Y  (optional) the start-up layer's A/AD1y.v: its DRV_G_LO / DRV_G_HI are compared with the measured hull

The hull [DRV_G_LO, DRV_G_HI) is the payload start of the first writable harness global (the first descriptor in the
writable segment, g_cfg) to the payload end of the last (OW). The counts replay AD2f's clip_out (only region bounds
decide how many pieces a clip leaves) on IMG_REGIONS in its order: IMG_L / IMG_LC with and without the hull clip, and
AD1x's IMG_XL = clipX IMG_L; `clip_identity` says whether the hull clip returns every region unchanged ([r]), and
the *_written rows compare the counts with the ones the stage-out states. Prints `name<TAB>value<TAB>how`."""
import re
import sys


def defs(text):
    out = {}
    for m in re.finditer(r'Definition (\w+) : Z := (0x[0-9a-fA-F]+|\d+)\.', text):
        out[m.group(1)] = int(m.group(2), 0)
    return out


def regions(text):
    rs = {}
    for m in re.finditer(r'Definition (R_\w+) : region :=\s*mkRegion (None|\(Some \d+\)) (-?\d+) (-?\d+) (-?\d+) (-?\d+)', text):
        rs[m.group(1)] = (m.group(2), int(m.group(3)), int(m.group(4)), int(m.group(5)), int(m.group(6)))
    order = re.search(r'Definition IMG_REGIONS : smem := \[([^\]]*)\]', text).group(1)
    names = [n.strip() for n in order.split(';')]
    return [(n,) + rs[n] for n in names]


def clip_out(lo, hi, r):
    name, base, rlo, rhi = r[0], r[1], r[2], r[3]
    if hi <= rlo or rhi <= lo:
        return [r]
    out = []
    if rlo < lo:
        out.append((name + '<', base, rlo, min(rhi, lo)))
    if hi < rhi:
        out.append((name + '>', base, max(rlo, hi), rhi))
    return out


def fm(f, rs):
    return [p for r in rs for p in f(r)]


def main():
    ad2j, ad2f, ad1x, glob = (open(p).read() for p in sys.argv[1:5])
    ad1y = open(sys.argv[5]).read() if len(sys.argv) > 5 else None
    d = defs(ad2f)
    d.update(defs(ad1x))
    rs = [(r[0], r[1], r[2], r[3]) for r in regions(ad2j)]
    gl = []
    for line in glob.splitlines():
        if line.startswith('#') or not line.strip():
            continue
        beg, size, szr, name = line.split('\t')
        gl.append((int(beg, 0), int(size), int(szr), name))
    w = [g for g in gl if g[0] >= 0x5d0000]
    glo, ghi = w[0][0], w[-1][0] + w[-1][1]
    so = lambda r: fm(lambda q: clip_out(d['SOBUF_LO'], d['SOBUF_HI'], q), clip_out(d['STDOUT_LO'], d['STDOUT_HI'], r))
    gc = lambda r: fm(lambda q: clip_out(glo, ghi, q), so(r))
    img_l0 = fm(so, rs)
    img_l = fm(gc, rs)
    ib = d['A_INITFLAG']
    clipx = lambda l: fm(lambda q: clip_out(ib, ib + 1, q), fm(lambda q: clip_out(d['F_STDERR_LO'], d['F_STDERR_HI'], q), fm(so, l)))
    print(f'globals\t{len(w)}\twritable harness globals (beg >= 0x5d0000) in asan_globals: ' + ', '.join(f'{g[3]} {g[0]:#x}/{g[1]}' for g in w))
    print(f'DRV_G_LO\t{glo:#x}\tpayload start of {w[0][3]}')
    print(f'DRV_G_HI\t{ghi:#x}\tpayload end of {w[-1][3]} ({w[-1][0]:#x} + {w[-1][1]})')
    print(f'IMG_REGIONS\t{len(rs)}\tregions of the start-up list')
    print(f'IMG_L_noG\t{len(img_l0)}\tIMG_L / IMG_LC without the hull clip (stage-out value)')
    print(f'IMG_L\t{len(img_l)}\tIMG_L / IMG_LC with the hull clip, outermost (bounds of IMG_B / IMG_E are those of IMG_REGIONS)')
    meet = [r[0] for r in rs if not (ghi <= r[2] or r[3] <= glo)]
    print(f'hull_meets\t{len(meet)}\tregions of IMG_REGIONS that meet the hull: ' + ' '.join(meet))
    gone = [r[0] for r in rs if glo <= r[2] and r[3] <= ghi]
    print(f'hull_drops\t{len(gone)}\tregions inside the hull, dropped by the clip: ' + ' '.join(gone))
    print(f'IMG_XL_noG\t{len(clipx(img_l0))}\tAD1x IMG_XL = clipX IMG_L without the hull clip (stage-out value)')
    print(f'IMG_XL\t{len(clipx(img_l))}\tAD1x IMG_XL = clipX IMG_L with the hull clip')
    left = [r for r in img_l if r[1] == 'None' and not (ghi <= r[2] or r[3] <= glo)]
    print(f'L_mem_avoids_G\t{"true" if not left else "false"}\tevery None-based region of the clipped IMG_LC avoids the hull (region_avoids_G)')
    keep = [('STDOUT', d['STDOUT_LO'], d['STDOUT_HI']), ('SOBUF', d['SOBUF_LO'], d['SOBUF_HI']), ('F_STDERR', d['F_STDERR_LO'], d['F_STDERR_HI'])]
    for n, lo, hi in keep:
        print(f'{n}_off_hull\t{"true" if hi <= glo or ghi <= lo else "false"}\t[{lo:#x}, {hi:#x}) vs hull')
    ident = all(clip_out(glo, ghi, q) == [q] for r in rs for q in so(r))
    print(f'clip_identity\t{"true" if ident else "false"}\tthe hull clip returns [r] for every piece of IMG_REGIONS after the STDOUT / SOBUF clips')
    wl = re.search(r'length IMG_L = (\d+)%nat', ad2f)
    wc = re.search(r'length IMG_LC = (\d+)%nat', ad2f)
    wx = re.search(r'length IMG_XL = (\d+)%nat', ad1x)
    for n, m, v in (('IMG_L', wl, len(img_l)), ('IMG_LC', wc, len(img_l)), ('IMG_XL', wx, len(clipx(img_l)))):
        got = int(m.group(1)) if m else None
        print(f'{n}_written\t{got}\t{"stands" if got == v else "DIFFERS"}: stage-out states {got}, the hull-clipped count is {v}')
    if ad1y is not None:
        y = defs(ad1y)
        for n, v in (('DRV_G_LO', glo), ('DRV_G_HI', ghi)):
            print(f'AD1y_{n}\t{y.get(n, 0):#x}\t{"equal" if y.get(n) == v else "DIFFERS"} to the measured {v:#x}')


main()
