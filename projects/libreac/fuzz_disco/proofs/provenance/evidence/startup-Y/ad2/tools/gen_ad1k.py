#!/usr/bin/env python3
"""gen_ad1k.py -- cgif's lib/A/AD1k.v (image A) / lib/YD1k.v (image B) for another image: the donor's text with only its
image literals regenerated.

  - literals that restate a chunk of AD2j/YD2j come from the GENERATED AD2j/YD2j (gen_ad2.py): R_A1h, R_A1i, R_A1d, R_A3,
    the canary .got chunk (the split CImg 8 chunk; its region's name follows the generated table), the canary cell of R_A7b,
    and the CH alternatives of ro_img_of_IMG (one per R_A1* region, in table order);
  - rodata_zero_shadow / rodata_hull_zero / rodata_shadow_facts: the first range of the owned-static file's
    Tfib_zero_shadow, the first asan global's beg (the hull bound) and R_A1h's lo, with the derived quotients;
  - STDOUT_BUFA / F_STDOUT / F_STDERR (restating AD1x/AE* definitions): the twin's __stdout_FILE / __stderr_FILE and the
    image word at __stdout_FILE + 88 (FILE.buf).
Every donor literal is checked to have the same role in the donor's own AD2j / AF0m / image before it is replaced.

  gen_ad1k.py --tmpl-ad1k DONOR/A/AD1k.v --tmpl-ad2j DONOR/A/AD2j.v --tmpl-owned DONOR/A/AF0m.v --tmpl-image DONOR_IMG
      --ad2j OUT/A/AD2j.v --owned OUT/A/AF0m.v --image IMG --twin TWIN_SYMTAB [--ns FROM=TO ...] [--modified TEXT]
      --out OUT/A/AD1k.v --sites SITES.md --label 'A/AD1k.v'
"""
import argparse, os, re, struct, sys

sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen_ad2 as g  # noqa: E402
from elftools.elf.elffile import ELFFile  # noqa: E402


def zero_shadow(path):
    t = open(path).read()
    m = re.search(r'Definition \w+_zero_shadow : list \(Z \* Z\) :=\n\[(.*?)\]\.', t, re.S)
    out = []
    for e in g.hsform.split_top(m.group(1)):
        a, n = g.hsform.split_top(e.strip()[1:-1], ',')
        out.append((g._zeval(a, path), g._zeval(n, path), e.strip()))
    return out


def first_global(path):
    f = ELFFile(open(path, 'rb'))
    d = f.get_section_by_name('asan_globals').data()
    gl = [struct.unpack('<8Q', d[i:i + 64]) for i in range(0, len(d), 64)]
    return min(gl, key=lambda x: x[0])


def all_symbols(path):
    """the twin's .symtab entries (value, size, name), in .symtab order, from its symbol extract (twin/mknm.py: one
    `<16-hex value> <hex size> <type> <name>` line per entry; `#` lines are its header)"""
    out = []
    for l in open(path):
        f = l.split()
        if not l.startswith('#') and len(f) == 4:
            out.append((int(f[0], 16), int(f[1], 16), f[3]))
    return [(v, sz, n) for v, sz, n in out if n and not n.startswith('$')]


def containing(syms, a):
    best = [(v, sz, n) for v, sz, n in syms if v <= a < v + max(sz, 1) and sz]
    return min(best, key=lambda x: x[1]) if best else None


DONOR_MC = (0x10350, 0x10370)   # cgif A/AE39.v mc_bounds: MC_LO = 0x10350 /\ MC_HI = 0x10370 (both images)


def roles(regs, owned, img, mc_bytes=None, stdio=None):
    """the region roles AD1k uses, found by structure (names follow the table's letter order).
    When the image's R_A3 is CUT around owned cells (fuzz_reply: R_A3_1..R_A3_4), the R_A3 role is the
    piece that holds the stdio FILEs -- AD1k uses R_A3 only for img_facts and for stderr's file_is_img -- found from
    the twin's __stdout_FILE / __stderr_FILE."""
    by = {r['name']: r for r in regs}
    a1 = [x for x in regs if x['name'].startswith('R_A1')]
    if 'R_A3' in by:
        a3 = by['R_A3']
    else:
        cands = [x for x in regs if x['name'].startswith('R_A3_')]
        if stdio:
            cands = [x for x in cands if all(x['lo'] <= p and p + 232 <= x['hi'] for p in stdio)]
        assert len(cands) == 1, 'R_A3 is cut and no single piece holds the stdio FILEs: %s' % [x['name'] for x in cands]
        a3 = cands[0]
    r = {'R_A3': a3, 'R_A7b': by['R_A7b'], 'A1': a1}
    # MSG: the A1 regions around the owned 21-byte cell "memory at address %p\0" (cgif R_A1h / R_A1i)
    msg = [o for o in owned if o[1] == 21 and bytes(img.byte(o[0] + k) for k in range(21)) == b'memory at address %p\x00']
    assert len(msg) == 1, 'owned cell "memory at address %%p" not unique: %s' % msg
    hs = [x for x in a1 if x['hi'] == msg[0][0]]
    is_ = [x for x in a1 if x['lo'] == msg[0][0] + 21]
    assert len(hs) == 1 and len(is_) == 1, 'no A1 regions on both sides of the "memory at address" cell'
    r['H'], r['I'] = hs[0], is_[0]
    # MC: the A1 region whose chunk holds mconsts_view's 32 constant bytes
    if mc_bytes is None:
        mc = [x for x in a1 if x['lo'] <= DONOR_MC[0] and DONOR_MC[1] <= x['hi']]
        r['MC'], r['MCAT'] = mc[0], DONOR_MC[0]
    else:
        hits = [(x, a) for x in a1 for a in range(x['lo'], x['hi'] - len(mc_bytes) + 1)
                if x['hi'] - x['lo'] < 4096 and bytes(img.byte(a + k) for k in range(len(mc_bytes))) == mc_bytes]
        assert len(hits) == 1, 'mconsts bytes found %d times in the small A1 regions' % len(hits)
        r['MC'], r['MCAT'] = hits[0]
    # the canary .got chunk: the only multi-chunk R_A2* region, its CImg 8 chunk
    gots = [(x, o) for x in regs if x['name'].startswith('R_A2') and len(x['chunks']) > 1 for o, k in x['chunks'] if k == ('CImg', 8)]
    assert len(gots) == 1, 'canary .got chunk not unique: %s' % [(x['name'], o) for x, o in gots]
    r['GOT'] = gots[0]
    cells = [o for o, k in by['R_A7b']['chunks'] if k[0] == 'CVal' and k[1] == 8 and k[2] == ('SOff', 41, 0)]
    assert len(cells) == 1, cells
    r['CAN'] = cells[0]
    return r


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    for k in ('tmpl_ad1k', 'tmpl_ad2j', 'tmpl_owned', 'tmpl_image', 'ad2j', 'owned', 'image', 'out', 'sites', 'label'):
        ap.add_argument('--' + k.replace('_', '-'), required=True)
    ap.add_argument('--twin', help='symbol extract of the unstripped twin (symbols for the stdio FILEs); without it, their offsets in R_A3 are the donor\'s')
    ap.add_argument('--ns', action='append', default=[])
    ap.add_argument('--modified')
    a = ap.parse_args()
    timg, img = g.Image(a.tmpl_image), g.Image(a.image)
    T = roles(g.template_regions(open(a.tmpl_ad2j).read()), g.owned_static(a.tmpl_owned), timg)
    mcb = bytes(timg.byte(x) for x in range(*DONOR_MC))
    stdio = None
    if a.twin:
        _sy = {n: v for v, sz, n in all_symbols(a.twin)}
        stdio = [_sy['__stdout_FILE'], _sy['__stderr_FILE']]
    N = roles(g.template_regions(open(a.ad2j).read()), g.owned_static(a.owned), img, mcb, stdio)
    tz, nz = zero_shadow(a.tmpl_owned)[0], zero_shadow(a.owned)[0]
    tg, ng = first_global(a.tmpl_image), first_global(a.image)
    assert tz[0] == 0x10000 and tz[0] + tz[1] == tg[0] + (tg[1] // 8) * 8, 'donor zero-shadow range vs first global'
    assert nz[0] == 0x10000 and nz[0] + nz[1] == ng[0] + (ng[1] // 8) * 8, 'zero-shadow range vs first global'

    t = open(a.tmpl_ad1k).read()
    tl = t.split('\n')
    sites = []

    def sub(old, new, count, role, src):
        nonlocal t
        n = t.count(old)
        assert n == count, '%s: %r occurs %d times, expected %d' % (role, old, n, count)
        lines = [i + 1 for i, l in enumerate(tl) if old in l] if '\n' not in old else [i + 1 for i in range(len(tl)) if tl[i] in old.split('\n')[0]]
        t = t.replace(old, new)
        sites.append((lines, old, new, role, src))

    h, i, d, a3 = T['H'], T['I'], T['MC'], T['R_A3']
    nh, ni, nd, na3 = N['H'], N['I'], N['MC'], N['R_A3']
    (tgr, tgo), (ngr, ngo) = T['GOT'], N['GOT']
    sub('img_rd m %s %s /\\ img_rd m %s %s' % (g.hx(h['lo']), g.hx(h['hi']), g.hx(i['lo']), g.hx(i['hi'])),
        'img_rd m %s %s /\\ img_rd m %s %s' % (g.hx(nh['lo']), g.hx(nh['hi']), g.hx(ni['lo']), g.hx(ni['hi'])), 1,
        'img_facts: the A1 regions before / after the owned cell "memory at address %%p" (donor R_A1h / R_A1i; here %s / %s) [lo, hi)' % (nh['name'], ni['name']),
        'AD2j %s, %s (one CImg chunk each)' % (nh['name'], ni['name']))
    sub('img_rd m %d %d /\\ img_rd m %d %d' % (tgo, tgo + 8, a3['lo'], a3['hi']),
        'img_rd m %d %d /\\ img_rd m %d %d' % (ngo, ngo + 8, na3['lo'], na3['hi']), 1,
        'img_facts: canary .got chunk [a, a+8), R_A3 [lo, hi)', 'AD2j %s chunk (CImg 8), R_A3' % ngr['name'])
    for R0, R1 in ((h, nh), (i, ni), (a3, na3)):
        sub('IMG_REGIONS %s %d %d HM)' % (R0['name'], R0['lo'], R0['hi'] - R0['lo']), 'IMG_REGIONS %s %d %d HM)' % (R1['name'], R1['lo'], R1['hi'] - R1['lo']),
            1, 'img_facts: img_rd_of_mem_ok on donor %s (here %s) lo len' % (R0['name'], R1['name']), 'AD2j %s chunk' % R1['name'])
    sub('IMG_REGIONS %s %d 8 HM)' % (tgr['name'], tgo), 'IMG_REGIONS %s %d 8 HM)' % (ngr['name'], ngo), 1,
        'img_facts: img_rd_of_mem_ok on the canary .got chunk (region name follows the table)', 'AD2j %s chunk %d (CImg 8)' % (ngr['name'], ngo))
    sub('mkChunk %d (CVal 8 (SOff 41 0))' % T['CAN'], 'mkChunk %d (CVal 8 (SOff 41 0))' % N['CAN'], 1, 'img_facts: the canary cell chunk of R_A7b', 'AD2j R_A7b chunk')
    sub('change A_canary with (0 + %d)' % T['CAN'], 'change A_canary with (0 + %d)' % N['CAN'], 1, 'img_facts: A_canary = that chunk\'s offset', 'AD2j R_A7b chunk')
    sub('E m 0 %d 8 (SOff 41 0)' % T['CAN'], 'E m 0 %d 8 (SOff 41 0)' % N['CAN'], 1, 'img_facts: val_of_chunk_ok at that chunk', 'AD2j R_A7b chunk')
    sub('IMG_REGIONS %s %d %d HM' % (d['name'], d['lo'], d['hi'] - d['lo']), 'IMG_REGIONS %s %d %d HM' % (nd['name'], nd['lo'], nd['hi'] - nd['lo']), 1,
        'mconsts_of_IMG: the A1 region holding mconsts_view\'s 32 constant bytes (donor R_A1d; here %s); MC_LO..MC_HI here %s..%s '
        '(must equal the relocated AE39 mc_bounds)' % (nd['name'], g.hx(N['MCAT']), g.hx(N['MCAT'] + 32)),
        'AD2j %s chunk; the bytes of donor [0x10350, 0x10370) found once, at %s' % (nd['name'], g.hx(N['MCAT'])))
    sub('file_is_img _ %d %d)' % (a3['lo'], a3['hi']), 'file_is_img _ %d %d)' % (na3['lo'], na3['hi']), 2, 'fwrite/refused sites: R_A3 [lo, hi)', 'AD2j R_A3')
    # ro_img_of_IMG: one CH alternative per R_A1* region
    alt = '| apply (CH %s %d %d); [cbn; tauto | reflexivity | cbn; tauto | cbn; lia | cbn; lia]'
    old = '\n'.join(['[ first [ ' + (alt % (r['name'], r['chunks'][0][0], r['chunks'][0][1][1]))[2:] if j == 0 else alt % (r['name'], r['chunks'][0][0], r['chunks'][0][1][1])
                     for j, r in enumerate(T['A1'])]) + ' ] |]).'
    for r in T['A1'] + N['A1']:
        assert len(r['chunks']) == 1 and r['chunks'][0] == (r['lo'], ('CImg', r['hi'] - r['lo'])), r['name']
    new = '\n'.join(['[ first [ ' + (alt % (r['name'], r['lo'], r['hi'] - r['lo']))[2:] if j == 0 else alt % (r['name'], r['lo'], r['hi'] - r['lo'])
                     for j, r in enumerate(N['A1'])]) + ' ] |]).'
    assert t.count(old) == 1, 'CH block not found'
    l0 = t[:t.index(old)].count('\n') + 1
    t = t.replace(old, new)
    sites.append((list(range(l0, l0 + len(T['A1']))), '%d CH alternatives (%s .. %s)' % (len(T['A1']), T['A1'][0]['name'], T['A1'][-1]['name']),
                  '%d CH alternatives (%s .. %s)' % (len(N['A1']), N['A1'][0]['name'], N['A1'][-1]['name']), 'ro_img_of_IMG: CH r lo len for every R_A1* region', 'AD2j R_A1* (one CImg chunk each)'))
    # zero shadow / hull (AF0m Tfib_zero_shadow first range, first global's beg, R_A1h lo)
    tze, nze = tz[0] + tz[1], nz[0] + nz[1]
    sub('0x10000 (%s - 0x10000)' % g.hx(tze), '0x10000 (%s - 0x10000)' % g.hx(nze), 2, 'rodata_zero_shadow / rodata_shadow_facts: zero-shadow range', 'owned-static file Tfib_zero_shadow, first range')
    sub('(0x10000, %s - 0x10000)' % g.hx(tze), '(0x10000, %s - 0x10000)' % g.hx(nze), 1, 'rodata_zero_shadow: al_zshadow range', 'owned-static file Tfib_zero_shadow, first range')
    sub('%s <= p -> p + n <= %s' % (g.hx(h['lo']), g.hx(tg[0])), '%s <= p -> p + n <= %s' % (g.hx(nh['lo']), g.hx(ng[0])), 2,
        'rodata_hull_zero / rodata_shadow_facts: [lo of donor R_A1h (here %s), first asan global beg)' % nh['name'], 'AD2j %s lo; asan_globals descriptor with the lowest beg' % nh['name'])
    sub('assert (L1 : %s / 8' % g.hx(h['lo']), 'assert (L1 : %s / 8' % g.hx(nh['lo']), 1, 'rodata_hull_zero: lo of donor R_A1h (here %s)' % nh['name'], 'AD2j %s lo' % nh['name'])
    sub('(%s - 1) / 8) by' % g.hx(tg[0]), '(%s - 1) / 8) by' % g.hx(ng[0]), 1, 'rodata_hull_zero: hull bound', 'first asan global beg')
    sub('change (%s / 8) with %d in L1. change ((%s - 1) / 8) with %d in L2.' % (g.hx(h['lo']), h['lo'] // 8, g.hx(tg[0]), (tg[0] - 1) // 8),
        'change (%s / 8) with %d in L1. change ((%s - 1) / 8) with %d in L2.' % (g.hx(nh['lo']), nh['lo'] // 8, g.hx(ng[0]), (ng[0] - 1) // 8), 1,
        'rodata_hull_zero: the quotients', '%s lo / 8; (first global beg - 1) / 8' % nh['name'])
    sub('change ((%d - 65536) / 8) with %d.' % (tze, (tze - 65536) // 8), 'change ((%d - 65536) / 8) with %d.' % (nze, (nze - 65536) // 8), 1,
        'rodata_hull_zero: zero-shadow range end and its granule count', 'Tfib_zero_shadow first range end')
    # restated AD1x / AE* definitions (stdio FILEs, stdout buffer)
    to = int(re.search(r'F_STDOUT = (\d+)\) by reflexivity', t).group(1))
    te = int(re.search(r'F_STDERR = (0x[0-9a-f]+)\) by reflexivity', t).group(1), 16)
    tbuf = int(re.search(r'STDOUT_BUFA = (\d+)\) by reflexivity', t).group(1))
    assert timg.word(to + 88, 8) == tbuf and timg.word(to + 96, 8) == 1024, 'donor F_STDOUT.buf'
    if a.twin:
        syms = all_symbols(a.twin)
        sy = {n: (v, sz) for v, sz, n in syms}
        fo, fe = sy['__stdout_FILE'][0], sy['__stderr_FILE'][0]
        assert sy['__stdout_FILE'][1] == 232 and sy['__stderr_FILE'][1] == 232, 'FILE_SZ 232'
        so, se = 'twin __stdout_FILE = %s (232 bytes)' % g.hx(fo), 'twin __stderr_FILE = %s (232 bytes)' % g.hx(fe)
    else:
        fo, fe = na3['lo'] + (to - a3['lo']), na3['lo'] + (te - a3['lo'])
        so = se = 'R_A3 lo + the donor\'s offset (no twin given)'
    if not a.twin:
        assert (fo - na3['lo'], fe - na3['lo']) == (to - a3['lo'], te - a3['lo']), 'stdio FILEs not at the donor\'s offsets in R_A3'
    assert na3['lo'] <= fo and fo + 232 <= na3['hi'] and na3['lo'] <= fe and fe + 232 <= na3['hi'], 'stdio FILEs outside %s' % na3['name']
    bufa, bsz = img.word(fo + 88, 8), img.word(fo + 96, 8)
    assert bsz == 1024, 'stdout buf_size %r' % bsz
    bobj = containing(syms, bufa) if a.twin else None
    sb = 'image word at __stdout_FILE+88 (FILE.buf)' + (' = %s+%d (%s, %d bytes)' % (bobj[2], bufa - bobj[0], g.hx(bobj[0]), bobj[1]) if bobj else '')
    sub('STDOUT_BUFA = %d) by reflexivity' % tbuf, 'STDOUT_BUFA = %d) by reflexivity' % bufa, 1,
        'tfib_xst_frame: STDOUT_BUFA (restates AD1x/AE*; must equal the relocated value)', sb)
    sub('F_STDOUT = %d) by reflexivity' % to, 'F_STDOUT = %d) by reflexivity' % fo, 1,
        'tfib_xst_frame: F_STDOUT (restates AD1x/AE*; must equal the relocated value)', so)
    sub('F_STDERR = %s) by reflexivity' % g.hx(te), 'F_STDERR = %s) by reflexivity' % g.hx(fe), 2,
        'fwrite/refused sites: F_STDERR (restates AD1x/AE*; must equal the relocated value)', se)
    t = g.header_mod(t, [x.split('=', 1) for x in a.ns], a.modified)
    open(a.out, 'w').write(t)
    ol = t.split('\n')
    rows = ['| %s donor line(s) | out line(s) | old | new | role | AD2j / source |' % a.label, '|---|---|---|---|---|---|']
    for lines, old, new, role, src in sites:
        first = new.split('\n')[0]
        if 'CH alternatives' in first:
            k0 = next(k for k, l in enumerate(ol) if l.startswith('[ first [ apply (CH '))
            outl = list(range(k0 + 1, k0 + 1 + len(N['A1'])))
        else:
            outl = [k + 1 for k, l in enumerate(ol) if first in l]
        rows.append('| %s | %s | `%s` | `%s` | %s | %s |' % (
            ','.join(map(str, lines[:3])) + ('..%d' % lines[-1] if len(lines) > 3 else ''),
            ','.join(map(str, outl[:3])) + ('..%d' % outl[-1] if len(outl) > 3 else ''), old.split('\n')[0][:110], first[:110], role, src))
    rows.append('')
    rows.append('CH alternatives (ro_img_of_IMG), one per R_A1* region of the generated table, `CH name lo len` = its single CImg chunk:')
    rows.append('')
    rows.append('| out line | region | chunk lo | chunk len |')
    rows.append('|---|---|---|---|')
    k0 = next(k for k, l in enumerate(ol) if l.startswith('[ first [ apply (CH '))
    for j, r in enumerate(N['A1']):
        rows.append('| %d | %s | %d | %d |' % (k0 + 1 + j, r['name'], r['lo'], r['hi'] - r['lo']))
    open(a.sites, 'w').write('\n'.join(rows) + '\n')
    print('gen_ad1k: wrote %s (%d sites); table %s' % (a.out, len(sites), a.sites))


if __name__ == '__main__':
    main()
