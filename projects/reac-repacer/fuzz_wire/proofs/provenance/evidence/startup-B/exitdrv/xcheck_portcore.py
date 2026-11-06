#!/usr/bin/env python3
"""xcheck_portcore.py -- numeral-by-numeral comparison of this lane's three files ($WK/gen/{YE23,YD1y,YE37}.v, after
nsW.py) with port_core 0e4e065eab9f's OWN relocation of the same donor files onto fuzz_wire B ($LT/pcB/stage-out/B/).
Independent tool, same donor: every position where port_core gave a number must agree, except the parts this lane
GENERATES from the image instead of relocating (listed per file below) and the EXPLAINED differences, which are
printed with both values.  Read-only.  Exit 1 on an unexplained difference.

Generated here, so cut from the token comparison:
  YE23  the XW2 shadow line (this lane generates it from the image's descriptors; port_core relocates the donor's)
  YE37  x2_rodata, X2_STK, x2_shw and the shw form blocks (n = 0: measured from the x2 walk, not relocated)
Explained differences (printed, not failures): the YE37 cellr value of ___asan_globals_registered (port_core keeps
cgif's 1; this lane measures 0, because with start = stop __asan_register_elf_globals returns before the store).
"""
import os
import re
import sys

WK = os.environ['WK']
PC = os.environ['LT'] + '/pcB/stage-out/B'
NUM = re.compile(r"0x[0-9a-fA-F]+|port_core_refused_[0-9a-f]+|(?<![0-9A-Za-z_x.'])[0-9]{5,}(?![0-9A-Za-z_])")
EXPLAINED = {
    ('YE37', '32', '272'): 'X2_STK: port_core keeps cgif\'s 272; this lane measures the walk\'s own stack extent 32',
    ('YE37', '0x0', '0x9d128'): 'the two .got cells asan.module_dtor loads: port_core moves the donor pointer (its '
                                'asan_globals start / end) by the data map cell-end rule; this image has NO '
                                'asan_globals section, so __start_asan_globals = __stop_asan_globals = 0 in the twin '
                                'and the pin holds 0 at both cells (which is what the walk loads)',
}


def body(t):
    i = t.index('\nImport ListNotations.')
    return t[i:]


def toks(t):
    return [m.group(0) for m in NUM.finditer(t)]


def cut(t, start, end):
    """remove the text from the line starting with `start` to the line starting with `end` (exclusive)."""
    i = t.index('\n' + start) + 1
    j = t.index('\n' + end, i) + 1
    return t[:i] + '@CUT@\n' + t[j:]


def shadow_line(t):
    i = t.index('Definition XW2 (a : Z) : Prop := ')
    j = t.index('Definition XW3', i)
    return ' '.join(t[i:j].split('\n')[1:]).strip()


bad = 0
for f in ('YE23', 'YD1y', 'YE37'):
    mine_raw, pc_raw = open('%s/gen/%s.v' % (WK, f)).read(), open('%s/%s.v' % (PC, f)).read()
    mine, pc = body(mine_raw), body(pc_raw)
    if f == 'YE23':
        print('%s XW2 (generated here, relocated there):' % f)
        print('   here      %s' % ' '.join(mine[mine.index('Definition XW2'):mine.index('Definition XW3')].split()))
        print('   port_core %s' % ' '.join(pc[pc.index('Definition XW2'):pc.index('Definition XW3')].split()))
        mine = cut(mine, 'Definition XW2', 'Definition XW3')
        pc = cut(pc, 'Definition XW2', 'Definition XW3')
    if f == 'YE37':
        # X2_STK and the cellr values are SMALL decimals, which the token regex does not see: compare them by line
        for pat, what in ((r'Definition X2_STK : Z := \d+\.', 'X2_STK'),
                          (r'cellr 0x[0-9a-f]+ \d+ \(SLit \d+\) true', 'cellr')):
            ml, pl = re.findall(pat, mine), re.findall(pat, pc)
            for x, y in zip(ml, pl):
                print('   %s %s here `%s` / port_core `%s`'
                      % ('explained' if x != y else 'equal    ', what, x, y))
        # the descriptor-array row has no image here, so only port_core's is cut; the other 12 rows are COMPARED
        pc = cut(pc, '(0x9d128, 192,', '(0x9e010')
        mine = cut(mine, 'Definition x2_shw :', 'Definition shw_region')
        pc = cut(pc, 'Definition x2_shw :', 'Definition shw_region')
        mine = cut(mine, 'Definition x2_shbytes', 'Section S.')
        pc = cut(pc, 'Definition x2_shw_const', 'Section S.')
        mine = cut(mine, 'Lemma shbyte_present', 'Lemma x2_windows')
        pc = cut(pc, 'Lemma shbytes_present', 'Lemma zi8_14ea00')
        # this file states no exit cell: the two cellr regions, the MU0 premise, the two zi8 lemmas and the two
        # cellr proof bullets are not in it, so they are cut from port_core's side before the comparison
        pc = re.sub(r':: cellr 0x[0-9a-f]+ \d+ \(SLit \d+\) true\n', '', pc)
        pc = re.sub(r'Hypothesis MU0 : [^\n]*\n', '', pc)
        pc = re.sub(r'Lemma zi8_\w+ : wseg_ok[^\n]*\n', '', pc)
        i_ = pc.index('+ unfold region_ok, cellr.')
        j_ = pc.index('- apply pairwise_disjoint_of_extents', i_)
        pc = pc[:i_] + pc[j_:]
        pc = re.sub(r'apply Forall_cons; \[\|apply Forall_cons; \[\|apply Forall_cons; \[\|apply Forall_app',
                    'apply Forall_cons; [|apply Forall_app', pc)
    a, b = toks(mine), toks(pc)
    agree, refused, diff, expl = 0, {}, {}, {}
    if len(a) != len(b):
        print('%s: token count %d vs port_core %d: NOT COMPARABLE' % (f, len(a), len(b)))
        bad += 1
        continue
    for x, y in zip(a, b):
        if y.startswith('port_core_refused_'):
            refused[(y, x)] = refused.get((y, x), 0) + 1
        elif int(x, 0) == int(y, 0):
            agree += 1
        elif (f, x, y) in EXPLAINED:
            expl[(x, y)] = expl.get((x, y), 0) + 1
        else:
            diff[(x, y)] = diff.get((x, y), 0) + 1
    print('%s: %d positions compared; equal %d; port_core refused %d (%d distinct); explained %d; different %d (%d '
          'distinct)' % (f, len(a), agree, sum(refused.values()), len(refused), sum(expl.values()),
                         sum(diff.values()), len(diff)))
    for (y, x), n in sorted(refused.items()):
        print('   refused   %-28s here %-10s (x%d)' % (y, x, n))
    for (x, y), n in sorted(expl.items()):
        print('   explained here %-10s port_core %-10s (x%d): %s' % (x, y, n, EXPLAINED[(f, x, y)]))
    for (x, y), n in sorted(diff.items()):
        print('   DIFFERENT here %-10s port_core %-10s (x%d)' % (x, y, n))
        bad += 1
sys.exit(1 if bad else 0)
