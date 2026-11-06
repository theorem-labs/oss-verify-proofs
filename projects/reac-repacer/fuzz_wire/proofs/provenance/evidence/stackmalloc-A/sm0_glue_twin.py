#!/usr/bin/env python3
"""sm0_glue_twin.py GRANT_SM0 GRANT_AF0S KNOCK_AF0S OUT -- the class-0 knock twin of A/Rt/StackMalloc0.v for the glue
(the unit owner's ruling, 2026-10-31 17:36Z): fuzz_knock links class 1 only, so no released knock file carries a class-0
SZ step on the empty-depot kernel. The glue takes knock's released class-1 line instead.

GRANT_SM0 / GRANT_AF0S: the unit's relocated grant texts of A/Rt/StackMalloc0.v and A/Rt/AF0s.v. KNOCK_AF0S:
fuzz_knock's released lib/A/AF0s.v relocated onto the unit's image by port_core (the knock run's flags).
The SZ step is the line `{ unfold owned_extents in Hex. cbn [In] in Hex. decompose [or] Hex; subst; cbn [snd];`.
It refuses (exit 1, nothing written) unless:
  - that line occurs exactly once in GRANT_SM0 and exactly once in GRANT_AF0S, byte-equal (the two grant files share it);
  - KNOCK_AF0S has exactly one line that is that line with `try destruct (ly_NB ly =? 0); try destruct (ly_SB ly =? 0); `
    inserted before `cbn [snd];`, and nothing else on it changed (knock's released AF0s.v:74, which the relocation
    leaves byte-equal: it holds no address).
OUT is GRANT_SM0 with that one line replaced by knock's line: the twin that depot_classify.py --consumer and
depot_apply.py --consumer read as KNOCK_LIB/A/Rt/StackMalloc0.v, so that the take is depot_apply's, one hunk, with its
patch."""
import sys

GRANT_LINE = '{ unfold owned_extents in Hex. cbn [In] in Hex. decompose [or] Hex; subst; cbn [snd];'
INSERT = 'try destruct (ly_NB ly =? 0); try destruct (ly_SB ly =? 0); '


def main():
    gsm0, gaf0s, kaf0s, out = sys.argv[1:5]
    S = open(gsm0, encoding='utf-8').read().split('\n')
    A = open(gaf0s, encoding='utf-8').read().split('\n')
    K = open(kaf0s, encoding='utf-8').read().split('\n')
    want = GRANT_LINE.replace('cbn [snd];', INSERT + 'cbn [snd];')
    hs = [i for i, l in enumerate(S) if l == GRANT_LINE]
    ha = [i for i, l in enumerate(A) if l == GRANT_LINE]
    hk = [i for i, l in enumerate(K) if l == want]
    errs = []
    if len(hs) != 1:
        errs.append('the SZ line occurs %d times in %s' % (len(hs), gsm0))
    if len(ha) != 1:
        errs.append('the SZ line occurs %d times in %s' % (len(ha), gaf0s))
    if len(hk) != 1:
        errs.append("knock's SZ line occurs %d times in %s" % (len(hk), kaf0s))
    if errs:
        sys.exit('sm0_glue_twin: REFUSED, nothing written: ' + '; '.join(errs))
    T = list(S)
    T[hs[0]] = K[hk[0]]
    open(out, 'w', encoding='utf-8').write('\n'.join(T))
    print('sm0_glue_twin: StackMalloc0.v line %d (byte-equal to AF0s.v line %d) <- knock AF0s.v line %d: %s'
          % (hs[0] + 1, ha[0] + 1, hk[0] + 1, K[hk[0]]))


if __name__ == '__main__':
    main()
