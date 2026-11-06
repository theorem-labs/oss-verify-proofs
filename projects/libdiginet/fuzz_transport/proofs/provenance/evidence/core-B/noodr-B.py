#!/usr/bin/env python3
"""noodr-B.py STAGE_OUT DIFF_DIR OUT_PATCH: B-noodr.patch, the donor's ODR-page hunks of B/YD1d.v, YD1e.v, YD1f.v and YD1g.v
reversed, cut against a PATCHES=0-equivalent stage-out (port_core's own provenance line left out, as cutpatch-B.py does).

Why: libreac/fuzz_decode.asan-ubsan's 50 collected hand-off states hold a FOURTH head map, the 4 KiB ODR-registration
page (epg 551), and the released lib/B/YD1d / YD1e / YD1f / YD1g were edited for it (eODR, TFIB_HEAD3 of 4 maps,
musl_maps from index 4, KRange (EVar 551), the a_eager bound 16519168, ODR_extra, the 3 -> 4 index shifts). libdiginet
fuzz_decode.asan-ubsan's 50 hand-off states (its own lib/B/YB01.v) hold NO such page: measure_ad1g.py (sha256
247f39888c46) gives HEAD = [epg 518; epg 501; epg 500] (3 maps), HEAD + TAIL = 15, a_eager max 16515072, as
cgif_file_fuzzer's and fuzz_grant's (measure-ad1g-B.out). So those edits are undone; nothing else changes.

DIFF_DIR holds the four edit diffs of the donor's start-up-shape writer (final.YD1{d,e,f,g}.vsHEAD.diff, sha256 in
measure-ad1g-B.out's header). A hunk is reversed when it is an ODR-page hunk: it adds or removes a line that names
eODR / dODR / uODR / ODR_extra / dODR_val / epg 551 / EVar 551 / 551%nat / 16519168, or shifts a head index 3 -> 4
(`3 + j`, `3 + length (musl_maps ch)`, `length TFIB_HEAD3) with 3`, `i < 3`, musl_maps' `skipn 3` / `- 15`, the HEAD indices 1 / 2 -> 2 / 3), or the
destruct pattern that counts AVIS13's entries. Kept as the donor states them (not ODR hunks): each file's notice lines,
YD1g's Require layout and image window (6184960 = 1510 * 4096 is relocated by port_core), and YD1d's kz_chk 1446400
(= 11571200 / 8, the fake stack's shadow length, in both images). Each reversed hunk's new side must occur exactly once
in the stage-out text (module path libreac -> libdiginet), else the script exits 1. No patch line is a comment line
added by hand; the comment lines the donor added with its ODR code are removed with that code."""
import difflib, os, re, sys

so, dd, outp = sys.argv[1:4]
HEAD = re.compile(r'^\(\* Modified by Theorem Labs, \d{4}-\d{2}: copied from proofs/libreac/fuzz_decode/lib/')
ODR = re.compile(r'eODR|dODR|uODR|ODR_extra|dODR_val|epg 551|EVar 551|551%nat|16519168|ODR-registration|\beODR\b')
SHIFT = re.compile(r'\b[34] \+ (j|length \(musl_maps ch\))|length TFIB_HEAD3\) with [34]%nat|\(i < [34]\)%nat|'
                   r'Nat\.lt_ge_cases i [34]\)|head_band [123] |seps_pair _ S0 [123] [23] |HDx [123]%nat|'
                   r'\(i <> [123]\)%nat|- [34] - length|[34] \+ j - [34]|destruct H13 as|<= [12]\)%nat\)\.$|'
                   r'destruct \(known dODR\)|destruct Hh as \[<-|\(skipn [34] \(a_maps ch\)\)')
fix = lambda s: s.replace('OssFuzzTheorems.Proofs.libreac.fuzz_decode.lib', 'OssFuzzTheorems.Proofs.libdiginet.fuzz_transport.lib')


def hunks(path):
    out, cur = [], None
    for line in open(path).read().split('\n'):
        if line.startswith('@@'):
            cur = []
            out.append(cur)
        elif cur is not None and line[:1] in (' ', '-', '+') and not line.startswith(('---', '+++')):
            cur.append((line[0], fix(line[1:])))
    return out


MASK = re.compile(r'(?<![A-Za-z0-9_])(0x[0-9a-fA-F]+|\d+)(?![A-Za-z0-9_])')


def same(tag, want, have):
    """a changed line must be equal; a context line equal with its numerals masked (port_core relocated them)"""
    return want == have if tag == '+' else MASK.sub('#', want) == MASK.sub('#', have)


res, bad = [], 0
for f in ('YD1d', 'YD1e', 'YD1f', 'YD1g'):
    rel = f'B/{f}.v'
    lines = open(os.path.join(so, rel)).read().split('\n')
    h = [i for i, l in enumerate(lines) if HEAD.match(l)]
    assert len(h) <= 1, (rel, len(h))   # port_core 83f5203d2a2f writes no such line before --patch (item 92)
    text = lines[:h[0]] + lines[h[0] + 1:] if h else lines
    new = list(text)
    nrev = 0
    for hk in hunks(os.path.join(dd, f'final.{f}.vsHEAD.diff')):
        chg = [x for tg, x in hk if tg in '-+']
        if any(l.startswith('(* Modified by') for l in chg):
            continue                                   # notice hunks: inherited lines stay as the donor wrote them
        if not any(ODR.search(l) or SHIFT.search(l) for l in chg):
            continue                                   # Require layout, image window, kz_chk: not the ODR page
        newside = [(tg, x) for tg, x in hk if tg in ' +']
        hits = [i for i in range(len(new) - len(newside) + 1)
                if all(same(tg, x, new[i + k]) for k, (tg, x) in enumerate(newside))]
        if len(hits) != 1:
            print(f'{rel}: ODR hunk new side matches {len(hits)} times: {chg[0][:90]!r}'); bad += 1; continue
        i, rep, k, j = hits[0], [], 0, 0
        while j < len(hk):                             # one change block = a run of '-' / '+' lines
            if hk[j][0] == ' ':
                rep.append(new[i + k]); k += 1; j += 1   # the stage-out's own context line (its relocated numerals)
                continue
            e = j
            while e < len(hk) and hk[e][0] != ' ':
                e += 1
            blk = hk[j:e]
            nplus = sum(tg == '+' for tg, _ in blk)
            if any(ODR.search(x) or SHIFT.search(x) for _, x in blk) or not any(tg == '-' for tg, _ in blk):
                # an ODR block, or a block of added lines only inside an ODR hunk (YD1e's GV_extra at index 1, which the
                # donor added beside ODR_extra at index 0): the text before the donor's ODR edit
                rep += [x for tg, x in blk if tg == '-']
            else:
                rep += new[i + k:i + k + nplus]           # not ODR (e.g. YD1d's kz_chk 1446400): the donor's text stays
            k += nplus
            j = e
        new[i:i + len(newside)] = rep
        nrev += 1
    d = list(difflib.unified_diff([l + '\n' for l in text], [l + '\n' for l in new], fromfile=rel, tofile=rel, n=3))
    res += d
    print(f'{rel}: {nrev} ODR hunk(s) reversed')
open(outp, 'w').write(''.join(res))
sys.exit(1 if bad else 0)
