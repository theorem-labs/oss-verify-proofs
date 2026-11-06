#!/usr/bin/env python3
"""depot_classify.py [--consumer GREPO KREPO] GRANT_LIB KNOCK_LIB CGIF_LIB FILE... -- every difference between fuzz_grant's released kernel text and
libreac/fuzz_knock's released text of each FILE, classed depot / layout-grow / other.

GRANT_LIB: fuzz_grant's released lib at origin/ossv/recipes 4f87de75d67 with lib/Reusable/* at its root (module text
...fuzz_grant.lib.Reusable -> ...fuzz_grant.lib; line numbers are those of lib/Reusable/<F>). KNOCK_LIB: fuzz_knock's
released lib at origin/ossv/recipes 88154566652a (lib/Reusable/<F>, lib/A/...). CGIF_LIB: cgif_file_fuzzer's lib at
c8557374ad2e (the cgif lineage knock's kernel was ported from), one <F> per FILE, flat. FILE: names like YG0r.v.

Method.
1. Both texts are tokenized with comments removed; a unit's module paths become LIB / IMG and the record names
   (GrantB / KnockB / GrantSyms / ...) one placeholder, so only proof text is compared.
2. knock's text is REDUCED to its one-trace configuration (DepotCfg.depot_has_trace = true), the way Rocq reads it:
   `Eval cbv delta [depot_has_trace] iota in`, `if depot_has_trace then T else E` -> T, `depot_pick T E` -> T,
   `lazymatch eval cbv in depot_has_trace with | true => T | false => E end` -> T, `Require ... DepotCfg` -> dropped.
   Every E (the empty-depot alternative) is recorded with its knock lines.
3. The token difference grant -> reduced knock is the RESIDUE: what knock changes outside the switch's own arms.
4. Every line hunk of the plain line diff (comment-stripped lines, original line numbers) is classed:
     depot        the hunk carries no residue: it is the switch (its E arm, the guard, the DepotCfg Require), so with
                  depot_has_trace = true the text is grant's; OR its residue only defines names used nowhere in knock's
                  reduced lib but inside such definitions (support of the empty-depot alternative);
     layout-grow  residue naming the first-Put layout growth (layout_grow, gle_le, KnLayoutGle, KnBlockExt, nb_ext,
                  sb_ext, the ly_NB / ly_SB = 0 sentinel arms, vm_takes, kd_avoid, *_takes);
     other        any other residue: knock's proof or statement text differs from grant's in the one-trace configuration.
   For each 'other' hunk the cgif lineage is read: whether grant's side and / or knock's side occur in cgif's c8557374ad2e
   text (with three tokens of context).
5. Output: a TSV (file, hunk, class, grant lines, knock lines, residue tokens, cgif lineage) on stdout, then per-file counts;
   the extra knock files each file Requires (DepotCfg, KnBlockExt, KnLayoutGle, YC85).
Paths are printed repo-relative.
--consumer GREPO KREPO (lib/A consumers; KNOCK_LIB/A/<F> is knock's text RELOCATED onto the unit's image by port_core, and
GRANT_LIB/<F> the unit's relocated grant text, so numerals compare): a residue that names the empty-depot form (DEPOTNAME:
the knock-only kernel, the depot cells and lemmas, the NB / SB sentinel, ts_hash, TFIB_HEAD3 / TFIB_TR0 ...) is class
depot too, since a consumer carries no switch of its own; GREPO / KREPO are the path prefixes the table prints.
"""
import difflib, os, re, sys
from collections import defaultdict

TOK = re.compile(r"[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*|\d+|\.(?=\s|$)|\S")
MOD = re.compile(r'^OssFuzzTheorems\.Proofs\.\w+\.\w+\.lib(?:\.Reusable)?$')
IMG = re.compile(r'^OssFuzzTheorems\.\w+\.\w+\.images(?:\.\w+)?$')
REC = re.compile(r'^(?:Grant|Knock|Wire|Tfib)(B|Syms|B_syms|B_ok)$')
EXTRA = ('DepotCfg', 'KnBlockExt', 'KnLayoutGle', 'YC85')
GROW = re.compile(r'layout_grow|gle_le|KnLayoutGle|KnBlockExt|nb_ext|sb_ext|vm_takes|kd_avoid|_takes\b|'
                  r'ly_NB ly = \? 0|ly_SB ly = \? 0|ly_NB ly < > 0|ly_SB ly < > 0')
PUNCT = {'<EOS>', ';', '-', '+', '*', '{', '}', '[', ']', '|', 'by', '(', ')'}
USING = re.compile(r'^(?:# \[ using = " [\w ]+ " \] ?)+$')
# names of the empty-depot form (used for consumer hunks, which carry no switch of their own): a residue that names one of
# these is the consumer's side of the depot change
DEPOTNAME = re.compile(r'\b(?:DepotCfg|depot_pick|depot_has_trace|KnBlockExt|KnLayoutGle|YC85|d_mu|s_alloc|s_stored0|s_mtx0|'
                       r'depot_\w+|st_depot|ts_hash|as_dhash|TFIB_HEAD3|eNB|eSB|eGV|TFIB_TR0|tfib_dhash_tr0|TFIB_HASH|'
                       r'tfib_hash_buckets|ly_tr0|HHc|IF_CELLS_H|IF_ZERO_H|if_tab|if_node1|if_store_total|ANB|ASB|ly_NB|ly_SB|'
                       r'kNodesBlockSize|kStoreBlockSize|nb_eager|perm_live|layout_grow\w*|gle_\w+|AR_first_put_facts|'
                       r'ameter_depot_step|lo_vis0_cover|\w+_extents_set|vis0_zones_set|lazy_zones_set|perm_maps_set|'
                       # added by measurement (a build break whose knock fix uses the name): AD3j, knock's depot module
                       # (A/AFis.v:231, A/AFj6.v:232 `The reference AD3j.tfib_dzone_lo was not found`; knock's fix is
                       # `Require Import AD3j`)
                       r'AD3j|'
                       # by measurement: ly_mapped (A/AFem.v:176 `The variable HNS was not found`; knock's fix is the binder
                       # `{HNS : ly_mapped ly}`), top_ok_gle (A/AD26.v:275, A/AD29.v:243 `Hlyle ... expected layout_le`;
                       # knock's fix is top_ok_gle, the grow-then-le reading)
                       r'ly_mapped|top_ok_gle|'
                       # by measurement: HEAD3 / dGV / dSB / dNB (A/AD1g.v:723 `The reference dGV was not found`: knock's fix
                       # drops the depot head maps), HIGH_m (A/AFex.v:618, A/AFfl.v:541: knock's fix uses the NB / SB-mapped
                       # zone fact HIGH_m)
                       r'HEAD3|dGV|dSB|dNB|HIGH_m|'
                       # by measurement: layout_gle* (A/AFet.v:321, A/AFg0.v:262, A/AFg4.v:344, A/AFg5.v:597 `apply
                       # layout_le_refl` fails under the empty-depot acall_post; knock's fix is layout_gle_refl)
                       r'layout_gle\w*)\b')
GREPO = 'proofs/libreac/fuzz_grant/lib/Reusable/'
KREPO = 'proofs/libreac/fuzz_knock/lib/Reusable/'


def decomment(t):
    """the text with every comment replaced by spaces (newlines kept), strings honoured"""
    out, d, i, s = [], 0, 0, False
    while i < len(t):
        two = t[i:i + 2]
        if not s and two == '(*':
            d += 1; out.append('  '); i += 2; continue
        if d and two == '*)':
            d -= 1; out.append('  '); i += 2; continue
        c = t[i]
        if d == 0:
            if c == '"':
                s = not s
            out.append(c)
        else:
            out.append('\n' if c == '\n' else ' ')
        i += 1
    return ''.join(out)


def tokens(t):
    t = decomment(t)
    out = []
    for ln, line in enumerate(t.split('\n'), 1):
        for m in TOK.finditer(line):
            x = m.group(0)
            if x == '.' and (m.end() == len(line) or line[m.end()].isspace()):
                x = '<EOS>'
            elif MOD.match(x):
                x = 'LIB'
            elif IMG.match(x):
                x = 'IMG'
            elif REC.match(x):
                x = 'U' + REC.match(x).group(1)
            elif x == 'DepotCfg.depot_has_trace':
                x = 'depot_has_trace'
            out.append((x, ln))
    return out


def seq(ts, i, words):
    return [t for t, _ in ts[i:i + len(words)]] == words


def group_end(ts, i):
    """index after the balanced group opening at ts[i] ('(' '[' '{'), or after the single token ts[i]"""
    if ts[i][0] not in '([{':
        return i + 1
    d = 0
    for j in range(i, len(ts)):
        if ts[j][0] in '([{':
            d += 1
        elif ts[j][0] in ')]}':
            d -= 1
            if d == 0:
                return j + 1
    raise ValueError('unbalanced group at line %d' % ts[i][1])


def reduce(ts, removed):
    out, i = [], 0
    while i < len(ts):
        t = ts[i][0]
        if seq(ts, i, ['Eval', 'cbv', 'delta', '[', 'depot_has_trace', ']', 'iota', 'in']):
            i += 8
            continue
        if t == 'DepotCfg':                         # a Require list entry
            i += 1
            continue
        if seq(ts, i, ['if', 'depot_has_trace', 'then']):
            j, d, ifs = i + 3, 0, 0
            while True:
                x = ts[j][0]
                if x in '([{':
                    d += 1
                elif x in ')]}':
                    d -= 1
                elif x == 'if' and d == 0:
                    ifs += 1
                elif x == 'else' and d == 0:
                    if ifs == 0:
                        break
                    ifs -= 1
                j += 1
            k, d = j + 1, 0
            while k < len(ts):
                x = ts[k][0]
                if x in '([{':
                    d += 1
                elif x in ')]}':
                    if d == 0:
                        break
                    d -= 1
                elif x == '<EOS>' and d == 0:
                    break
                k += 1
            removed.append(ts[j + 1:k])
            removed.append(('SPAN', ts[i][1], ts[min(k, len(ts) - 1)][1]))
            body = reduce(ts[i + 3:j], removed)
            if out and out[-1][0] == '(' and k < len(ts) and ts[k][0] == ')':
                out.pop()
                k += 1
            out.extend(body)
            i = k
            continue
        if t == 'depot_pick':
            j = group_end(ts, i + 1)
            k = group_end(ts, j)
            a1 = ts[i + 1:j]
            if a1 and a1[0][0] == '(':
                a1 = a1[1:-1]
            removed.append(ts[j:k])
            removed.append(('SPAN', ts[i][1], ts[k - 1][1]))
            out.extend(reduce(a1, removed))
            i = k
            continue
        if seq(ts, i, ['lazymatch', 'eval', 'cbv', 'in', 'depot_has_trace', 'with']):
            j, d, m, br, cur, st = i + 6, 0, 0, {}, None, None
            if ts[j][0] in ('true', 'false') and seq(ts, j + 1, ['=', '>']):
                cur, st = ts[j][0], j + 3
                j += 3
            while True:
                x = ts[j][0]
                if x in '([{':
                    d += 1
                elif x in ')]}':
                    d -= 1
                elif x in ('match', 'lazymatch', 'multimatch'):
                    m += 1
                elif x == 'end':
                    if m == 0 and d == 0:
                        br[cur] = (st, j)
                        break
                    m -= 1
                elif x == '|' and d == 0 and m == 0 and ts[j + 1][0] in ('true', 'false') and seq(ts, j + 2, ['=', '>']):
                    if cur is not None:
                        br[cur] = (st, j)
                    cur, st = ts[j + 1][0], j + 4
                    j += 4
                    continue
                j += 1
            if set(br) != {'true', 'false'}:
                raise ValueError('lazymatch on depot_has_trace at line %d: branches %s' % (ts[i][1], sorted(br, key=str)))
            removed.append(ts[br['false'][0]:br['false'][1]])
            removed.append(('SPAN', ts[i][1], ts[j][1]))
            tb = reduce(ts[br['true'][0]:br['true'][1]], removed)
            i = j + 1
            if [x for x, _ in tb] == ['idtac']:                 # a guard-only step: no tactic in the one-trace text
                if i < len(ts) and ts[i][0] == '<EOS>':
                    i += 1
                continue
            if tb and tb[0][0] == 'exact' and [x for x, _ in out[-3:]] == ['ltac', ':', '('] and i < len(ts) and ts[i][0] == ')':
                del out[-3:]                                     # ltac:(exact t) of the true arm is the term t
                out.extend(tb[1:])
                i += 1
                continue
            out.extend(tb)
            continue
        out.append(ts[i])
        i += 1
    return out


def drop_empty_requires(ts):
    out, i = [], 0
    while i < len(ts):
        w = [x for x, _ in ts[i:i + 5]]
        if w[:4] in (['From', 'LIB', 'Require', 'Import'], ['From', 'LIB', 'Require', 'Export']) and w[4:5] == ['<EOS>']:
            i += 5
            continue
        if w[:3] == ['From', 'LIB', 'Require'] and w[3:4] == ['<EOS>']:
            i += 4
            continue
        out.append(ts[i])
        i += 1
    return out


def norm_lines(t):
    return [(n, ' '.join(l.split())) for n, l in enumerate(decomment(t).split('\n'), 1) if l.strip()]


def defined(ts):
    names = []
    for i, (t, _) in enumerate(ts):
        if t in ('Definition', 'Lemma', 'Fixpoint', 'Theorem', 'Corollary', 'Fact', 'Notation', 'Let') and i + 1 < len(ts):
            names.append(ts[i + 1][0])
    return names


def def_spans(ts):
    """{name: [(start, end)]} of every definition / lemma sentence span (through Qed / Defined for proofs)"""
    sp = defaultdict(list)
    for i, (t, _) in enumerate(ts):
        if t in ('Definition', 'Lemma', 'Fixpoint', 'Theorem', 'Corollary', 'Fact', 'Notation', 'Let') and i + 1 < len(ts):
            j = i
            proof = t in ('Lemma', 'Theorem', 'Corollary', 'Fact')
            while j < len(ts):
                if ts[j][0] == '<EOS>' and (not proof or ts[j - 1][0] in ('Qed', 'Defined', 'Admitted')):
                    break
                j += 1
            sp[ts[i + 1][0]].append((i, j))
    return sp


def main():
    global GREPO, KREPO
    args = sys.argv[1:]
    sub, consumer = 'Reusable', False
    while args and args[0].startswith('--'):
        if args[0] == '--consumer':          # lib/A consumers: both texts relocated onto the unit's image
            consumer, sub = True, 'A'
            GREPO, KREPO = args[1], args[2]
            args = args[3:]
        else:
            sys.exit('depot_classify: unknown option %s' % args[0])
    gl, kl, cl = args[:3]
    files = args[3:]
    # knock's whole released lib, reduced: where each candidate support name is used
    klib, kspans = {}, {}
    for d in ('Reusable', 'A'):
        for f in sorted(os.listdir(os.path.join(kl, d))):
            if f.endswith('.v'):
                klib[d + '/' + f] = drop_empty_requires(reduce(tokens(open(os.path.join(kl, d, f)).read()), []))
                kspans[d + '/' + f] = def_spans(klib[d + '/' + f])
    sw = set()
    for d in ('Reusable', 'A'):
        for f in sorted(os.listdir(os.path.join(kl, d))):
            if f.endswith('.v'):
                ot = tokens(open(os.path.join(kl, d, f)).read())
                for nm, sps in def_spans(ot).items():
                    if any(any(x in ('depot_pick', 'depot_has_trace') for x, _ in ot[a_:b_ + 1]) for a_, b_ in sps):
                        sw.add(nm)
    print('file\thunk\tclass\tgrant (4f87de75d67)\tknock (88154566652a)\tresidue\tcgif c8557374ad2e lineage')
    counts, rows_other = {}, []
    for f in files:
        gt = open(os.path.join(gl, f)).read()
        kt = open(os.path.join(kl, sub, f)).read()
        ct = open(os.path.join(cl, f)).read() if os.path.exists(os.path.join(cl, f)) else ''
        gtok, ktok = tokens(gt), tokens(kt)
        removed = []
        kred = drop_empty_requires(reduce(ktok, removed))
        ctoks = [t for t, _ in tokens(ct)]
        sm = difflib.SequenceMatcher(None, [t for t, _ in gtok], [t for t, _ in kred], autojunk=False)
        res = []
        for tag, i1, i2, j1, j2 in sm.get_opcodes():
            if tag == 'equal':
                continue
            gs, ks = gtok[i1:i2], kred[j1:j2]
            if all(t in '()' for t, _ in gs + ks):
                continue                                    # a pair of parentheses the switch left
            res.append((tag, i1, i2, j1, j2, gs, ks))
        # support names: defined by residue, used in knock's reduced lib only inside support definitions
        cand = set()
        for r in res:
            cand.update(n for n in defined(r[6]) if n not in [t for t, _ in gtok])
        support = set()
        changed = True
        while changed:
            changed = False
            for n in sorted(cand - support):
                ok = True
                for path, ts in klib.items():
                    if n not in {x for x, _ in ts}:
                        continue
                    sp = kspans[path]
                    inside = [(a, b) for m in support | {n} for (a, b) in sp.get(m, [])]
                    for i, (t, _) in enumerate(ts):
                        if t == n and not any(a <= i <= b for a, b in inside):
                            ok = False
                            break
                    if not ok:
                        break
                if ok:
                    support.add(n)
                    changed = True
        gl_lines, kl_lines = norm_lines(gt), norm_lines(kt)
        lm = difflib.SequenceMatcher(None, [l for _, l in gl_lines], [l for _, l in kl_lines], autojunk=False)
        n = {'depot': 0, 'layout-grow': 0, 'other': 0}
        h = 0
        for tag, i1, i2, j1, j2 in lm.get_opcodes():
            if tag == 'equal':
                continue
            h += 1
            gL = [x for x, _ in gl_lines[i1:i2]]
            kL = [x for x, _ in kl_lines[j1:j2]]
            g_rng = (gL[0], gL[-1]) if gL else ((gl_lines[i1 - 1][0] if i1 else 0),) * 2
            k_rng = (kL[0], kL[-1]) if kL else ((kl_lines[j1 - 1][0] if j1 else 0),) * 2
            mine = [r for r in res if any(g_rng[0] <= ln <= g_rng[1] for _, ln in r[5])
                    or any(k_rng[0] <= ln <= k_rng[1] for _, ln in r[6])]
            spans = [x for x in removed if isinstance(x, tuple) and x and x[0] == 'SPAN']
            in_switch = bool(kL) and all(any(s[1] <= ln <= s[2] for s in spans) for ln in kL)
            lin = '-'
            if not mine:
                cls, why = 'depot', 'switch (no residue with depot_has_trace = true)'
            else:
                txt = ' '.join(t for r in mine for t, _ in r[6]) + ' || ' + ' '.join(t for r in mine for t, _ in r[5])
                defs = [d for r in mine for d in defined(r[6])]
                kspan = def_spans(ktok)
                acc = set()
                for _ in range(len(defs) + 1):
                    for d in defs:
                        if d not in acc and any(any(x in sw or x in acc for x, _ in ktok[a_:b_ + 1] if x != d)
                                                for a_, b_ in kspan.get(d, [])):
                            acc.add(d)
                punct = all([x for x, _ in r[5] if x not in PUNCT] == [x for x, _ in r[6] if x not in PUNCT] for r in mine)
                attr = all(not r[5] and USING.match(' '.join(x for x, _ in r[6])) for r in mine)
                detail = '; '.join('%s grant[%s] -> knock[%s]' % (r[0], ' '.join(t for t, _ in r[5])[:160],
                                                                 ' '.join(t for t, _ in r[6])[:160]) for r in mine)
                if punct and in_switch:
                    cls, why = 'depot', 'true arm restated (sentences joined by ; and bullets as [ | ] inside the switch): '
                elif attr:
                    cls, why = 'depot', '#[using] attribute of a switch-picked definition: '
                elif defs and all(not r[5] for r in mine) and all(d in support for d in defs):
                    cls, why = 'depot', 'support of the empty-depot alternative (%s: used only there): ' % ', '.join(defs)
                elif defs and all(not r[5] for r in mine) and all(d in acc for d in defs) and not GROW.search(txt):
                    cls, why = 'depot', 'switch accessor (%s: states or proves through a switch-picked name): ' % ', '.join(defs)
                elif consumer and DEPOTNAME.search(txt):
                    cls, why = 'depot', 'names the depot form (%s): ' % DEPOTNAME.search(txt).group(0)
                elif GROW.search(txt):
                    used = [d for d in defs if d not in support]
                    cls, why = 'layout-grow', ('first-Put layout growth; names used in the one-trace configuration: %s: '
                                               % (', '.join(used) or 'none'))
                else:
                    cls, why = 'other', ('punctuation only, outside a switch: ' if punct else '')
                why += detail
                lin = '-'
                if cls == 'other':
                    def occurs(side):
                        for r in mine:
                            s = [t for t, _ in (r[5] if side == 'g' else r[6])]
                            if not s:
                                continue
                            src = gtok if side == 'g' else kred
                            a = r[1] if side == 'g' else r[3]
                            b = r[2] if side == 'g' else r[4]
                            ctx = [t for t, _ in src[max(0, a - 3):b + 3]]
                            if not any(ctoks[k:k + len(ctx)] == ctx for k in range(len(ctoks) - len(ctx) + 1)):
                                return False
                        return True
                    gi, ki = occurs('g'), occurs('k')
                    lin = ('knock = cgif, grant changed' if ki and not gi else 'grant = cgif, knock changed' if gi and not ki
                           else 'both = cgif' if gi and ki else 'neither = cgif')
            n[cls] += 1
            print('%s\t%d\t%s\t%s%s:%d-%d\t%s%s:%d-%d\t%s\t%s' % (f, h, cls, GREPO, f, g_rng[0], g_rng[1], KREPO, f,
                                                                 k_rng[0], k_rng[1], why.replace('\t', ' '), lin))
        counts[f] = (h, n)
    print()
    for f, (h, n) in counts.items():
        req = [e for e in EXTRA if re.search(r'Require[^.]*\b%s\b' % e, decomment(open(os.path.join(kl, sub, f)).read()))]
        print('%s: %d hunks: depot %d, layout-grow %d, other %d; Requires of knock-only files: %s'
              % (f, h, n['depot'], n['layout-grow'], n['other'], ' '.join(req) or '-'))
    tot = {c: sum(n[c] for _, n in counts.values()) for c in ('depot', 'layout-grow', 'other')}
    print('total: %d hunks: depot %d, layout-grow %d, other %d' % (sum(h for h, _ in counts.values()), tot['depot'],
                                                                   tot['layout-grow'], tot['other']))


if __name__ == '__main__':
    main()
