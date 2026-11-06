#!/usr/bin/env python3
"""layout_growth_classify.py [--image A|B] [--ops OPS.tsv] GRANT_REL KNOCK_REL CLASSES.tsv MEMBERS.tsv -- the DEFINITION of the
GROWN-LAYOUT statement class (the ruling's condition (f); its forms as ruled): each member hunk's diff must reduce to
the class's forms only. --ops writes one row per edit operation (member, form, grant file:lines, knock file:lines, text).

layout_growth_classify.py [--image A|B] --complete PATCHED_REL KNOCK_REL FILE... -- the class's COMPLETENESS check (class review
2, item 4): it diffs each FILE of the PATCHED unit lib (PATCHED_REL/<side>/FILE) against knock's relocated text and
prints every remaining operation that a class form matches: grant's pattern left where knock has the new one, i.e. a
missed member. The class is complete only at 0 (exit 0); any miss exits 1. Its control: a scratch copy with one
member's grant line put back must count exactly 1.

GRANT_REL / KNOCK_REL: the two texts the class compares, both relocated onto the unit's image (GRANT_REL/<side>/<F>:
grant's released text through the core run of record; KNOCK_REL/<side>/<F>: knock's released text through the knock
run), <side> = A or B. CLASSES.tsv: depot_classify.py --consumer's table (it gives each hunk's grant and knock line
range). MEMBERS.tsv: the class table (file, hunk, ...). For each member, the comment-stripped tokens of the grant lines
and of the knock lines of the hunk are diffed (the token form of depot_classify.py, full length), and each edit
operation is matched against the forms below. Per hunk the script prints the forms used and every operation no form
matches (the RESIDUE: a STOP, it goes to the ruling one by one). Exit 0: no residue; exit 1: a residue.

FORMS (first ruling: PE DZ WW RET ARGS; DW from the class review; SECH = condition (g)'s Section header; second
ruling: DPT CLOS PU ABBR BND WLM DXA RETD LYF LEM, with per-member review conditions: DPT / BND reviewed per member with
every instantiation site, LEM taken with its proof, every CLOS `_` solved by unification with no evar left):
  PE    the `exists ly' md', put_effect layout_grow ..` conjunct (an insert naming put_effect layout_grow)
  DZ    DZONE -> DZONE_at_A ly' (or DZONE_at ly')
  WW    W -> W'
  RET   at_RET -> at_RET_at ly' md'
  ARGS  the extra post-Put arguments: ly' Wy md1 and its namings (l / ly' / ly2, W' / Wy / Wz / W2, md' / md1 / mdl /
        mdz / md2), inserted together or one by one
  DW    `(forall a, DZONE_at_A l a -> ~ WIN a) ->` in place of grant's Section fact DZONE_disj, and its uses: the
        premise's name DW / DZW' passed or introduced where grant used `DZONE_disj` / `proj1 (DZONE_disj ..`
  SECH  the new Section header `Variable ly' : alayout` + `Hypothesis LY' / IMG' / DZ'` (+ `Let DZW'`), condition (g)
  DPT   Section `Variable DPOST` gains `alayout -> world tfibsegs -> Model ->` (the type `DPOST ly' W' md'` presupposes)
  WLM   ly -> ly', md0 / md -> md', an inserted W' (the post-Put layout / model / world, like WW)
  BND   binders `(ly' : alayout)` / `(md' : Model)` / `(l : alayout) (W' : world tfibsegs) (md' : Model)` added
  DXA   DX -> DX_at ly' (DX is the complement zone of DZONE; DZ one level up)
  LYF   lyF -> (lyF_at ly'), and knock's `Definition lyF_at (l : alayout) : alayout := set_ly_sec l (rS S) mb`
  RETD  the wrapper `Definition at_RET .. := exists ly' md', at_RET_at ly' md' ..`
  ABBR  inserted `Local Abbreviation N := (@M.N ..)` / `Local Notation N := M.N (only parsing)` lines
  CLOS  an abbreviation's argument list follows the callee's closed Section: arguments deleted (`ly`, `ch`,
        `LY IMG Hsp`, `Hmap_apart`, an `@` / `_`) or added (`B`, `TS`, `_` holes for the callee's new leading arguments)
  PU    a `Proof using ..` / `clear - ..` insert (the R1 class's own form), and names inserted into / replacing the
        name list of a `Proof using` / `clear -` line of the same hunk
  LEM   a new lemma taken from knock with its proof (an insert `Lemma N : .. Qed.`)
  LIN   the YImgTop lineage (rulings (A) / (E1), applied by imgtop_rule.py): `, YImgTop.IMG_LO , YImgTop.IMG_TOP` in
        an unfold list, an `unfold YImgTop.IMG_TOP in H` line, a numeral written as YImgTop.IMG_LO / IMG_TOP
  VAR   a Section `Variable as_const_g2 : asyms -> alayout -> list acell` that knock declares where the Section's text
        names as_const_g2 (class review 2, item 3, as ruled; reviewed per member like DPT / BND)
"""
import difflib, os, re, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from depot_classify import norm_lines, tokens  # noqa: E402

LISTED = {'PE', 'DZ', 'WW', 'RET', 'ARGS', 'DW', 'SECH', 'DPT', 'CLOS', 'PU', 'ABBR', 'BND', 'WLM', 'DXA', 'RETD', 'LYF', 'LEM',
          'LIN', 'VAR'}
P_LY, P_W, P_MD = r"(?:ly'|l|ly2)", r"(?:W'|Wy|Wz|W2)", r"(?:md'|md1|mdl|mdz|md2)"
ID = r"[A-Za-z_][\w'.]*"
FORMS = [
    ('PE', 'insert', None, r".*\bput_effect layout_grow\b.*"),
    ('DZ', 'replace', r"DZONE", r"DZONE_at(?:_A)? ly'"),
    ('WW', 'replace', r"W", r"W'"),
    ('RET', 'replace', r"at_RET", r"at_RET_at ly' md'"),
    ('ARGS', 'insert', None, r"(?:%s %s %s|%s|%s|%s %s)" % (P_LY, P_W, P_MD, P_LY, P_MD, P_LY, P_MD)),
    ('DW', 'insert', None, r"(?:\( forall a , DZONE_at_A l a - > ~ WIN a \) - >|DZW'|DW)"),
    ('DW', 'replace', r"(?:proj1 \( )?DZONE_disj", r"DW|DZW'"),
    ('SECH', 'insert', None, r"(?:<EOS> )?Variable ly' : alayout <EOS> Hypothesis LY' : layout_ok ly' <EOS> "
                             r"Hypothesis IMG' : img_cover ly' <EOS> Hypothesis DZ' : forall a , DZONE_at(?:_A)? ly' a - > .*"),
    ('DPT', 'insert', None, r"alayout - > world tfibsegs - > Model - >"),
    ('WLM', 'replace', r"ly|md0|md", r"ly'|md'"),
    ('WLM', 'insert', None, r"W'"),
    ('BND', 'insert', None, r"(?:\) \( )?(?:ly' : alayout \) \(|ly' : alayout|md'|md' : Model|l : alayout \) \( "
                            r"W' : world tfibsegs \) \( md' : Model \) \()"),
    ('DXA', 'replace', r"DX", r"DX_at ly'"),
    ('LYF', 'replace', r"lyF", r"\( lyF_at ly' \)"),
    ('LYF', 'insert', None, r"(?:<EOS> )?Definition lyF_at \( l : alayout \) : alayout : = set_ly_sec l \( rS S \) mb(?: <EOS>)?"),
    ('RETD', 'insert', None, r"(?:<EOS> )?Definition at_RET \( odd : bool \) \( z : Z \) \( W' : world tfibsegs \) "
                             r"\( c' : config \) : Prop : = exists ly' md' , at_RET_at ly' md' odd z W' c'(?: <EOS>)?"),
    ('ABBR', 'insert', None, r"(?:\) )?(?:<EOS> )?(?:(?:Local )?(?:Abbreviation|Notation) %s : = (?:\( @? ?%s [^()]*\)|%s"
                             r"(?: \( only parsing \))?)(?: <EOS>)? ?)+(?:Local Abbreviation)?" % (ID, ID, ID)),
    ('CLOS', 'delete', r"(?:ly|ch|LY IMG Hsp|Hmap_apart|LY IMG Hsp Hmap_apart|@|_)", None),
    ('CLOS', 'insert', None, r"(?:_(?: _)*|B|TS)"),
    ('PU', 'insert', None, r"(?:<EOS> )?(?:using(?: [\w' ]*?)?(?: <EOS>)?(?: clear - [\w' ]*?)?|clear - [\w' ]*?)(?: <EOS>)?"),
    ('LEM', 'insert', None, r"(?:<EOS> )?Lemma [\w']+ : .* Qed(?: <EOS>)?"),
    ('LIN', 'insert', None, r"(?:, YImgTop\.IMG_LO , YImgTop\.IMG_TOP|, YImgTop\.IMG_TOP|(?:<EOS> )?(?:pose proof [\w']+ as "
                            r"[\w']+ <EOS> )?unfold YImgTop\.IMG_TOP in [\w']+(?: <EOS>)?|unfold YImgTop\.IMG_TOP ;)"),
    ('LIN', 'replace', r"0 x5f5000|0 x10000|6180864|65536", r"YImgTop\.IMG_TOP|YImgTop\.IMG_LO|\( YImgTop\.IMG_TOP - YImgTop\.IMG_LO \)"),
    ('VAR', 'insert', None, r"(?:<EOS> )?Variable as_const_g2 : asyms - > alayout - > list acell(?: <EOS>)?(?: Variable)?"),
]


IDENT = re.compile(r"[A-Za-z_][\w']*")


def in_name_list(ctx, pos):
    """True when knock token ctx[pos] lies inside the name list of a `Proof using` / `clear -` sentence"""
    p = pos - 1
    while p >= 0 and ctx[p] not in ('using', 'clear') and (IDENT.fullmatch(ctx[p]) or ctx[p] == '-'):
        p -= 1
    return p >= 0 and ctx[p] in ('using', 'clear')


def form_of(kind, g, k, ctx=(), pos=None):
    """the form of one edit operation; ctx / pos: the knock tokens of its hunk and the operation's first knock token
    (a name-list edit inside a `Proof using` / `clear -` sentence is PU)"""
    for name, kd, gre, kre in FORMS:
        if kd != kind:
            continue
        if gre is not None and not re.fullmatch(gre, g):
            continue
        if kre is not None and not re.fullmatch(kre, k):
            continue
        return name
    names = lambda s: all(IDENT.fullmatch(x) or x == '-' for x in s.split())
    if kind in ('insert', 'replace') and pos is not None and k and names(k) and names(g) and in_name_list(ctx, pos):
        return 'PU'
    return None


def rng(s):
    a, b = s.rsplit(':', 1)[1].split('-')
    return int(a), int(b)


def hunks_of(f, grel, krel, side, cache):
    """{hunk number: (grant line numbers, knock line numbers)}, numbered as depot_classify.py numbers them"""
    if f not in cache:
        gl = norm_lines(open(os.path.join(grel, side, f)).read())
        kl = norm_lines(open(os.path.join(krel, side, f)).read())
        lm = difflib.SequenceMatcher(None, [l for _, l in gl], [l for _, l in kl], autojunk=False)
        out, h = {}, 0
        for tag, i1, i2, j1, j2 in lm.get_opcodes():
            if tag != 'equal':
                h += 1
                out[h] = ({n for n, _ in gl[i1:i2]}, {n for n, _ in kl[j1:j2]})
        cache[f] = out
    return cache[f]


def complete(side, patched, krel, files):
    """the completeness check: every edit operation still between the PATCHED unit text and knock's relocated text
    that a class form matches is a MISSED member (grant's pattern left where knock has the class's new one)"""
    print('missed: file\tform\tpatched file:lines\tknock file:lines\toperation')
    n = 0
    for f in files:
        pt = open(os.path.join(patched, side, f)).read()
        kt = open(os.path.join(krel, side, f)).read()
        pl, kl = norm_lines(pt), norm_lines(kt)
        ptok, ktok = tokens(pt), tokens(kt)
        lm = difflib.SequenceMatcher(None, [l for _, l in pl], [l for _, l in kl], autojunk=False)
        for tag, i1, i2, j1, j2 in lm.get_opcodes():
            if tag == 'equal':
                continue
            pL, kL = {x for x, _ in pl[i1:i2]}, {x for x, _ in kl[j1:j2]}
            gp = [(t, ln) for t, ln in ptok if ln in pL]
            kp = [(t, ln) for t, ln in ktok if ln in kL]
            gs, ks = [t for t, _ in gp], [t for t, _ in kp]
            sm = difflib.SequenceMatcher(None, gs, ks, autojunk=False)
            for tg, a1, a2, b1, b2 in sm.get_opcodes():
                if tg == 'equal' or all(t in '()' for t in gs[a1:a2] + ks[b1:b2]):
                    continue
                g_, k_ = ' '.join(gs[a1:a2]), ' '.join(ks[b1:b2])
                fm = form_of(tg, g_, k_, ks, b1)
                if not fm or fm == 'LIN':
                    continue
                gln = sorted({ln for _, ln in gp[a1:a2]}) or [gp[a1 - 1][1] if a1 else min(pL, default=0)]
                kln = sorted({ln for _, ln in kp[b1:b2]}) or [kp[b1 - 1][1] if b1 else min(kL, default=0)]
                n += 1
                print('missed\t%s\t%s\t%s:%d-%d\t%s:%d-%d\t%s grant[%s] -> knock[%s]' % (
                    f, fm, f, gln[0], gln[-1], f, kln[0], kln[-1], tg, g_[:300], k_[:300]))
    print('layout_growth_classify --complete: %d file(s); %d missed member operation(s)' % (len(files), n))
    return n


def main():
    args = sys.argv[1:]
    side, OPS = 'A', None
    while args[:1] in (['--image'], ['--ops']):
        if args[0] == '--image':
            side = args[1]
        else:
            OPS = args[1]
        args = args[2:]
    if args[:1] == ['--complete'] and len(args) >= 4:
        sys.exit(1 if complete(side, args[1], args[2], args[3:]) else 0)
    if len(args) != 4:
        sys.exit(__doc__)
    grel, krel, ctsv, mtsv = args
    rows = {}
    for line in open(ctsv).read().splitlines()[1:]:
        p = line.split('\t')
        if len(p) >= 7 and p[1].isdigit():
            rows[(p[0], int(p[1]))] = p
    members = [l.split('\t')[:2] for l in open(mtsv).read().splitlines()[1:] if l.strip()]
    toks, lines = {}, {}
    bad = new = 0
    print('member file\thunk\tgrant lines (relocated)\tknock lines (relocated)\tforms\tlisted\tresidue')
    opsrows = []
    for f, h in members:
        r = rows.get((f, int(h)))
        if r is None:
            print('%s\t%s\t-\t-\tRESIDUE: not in %s' % (f, h, ctsv))
            bad += 1
            continue
        if f not in toks:
            toks[f] = (tokens(open(os.path.join(grel, side, f)).read()), tokens(open(os.path.join(krel, side, f)).read()))
        gL, kL = hunks_of(f, grel, krel, side, lines)[int(h)]
        gp = [(t, ln) for t, ln in toks[f][0] if ln in gL]
        kp = [(t, ln) for t, ln in toks[f][1] if ln in kL]
        gs, ks = [t for t, _ in gp], [t for t, _ in kp]
        if (min(gL, default=None), min(kL, default=None)) != (None if not gL else rng(r[3])[0], None if not kL else rng(r[4])[0]):
            print('%s\t%s\t-\t-\tRESIDUE: hunk numbering differs from %s' % (f, h, ctsv))
            bad += 1
            continue
        sm = difflib.SequenceMatcher(None, gs, ks, autojunk=False)
        forms, left = [], []
        for tag, i1, i2, j1, j2 in sm.get_opcodes():
            if tag == 'equal':
                continue
            g_, k_ = ' '.join(gs[i1:i2]), ' '.join(ks[j1:j2])
            if all(t in '()' for t in gs[i1:i2] + ks[j1:j2]):
                continue
            fm = form_of(tag, g_, k_, ks, j1)
            gln = sorted({ln for _, ln in gp[i1:i2]}) or [gp[i1 - 1][1] if i1 else min(gL, default=0)]
            kln = sorted({ln for _, ln in kp[j1:j2]}) or [kp[j1 - 1][1] if j1 else min(kL, default=0)]
            opsrows.append('%s\t%s\t%s\t%s:%s\t%s:%s\t%s grant[%s] -> knock[%s]' % (
                f, h, fm or 'RESIDUE', f, '-'.join(map(str, (gln[0], gln[-1]))), f, '-'.join(map(str, (kln[0], kln[-1]))),
                tag, g_[:400], k_[:400]))
            if fm:
                forms.append(fm)
            else:
                left.append('%s grant[%s] -> knock[%s]' % (tag, g_[:300], k_[:300]))
        fs = sorted(set(forms))
        unl = [x for x in fs if x not in LISTED]
        bad += bool(left)
        new += bool(unl) and not left
        print('%s\t%s\t%s\t%s\t%s\t%s\t%s' % (f, h, r[3].rsplit(':', 1)[1], r[4].rsplit(':', 1)[1], ' '.join(fs) or '-',
                                          ('NOT-YET-LISTED ' + ' '.join(unl)) if unl else 'listed',
                                          ('RESIDUE: ' + ' || '.join(left)) if left else '-'))
    if OPS:
        open(OPS, 'w').write('member file\thunk\tform\tgrant file:lines (relocated)\tknock file:lines (relocated)\toperation\n'
                             + '\n'.join(opsrows) + '\n')
    print('layout_growth_classify: %d member(s); %d with residue; %d without residue but using a form not yet listed'
          % (len(members), bad, new))
    sys.exit(1 if bad else (2 if new else 0))


if __name__ == '__main__':
    main()
