#!/usr/bin/env python3
"""Validate the rewriter: relocate fm 3e35620c52e text with NO numeral substitution for every class a/b/c
route file (the route table), both targets, and classify every changed line.  Only header / Require /
module-path / renamed-name / zify-flag `Local` lines may change, and the YImgTop hook line may be added; any other
changed line is counted as `other` and listed.  Comments are never changed.

  python3 validate.py --routes ROUTES --out-dir DIR [--wt WORKTREE]   writes DIR/<target>.tsv and prints the counts

Second check (boxreg's validate.sh method): the hand relocations already in disco that came from one fm file
(P3's lib/{A,B}/RT_gxa_inst.v) against the tool's no-numeral text: what is left must be numerals.
New version of the G9 tool's validate.py of record (sha256 ce6b6d27a8a2...): the route table (columns `fm path (lib/)`
and `class`) and the output directory are arguments instead of paths beside the script.
"""
import os, re, sys, csv, difflib, collections, argparse
TOOLDIR = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, TOOLDIR)
import reloc

HEX = re.compile(r'0x[0-9a-fA-F]+|\b\d{5,}\b')


def req_flags(lines):
    """Per line: is it part of a Require statement?"""
    flags = [False] * len(lines)
    i = 0
    while i < len(lines):
        s = lines[i]
        if (s.startswith('From ') and ' Require' in s) or s.startswith('Require '):
            j = i
            while not lines[j].rstrip().endswith('.') and j + 1 < len(lines):
                j += 1
            for k in range(i, j + 1):
                flags[k] = True
            i = j + 1
            continue
        i += 1
    return flags


def name_tokens(target):
    cfg = reloc.TARGETS[target]
    toks = [d for _, _, d in cfg['record']] + [m for _, m, _ in cfg['record']]
    toks += [b for _, b in reloc.COMMON_IDENT] + [v.rsplit('.', 1)[1] for v in cfg['core'].values()]
    toks += [v.rsplit('.', 1)[1] for v in list(reloc.COMMON.values()) + list(cfg['rename'].values())]
    return set(toks)


def old_tokens(target):
    cfg = reloc.TARGETS[target]
    return set(['RT_IImgA'] + [n for n, _, _ in cfg['record']] + [a for a, _ in reloc.COMMON_IDENT] +
               list(cfg['core']) + list(reloc.COMMON) + list(cfg['rename']))


def masker(target):
    """Mask module prefixes and every old/new renamed name: a pure rename line masks to the same text."""
    toks = sorted(name_tokens(target) | old_tokens(target), key=len, reverse=True)
    rx = re.compile(r'(?<![\w])(?:%s)(?![\w])' % '|'.join(re.escape(t) for t in toks))
    pfx = re.compile(r'(?:%s|%s)[A-Za-z0-9_.]*' % (re.escape(reloc.SRCPFX), re.escape(reloc.DSTPFX)))
    return lambda s: rx.sub('NAME', pfx.sub('PATH', s))


def classify(target, old, new):
    ol, nl = old.split('\n'), new.split('\n')
    of, nf = req_flags(ol), req_flags(nl)
    mask = masker(target)
    c = collections.Counter()
    bad = []
    sm = difflib.SequenceMatcher(a=ol, b=nl, autojunk=False)
    for op, i1, i2, j1, j2 in sm.get_opcodes():
        if op == 'equal':
            continue
        # lines outside Require statements must pair one to one and agree once paths and names are masked
        oo = [ol[i] for i in range(i1, i2) if not of[i]]
        nn = [(j, nl[j]) for j in range(j1, j2) if j != 0 and not nf[j]]
        c['hook'] += sum(1 for j, s in nn if s == reloc.IMG_HOOK)
        nn = [(j, s) for j, s in nn if s != reloc.IMG_HOOK]
        if j1 == 0 and j2 > 0:
            c['header'] += 1
        c['require'] += sum(1 for j in range(j1, j2) if nf[j])
        if len(oo) == len(nn):
            for o, (j, s) in zip(oo, nn):
                if s == 'Local ' + o and reloc.ZIFY_FLAG.match(o):
                    c['local'] += 1
                elif mask(o) != mask(s):
                    c['other'] += 1
                    bad.append('%d: %s => %s' % (j + 1, o, s))
                elif reloc.DSTPFX in s:
                    c['path'] += 1
                else:
                    c['name'] += 1
        else:
            c['other'] += max(len(oo), len(nn))
            bad += ['-%s' % o for o in oo] + ['+%d: %s' % (j + 1, s) for j, s in nn]
    return c, bad


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--wt', default=os.environ.get('WT', os.getcwd()))
    ap.add_argument('--routes', required=True, help='route table: columns `fm path (lib/)` and `class`')
    ap.add_argument('--out-dir', required=True)
    a = ap.parse_args()
    rows = [r for r in csv.DictReader(open(a.routes), delimiter='\t') if r['class'] in ('a', 'b', 'c')]
    os.makedirs(a.out_dir, exist_ok=True)
    for target in sorted(reloc.TARGETS):
        tot = collections.Counter()
        files = collections.Counter()
        with open(os.path.join(a.out_dir, target + '.tsv'), 'w') as fh:
            fh.write('fm file\tclass\theader\trequire\tpath\tname\tlocal\tother\tSTOP modules\tunexpected lines\n')
            for r in rows:
                f = r['fm path (lib/)'][2:-2]
                reloc.set_target(target)
                old = reloc.fm_text(f)
                new = reloc.relocate(old, {}, '(* HEADER *)')
                stops = sorted(k for k, v in reloc.NOTES.items() if v.startswith('STOP'))
                c, bad = classify(target, old, new)
                for k, v in c.items():
                    tot[k] += v
                files['files'] += 1
                files['class ' + r['class']] += 1
                if stops:
                    files['files naming a STOP module'] += 1
                if c['other'] or c['other-removed']:
                    files['files with other lines'] += 1
                fh.write('%s\t%s\t%d\t%d\t%d\t%d\t%d\t%d\t%s\t%s\n' % (
                    f, r['class'], c['header'], c['require'], c['path'], c['name'], c['local'],
                    c['other'] + c['other-removed'], ','.join(stops) or '-', ' | '.join(bad)[:2000]))
        print('%s: %s; changed lines %s' % (target, dict(files), dict(tot)))
    # hand relocation check
    for target, img in (('disco-A', 'A'), ('disco-Y', 'B')):
        p = os.path.join(a.wt, reloc.DST_UNIT, 'lib', img, 'RT_gxa_inst.v')
        if not os.path.exists(p):
            print('%s: %s absent, skipped' % (target, p))
            continue
        reloc.set_target(target)
        new = reloc.relocate(reloc.fm_text('RT_gxa_inst'), {}, '(* HEADER *)').split('\n')[1:]
        hand = [l for l in open(p).read().split('\n') if not l.startswith('(* Copied from')]
        d = [l for l in difflib.unified_diff(hand, new, lineterm='', n=0) if l[:1] in '+-' and l[:3] not in ('+++', '---')]
        nonnum = [l for l in d if HEX.sub('N', l[1:]) not in {HEX.sub('N', x[1:]) for x in d if x[0] != l[0]}]
        print('%s: tool vs P3 hand lib/%s/RT_gxa_inst.v: %d differing lines, %d not explained by numerals%s' % (
            target, img, len(d), len(nonnum), (': ' + ' | '.join(nonnum)) if nonnum else ''))


if __name__ == '__main__':
    main()
