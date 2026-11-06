#!/usr/bin/env python3
"""gottriage.py - give every row of gotcheck.py's output a measured reason (the triage columns).

  gottriage.py --raw got-cells.raw.tsv --lib LIBDIR --img A=PIN:TWIN --img B=PIN:TWIN --donor-img A=PIN:TWIN
               --donor-lib DONORLIB --out got-cells.tsv

Rows gotcheck accepted (status OK, every perturbation refused) get reason CHECKED with the rules that accepted them.
NOT-ADDRESS rows get the reason gotcheck measured (a length operand, an auipc result). Every other row (FLAG,
UNCHECKED, or OK but a perturbation still accepted) is settled here by a HAND rule; each hand rule MEASURES its fact
from the images and the files when this script runs, and re-judges the row with the value +4 / +8 / -8: the rule must
refuse each perturbed value (printed as `control`). A row no rule settles stays OPEN (the script exits 1).
Triage columns: reason, measurement, result (OK | FINDING), finding_kind, new_value, read_by.
"""
import argparse, csv, os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gotcheck as g


def words(img, lo, hi):
    return [(a, img.cell(a)[1], img.cell(a)[2]) for a in range(lo, hi, 8)]


def fmt(ws):
    return ', '.join('%#x->%s' % (a, g.label(k)) for a, w, k in ws)


def loads(img, fn_lo, fn_size):
    """the .got words that auipc + ld|addi pairs inside [fn_lo, fn_lo + fn_size) compute"""
    t = {}
    for p in range(fn_lo, fn_lo + fn_size, 2):
        t.update({a: q for a, q in img.auipc_targets(p).items() if fn_lo <= q < fn_lo + fn_size})
    return sorted(a for a in t if img.in_got(a))


def fn_at(img, pc):
    return next(((s, sz, n) for s, sz, n in img.syms if s <= pc < s + max(sz, 1) and sz), None)


def own_words(img, dimg):
    """the GOT words of img whose pointee names no word of the donor's GOT (the program's own objects)"""
    dk = [k for k in dimg.keys if k[0] == 'SYM']
    return [img.glo + 8 * i for i, k in enumerate(img.keys) if k[0] == 'SYM' and not any(g.same(k, d) for d in dk)]


class Hand:
    def __init__(self, a):
        self.lib, self.dlib = a.lib, a.donor_lib
        self.imgs = {k: g.Img(*v.split(':'), role=k) for k, v in (x.split('=', 1) for x in a.img)}
        self.dimgs = {k: g.Img(*v.split(':'), role='donor ' + k) for k, v in (x.split('=', 1) for x in a.donor_img)}

    def text(self, rel):
        return open(os.path.join(self.lib, rel.split('lib/', 1)[1])).read()

    # ---- rules: each returns (ok, measurement) for value v of the row; called again with perturbed values ----
    def program_block(self, row, v):
        """the numeral starts (or, in a comment, names) a range [v, hi) of the file's own text that is exactly the
        GOT words whose pointee names no word of the donor's GOT (the program's own objects)"""
        img, dimg = self.imgs[row['image']], self.dimgs[row['image']]
        t = self.text(row['file']).split('\n')[int(row['line']) - 1]
        mm = re.search(r'%s\s*(?:<=\s*a\s*<|\.\.)\s*(0x[0-9a-f]+)' % re.escape(row['value']), t)
        if not mm:
            return False, 'no range [%s, hi) on the line' % row['value']
        hi = int(mm.group(1), 16)
        own = own_words(img, dimg)
        rng = list(range(v, hi, 8))
        ok = rng == own
        return ok, ('the line\'s range [%#x,%#x) holds %s; the GOT words whose pointee is in no word of the donor GOT '
                    '(cgif_file_fuzzer %s) are %s; equal: %s' % (
                        v, hi, fmt(words(img, v, hi)), row['image'], ', '.join('%#x' % x for x in own), ok))

    def block_start(self, row, v):
        """a comment that names a GOT block starting at v: the function at the pc the comment's line names (`helper
        at PC`, `MemToShadow PC`) loads (auipc + ld) exactly the consecutive GOT words that the file's code states as
        one list (v, n, [...])"""
        img = self.imgs[row['image']]
        t = self.text(row['file'])
        mm = re.search(r'\(%s,\s*(\d+),\s*\[' % re.escape(row['value']), t)
        if not mm:
            return False, 'the file states no list (%s, n, [...])' % row['value']
        n = int(mm.group(1))
        line = t.split('\n')[int(row['line']) - 1]
        pm = re.search(r'(?:helper at|MemToShadow)\s+(0x[0-9a-f]+)', line)
        if not pm:
            return False, 'the line names no helper pc'
        fn = fn_at(img, int(pm.group(1), 16))
        if fn is None:
            return False, 'no function at %s' % pm.group(1)
        got = loads(img, fn[0], fn[1])
        want = list(range(v, v + n, 8))
        ok = got == want
        return ok, ('the file states the list (%s, %d, [...]); the function at the line\'s pc %s is %s (%#x, %d bytes); '
                    'it loads by auipc+ld the GOT words %s = %s; equal to [%#x, %#x): %s' % (
                        row['value'], n, pm.group(1), fn[2], fn[0], fn[1], ', '.join('%#x' % x for x in got),
                        fmt(words(img, got[0], got[-1] + 8)) if got else '-', v, v + n, ok))

    def named_cell(self, row, v):
        """the comment calls the word right before the numeral by the pointee's name (`the shadow-base .got word V`)
        and writes the pointee's value after it"""
        img = self.imgs[row['image']]
        t = self.text(row['file']).split('\n')[int(row['line']) - 1]
        i = t.find(row['value'])
        before = t[max(0, i - 30):i].lower()
        c = img.cell(v)
        if c is None:
            return False, 'not in .got'
        nm = [w for w in g.name_words(c[2]) if w.lower() in before]
        stated = re.search(r'shadow-base cell (0x[0-9a-f]+)', t)
        ok = bool(nm) and stated is not None and int(stated.group(1), 16) == c[1]
        return ok, ('the 30 characters before it name %s; the word at %#x is %#x (%s); the comment writes the '
                    'shadow-base cell %s' % (nm or '-', v, c[1], g.label(c[2]), stated.group(1) if stated else '-'))

    def quotes_premise(self, row, v):
        """the comment's interval [v, e) quotes the premise of the file and line it cites, and v's word points into
        the object that holds e"""
        img = self.imgs[row['image']]
        t = self.text(row['file'])
        mm = re.search(r'\[%s, (0x[0-9a-f]+)\) \(:(\d+),\s*(I_\w+\.v):(\d+)\)' % re.escape(row['value']), t)
        if not mm:
            return False, 'no cited interval'
        e = int(mm.group(1), 16)
        cited = []
        for f, ln in (('I_strtolw.v', int(mm.group(2))), (mm.group(3), int(mm.group(4)))):
            p = os.path.join(self.lib, row['file'].split('lib/', 1)[1].split('/')[0], 'Bz', 'A', f)
            cited.append((f, ln, open(p).read().split('\n')[ln - 1].strip()))
        quoted = all(('%#x' % v) in c[2] and ('%#x' % e) in c[2] for c in cited)
        w = img.cell(v)
        se = img.sym(e)
        same_obj = w is not None and se is not None and img.sym(w[1]) is not None and img.sym(w[1])[0] == se[0]
        return quoted and same_obj, ('the cited lines %s; the word at %#x is %#x (%s) and %#x is %s+%#x' % (
            ' | '.join('%s:%d `%s`' % c for c in cited), v, w[1] if w else 0, g.label(w[2]) if w else '-', e,
            '|'.join(sorted(se[0])) if se else '-', se[1] if se else 0))

    # ---- supplements for rows the twin check alone accepted (the A-to-B relay copies a pointee by name, so a twin
    #      agreement cannot see an error made before the relay): each measures the word or the name independently ----
    def field_name(self, row, v):
        """the record field the numeral is assigned to names the pointee (`as_got_shadow := V`)"""
        img = self.imgs[row['image']]
        t = self.text(row['file']).split('\n')[int(row['line']) - 1]
        mm = re.search(r'(\w+)\s*:=\s*%s\b' % re.escape(row['value']), t)
        if not mm or g.name_token(mm.group(1)) is None:
            return False, 'no field name that names a symbol'
        c = img.cell(v)
        res, det = g.name_check(mm.group(1), c[2] if c else None)
        return res in ('MATCH', 'ALIAS'), 'field %s: %s %s; the word at %#x points at %s' % (
            mm.group(1), res, det, v, g.label(c[2]) if c else '-')

    def same_file(self, row, v):
        """another row of the same file with the same value is accepted by a rule that measures the word or the name
        (stated, donor, name, comment WORD / DISASM / NAME)"""
        hits = [x for x in self.rows if x['file'] == row['file'] and int(x['value'], 16) == v and x is not row and (
            x['stated'].startswith('OK') or x['donor'].startswith('SAME') or x['name_check'].split()[0] in ('MATCH', 'ALIAS')
            or x['comment'].split()[0] in ('WORD', 'DISASM', 'NAME'))]
        if not hits:
            return False, 'no other row of the file with %#x is checked by word or name' % v
        h = hits[0]
        why = h['stated'] if h['stated'].startswith('OK') else (h['donor'] if h['donor'].startswith('SAME') else (
            h['name_check'] if h['name_check'].split()[0] in ('MATCH', 'ALIAS') else h['comment']))
        return True, 'the same file states it at :%s (%s)' % (h['line'], why[:160])

    def sibling_stated(self, row, v):
        """the definition is a read-only cell list whose sibling file (RtSM0T.v, the class-0 twin of the stack
        classes) states the same cell with its word, and the word is the image's"""
        img = self.imgs[row['image']]
        p = os.path.join(self.lib, row['file'].split('lib/', 1)[1].rsplit('/', 1)[0], 'RtSM0T.v')
        t = open(p).read()
        mm = re.search(r'\(%#x,\s*\d+,\s*\[\(0,\s*8%%N,\s*(0x[0-9a-f]+|\d+)\)' % v, t)
        c = img.cell(v)
        if not mm or c is None:
            return False, 'RtSM0T.v states no list at %#x' % v
        w = g.num(mm.group(1))
        return w == c[1], 'RtSM0T.v states (%#x, n, [(0, 8%%N, %#x)...]); the image word at %#x is %#x (%s)' % (
            v, w, v, c[1], g.label(c[2]))

    def named_const(self, row, v):
        """the stated words are named constants (A_ASAN_GLOBALS, A_ASAN_GLOBALS_SZ of RtDtorTbl.v); their values equal
        the image words at v and v + 8"""
        img = self.imgs[row['image']]
        d = os.path.join(self.lib, row['file'].split('lib/', 1)[1].rsplit('/', 1)[0], 'RtDtorTbl.v')
        defs = {n: g.num(x) for n, x in re.findall(r'Definition (\w+) : Z := (0x[0-9a-f]+|\d+)\.', open(d).read())}
        a, s = defs.get('A_ASAN_GLOBALS'), defs.get('A_ASAN_GLOBALS_SZ')
        c0, c1 = img.cell(v), img.cell(v + 8)
        ok = c0 is not None and c1 is not None and c0[1] == a and c1[1] == a + s
        return ok, ('RtDtorTbl.v: A_ASAN_GLOBALS = %#x, A_ASAN_GLOBALS_SZ = %d; the image words at %#x, %#x are %s, %s' % (
            a, s, v, v + 8, '%#x (%s)' % (c0[1], g.label(c0[2])) if c0 else '-', '%#x (%s)' % (c1[1], g.label(c1[2])) if c1 else '-'))

    def program_bound(self, row, v):
        """the numeral is a bound of `(... <=? lo) || (hi <=? ...)` whose [lo, hi) is exactly the program's own GOT
        words (as program_block)"""
        img, dimg = self.imgs[row['image']], self.dimgs[row['image']]
        t = self.text(row['file']).split('\n')[int(row['line']) - 1]
        mm = re.search(r'<=\?\s*(0x[0-9a-f]+)\)\s*\|\|\s*\((0x[0-9a-f]+)\s*<=\?', t)
        if not mm:
            return False, 'no bound pair'
        lo, hi = int(mm.group(1), 16), int(mm.group(2), 16)
        role = 'lo' if row['value'] == mm.group(1) else 'hi'
        if role == 'lo':
            lo = v
        else:
            hi = v
        own = own_words(img, dimg)
        ok = list(range(lo, hi, 8)) == own
        return ok, 'the line\'s bound pair [%#x, %#x) (this numeral is its %s) holds %s; the program\'s own GOT words are %s' % (
            lo, hi, role, fmt(words(img, lo, hi)) if hi > lo else '-', ', '.join('%#x' % x for x in own))

    def gotw_bound(self, row, v):
        """the numeral is the GOT word musl's vfprintf loads its stack-protector canary through: RtPFCmd.v's comment
        names the ld's pc, and the auipc + ld there compute v; the word points at __stack_chk_guard"""
        img = self.imgs[row['image']]
        p = os.path.join(self.lib, row['file'].split('lib/', 1)[1].rsplit('/', 1)[0], 'RtPFCmd.v')
        mm = re.search(r'ld s2 at (0x[0-9a-f]+)', open(p).read())
        if not mm:
            return False, 'RtPFCmd.v names no ld pc'
        pc = int(mm.group(1), 16)
        hits = {a: q for a, q in img.auipc_targets(pc - 4).items() if q in (pc - 4, pc - 2)}
        c = img.cell(v)
        ok = v in hits and c is not None and c[2][0] == 'SYM' and '__stack_chk_guard' in c[2][1]
        return ok, 'RtPFCmd.v: `ld s2 at %#x`; the auipc + ld there compute %s; the word at %#x is %s (%s)' % (
            pc, ', '.join('%#x' % a for a in hits) or '-', v, '%#x' % c[1] if c else '-', g.label(c[2]) if c else '-')


SUPPLEMENTS = ['field_name', 'same_file', 'sibling_stated', 'named_const', 'program_bound', 'gotw_bound']

HAND = {  # (file, line, value): (reason, rule)
    ('lib/A/ACeg.v', '25', '0xa7068'): ('PROGRAM-GOT-BLOCK', 'program_block'),
    ('lib/B/YCeg.v', '26', '0xa6bc8'): ('PROGRAM-GOT-BLOCK', 'program_block'),
    ('lib/A/ACeg.v', '4', '0xa7068'): ('PROGRAM-GOT-BLOCK', 'program_block'),
    ('lib/A/Rt/RtSF7.v', '34', '0xa63e8'): ('GOT-BLOCK-START', 'block_start'),
    ('lib/B/Rt/RtSF7.v', '35', '0xa5f48'): ('GOT-BLOCK-START', 'block_start'),
    ('lib/B/Rt/RtSF7.v', '5', '0xa5f48'): ('GOT-BLOCK-START', 'block_start'),
    ('lib/B/Rt/RtSF5.v', '5', '0xa5f48'): ('GOT-BLOCK-START', 'block_start'),
    ('lib/B/Rt/RtSF5.v', '5', '0xa5f50'): ('GOT-CELL-NAMED', 'named_cell'),
    ('lib/A/Rt/RtNumber.v', '100', '0xa63e0'): ('COMMENT-QUOTES-PREMISE', 'quotes_premise'),
}
DONOR_NOTE = {  # the gate's pairing for PROGRAM-GOT-BLOCK rows, measured from the donor file's own line
    'PROGRAM-GOT-BLOCK': 'donor line lib/A/ACeg.v:24 (Y: lib/YCeg.v:24) is `(0x103b0 <= a < 0x103b8) \\/ (0x9ec10 <= a '
                         '< 0x9ec28)`: its second range is cgif\'s own program GOT block; the gate paired our first '
                         'numeral with the donor\'s first (a .rodata constant range ours does not carry)',
}


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--raw', required=True)
    ap.add_argument('--lib', required=True)
    ap.add_argument('--donor-lib', required=True)
    ap.add_argument('--img', action='append', required=True)
    ap.add_argument('--donor-img', action='append', required=True)
    ap.add_argument('--out', required=True)
    a = ap.parse_args()
    H = Hand(a)
    rows = list(csv.DictReader(open(a.raw), delimiter='\t'))
    H.rows = rows
    cols = list(rows[0].keys()) + ['reason', 'measurement', 'result', 'finding_kind', 'new_value', 'read_by']
    cnt, opened = {}, []
    for r in rows:
        key = (r['file'], r['line'], r['value'])
        if key in HAND:
            reason, rule = HAND[key]
            fn = getattr(H, rule)
            v = int(r['value'], 16)
            ok, meas = fn(r, v)
            ctl = []
            for d in (4, 8, -8):
                pok, _ = fn(r, v + d)
                ctl.append('%+d %s' % (d, 'ACCEPTED' if pok else 'refused'))
            meas = '%s; control: %s' % (meas, ', '.join(ctl))
            if reason in DONOR_NOTE and r['in_comment'] == 'no':
                meas += '; ' + DONOR_NOTE[reason]
            good = ok and all(c.endswith('refused') for c in ctl)
            r.update(reason=reason if good else 'OPEN-' + reason, measurement=meas, result='OK' if good else 'OPEN')
            if not good:
                opened.append(key)
        elif r['status'] == 'OK' and r['control'] == 'refused':
            rules = [x for x, ok in (('donor', r['donor'].startswith('SAME')),
                                      ('name', r['name_check'].split()[0] in ('MATCH', 'ALIAS')),
                                      ('stated', r['stated'].startswith('OK')), ('twin', r['twin'].startswith('SAME')),
                                      ('comment-' + r['comment'].split()[0], r['comment'].split()[0] != '-')) if ok]
            meas = 'accepted by %s; +4 / +8 / -8%s refused' % (
                ', '.join(rules), ' / the donor value' if r['donor_value'] != '-' else '')
            reason = 'CHECKED'
            if rules == ['twin']:
                # the twin agreement alone: add a check that measures this image's word or name
                v = int(r['value'], 16)
                sup = None
                for rule in SUPPLEMENTS:
                    fn = getattr(H, rule)
                    try:
                        ok, m = fn(r, v)
                    except FileNotFoundError:
                        continue      # the rule's file (RtSM0T.v, RtDtorTbl.v, RtPFCmd.v) is not beside this file
                    if ok:
                        ctl = ['%+d %s' % (d, 'ACCEPTED' if fn(r, v + d)[0] else 'refused') for d in (4, 8, -8)]
                        sup = (rule, m, ctl)
                        if all(c.endswith('refused') for c in ctl):
                            break
                if sup and all(c.endswith('refused') for c in sup[2]):
                    reason = 'CHECKED-TWIN+' + sup[0].upper().replace('_', '-')
                    meas += '; the twin agreement alone cannot see an error made before the A-to-B relay, so also ' \
                            '%s: %s; control: %s' % (sup[0], sup[1], ', '.join(sup[2]))
                else:
                    reason = 'OPEN-TWIN-ONLY'
                    meas += '; twin only, no supplement settles it%s' % (
                        (' (%s: %s; control %s)' % (sup[0], sup[1], sup[2])) if sup else '')
                    opened.append(key)
            r.update(reason=reason, result='OK' if reason.startswith('CHECKED') else 'OPEN', measurement=meas)
        elif r['status'] == 'NOT-ADDRESS':
            r.update(reason='AUIPC-VALUE' if r['qty'].startswith('the result of the auipc') else 'NOT-ADDRESS-LENGTH',
                     result='OK', measurement=r['qty'] + (' (the file\'s own text)' if 'auipc' not in r['qty'] else
                                                          ' (the instruction word in the image)'))
        else:
            r.update(reason='OPEN', result='OPEN', measurement='no rule settles it')
            opened.append(key)
        r.update(finding_kind='-', new_value='-', read_by='-')
        cnt[r['reason']] = cnt.get(r['reason'], 0) + 1
    with open(a.out, 'w') as f:
        w = csv.DictWriter(f, fieldnames=cols, delimiter='\t', lineterminator='\n')
        w.writeheader()
        w.writerows(rows)
    print('gottriage: %d rows: %s' % (len(rows), ', '.join('%s %d' % kv for kv in sorted(cnt.items()))))
    for r in rows:
        if r['reason'] not in ('CHECKED',):
            print('  %s:%s %s %s: %s' % (r['file'], r['line'], r['value'], r['reason'], r['measurement'][:600]))
    if opened:
        print('gottriage: OPEN rows: %s' % opened)
        sys.exit(1)


if __name__ == '__main__':
    main()
