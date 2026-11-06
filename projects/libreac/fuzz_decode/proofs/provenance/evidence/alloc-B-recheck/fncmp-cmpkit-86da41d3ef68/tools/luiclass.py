#!/usr/bin/env python3
"""luiclass.py -- the settlement class of every lui row (<agent> 18:5xZ classes and the 20:12Z addendum), from luitrace's
traces (scans/luitrace.tsv and scans/luitrace-luiconst.tsv) and the cited contracts (contracts.py). Every USE of V and of
every value derived from it -- in the main trace and in every follow-up, in BOTH images -- gets one class:
  (i)    CALL ARGUMENT: an integer parameter whose pinned-source contract says byte count / length / count / size /
         flags / mode / prot / alignment (contracts.CONTRACT: the declaration and the contract line); a syscall argument
         by the syscall's contract (contracts.SYSCALL_CONTRACT)
  (i-b)  CHECKFAILED VALUE: CheckFailed's v1 / v2 (printed only): the CHECK line (the call's DWARF line in each image)
         and the CheckFailed body (contracts.CONTRACT)
  (ii)   RETURN: the function returns it, an integer and not an address by its meaning (contracts.RETURNS)
  (iii)  DISPLACEMENT: a load / store / AMO base (or a pointer passed / stored) onto an object pointer (an argument, a
         load, an allocator return: luitrace OFFSET-RUNTIME-OBJECT), or onto an image address with the FULL address
         compared as symbol + offset in both images (OFFSET-SAME-SYMBOL)
  (iv)   STORE: stored into an integer, non-address field (contracts.STORES: the struct line)
  (c)    COMPARE: a branch / compare operand
  (d)    FRAME: an sp-derived frame base (`stack frame + c`)
  (e)    DEAD-AT-CALL: the callee never reads the register on any path to its return (deadreg), the trace continued in
         the caller when the callee may hand it back
Not uses (the trace follows them): copies and ALU steps, spills and reloads, a call argument followed INTO its callee (its
uses are classed there: luitrace IN-CALLEE), a value handed back followed INTO each caller (IN-CALLER), a path that ends
at a no-return call, an ecall that does not read the register, an overwrite.
A row SETTLES when: every use in both images has a class; the two images' main traces are the same and the follow-ups
both images have are the same (luitrace `same`); a follow-up only one image has (a caller the other program does not
have) has its uses classed on its own, and its bases are object displacements or frame bases; no follow-up was left at
the depth limit; luitrace's verdict is not DIFFERS / REVIEW / ABSOLUTE-USE. The row's class is the set of its use
classes. Else: NOT CERTIFIED: REAL 0, with the unsettled uses listed.
Writes scans/luiclass.tsv and prints the counts. usage: luiclass.py [TRACE.tsv ..] (default: both trace files)"""
import collections, os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common, contracts

ARGRE = re.compile(r'^ARG (?:call|tail call) (\S+) (\w+) \[param: (.*?)\]( -> passes a pointer)?')
SYSRE = re.compile(r'^SYSCALL (\S+) (.*) \(a7 = (\S+)\)$')
STRE = re.compile(r'^STORE-DATA (.*) into (\S+) \((.*)\)$')


def split_uses(main):
    """'+0x.. INS :: TEXT | TEXT' ;; .. -> [(pc offset, text)]"""
    out = []
    for ent in main.split(' ;; ') if main and main != '-' else []:
        m = re.match(r'^\+(0x[0-9a-f]+|-0x1) (.*?) :: (.*)$', ent)
        if not m:
            out.append((None, ent)); continue
        for t in m.group(3).split(' | '):
            out.append((int(m.group(1), 16), t))
    return out


def split_follow(col):
    """follow-up lines -> [(depth, header, [(pc offset, text)], bases text)]"""
    out = []
    for ln in col.split(' ;; ') if col and col != '-' else []:
        d = (len(ln) - len(ln.lstrip(' '))) // 2
        m = re.match(r'^(IN-CALLE[ER] .*?): (.*)$', ln.strip())
        if not m:
            continue
        hdr, body = m.group(1), m.group(2)
        bases = ''
        if ' ; BASES ' in body:
            body, bases = body.split(' ; BASES ', 1)
        uses = []
        if not body.startswith(('no use', 'a tail call there')):
            for u in body.split(' ; '):
                um = re.match(r'^\+(0x[0-9a-f]+) (.*)$', u)
                uses.append((int(um.group(1), 16) if um else None, um.group(2) if um else u))
        out.append((d, hdr, uses, bases, body))
    return out


def classify(fn, pc, text, img_tag, check_line):
    """one use -> (class or None for a non-use, citation / reason, settled?)"""
    t = text
    if t.startswith('CMP'):
        return '(c)', 'compare operand', True
    if t.startswith('ARG-BEYOND-READ'):
        m = re.match(r'^ARG-BEYOND-READ (\w+) .*?: (\S+) reads it', t)
        cite = contracts.ARGBEYOND.get((m.group(2), m.group(1))) if m else None
        if cite:
            return cite[0], cite[1], True
        return None, 'a callee reads it beyond its signature: %s' % t[:200], False
    if t.startswith('ARG '):
        m = ARGRE.match(t)
        if not m:
            return None, 'unparsed argument use: %s' % t[:160], False
        callee, reg, pt, ptr = m.groups()
        if ptr:
            return '(iii)', 'a pointer passed to %s %s: its full address in the BASE columns' % (callee, reg), True
        c = contracts.lookup(callee, reg)
        if c:
            if c[0] == 'i-b':                        # CheckFailed v1 / v2
                return '(i-b)', 'CheckFailed %s (%s); the CHECK: %s; %s' % (reg, c[1], check_line(fn, pc), c[2]), True
            return '(i)', '%s %s %s: %s' % (callee, reg, c[1], c[2]), True
        return 'FOLLOW-CALLEE', '%s %s [%s]' % (callee, reg, pt), True
    if t.startswith('STORE-DATA'):
        m = STRE.match(t)
        if not m:
            return None, 'unparsed store: %s' % t[:160], False
        role, dst, prov = m.groups()
        if role.startswith('P('):
            return '(iii)', 'a pointer stored into %s: its full address in the BASE columns (`stored:`)' % dst, True
        c = contracts.STORES.get((fn, pc)) or contracts.STORES.get((fn, dst))
        if c:
            return '(iv)', c, True
        return None, 'STORE of %s into %s (%s): no field cited' % (role[:80], dst, prov[:80]), False
    if t.startswith('RET'):
        c = contracts.RETURNS.get(fn)
        if c:
            return '(ii)', c, True
        return 'FOLLOW-CALLERS', 'returned: followed into the callers', True
    if t.startswith('LIVE-AT-RETURN'):
        return 'FOLLOW-CALLERS', 'handed back in a caller-saved register: followed into the callers', True
    if t.startswith('DEAD-AT-CALL'):
        if 'UNKNOWN' in t:
            return None, t if len(t) <= 300 else t[:140] + ' .. ' + t[-160:], False
        return '(e)', t[t.index(':') + 2:][:220], True
    if t.startswith('SYSCALL-IGNORES'):
        return None, 'not read by the syscall', True
    if t.startswith('SYSCALL '):
        m = SYSRE.match(t)
        if not m:
            return None, 'unparsed syscall use: %s' % t[:160], False
        name = m.group(1)
        regs = [x.split('=')[0] for x in m.group(2).split(', ')]
        cites = [contracts.SYSCALL_CONTRACT.get((name, r)) for r in regs]
        if all(cites):
            return '(i)', '; '.join('%s %s %s: %s' % (name, r, c[1], c[2]) for r, c in zip(regs, cites)), True
        return None, 'syscall %s argument %s: no contract cited' % (name, regs), False
    if t.startswith('BASE'):
        if 'P(stack' in t:
            return '(d)', 'an sp-derived frame base', True
        return '(iii)', 'a base: its full address in the BASE columns', True
    if t.startswith('JUMP'):
        return None, 'a jump base: %s' % t[:160], False
    if t.startswith('path ends') or t.startswith(('SPILL', 'RELOAD', 'copy', 'ends')) or ' -> ' in t:
        return None, 'not a use', True
    if t == 'LIMIT':
        return None, 'the trace hit its step limit', False
    return None, 'unclassified: %s' % t[:160], False


def main():
    import dwarfline
    files = sys.argv[1:] or [os.path.join(common.SCANS, 'luitrace.tsv'), os.path.join(common.SCANS, 'luitrace-luiconst.tsv')]
    import escape
    imgs = {'X': escape.Image(common.CGIF_B_TWIN), 'Y': escape.Image(common.DECODE_B_TWIN)}
    starts = {}
    for tag, img in imgs.items():
        img._index()
        starts[tag] = {}
        for a in sorted(img.starts):
            starts[tag].setdefault(img.name_at(a), a)

    def check_line_for(tag):
        path = common.CGIF_B_TWIN if tag == 'X' else common.DECODE_B_TWIN
        return lambda fn, pc: ('%s line %s' % (tag, dwarfline.where(path, starts[tag][fn] + pc))
                               if fn in starts[tag] and pc is not None else '%s ?' % tag)

    rows_out, cnt, ncert = [], collections.Counter(), collections.Counter()
    for fpath in files:
        for l in list(open(fpath))[1:]:
            c = l.rstrip('\n').split('\t')
            member, word, vv, verdict = c[0], c[3], c[4], c[10]
            classes, unsettled, cites = collections.Counter(), [], []
            for tag, main_col, fol_col in (('X', 6, 11), ('Y', 9 if c[9] != 'same' else 6, 13)):
                main = c[main_col][len('DIFFER: '):] if c[main_col].startswith('DIFFER: ') else c[main_col]
                cl = check_line_for(tag)
                fol = split_follow(c[fol_col])
                headers = {e[1] for e in fol}
                entries = [(-1, 'MAIN %s' % member, split_uses(main), '', '')] + fol
                for d, hdr, uses, bases, body in entries:
                    fn = hdr.split(' ')[1]
                    for pc, t in uses:
                        k, why, ok = classify(fn, pc, t, tag, cl)
                        where = '%s %s +%s' % (tag, fn[:60], '%#x' % pc if pc is not None else '?')
                        if not ok:
                            unsettled.append('%s: %s' % (where, why))
                        elif k == 'FOLLOW-CALLEE':
                            callee, reg = why.split(' ')[0], why.split(' ')[1]
                            if not any(h.startswith('IN-CALLEE %s %s ' % (callee, reg)) for h in headers):
                                unsettled.append('%s: argument %s not followed into its callee' % (where, why[:120]))
                        elif k == 'FOLLOW-CALLERS':
                            a = starts[tag].get(fn)
                            if a is None or not imgs[tag].callers(a):
                                unsettled.append('%s: handed back, but %s has no direct caller in this image' % (
                                    where, fn[:60]))
                            elif t.startswith('LIVE-AT-RETURN'):
                                # a caller-saved register left holding the value at a return: each caller's trace
                                # (IN-CALLER) continues from the call; its uses there are classed in their turn
                                classes['(e)'] += 1
                                cites.append('(e) %s: handed back in a caller-saved register, traced on in each of the %d '
                                             'callers (IN-CALLER)' % (where, len(imgs[tag].callers(a))))
                        elif k:
                            classes[k] += 1
                            cites.append('%s %s: %s' % (k, where, why))
            if c[12] != '-':
                unsettled.append('a follow-up was left at the depth limit (4 levels)')
            if verdict in ('DIFFERS', 'REVIEW', 'ABSOLUTE-USE'):
                unsettled.append('luitrace verdict %s (follow-ups: %s)' % (verdict, c[14]))
            for tag, col in (('X', 15), ('Y', 16)):
                for b in (c[col].split(' ;; ') if c[col] != '-' else []):
                    if not b.startswith(('runtime object', 'stack frame', 'passed: runtime object', 'stored: runtime object')):
                        unsettled.append('%s a base in a follow-up only this image has: %s' % (tag, b[:200]))
            settled = not unsettled
            ks = '+'.join(sorted(classes)) or '(none)'
            if settled:
                cnt[ks] += 1
                for k in classes:
                    ncert[k] += 1
            else:
                cnt['NOT CERTIFIED'] += 1
            rows_out.append((member, c[1], word, vv, os.path.basename(fpath), verdict,
                             ks if settled else 'NOT CERTIFIED: REAL 0', ' ;; '.join(cites), ' ;; '.join(unsettled) or '-'))
    with open(os.path.join(common.SCANS, 'luiclass.tsv'), 'w') as f:
        f.write('member\tX addr\tword\tV\ttrace file\tluitrace verdict\tclass (the classes of its uses)\tevery classed use '
                '(class image function +pc: citation)\tunsettled uses\n')
        for r in rows_out:
            f.write('\t'.join(r) + '\n')
    print('rows %d: %s' % (len(rows_out), dict(sorted(cnt.items()))))
    print('settled rows per class (a row counts once in each class its uses have): %s' % dict(sorted(ncert.items())))
    for r in rows_out:
        if r[6].startswith('NOT'):
            print('  NOT CERTIFIED %s %s %s: %s' % (r[0][:60], r[2], r[3], r[8][:300]))


if __name__ == '__main__':
    main()
