#!/usr/bin/env python3
"""Code identity of the G9 route functions, fm image against each fuzz_disco image, judged by the comparison kit of
record (86da41d3ef68) and, as first recorded, by the kit it supersedes (4bbd3a74be89).

  codeid_kit.py OLD_KIT NEW_KIT PAIRS FM_TWIN FM_PIN [--measure TABLE ...] [--review TABLE ...] [--luiscan TABLE]
                --addrsite TABLE --trace TABLE TAG=TWIN:PIN ...  > codeid-kit.tsv

OLD_KIT / NEW_KIT: directories that hold exactly the files of each kit (its SHA256SUMS is checked; the kit id is the
first 12 hex of sha256(SHA256SUMS)). PAIRS: pairs.tsv (the function list and pairing, columns `<TAG> addr` / `<TAG>
size` per image). FM_TWIN / TWIN: the unstripped images (the kits read their .symtab); FM_PIN / PIN: the stripped
images of record. The header names each image's twin and pin sha256 and checks that PT_LOAD 2..4 of twin and pin are
byte-equal; the kit's own `twins` line is added beside it.

Every paired function is compared BY ADDRESS (the pair of PAIRS), after the symbol at each address is checked to carry
the function's name (or its alias) and the record's size:
  - old kit: strictcmp2 tcmp (its word compare and target lists in the first columns; `=` only with no differing
    target) and, where tcmp is not `=` with the same words up to immediates, its jtcheck 824905e26211;
  - new kit: strictcmp3 tcmp (combined verdict, never written `=`), the full list of its differing targets, and, where
    it is not EQUAL / EQUAL-mod-pcrel with the same words, its jtcheck 8b0ea3862423.
Every differing target of the NEW kit's full list (taken from the call, never from printed lines) is settled by its
jtcheck (judged, and the word left open in none of its lines), else by a hand measurement (--measure: regdef.py and
luiuse.py tables, settling the offsets their `what the instruction does` does not call not settled), else it is open;
`certified` only with no open target. --review: fresh reviewer verdicts (columns image, fm function, reviewer verdict,
what the reviewer checked), joined per function and image; a row any reviewer sends back is not certified. --luiscan:
the kit's luiscan output; its exposure for the two compared copies goes into a column. --addrsite: an addrsite.py
table (every site where a value built from an immediate word may reach a base, and every store of such a value to
memory the scan does not follow); --trace: the hand trace of those sites (columns function, kind, site, class,
reviewer verdict, ...). A function with such a site is certified only when every one of its sites has a hand trace of
class stack address, same object up to relocation, pointer plus offset, numeric bias, call argument not read or not an
address, and the reviewer verdict CONFIRM; a function addrsite.py could not scan is not certified. For a name several
STT_FUNC symbols of one twin carry, the columns give the copy counts and the old kit's compare of the lowest-address
copies, which is what a lookup by name took (the new kit refuses such a name). The record verdict is `=` only when both
kits say so with no differing target and no such site; otherwise it states each kit's result, the hand arguments, the
sites and the reviewers. A function the pairing calls absent is checked to
have no symbol of its name or alias in that image. No verdict is read from any earlier record.
"""
import argparse
import contextlib
import csv
import hashlib
import importlib.util
import io
import os
import re
import subprocess
import sys

from elftools.elf.elffile import ELFFile

OLD, NEW = 'old kit (4bbd3a74be89)', 'new kit (86da41d3ef68)'


def sha(path):
    return hashlib.sha256(open(path, 'rb').read()).hexdigest()


def load_kit(d, compare):
    sums = os.path.join(d, 'SHA256SUMS')
    members = []
    for line in open(sums).read().split('\n'):
        if line.strip():
            h, n = line.split(None, 1)
            n = n.lstrip('*')
            if sha(os.path.join(d, n)) != h:
                sys.exit('codeid_kit.py: %s does not match the kit SHA256SUMS' % n)
            members.append((n, h))
    spec = importlib.util.spec_from_file_location(compare, os.path.join(d, compare + '.py'))
    s = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(s)
    dc = importlib.util.spec_from_file_location('drvcmp_twins', os.path.join(d, 'drvcmp.py'))
    dm = importlib.util.module_from_spec(dc)
    dc.loader.exec_module(dm)
    return sha(sums)[:12], members, s, dm


def loads(path):
    return [(g['p_vaddr'], g['p_memsz'], g.data()) for g in ELFFile(open(path, 'rb')).iter_segments()
            if g['p_type'] == 'PT_LOAD']


def twin_line(tag, twin, pin, dm):
    lt, lp = loads(twin), loads(pin)
    same = len(lt) >= 4 and len(lp) >= 4 and lt[1:4] == lp[1:4]
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        dm.twins(pin, twin)
    return ['# image %s: twin %s sha256 %s; pin %s sha256 %s; PT_LOAD 2..4 of twin and pin byte-equal: %s'
            % (tag, os.path.basename(twin), sha(twin), os.path.basename(pin), sha(pin), 'yes' if same else 'NO'),
            '# image %s kit twins: %s' % (tag, buf.getvalue().strip())], same


def names_at(img, addr, size):
    return {n for v, z, n, t in img.syms if v == addr and z == size and t == 'STT_FUNC'}


def jtcheck(kit, x, y, fn):
    """a kit's jtcheck on one same-named function: (text 'settled ...' / 'not settled ...', {word offset: how it is
    left open}, the table offsets it accepted, whether it judged the function at all). Its counts and its DIFF /
    UNMEASURED / UNPAIRED lines are complete (jtcheck prints every one)."""
    r = subprocess.run([sys.executable, os.path.join(kit, 'jtcheck.py'), x, y, fn], capture_output=True, text=True,
                       env=dict(os.environ, PYTHONDONTWRITEBYTECODE='1'))
    lines = r.stdout.split('\n')
    head = next((l for l in lines if l.startswith(fn + '\t')), None)
    if r.returncode or head is None or 'target differs' not in head:
        return 'not settled: jtcheck did not judge it (rc %d): %s' % (
            r.returncode, (head or r.stderr or r.stdout).strip()[-300:]), {}, [], False
    cnt = {k: int(v) for k, v in re.findall(r'(target differs|target unmeasured|unpaired) (\d+)', head)}
    tm = [m for m in (re.match(r'\s+ACCEPT \S+ table (\+0x[0-9a-f]+) \[[^]]*\] (.*)$', l) for l in lines) if m]
    tabs = ['%s %s' % (m.group(1), m.group(2)) for m in tm]
    open_ = [l.strip().split(' ')[:2] for l in lines if re.match(r'\s+(DIFF|UNMEASURED|UNPAIRED)\b', l)]
    offs = {int(o.lstrip('+'), 16): k for k, o in open_}
    settled = not any(cnt.values())
    return '%s: target differs %d, target unmeasured %d, unpaired %d%s; tables accepted: %s' % (
        'settled' if settled else 'not settled', cnt.get('target differs', 0), cnt.get('target unmeasured', 0),
        cnt.get('unpaired', 0), (' (%s)' % ', '.join(' '.join(x) for x in open_)) if open_ else '',
        ', '.join(tabs) or 'none'), offs, [int(m.group(1).lstrip('+'), 16) for m in tm], True


def measurements(paths):
    """{(image tag, function): (text, {word offset a measurement settles: its table's file name})} from regdef.py /
    luiuse.py tables"""
    out = {}
    for p in paths:
        lines = open(p).read().split('\n')
        fn = re.match(r'# (\S+)\+0x[0-9a-f]+,', lines[0]).group(1)
        for r in csv.DictReader([l for l in lines[1:] if l], delimiter='\t'):
            off = r['instruction'].split(' ')[0]
            t, s = out.setdefault((r['image'], fn), ([], {}))
            t.append('%s (%s): %s' % (off, os.path.basename(p), r['what the instruction does']))
            if r['what the instruction does'] != 'not settled by this measurement':
                s[int(off.lstrip('+'), 16)] = os.path.basename(p)
    return {k: (' | '.join(t), s) for k, (t, s) in out.items()}


def reviews(paths):
    """{(image tag, function): ('verdict (table: what was checked) | ...', [verdicts])} from reviewer tables, joined in
    their order"""
    out = {}
    for p in paths:
        for r in csv.DictReader(open(p), delimiter='\t'):
            t, v = out.setdefault((r['image'], r['fm function']), ([], []))
            t.append('%s (%s: %s)' % (r['reviewer verdict'], os.path.basename(p), r['what the reviewer checked']))
            v.append('%s (%s)' % (r['reviewer verdict'], os.path.basename(p)))
    return {k: (' | '.join(t), v) for k, (t, v) in out.items()}


def exposures(path):
    """{(image file name, address): exposure} from a luiscan output"""
    out = {}
    if path:
        for l in open(path).read().split('\n'):
            x = l.split('\t')
            if x[0] == 'ROW' and x[3] != 'addr':
                out[(x[1], int(x[3], 16))] = x[12]
    return out


def sites(path):
    """({function: [(kind, site, scan verdict)]}, {(image tag, function): reason}) from an addrsite.py table: the cross
    lines of the compared functions and the functions it could not scan"""
    out, unscanned = {}, {}
    for l in open(path).read().split('\n'):
        x = l.split('\t')
        if x[0] == 'cross' and x[1] != 'function':
            out.setdefault(x[1], []).append((x[2], x[3], x[5]))
        m = re.match(r'# (\S+) (.+?): not scanned: (.*)', l)
        if m:
            unscanned[(m.group(1), m.group(2))] = m.group(3)
    return out, unscanned


TRACE_OK = ('stack address', 'same object up to relocation', 'pointer plus offset', 'numeric bias',
            'call argument not read', 'not an address')


def traces(path):
    """{(function, kind, site): (class, reviewer verdict)} from the hand-trace table"""
    return {(r['function'], r['kind'], r['site']): (r['class'], r['reviewer verdict'])
            for r in csv.DictReader(open(path), delimiter='\t')}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('old_kit')
    ap.add_argument('new_kit')
    ap.add_argument('pairs')
    ap.add_argument('fm_twin')
    ap.add_argument('fm_pin')
    ap.add_argument('images', nargs='+')
    ap.add_argument('--measure', action='append', default=[])
    ap.add_argument('--review', action='append', default=[])
    ap.add_argument('--luiscan')
    ap.add_argument('--addrsite', required=True)
    ap.add_argument('--trace', required=True)
    a = ap.parse_args()
    imgs = [(t, *tp.split(':', 1)) for t, tp in (x.split('=', 1) for x in a.images)]
    kid, members, s2, dm = load_kit(a.old_kit, 'strictcmp2')
    kid3, members3, s3, dm3 = load_kit(a.new_kit, 'strictcmp3')
    hand = measurements(a.measure)
    rev = reviews(a.review)
    expo = exposures(a.luiscan)
    site_map, unscanned = sites(a.addrsite)
    tr = traces(a.trace)
    out = ['# code identity of the G9 route functions by the comparison kit %s (%s), first recorded with the kit %s '
           '(%s), which it supersedes' % (kid3, ', '.join('%s %s' % (n, h[:12]) for n, h in members3), kid,
                                          ', '.join('%s %s' % (n, h[:12]) for n, h in members))]
    lines, ok = twin_line('fm', a.fm_twin, a.fm_pin, dm)
    out += lines
    for tag, twin, pin in imgs:
        lines, same = twin_line(tag, twin, pin, dm)
        out += lines
        ok = ok and same
    if not ok:
        sys.exit('\n'.join(out + ['codeid_kit.py: a twin is not its pin in PT_LOAD 2..4']))
    cols = ['image', 'fm function', 'fm addr', 'image addr', 'size', 'pairing', 'function kind',
            OLD + ' word compare (not a verdict)', 'pcrel', 'real', 'unmeasured',
            'accepted targets (full bytes, got value or tls index, C string)', 'target differences', 'differences',
            'value / full-bytes acceptances', 'C-string acceptances', OLD + ' tcmp', OLD + ' jtcheck',
            NEW + ' strictcmp3 by address (combined verdict, targets)', NEW + ' differing targets (full list)',
            NEW + ' jtcheck', 'luiscan exposure (fm, image)', 'hand measurement', 'reviewer verdict',
            'name copies (fm, image)', 'lowest-address copies compared by the old kit (what a lookup by name took)',
            NEW + ' differing targets (total, settled by jtcheck, settled by hand measurement, unmeasured)',
            'immediate-built address sites (addrsite: sites, hand-trace classes, reviewer verdicts)', 'certified',
            'record verdict']
    out.append('\t'.join(cols))
    I = {'fm': s2.Img(a.fm_twin)}
    I3 = {'fm': s3.Img(a.fm_twin)}
    fmname = os.path.basename(a.fm_twin)
    rows = list(csv.DictReader(open(a.pairs), delimiter='\t'))
    paired = [r['fm function'] for r in rows if r['pairing'] != 'absent']
    for tag, twin, pin in imgs:
        I[tag], I3[tag] = s2.Img(twin), s3.Img(twin)
        for r in rows:
            fn, alias = r['fm function'], r['aliases']
            names = {fn} | ({alias} if alias not in ('', '-') else set())
            base = [tag, fn, r['fm addr'], r[tag + ' addr'], r['fm size'], r['pairing'], r['function kind']]
            if r['pairing'] == 'absent':
                present = sorted(n for n in names if any(t == 'STT_FUNC' for v, z, t in I[tag].byname.get(n, ())))
                out.append('\t'.join(base + [''] * (len(cols) - 8) + ['present: ' + ', '.join(present) if present
                                                                      else 'ABSENT']))
                continue
            fa, fs = int(r['fm addr'], 16), int(r['fm size'])
            da, ds = int(r[tag + ' addr'], 16), int(r[tag + ' size'])
            bad = []
            if not names & names_at(I['fm'], fa, fs):
                bad.append('fm symbol at %#x size %d is not %s' % (fa, fs, '/'.join(sorted(names))))
            if not names & names_at(I[tag], da, ds):
                bad.append('%s symbol at %#x size %d is not %s' % (tag, da, ds, '/'.join(sorted(names))))
            if fs != ds:
                bad.append('size %d vs %d' % (fs, ds))
            if bad:
                row = dict.fromkeys(cols, '')
                row.update(zip(cols, base))
                row.update({OLD + ' tcmp': 'not =', 'certified': 'not certified',
                            'record verdict': 'not =: pairing: ' + '; '.join(bad)})
                out.append('\t'.join(row[c] for c in cols))
                continue
            # old kit
            fb = []
            v, c, t3, diff = s2.tcmp(I, 'fm', fa, tag, da, fs, fb)
            same = v in ('EQUAL', 'EQUAL-mod-pcrel') and not diff
            jt = jtcheck(a.old_kit, a.fm_twin, twin, fn)[0] if not same and v in ('EQUAL-mod-pcrel', 'UNMEASURED') \
                else ''
            # new kit
            v3, c3, t33, diff3 = s3.tcmp(I3, 'fm', fa, tag, da, fs, [])
            nv = s3.verdict(v3, diff3)
            same3 = nv in ('EQUAL', 'EQUAL-mod-pcrel') and not diff3
            jt3, jopen, jtabs, judged = jtcheck(a.new_kit, a.fm_twin, twin, fn) if not same3 and v3 in (
                'EQUAL-mod-pcrel', 'UNMEASURED') else ('', {}, [], False)
            hm, hset = hand.get((tag, fn), ('', {}))
            offs = [int(d[0], 16) for d in diff3]
            by_jt = [o for o in offs if judged and o not in jopen]
            by_hand = [o for o in offs if o not in by_jt and o in hset]
            open_t = [o for o in offs if o not in by_jt and o not in by_hand]
            key = fn if paired.count(fn) == 1 else '%s (copy at fm %s)' % (fn, r['fm addr'])
            sites_ = site_map.get(key, [])
            got = [(k_, s_) + tr.get((key, k_, s_), ('no hand trace', '')) for k_, s_, vd in sites_]
            bad_sites = [g for g in got if g[2] not in TRACE_OK or not g[3].startswith('CONFIRM')]
            scanned = (tag, key) not in unscanned and ('fm', key) not in unscanned
            traced = scanned and not bad_sites
            rv, rvs = rev.get((tag, fn), ('', []))
            reviewed = all(x.startswith('CONFIRM') for x in rvs)
            cert = 'certified' if c3 is not None and not open_t and traced and reviewed else 'not certified'
            classes = {}
            for g in got:
                classes[g[2]] = classes.get(g[2], 0) + 1
            ctext = ('%d sites (%d base, %d store); hand trace: %s; reviewer: %d CONFIRM%s' % (
                len(got), sum(1 for g in got if g[0] == 'base'), sum(1 for g in got if g[0] == 'store'),
                ', '.join('%s %d' % kv for kv in sorted(classes.items())),
                sum(1 for g in got if g[3].startswith('CONFIRM')),
                '; NOT settled: ' + ', '.join('%s %s (%s, %s)' % (g[0], g[1], g[2], g[3] or 'no reviewer verdict')
                                              for g in bad_sites) if bad_sites else '')
                     if got else 'none') + ('' if scanned else '; NOT SCANNED')
            items = []
            tab_ok = [o for o in by_jt if o in jtabs]
            if tab_ok:
                items.append('%d jump table%s accepted %s' % (len(tab_ok), 's' if len(tab_ok) > 1 else '',
                                                              ' '.join('+%#x' % o for o in tab_ok)))
            for d in diff3:
                o = int(d[0], 16)
                if o not in tab_ok:
                    items.append('+%#x %s' % (o, {'UNPAIRED': 'unpaired'}.get(jopen.get(o), d[3])))
            newtext = '%s, %d target%s%s' % (nv, len(diff3), '' if len(diff3) == 1 else 's',
                                             ' (%s)' % ', '.join(items) if items else '')
            copies = [len([1 for v_, z_, t_ in I[k].byname.get(fn, ()) if t_ == 'STT_FUNC']) for k in ('fm', tag)]
            low = ''
            if max(copies) > 1:
                lf, li = I['fm'].fsym(fn), I[tag].fsym(fn)
                if lf and li and lf[1] == li[1]:
                    lv, lc, lt, ld = s2.tcmp(I, 'fm', lf[0], tag, li[0], lf[1], [])
                    low = '%#x : %#x: %s, %d target differences: %s' % (
                        lf[0], li[0], lv, len(ld), '=' if lv in ('EQUAL', 'EQUAL-mod-pcrel') and not ld else 'not =')
                else:
                    low = '%s : %s: sizes differ, not =' % (lf and hex(lf[0]), li and hex(li[0]))
            ex = '%s, %s' % (expo.get((fmname, fa), '?'), expo.get((os.path.basename(twin), da), '?')) if expo else ''
            if same and same3 and not got and scanned:
                verdict = '='
            else:
                verdict = '%s: %s; %s strictcmp3: %s%s%s%s%s; targets %d: %d jtcheck, %d hand, %d unmeasured: %s' % (
                    OLD, '=' if same else 'not =', NEW, newtext, '; jtcheck: ' + jt3.split(';')[0] if jt3 else '',
                    '; hand argument: ' + ', '.join('+%#x settled (%s)' % (o, hset[o]) for o in by_hand)
                    if by_hand else '',
                    '; immediate-built address sites: %d, %s' % (len(got), 'each traced and confirmed' if traced else
                                                                 'NOT all traced and confirmed') if got or not scanned
                    else '',
                    '; reviewer: ' + ', '.join(rvs) if rvs else '',
                    len(offs), len(by_jt), len(by_hand), len(open_t), cert)
            row = base + [
                v, str(c[0]) if c else '', str(c[1]) if c else '', str(c[2]) if c else '', '%d,%d,%d' % t3,
                str(len(diff)), ' | '.join('%s %s %s %s' % d[:4] for d in diff), s2.fb_text(fb),
                ' '.join('%s@%#x|%#x=%r' % (o, x1, x2, s) for k, o, x1, x2, s in fb if k == 'cstr'),
                '=' if same else 'not =', jt, newtext,
                ' | '.join('%s %s %s %s' % d[:4] for d in diff3), jt3, ex, hm, rv, '%d, %d' % tuple(copies), low,
                '%d, %d, %d, %d%s' % (len(offs), len(by_jt), len(by_hand), len(open_t),
                                      (' (open: %s)' % ', '.join('+%#x' % o for o in open_t)) if open_t else ''),
                ctext, cert, verdict]
            out.append('\t'.join(row))
    sys.stdout.write('\n'.join(out) + '\n')


if __name__ == '__main__':
    main()
