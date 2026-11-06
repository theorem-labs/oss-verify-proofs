#!/usr/bin/env python3
"""donor_map.py UNIT_LIB KNOCK_LIB [--unit UNIT] [--image A|B] [--break FILE=CAUSE ...] -- the donor map of reac-repacer/fuzz_wire image A's core
(the unit owner's (b'), file-level donor choice): every lib/A file of the unit -> knock | grant, with its measured reason.

UNIT_LIB: the unit's lib (projects/reac-repacer/fuzz_wire/proofs/lib); KNOCK_LIB: libreac/fuzz_knock's released lib at
origin/ossv/recipes 88154566652a (repository layout: A/, Reusable/).
A file's donor is KNOCK when
  (1) its knock counterpart names the empty-depot form (DEPOT below: the switch, the knock-only kernel files, the empty-depot
      cells, the NB / SB sentinel lemmas, the first-Put layout growth), or
  (2) a measured build broke it with a depot cause (--break FILE=CAUSE, each from a recorded build log), or
  (3) it is in the Require closure of a knock-donor file and the unit's lib does not hold it ('Required by <file>';
      knock-only lib/A files and the knock-only kernel files KnBlockExt / KnLayoutGle / YC85).
--exclude FILE=REASON keeps a knock file OUT (a ruling): it is not followed in the closure, and its Requirers are listed
(each needs glue or a grant counterpart). Every other unit lib/A file keeps GRANT (fuzz_grant's release 4f87de75d67, the run of record) as its donor.
Output (stdout, TSV): unit and image (--unit, default reac-repacer/fuzz_wire; --image, default A: the key that lets another
unit's rows, e.g. fuzz_egress's, sit in the same table), file, donor, reason, the image-B twin name (Y<x> in knock's lib/AU, measured by file existence;
a kernel file is shared), and whether knock's lib/AU has it; then the size check: knock-donor files and lines over the unit's lib/A
(lines of the knock texts against the unit's current lib/A)."""
import os, re, sys

DEPOT = re.compile(r'\b(KnBlockExt|KnLayoutGle|YC85|DepotCfg|depot_pick|depot_has_trace|layout_grow|d_mu|s_alloc|s_stored0|'
                   r's_mtx0|depot_cells_post|depot_cells_pre|depot_ok_post|depot_ok_pre|depot_ok_mapped|AR_first_put_facts|'
                   r'depot_same|ameter_depot_step|nb_eager|perm_live|vm_takes|kd_avoid|lo_vis0_cover|owned_extents_set|'
                   r'static_extents_set|vis0_zones_set|core_extents_set|lazy_zones_set|perm_maps_set)\b')
REQ = re.compile(r'From\s+OssFuzzTheorems\.Proofs\.libreac\.fuzz_knock\.lib\.(A|Reusable)\s+Require(?:\s+Import|\s+Export)?'
                 r'\s+([^.]+)\.')


def strip(t):
    out, d, i, s = [], 0, 0, False
    while i < len(t):
        two = t[i:i + 2]
        if not s and two == '(*':
            d += 1; i += 2; continue
        if d and two == '*)':
            d -= 1; i += 2; continue
        if d == 0:
            if t[i] == '"':
                s = not s
            out.append(t[i])
        i += 1
    return ''.join(out)


def main():
    ul, kl = sys.argv[1:3]
    breaks, excl = {}, {}
    unit, image = 'reac-repacer/fuzz_wire', 'A'
    a = sys.argv[3:]
    while a:
        if a[0] == '--unit':
            unit, a = a[1], a[2:]
            continue
        if a[0] == '--image':
            image, a = a[1], a[2:]
            continue
        if a[0] not in ('--break', '--exclude'):
            sys.exit('donor_map: unknown argument %s' % a[0])
        f, c = a[1].split('=', 1)
        (breaks if a[0] == '--break' else excl)[f] = c
        a = a[2:]
    U = '%s\t%s\t' % (unit, image)
    ua = sorted(f for f in os.listdir(os.path.join(ul, 'A')) if f.endswith('.v'))
    ur = set(os.listdir(os.path.join(ul, 'Reusable')))
    ktext = {}
    for d in ('A', 'Reusable'):
        for f in os.listdir(os.path.join(kl, d)):
            if f.endswith('.v'):
                ktext['%s/%s' % (d, f)] = strip(open(os.path.join(kl, d, f)).read())
    rows = {}
    for f in ua:
        k = ktext.get('A/' + f)
        if k is None:
            continue
        m = DEPOT.search(k)
        if m:
            rows['A/' + f] = 'knock counterpart names the depot form (first: %s, line %d)' % (
                m.group(1), k.count('\n', 0, m.start()) + 1)
    for f, c in breaks.items():
        if 'A/' + f not in rows:
            if 'A/' + f not in ktext:
                sys.exit('donor_map: --break %s has no knock counterpart' % f)
            rows['A/' + f] = 'measured break with a depot cause: %s' % c
    # Require closure: knock modules a knock-donor file Requires that the unit's lib does not hold
    excl_by = {}
    todo = sorted(rows)
    while todo:
        x = todo.pop(0)
        for m in REQ.finditer(ktext[x]):
            d = m.group(1)
            for n in m.group(2).split():
                p = '%s/%s.v' % (d, n)
                held = (n + '.v' in ua) if d == 'A' else (n + '.v' in ur)
                if held or p in rows:
                    continue
                if p in excl:
                    excl_by.setdefault(p, []).append(x)
                    continue
                if p not in ktext:
                    sys.exit('donor_map: %s Requires %s, which neither lib holds' % (x, p))
                rows[p] = 'Required by %s' % x
                todo.append(p)
    au = set(os.listdir(os.path.join(kl, 'AU'))) if os.path.isdir(os.path.join(kl, 'AU')) else set()

    def twin(p):
        if p.startswith('Reusable/'):
            return p, 'shared kernel file'
        n = os.path.basename(p)
        for c in ('Y' + n[1:], n):
            if c in au:
                return 'AU/' + c, 'yes'
        return 'AU/Y' + n[1:], 'no'
    print('unit\timage\tfile\tdonor\treason\timage-B twin\tknock lib/AU has it')
    for f in ua:
        p = 'A/' + f
        tw = twin(p) if p in rows else ('-', '-')
        print(U + '%s\t%s\t%s\t%s\t%s' % (p, 'knock' if p in rows else 'grant', rows.get(p, 'grant release (run of record)'), tw[0], tw[1]))
    for p in sorted(x for x in rows if x not in ['A/' + f for f in ua]):
        print(U + '%s\tknock\t%s\t%s\t%s' % ((p, rows[p]) + twin(p)))
    for p in sorted(excl):
        print(U + '%s\tout\t%s; Required by %s\t%s\t%s' % ((p, excl[p], ', '.join(sorted(excl_by.get(p, []))) or 'none') + twin(p)))
    kfiles = [p for p in rows if p.startswith('A/')]
    klines = sum(len(open(os.path.join(kl, p)).read().splitlines()) for p in kfiles)
    ulines = sum(len(open(os.path.join(ul, 'A', f)).read().splitlines()) for f in ua)
    rep = [p for p in kfiles if p[2:] in ua]
    rlines = sum(len(open(os.path.join(ul, p)).read().splitlines()) for p in rep)
    print('# size: knock-donor lib/A files %d (%d replace a unit file, %d new) of the unit\'s %d lib/A files; knock-donor '
          'lib/A lines %d; the replaced unit files hold %d of the unit\'s %d lib/A lines (%.1f%%); knock kernel files %d'
          % (len(kfiles), len(rep), len(kfiles) - len(rep), len(ua), klines, rlines, ulines, 100.0 * rlines / ulines,
             len([p for p in rows if p.startswith('Reusable/')])))


if __name__ == '__main__':
    main()
