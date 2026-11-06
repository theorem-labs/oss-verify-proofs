#!/usr/bin/env python3
"""rangetab-sm1.py DONOR_YF0r.v TARGET_YF0r.v DONOR_TWIN TARGET_TWIN: the keyed range-table check of YF0r.v's code
table `fs_ranges` (in place of atable for these files: atable.py only emits the YB12 atable record, and YF0r / YF0s /
YF0v state no atable field).

Each row (start, count) covers the words [start, start + 4 * count). The KEY of a row is the sized FUNC symbol that
holds its start, read from the image's own twin: (name, which copy of the name in address order, offset of start in
it). The check REFUSES unless
  - every target row has exactly one donor row with the same key and the same count, and lies inside its symbol;
  - every donor row without a target twin names a symbol the target twin does not define (a row the target cannot
    have), and every donor row whose symbol the target defines has its twin;
  - the two twins are the pinned ones (sha256).
Exit 0 on PASS, 1 on a refusal."""
import bisect, hashlib, re, sys

from elftools.elf.elffile import ELFFile

SHA = {'donor': '5a5ee7c02b4e2a1d1653dc0c256182c9b65c33dde3a7ddc98b9de2afffe7a417',
       'target': '8d07ffcf594874884207465cc34ff9f3b1062f21f6d9b3622e0771fa76490b16'}
ROW = re.compile(r'\((0x[0-9a-fA-F]+|\w+), (\d+)%nat\)')


class Twin:
    def __init__(self, path, role):
        sha = hashlib.sha256(open(path, 'rb').read()).hexdigest()
        if sha != SHA[role]:
            sys.exit(f'{role} twin {path}: sha256 {sha} is not {SHA[role]}')
        e = ELFFile(open(path, 'rb'))
        f = sorted({(s['st_value'], s['st_size'], s.name) for s in e.get_section_by_name('.symtab').iter_symbols()
                    if s['st_info']['type'] == 'STT_FUNC' and s['st_size'] > 0 and s.name})
        self.funcs, self.starts = f, [x[0] for x in f]
        self.copies = {}
        for a, sz, n in f:
            self.copies.setdefault(n, []).append(a)

    def key(self, a):
        i = bisect.bisect_right(self.starts, a) - 1
        best = None
        for j in range(max(0, i - 8), i + 1):
            st, sz, n = self.funcs[j]
            if st <= a < st + sz and (best is None or sz < best[1]):
                best = (st, sz, n)
        if best is None:
            return None, None
        st, sz, n = best
        return (n, sorted(set(self.copies[n])).index(st), a - st), st + sz


def rows(path):
    t = open(path).read()
    m = re.search(r'Definition fs_ranges : list \(Z \* nat\) :=\s*\[(.*?)\]\.', t, re.S)
    return [(int(a, 0), int(c)) for a, c in ROW.findall(m.group(1))]


def main():
    dpath, tpath, dtw, ttw = sys.argv[1:5]
    D, T = Twin(dtw, 'donor'), Twin(ttw, 'target')
    dr, tr = rows(dpath), rows(tpath)
    dk = {}
    for a, c in dr:
        k, end = D.key(a)
        dk.setdefault(k, []).append((a, c, end))
    bad, used = 0, set()
    print(f'donor rows {len(dr)}, target rows {len(tr)}')
    print('| target row | key (symbol, copy, offset) | donor row | count | inside the symbol | verdict |\n|---|---|---|---|---|---|')
    for a, c in tr:
        k, end = T.key(a)
        twins = dk.get(k, [])
        ok_in = end is not None and a + 4 * c <= end
        if k is None or len(twins) != 1 or twins[0][1] != c or not ok_in:
            bad += 1
            v = 'REFUSED'
        else:
            v = 'PASS'
            used.add(k)
        dn = ', '.join(f'({x:#x}, {y})' for x, y, _ in twins) or 'none'
        name = f'{k[0][:60]}, {k[1]}, +{k[2]:#x}' if k else 'no symbol'
        print(f'| ({a:#x}, {c}) | {name} | {dn} | {c} | {ok_in} | {v} |')
    for k, lst in dk.items():
        if k in used:
            continue
        for a, c, _ in lst:
            if k is not None and k[0] not in T.copies:
                print(f'| - | {k[0][:60]}, {k[1]}, +{k[2]:#x} | ({a:#x}, {c}) | {c} | - | DROPPED (the target defines no {k[0]}) |')
            else:
                bad += 1
                print(f'| - | {k} | ({a:#x}, {c}) | {c} | - | REFUSED (the target defines the symbol; its row is missing) |')
    print(f'rangetab-sm1: {"PASS" if not bad else "REFUSED"} ({bad} refused rows)')
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
