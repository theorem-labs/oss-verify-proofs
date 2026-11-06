#!/usr/bin/env python3
"""gen_b1w_own.py --pin PIN --symbols SYMBOLS.tsv --table B1W.v --out OUT.v [--report REPORT.tsv]
                 [--old OLD_B1W.v --musl-lo MUSL_LO --musl-hi MUSL_HI]

Regenerates the FUNCTION-ENTRY rows (tfib_A_<name> / tfib_E_<name>) of a proof port's B1w table (YB1w.v) from the
TARGET image's OWN STT_FUNC symbols inside .text, names and ranges together: one row per distinct function start
address, [A, E) = [st_value, st_value + st_size); a size-0 symbol ends at the next function start (the last one at the
end of .text). Where several symbols share one start, the global (or weak) one wins, then the shortest name, and E
uses the largest size at that start. Names are the symbol names with every character outside [A-Za-z0-9_] replaced
by '_' (unique by a _<n> suffix). With OLD_B1W.v (the table this one replaces), NO OLD NAME CHANGES MEANING: a new row
whose name the old table defines with a different [A, E) and whose start lies in the musl text [MUSL_LO, MUSL_HI) is
renamed <name>_libc, so the bare old name (which meant the interceptor trampoline / wrapper / thunk) is retired and
every old citation fails to compile; a row outside musl keeps its name (its end is corrected from the donor's merged
value). An old name may disappear, never be reused. Every other line of B1W.v (header, section bounds, tfib_D_* /
tfib_at_* rows) is kept as is.

New version of gen_b1w_own.py (sha256 e278df58f942). The row logic is unchanged; only its two sources moved off the
unstripped image, which is not shipped:
  - the symbols come from SYMBOLS.tsv, the text extract written by extract/extract_symbols.py (one row per .symtab
    entry, in .symtab order: name, value hex, size, type, bind, section; '#' header lines first);
  - the .text bounds come from the section header of PIN, the pinned image (its .text header equals the twin's).
Every input is an argument. Needs pyelftools (for the PIN section header only).
"""
import argparse, re
from elftools.elf.elffile import ELFFile


def text_bounds(pin):
    with open(pin, 'rb') as f:
        text = ELFFile(f).get_section_by_name('.text')
        return text['sh_addr'], text['sh_addr'] + text['sh_size']


def read_symbols(path):
    """(name, value, size, type, bind) per extract row, in .symtab order; the '#' header is the leading lines only."""
    rows, body = [], False
    with open(path, newline='') as f:
        for line in f:
            line = line[:-1] if line.endswith('\n') else line
            if not body and line.startswith('#'):
                continue
            body = True
            name, value, size, typ, bind, _sec = line.rsplit('\t', 5)
            rows.append((name, int(value, 16), int(size), typ, bind))
    return rows


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--pin', required=True, help='pinned image (reads the .text section header)')
    ap.add_argument('--symbols', required=True, help='symbol extract of the unstripped twin of PIN')
    ap.add_argument('--table', required=True, help='B1w table whose function rows are replaced')
    ap.add_argument('--out', required=True)
    ap.add_argument('--report')
    ap.add_argument('--old', help='the B1w table this one replaces (name-meaning rule)')
    ap.add_argument('--musl-lo')
    ap.add_argument('--musl-hi')
    a = ap.parse_args()
    if a.old and not (a.musl_lo and a.musl_hi):
        ap.error('--old needs --musl-lo and --musl-hi')
    lo, hi = text_bounds(a.pin)
    by = {}
    for name, value, size, typ, bind in read_symbols(a.symbols):
        if typ != 'STT_FUNC' or not (lo <= value < hi):
            continue
        by.setdefault(value, []).append((bind != 'STB_GLOBAL' and bind != 'STB_WEAK', len(name), name, size))
    starts = sorted(by)
    rows, used = [], {}
    for i, start in enumerate(starts):
        _, _, name, size = min(by[start])
        size = max(sz for _, _, _, sz in by[start])
        end = start + size if size else (starts[i + 1] if i + 1 < len(starts) else hi)
        ident = re.sub(r'[^A-Za-z0-9_]', '_', name) or 'fn'
        k = used.get(ident, 0); used[ident] = k + 1
        if k: ident = f'{ident}_{k}'
        rows.append((ident, start, end, name))
    if a.old:
        old = {k: (int(s, 16), int(e, 16)) for k, s, e in re.findall(
            r'Definition tfib_A_(\w+) : Z := (0x[0-9a-f]+)\.\s+Definition tfib_E_\1 : Z := (0x[0-9a-f]+)\.', open(a.old).read())}
        mlo, mhi = int(a.musl_lo, 0), int(a.musl_hi, 0)
        taken = {n for n, _, _, _ in rows}
        fixed = []
        for n, s, e, sym in rows:
            if n in old and old[n] != (s, e):
                if not (mlo <= s < mhi):
                    fixed.append((n, s, e, sym)); continue
                cand = n + '_libc'
                while (cand in old and old[cand] != (s, e)) or (cand in taken and cand != n):
                    cand += '_libc'
                taken.discard(n); taken.add(cand); n = cand
            fixed.append((n, s, e, sym))
        rows = fixed
    lines = open(a.table).read().split('\n')
    pat = re.compile(r'^Definition tfib_A_\w+ : Z := 0x[0-9a-f]+\.\s+Definition tfib_E_\w+ : Z := 0x[0-9a-f]+\.$')
    first = next(i for i, l in enumerate(lines) if pat.match(l))
    last = max(i for i, l in enumerate(lines) if pat.match(l))
    body = [f'Definition tfib_A_{n} : Z := {s:#x}.  Definition tfib_E_{n} : Z := {e:#x}.' for n, s, e, _ in rows]
    open(a.out, 'w').write('\n'.join(lines[:first] + body + lines[last + 1:]))
    if a.report:
        open(a.report, 'w').write('ident\tA\tE\tsymbol\n' + '\n'.join(f'{n}\t{s:#x}\t{e:#x}\t{sym}' for n, s, e, sym in rows) + '\n')
    print(f'gen_b1w_own: {len(rows)} function rows from {a.symbols} .text [{lo:#x},{hi:#x}); out {a.out}')


if __name__ == '__main__':
    main()
