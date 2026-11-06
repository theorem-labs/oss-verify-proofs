#!/usr/bin/env python3
"""gen_b1w_own.py IMAGE_TWIN B1W.v OUT.v [REPORT.tsv] [OLD_B1W.v MUSL_LO MUSL_HI]

Regenerates the FUNCTION-ENTRY rows (tfib_A_<name> / tfib_E_<name>) of a proof port's AB1w.v / YB1w.v from the
TARGET image's OWN STT_FUNC symbols inside .text, names and ranges together (the row-set rule, 03:27Z): one row per
distinct function start address, [A, E) = [st_value, st_value + st_size); a size-0 symbol
ends at the next function start. Where several symbols share one start, the global one wins, then the shortest
name. Names are the symbol names with every character outside [A-Za-z0-9_] replaced by '_' (unique by a _<n>
suffix). With OLD_B1W.v (the table this one replaces), NO OLD NAME CHANGES MEANING: a new row whose name the old
table defines with a different [A, E) and whose start lies in the musl text [MUSL_LO, MUSL_HI) is renamed
<name>_libc, so the bare old name (which meant the interceptor trampoline / wrapper / thunk) is RETIRED and every
old citation fails to compile (ruling 06:17Z); a row outside musl keeps its name (target_run: its end is
corrected from the donor's merged value). An old name may disappear, never be reused. Every other line of B1W.v (header, section bounds, tfib_D_* / tfib_at_* rows) is kept as is.
IMAGE_TWIN is extract_twin.py's text extract (symbols, section headers) of the target's unstripped twin, read with
../twin/twin_syms.py.
"""
import os, re, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'twin'))
import twin_syms

def main():
    dbg, src, out = sys.argv[1:4]
    rep = sys.argv[4] if len(sys.argv) > 4 else None
    e = twin_syms.load(dbg)
    text = e.get_section_by_name('.text')
    lo, hi = text['sh_addr'], text['sh_addr'] + text['sh_size']
    by = {}
    for s in e.get_section_by_name('.symtab').iter_symbols():
        if s['st_info']['type'] != 'STT_FUNC' or not (lo <= s['st_value'] < hi):
            continue
        by.setdefault(s['st_value'], []).append((s['st_info']['bind'] != 'STB_GLOBAL' and s['st_info']['bind'] != 'STB_WEAK', len(s.name), s.name, s['st_size']))
    starts = sorted(by)
    rows, used = [], {}
    for i, a in enumerate(starts):
        _, _, name, size = min(by[a])
        size = max(sz for _, _, _, sz in by[a])
        end = a + size if size else (starts[i + 1] if i + 1 < len(starts) else hi)
        ident = re.sub(r'[^A-Za-z0-9_]', '_', name) or 'fn'
        k = used.get(ident, 0); used[ident] = k + 1
        if k: ident = f'{ident}_{k}'
        rows.append((ident, a, end, name))
    if len(sys.argv) > 7:
        old = {k: (int(a, 16), int(e, 16)) for k, a, e in re.findall(
            r'Definition tfib_A_(\w+) : Z := (0x[0-9a-f]+)\.\s+Definition tfib_E_\1 : Z := (0x[0-9a-f]+)\.', open(sys.argv[5]).read())}
        mlo, mhi = int(sys.argv[6], 0), int(sys.argv[7], 0)
        taken = {n for n, _, _, _ in rows}
        fixed = []
        for n, a, e, s in rows:
            if n in old and old[n] != (a, e):
                if not (mlo <= a < mhi):
                    fixed.append((n, a, e, s)); continue
                cand = n + '_libc'
                while (cand in old and old[cand] != (a, e)) or (cand in taken and cand != n):
                    cand += '_libc'
                taken.discard(n); taken.add(cand); n = cand
            fixed.append((n, a, e, s))
        rows = fixed
    lines = open(src).read().split('\n')
    pat = re.compile(r'^Definition tfib_A_\w+ : Z := 0x[0-9a-f]+\.\s+Definition tfib_E_\w+ : Z := 0x[0-9a-f]+\.$')
    first = next(i for i, l in enumerate(lines) if pat.match(l))
    last = max(i for i, l in enumerate(lines) if pat.match(l))
    body = [f'Definition tfib_A_{n} : Z := {a:#x}.  Definition tfib_E_{n} : Z := {e:#x}.' for n, a, e, _ in rows]
    open(out, 'w').write('\n'.join(lines[:first] + body + lines[last + 1:]))
    if rep:
        open(rep, 'w').write('ident\tA\tE\tsymbol\n' + '\n'.join(f'{n}\t{a:#x}\t{e:#x}\t{s}' for n, a, e, s in rows) + '\n')
    print(f'gen_b1w_own: {len(rows)} function rows from {dbg} .text [{lo:#x},{hi:#x}); out {out}')

if __name__ == '__main__':
    main()
