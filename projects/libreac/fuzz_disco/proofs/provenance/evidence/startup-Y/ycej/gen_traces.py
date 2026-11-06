#!/usr/bin/env python3
"""gen_traces.py -- the allocation-trace universe of a target's ASan build, in cgif_file_fuzzer's A/ACej.v form.

    gen_traces.py ELF SYMS --ipc malloc=0x52dec --ipc free=0x52c8c [--fp FUNC=RA ...] [--module MOD] > ACej.v

What it reads from the binary: every call of the memory-checking runtime's malloc and free wrappers (the 4-byte
jumps `__interceptor_trampoline_malloc` / `_free`, and the wrappers themselves), by function. A trace is
[ipc; the call site's return address; then the saved ra of each frame the fast unwinder walks from the caller's s0].
The unwinder stops at a caller that does not keep its frame pointer in s0, so the functions it walks through are
given with --fp FUNC=RA (FUNC keeps s0, and its own caller's call of it returns to RA). --ipc gives the address the
interceptor records as the first entry (the return address of its GetCurrentPc call, measured per build).

Output: `CTX_<fn>`, `TRACES_<fn>` per calling function, the universe closed under prefixes, and cgif's
`universe_ok` proof (the lemma text of A/ACej.v). Sizes and names are the target's; no value is relocated.
"""
import argparse, bisect, collections, os, sys

KIT = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'kit')  # the decoder rvelf.py, in kit/ beside this file
sys.path.insert(0, KIT)
sys.path.insert(0, __file__.rsplit('/', 1)[0])
import rvelf  # noqa: E402
from resolve_code import sym_ranges, text_code  # noqa: E402


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('elf')
    p.add_argument('syms', help="the ELF's unstripped twin or its nm text (a .txt file, e.g. extract_syms.py's output)")
    p.add_argument('--ipc', action='append', required=True, help='NAME=ADDR: the pc the NAME interceptor records')
    p.add_argument('--entry', action='append', default=[], help='NAME: a wrapper or its trampoline whose calls count'
                   ' (default: __interceptor_trampoline_<ipc name> and ___interceptor_<ipc name>)')
    p.add_argument('--fp', action='append', default=[], help='FUNC=RA: FUNC keeps its frame pointer, so the unwinder'
                   ' continues to RA (the return address of the call of FUNC)')
    p.add_argument('--exclude', action='append', default=[], help='FUNC: a calling function whose calls are not in a'
                   ' healthy run (the runtime\'s own error path, e.g. libunwind\'s cache)')
    p.add_argument('--module', default='', help='module prefix of the Require lines (default: no header)')
    a = p.parse_args()
    ipc = {k: int(v, 0) for k, v in (s.split('=') for s in a.ipc)}
    fp = {k: int(v, 0) for k, v in (s.split('=') for s in a.fp)}
    syms = sym_ranges(a.syms)
    los = [s[0] for s in syms]
    byname = {s[2]: s for s in syms}
    def fn_of(x):
        k = bisect.bisect_right(los, x) - 1
        return syms[k] if k >= 0 and x < syms[k][1] else None
    targets = {}
    for name in ipc:
        for cand in (a.entry or [f'__interceptor_trampoline_{name}', f'___interceptor_{name}', name]):
            if cand in byname:
                targets[byname[cand][0]] = name
    e = rvelf.Elf(a.elf)
    c = text_code(e)
    sites = collections.defaultdict(list)  # caller name -> [(ipc name, return address)]
    for k, pc in enumerate(c.pcs):
        s = c.sens[k]
        if not s or s[0] not in ('jal', 'c.j') or s[1] not in targets:
            continue
        if (c.raws[k] & 0x7f) == 0x6f and ((c.raws[k] >> 7) & 31) != 1:
            continue  # a tail jump, not a call
        f = fn_of(pc)
        if f is None:
            continue
        if f[2] in a.exclude:
            continue
        sites[f[2]].append((targets[s[1]], pc + c.lens[k]))
    def traces_of(fnname):
        out = []
        for name, ra in sorted(sites[fnname], key=lambda x: x[1]):
            t = [ipc[name], ra]
            out.append(list(t))
            cur = fnname
            while cur in fp:
                t = t + [fp[cur]]
                out.append(list(t))
                cur = (fn_of(fp[cur]) or (0, 0, ''))[2]
        return out
    univ = set()
    for fnname in sites:
        for t in traces_of(fnname):
            for j in range(1, len(t) + 1):
                univ.add(tuple(t[:j]))
    def fmt(ts):
        return '[' + ';\n'.join('[' + '; '.join(f'0x{x:x}' for x in t) + ']' for t in ts) + '].'
    print(f'(* Machine-generated data computed from the task\'s compiled program: the calls of the memory-checking '
          f'runtime\'s allocation entries in {a.elf.rsplit("/", 1)[-1]}, with the traces the runtime stores. *)')
    print('From Stdlib Require Import ZArith List Bool Lia.')
    if a.module:
        print(f'From {a.module} Require Import YG00 YG01.')
    print('Import ListNotations.\nLocal Open Scope Z_scope.')
    for fnname in sorted(sites):
        cs = sorted({fp.get(fnname)} - {None})
        print(f'Definition CTX_{fnname} : list (list Z) :=\n' + fmt([[x] for x in cs] or [[]]))
        print(f'Definition TRACES_{fnname} : list (list Z) :=\n' + fmt(traces_of(fnname)))
    print('Definition Tfib_universe : list (list Z) :=\n' + fmt(sorted(univ)))
    print(f'(* {len(univ)} traces, from {sum(len(v) for v in sites.values())} call sites in '
          f'{len(sites)} function(s): ' + ', '.join(sorted(sites)) + ' *)')


if __name__ == '__main__':
    main()
