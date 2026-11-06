#!/usr/bin/env python3
"""call_sites.py IMAGE SYMS NAME[@CALLER]... -- every direct call of each named function in the image's .text.

A direct call is `jal ra, NAME`. One line per call, in address order per NAME: the callee, the function that holds the
call, the pc of the call and its return address. NAME@CALLER keeps only the calls inside CALLER. SYMS is the twin symbol
listing (twin_symbols.py: `ADDRESS SIZE TYPE NAME` lines, a function's letter t/T/w/W).

Why: ACej.v's harness contexts (CTX_<fn>) are the return addresses of the calls of those functions, and gen_traces.py's
--fp / --ipc arguments are return addresses too; no script of record wrote them down, so this scan lists them."""
import bisect
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rvelf  # noqa: E402


def main():
    if len(sys.argv) < 4:
        sys.exit('usage: call_sites.py IMAGE SYMS NAME[@CALLER]...')
    image, syms_path, wanted = sys.argv[1], sys.argv[2], sys.argv[3:]
    syms, funcs = {}, []
    for line in open(syms_path):
        f = line.split()
        if len(f) == 4 and not line.startswith('#'):
            a, s = int(f[0], 16), int(f[1], 16)
            syms.setdefault(f[3], a)
            if f[2] in 'tTwW' and s:
                funcs.append((a, a + s, f[3]))
    funcs.sort()
    los = [x[0] for x in funcs]

    def holder(pc):
        k = bisect.bisect_right(los, pc) - 1
        return funcs[k][2] if k >= 0 and pc < funcs[k][1] else '-'
    e = rvelf.Elf(image)
    r = next(s for s in e.sections if s.kind == 'exec' and s.name == '.text')
    c = rvelf.Code(e.region_bytes(r), r.vaddr)
    calls = {}
    for k, pc in enumerate(c.pcs):
        s = c.sens[k]
        if s and s[0] == 'jal' and (c.raws[k] >> 7) & 31 == 1:
            calls.setdefault(s[1], []).append((pc, pc + c.lens[k]))
    print('callee\tcaller\tcall_pc\treturn_address')
    for w in wanted:
        name, _, caller = w.partition('@')
        if name not in syms:
            sys.exit('call_sites: %s is not in %s' % (name, syms_path))
        for pc, ra in calls.get(syms[name], []):
            if not caller or holder(pc) == caller:
                print('%s\t%s\t%#x\t%#x' % (name, holder(pc), pc, ra))


if __name__ == '__main__':
    main()
