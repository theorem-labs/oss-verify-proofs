"""Image setup: function starts, call graph, trampolines, run region (refactored from the trace kit's paths.py).
Vendored base.py, sha256 b2f755aab53e...; rvdis is local. This copy differs from base.py
b2f755aab53e in this docstring only."""
import sys, re, bisect
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rvdis import load, md
from collections import defaultdict


def tgt(i):
    m = re.match(r'(?:ra, )?(-?0x[0-9a-f]+|-?\d+)$', i.op_str)
    return i.address + int(m.group(1), 0) if m else None


class Image:
    def __init__(self, img):
        self.img = img
        base, data, e = load(img)
        self.base, self.data, self.e = base, data, e
        ins = list(md.disasm(data, base))
        self.ins = ins
        self.end = base + len(data)
        starts = set()
        for k, i in enumerate(ins):
            if i.mnemonic in ('jal', 'c.jal') and not i.op_str.startswith('zero'):
                t = tgt(i)
                if t is not None and base <= t < self.end:
                    starts.add(t)
            if i.mnemonic in ('ret', 'c.jr', 'j', 'c.j', 'jr') and k + 1 < len(ins):
                n = ins[k + 1]
                if re.match(r'(c\.)?addi(16sp)?$', n.mnemonic) and n.op_str.startswith('sp, sp, -'):
                    starts.add(n.address)
        self.starts = sorted(starts)
        self.idx = {i.address: k for k, i in enumerate(ins)}
        st = self.starts
        self.gcp = {a for a in st if [(x.mnemonic, x.op_str) for x in self.first(a, 2)] in
                    ([('c.mv', 'a0, ra'), ('c.jr', 'ra')], [('mv', 'a0, ra'), ('ret', '')], [('c.mv', 'a0, ra'), ('ret', '')])}
        tramps = []
        k = 0
        while k < len(ins):
            run = []
            while k < len(ins) and ins[k].mnemonic == 'j' and ins[k].size == 4:
                run.append(ins[k]); k += 1
            if 2 <= len(run) <= 6 and tgt(run[0]) == run[-1].address + 4:
                tramps.append(run)
            k += 1 if not run else 0
        self.tramps = tramps
        self.tramp_impl = {x.address: tgt(x) for run in tramps for x in run}
        calls = defaultdict(list); tails = defaultdict(list); self.indirect = []
        for i in ins:
            if i.mnemonic in ('jal', 'c.jal') and not i.op_str.startswith('zero'):
                t = tgt(i)
                if t is not None:
                    calls[t].append((self.owner(i.address), i.address + i.size))
            elif i.mnemonic in ('jalr', 'c.jalr') and not i.op_str.startswith('zero'):
                self.indirect.append(i.address)
        sset = set(st)
        for i in ins:
            if i.mnemonic in ('j', 'c.j'):
                t = tgt(i)
                if t is not None and t in sset:
                    o = self.owner(i.address)
                    if not (o <= t < self.nxt(o)):
                        tails[t].append(o)
        callees = defaultdict(set)
        for t, lst in calls.items():
            for g, _ in lst:
                callees[g].add(t)
        for t, lst in tails.items():
            for g in lst:
                callees[g].add(t)
        self.callees = callees
        entry = e.header['e_entry']
        self.entry = entry
        sec = [s for s in e.iter_sections() if s['sh_addr'] <= entry < s['sh_addr'] + s['sh_size']][0]
        ent_ins = list(md.disasm(sec.data()[entry - sec['sh_addr']:entry - sec['sh_addr'] + 0x60], entry))
        auipc = {}
        self.main = None
        for x in ent_ins:
            ops = x.op_str.split(', ')
            if x.mnemonic == 'auipc':
                auipc[ops[0]] = x.address + (int(ops[1], 0) << 12)
            if x.mnemonic == 'ld' and ops[0] == 'a5':
                m = re.match(r'(-?0x[0-9a-f]+|-?\d+)\((\w+)\)', ops[1])
                self.main = self.read64((auipc[m.group(2)] + int(m.group(1), 0)) & 0xffffffffffffffff)
                break
        imps = set(self.tramp_impl.values()) | set(self.tramp_impl)
        R = {self.main}; todo = [self.main]
        while todo:
            f = todo.pop()
            for t in callees.get(f, ()):
                if t in imps or t in R or t < self.main:
                    continue
                R.add(t); todo.append(t)
        self.R = R
        self.calls, self.tails = calls, tails

    def read64(self, va):
        for seg in self.e.iter_segments():
            if seg['p_type'] == 'PT_LOAD' and seg['p_vaddr'] <= va < seg['p_vaddr'] + seg['p_filesz']:
                off = va - seg['p_vaddr']
                return int.from_bytes(seg.data()[off:off + 8], 'little')

    def owner(self, a):
        return self.starts[bisect.bisect_right(self.starts, a) - 1]

    def nxt(self, a):
        j = bisect.bisect_right(self.starts, a)
        return self.starts[j] if j < len(self.starts) else self.end

    def first(self, a, n):
        k = self.idx.get(a)
        return self.ins[k:k + n] if k is not None else []

    def body(self, a):
        n = self.nxt(a); k = self.idx.get(a); out = []
        while k is not None and k < len(self.ins) and self.ins[k].address < n:
            out.append(self.ins[k]); k += 1
        return out
