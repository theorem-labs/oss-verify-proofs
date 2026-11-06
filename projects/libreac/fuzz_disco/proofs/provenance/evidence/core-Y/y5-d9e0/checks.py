#!/usr/bin/env python3
"""Per-file classification and the four registry checks on the dry run of port_core tag d9e0589898fd (Y5 inputs).

Usage: checks.py --work D9E0_WORK --abfd ABFD_STAGE_OUT --shipped TARGET_LIB --pin PIN --symbols EXTRACT.tsv
                 --files FILES.txt --log D9E0_LOG --out-dir DIR

Writes DIR/classify.tsv (one row per relocated file: sha256 of the shipped file, of the abfd17f8b3d2 re-run and of
the d9e0589898fd dry run, and the class) and DIR/checks.tsv (the four checks the tool registry names for every
d9e0589898fd output, with what each one measured). Exit 1 when a file differs (it must then be classified by hand as
provenance-only / patched / VALUE) or when a check fails.

The four checks (registry entry "port_core d9e0589898fd SCORED"):
  1 kept image-derived counts: every segment / section fact of the run's map (base, end, size, address, instruction
    count) that a staged file states must be the target's value, read from the target's own headers by the run;
  2 GOT[0]: the first .got word of the target pin, and every staged statement of that cell;
  3 shadow offsets and model constants by role: every numeral of a staged file at or above the image hull's low end
    that the run does not account for (moved code / data value, mapped decimal, GOT row) is explained by its role and
    the role is checked against the target: an instruction word occurs in the target's .text, a shadow numeral is the
    shadow base the target's FindDynamicShadowStart returns plus a small offset, kHighMemEnd / kHighMemBeg come from
    the kHighMemEnd cell of the target lib's own YF0m.v, a cell content equals the pin's bytes at the cell (or, for a
    cell with no file bytes, the value the target lib's own YF0m.v states for that cell);
  4 'no twin' drops: every row of the run's no-twin.tsv must name a function the target symtab lacks, and every
    moved code value's target symbol+offset must resolve in the target symtab to that value.
"""
import argparse
import collections
import csv
import hashlib
import os
import re
import sys

from capstone import Cs, CS_ARCH_RISCV, CS_MODE_RISCV64, CS_MODE_RISCVC
from elftools.elf.elffile import ELFFile

NUM = re.compile(r'(?<![\w.])(0x[0-9a-fA-F]+|\d+)(?!\w|\.\w)')  # a sentence-ending '.' may follow
INSN_LINE = re.compile(r'fetch_word|decode_any|%bv : bv 32|icpt_ld8')
CELL = re.compile(r'\((0x[0-9a-fA-F]+), 8, \[\(0, 8%N, (0x[0-9a-fA-F]+|\d+)\)\]\)')


def sha(p):
    return hashlib.sha256(open(p, 'rb').read()).hexdigest()


def strip_comments(t):
    """Coq comments (nested) replaced by spaces, newlines kept, so line numbers stay."""
    out, depth, i = [], 0, 0
    while i < len(t):
        if t.startswith('(*', i):
            depth += 1
            i += 2
            continue
        if depth and t.startswith('*)', i):
            depth -= 1
            i += 2
            continue
        out.append(t[i] if (not depth or t[i] == '\n') else ' ')
        i += 1
    return ''.join(out)


def tsv(path):
    return list(csv.DictReader(open(path), delimiter='\t'))


def extract(path):
    rows = []
    for line in open(path):
        if line.startswith('#'):
            continue
        f = line.rstrip('\n').split('\t')
        rows.append((f[0], int(f[1], 16), int(f[2]), f[3]))
    return rows


def loads(pin):
    e = ELFFile(open(pin, 'rb'))
    return e, [(s['p_vaddr'], s['p_filesz'], s.data()) for s in e.iter_segments() if s['p_type'] == 'PT_LOAD']


def read(segs, a, n):
    for v, fz, d in segs:
        if v <= a and a + n <= v + fz:
            return d[a - v:a - v + n]
    return None


def map_facts(map_txt):
    """(name, old, new) of every geometry and section fact of the run's map.txt."""
    facts = []
    for line in open(map_txt):
        m = re.match(r'^\s+(\S+)\s+(0x[0-9a-f]+) -> (0x[0-9a-f]+)', line)
        if m:
            facts.append((m.group(1), int(m.group(2), 16), int(m.group(3), 16)))
            continue
        m = re.match(r'^\s+(\S+)\s+\S+ (0x[0-9a-f]+)/(0x[0-9a-f]+) -> (0x[0-9a-f]+)/(0x[0-9a-f]+)'
                     r'(?:.*insns (\d+) -> (\d+))?', line)
        if m:
            facts.append((m.group(1) + '.addr', int(m.group(2), 16), int(m.group(4), 16)))
            facts.append((m.group(1) + '.size', int(m.group(3), 16), int(m.group(5), 16)))
            if m.group(6):
                facts.append((m.group(1) + '.insns', int(m.group(6)), int(m.group(7))))
    return facts


def main():
    p = argparse.ArgumentParser()
    for k in ('--work', '--abfd', '--shipped', '--pin', '--symbols', '--files', '--log', '--out-dir'):
        p.add_argument(k, required=True)
    a = p.parse_args()
    work, rows_out, bad = a.work, [], []

    # the relocated files: --files minus the ones the run keeps from the target lib
    kept = [l.strip() for l in open(os.path.join(work, 'kept.txt')) if l.strip()]
    files = [l.strip() for l in open(a.files) if l.strip() and not l.startswith('#')]
    reloc = [f for f in files if os.path.basename(f) not in kept]

    # classification
    cls = []
    for f in reloc:
        rel = os.path.join('Reusable', os.path.basename(f))
        s, b, d = (sha(os.path.join(x, rel)) for x in (a.shipped, a.abfd, os.path.join(work, 'stage-out')))
        c = 'same' if s == b == d else 'DIFFERS'
        if c != 'same':
            bad.append(f'classify {rel}')
        cls.append((rel, s, b, d, c))
    with open(os.path.join(a.out_dir, 'classify.tsv'), 'w') as fh:
        fh.write('# file\tsha256 shipped\tsha256 abfd17f8b3d2 re-run\tsha256 d9e0589898fd dry run\tclass\n')
        for r in cls:
            fh.write('\t'.join(r) + '\n')
        n = collections.Counter(r[4] for r in cls)
        fh.write(f'# {len(cls)} files: same {n["same"]}, provenance-only 0, patched 0, VALUE 0, '
                 f'unclassified {n["DIFFERS"]}; kept from the target lib, not relocated: {" ".join(kept)}\n')

    stage = os.path.join(work, 'stage-out', 'Reusable')
    text = {os.path.basename(f): strip_comments(open(os.path.join(stage, os.path.basename(f))).read()) for f in reloc}
    check = tsv(os.path.join(work, 'check.tsv'))
    dec = tsv(os.path.join(work, 'decimals.tsv'))
    got = tsv(os.path.join(work, 'got.tsv'))
    facts = map_facts(os.path.join(work, 'map.txt'))
    hull_lo = next(n for k, o, n in facts if k == 'hull.lo')
    e, segs = loads(a.pin)
    syms = extract(a.symbols)

    def occurrences(v):
        out = []
        for f, t in text.items():
            c = sum(len(re.findall(r'(?<![\w.])' + form + r'(?!\w|\.\w)', t)) for form in {hex(v), str(v)})
            if c:
                out.append(f'{f} x{c}')
        return out

    # check 1: kept image-derived counts
    hit_old, hit_new = [], []
    for k, o, n in facts:
        if o >= 0x100 and o != n and occurrences(o):
            hit_old.append(f'{k} {o:#x}: ' + ', '.join(occurrences(o)))
        if n >= 0x100 and occurrences(n):
            hit_new.append(f'{k} {n:#x}: ' + ', '.join(occurrences(n)))
    same_dec = [r for r in dec if r['action'] == 'mapped' and r['old'] == r['new']]
    v1 = 'PASS' if not hit_old and not same_dec else 'FAIL'
    rows_out.append(('1 kept image-derived counts',
                     f'{len(facts)} segment / section facts of the run map ({sum(1 for _, o, n in facts if o != n)} differ'
                     f' between the images): staged files state the donor value of {len(hit_old)}, the target value of '
                     f'{len(hit_new)}{" (" + "; ".join(hit_new) + ")" if hit_new else ""}; mapped decimals left '
                     f'unchanged {len(same_dec)} of {sum(1 for r in dec if r["action"] == "mapped")}; files kept from the '
                     f'target lib (not relocated): {" ".join(kept)}', v1))

    # check 2: GOT[0]
    gs = e.get_section_by_name('.got')
    g0 = int.from_bytes(read(segs, gs['sh_addr'], 8), 'little')
    old_cell, old_val = int(got[0]['old_word_or_file'], 16), int(got[0]['old_value_or_line'], 16)
    st_old, st_new = occurrences(old_cell), occurrences(gs['sh_addr'])
    v2 = 'PASS' if not st_old and (not st_new or old_val == g0) else 'FAIL'
    rows_out.append(('2 GOT[0]', f'target .got {gs["sh_addr"]:#x}, GOT[0] word {g0:#x}; donor cell {old_cell:#x} held '
                     f'{old_val:#x} (got.tsv row 1, {got[0]["content"]}); staged statements of the donor cell (stale, '
                     f'a FAIL): {len(st_old)}{" (" + ", ".join(st_old) + ")" if st_old else ""}; of the target cell: '
                     f'{len(st_new)}{" (" + ", ".join(st_new) + ")" if st_new else ""}', v2))

    # check 3: shadow offsets and model constants by role
    acc = collections.defaultdict(set)
    for r in check:
        acc[r['file'].split('/')[-1]].add(int(r['new'], 0))
    for r in dec:
        if r['action'] == 'mapped':
            acc[r['file'].split('/')[-1]].add(int(r['new']))
    gotv = {int(r[k], 16) for r in got for k in ('new_word_or_old', 'new_value_or_new') if r[k].startswith('0x')}
    byname = {n: v for n, v, s, t in syms}
    fds = byname['_ZN6__asan22FindDynamicShadowStartEv']
    md = Cs(CS_ARCH_RISCV, CS_MODE_RISCV64 | CS_MODE_RISCVC)
    body = read(segs, fds, 0x40)
    luis = [int(op.split(',')[1], 16) << 12 for _, _, mn, op in md.disasm_lite(body, fds) if mn == 'lui']
    shadow = luis[0]
    khe_addr = byname['_ZN6__asan11kHighMemEndE']
    yf = open(os.path.join(a.shipped, 'Reusable', 'YF0m.v')).read()
    khe = int(re.search(r'\(ANum ' + hex(khe_addr) + r'\) (0x[0-9a-f]+)', yf).group(1), 16)
    yfcell = {int(m.group(1), 16): int(m.group(2), 16) for m in re.finditer(r'\(ANum (0x[0-9a-f]+)\) (0x[0-9a-f]+)', yf)}
    tx = e.get_section_by_name('.text')
    tdata = read(segs, tx['sh_addr'], tx['sh_size'])
    words = collections.Counter(int.from_bytes(tdata[o:o + 4], 'little') for o in range(0, len(tdata) - 3, 2))
    roles, unexplained = collections.Counter(), []
    for f, t in text.items():
        for ln, line in enumerate(t.split('\n'), 1):
            for m in NUM.finditer(line):
                v = int(m.group(1), 0)
                if v < hull_lo or v in acc[f] or v in gotv:
                    continue
                if INSN_LINE.search(line) and v < 2 ** 32 and words[v]:
                    roles['instruction word, found in the target .text'] += 1
                elif v >= 2 ** 63 and 2 ** 64 - v <= 0x800:
                    roles[f'a 12-bit immediate sign-extended to 64 bits (2^64 - {2 ** 64 - v})'] += 1
                elif abs(v - shadow) < 0x1000:
                    roles[f'shadow base {shadow:#x} (FindDynamicShadowStart lui) {v - shadow:+#x}'] += 1
                elif v == khe:
                    roles[f'kHighMemEnd {khe:#x} (YF0m cell {khe_addr:#x})'] += 1
                elif v == (khe >> 3) + shadow + 1:
                    roles[f'kHighMemBeg = (kHighMemEnd >> 3) + shadow base + 1 = {v:#x}'] += 1
                elif any(int(c.group(2), 0) == v and read(segs, int(c.group(1), 16), 8) is not None
                         and int.from_bytes(read(segs, int(c.group(1), 16), 8), 'little') == v
                         for c in CELL.finditer(line)):
                    roles['cell content, equal to the pin bytes at the cell'] += 1
                elif any(int(c.group(2), 0) == v and read(segs, int(c.group(1), 16), 8) is None
                         and yfcell.get(int(c.group(1), 16)) == v for c in CELL.finditer(line)):
                    roles['content of a cell with no file bytes (.bss), equal to the target YF0m.v cell'] += 1
                else:
                    unexplained.append(f'{f}:{ln} {m.group(1)}')
    v3 = 'PASS' if not unexplained else 'FAIL'
    rows_out.append(('3 shadow offsets and model constants by role',
                     f'numerals >= hull low end {hull_lo:#x} not accounted by the run (moved value, mapped decimal, GOT '
                     f'row): {sum(roles.values()) + len(unexplained)}; by role: '
                     + '; '.join(f'{k}: {c}' for k, c in sorted(roles.items()))
                     + f'; unexplained: {len(unexplained)}{" (" + ", ".join(unexplained[:20]) + ")" if unexplained else ""}',
                     v3))

    # check 4: 'no twin' drops
    nt = [r for r in tsv(os.path.join(work, 'no-twin.tsv')) if any(r.values())]
    names = collections.defaultdict(set)
    for n, v, s, t in syms:
        names[n].add(v)
    nt_bad = [r for r in nt if list(r.values())[5] in names]  # column 6, source_name (its header carries a note)
    unres, code = [], [r for r in check if r['class'] == 'exec']
    for r in code:
        m = re.match(r'^(.*)\+(0x[0-9a-f]+)$', r['new_sym'])
        if not m or not any(v + int(m.group(2), 16) == int(r['new'], 0) for v in names.get(m.group(1), ())):
            unres.append(f'{r["file"]}:{r["line"]} {r["new_sym"]}')
    log = open(a.log).read()
    drop = re.search(r'function table: dropped (\d+) donor pairs', log)
    v4 = 'PASS' if not nt_bad and not unres and drop and drop.group(1) == '0' else 'FAIL'
    rows_out.append(("4 'no twin' drops", f'no-twin.tsv rows {len(nt)} (named in the target symtab: {len(nt_bad)}); '
                     f'function table: dropped {drop.group(1) if drop else "?"} donor pairs (run log); moved code '
                     f'values (check.tsv class exec) whose target function+offset resolves in the target symtab to the '
                     f'value: {len(code) - len(unres)} of {len(code)}'
                     f'{" (unresolved: " + ", ".join(unres[:20]) + ")" if unres else ""}', v4))

    with open(os.path.join(a.out_dir, 'checks.tsv'), 'w') as fh:
        fh.write('# check\tmeasured\tverdict\n')
        for r in rows_out:
            fh.write('\t'.join(r) + '\n')
    bad += [r[0] for r in rows_out if r[2] != 'PASS']
    if bad:
        sys.exit('checks.py: ' + '; '.join(bad))


if __name__ == '__main__':
    main()
