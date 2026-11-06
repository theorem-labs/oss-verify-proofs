#!/usr/bin/env python3
"""ab1w_unjudged.py LIB PIN TWIN JUDGED.tsv OUT.tsv -- every Definition of LIB/A/AB1w.v that the clause-2 classifier
did not judge (its name is not a row of JUDGED.tsv), read against fuzz_wire.asan.

Each cell's claim is read from its name and measured on the image:
  tfib_<sec>_lo / _hi           the section's sh_addr / sh_addr + sh_size (twin section table)
  tfib_entry, tfib_at_a_entry   e_entry
  tfib_gp                       the symbol __global_pointer$
  tfib_img_lo / _hi             YImgTop.IMG_LO / IMG_TOP (by name) = the first PT_LOAD's page / the image top
  tfib_at_img_lo / _hi          the same two quantities
  tfib_at_rw_lo / _rw_len       the writable PT_LOAD's page-down start / page-rounded length
  tfib_at_ph_addr_z / _ent_z / _num_z   the program headers' address (first PT_LOAD vaddr + e_phoff), e_phentsize, e_phnum
  tfib_at_x_<f>                 the start of the symbol the name gives (table SYMS below)
  tfib_at_x_<f>_k               an address inside that symbol (the column says where)
  tfib_at_shadow_off            the shadow base after start-up: the image's code reads it from the 8-byte cell
                                __asan_shadow_memory_dynamic_address, so it is the value that cell holds in the start-up
                                hand-off states (A/AB01.v, its KWord at that address)
  tfib_at_x_sniff, tfib_at_sniff_tab, tfib_at_sniff_cell   0 = the image has no sniff routine (no symbol)
  tfib_at_stops_more            the image's self-loop stops: every `j 0` / `c.j 0` (a jump to itself) of .text,
                                found by disassembling .text (capstone, RV64GC); compared with A/AB12.v's stops_more too
  tfib_at_n_res, tfib_at_x_sealed, tfib_at_x_popfree   compared with the atable record A/AB12.v (the start-up tool
                                of record's measured output) field by field
For every cell, the readers: uses of its name in LIB's .v files (comments stripped), outside its own Definition.
OUT.tsv: cell, value, claim, measured, verdict (TRUE / FALSE / SEE-NOTE), readers, note, and the next-series action
(a FALSE cell with 0 readers is a removal row; a FALSE cell with readers is a STOP)."""
import bisect, os, re, sys

sys.path.insert(0, os.environ.get('PYLIB', ''))
from elftools.elf.elffile import ELFFile
import capstone

SYMS = {'imemset': '__sanitizer_internal_memset', 'imemcpy': '__sanitizer_internal_memcpy',
        'memset': 'memset', 'memcpy': 'memcpy', 'memiszero': '_ZN11__sanitizer11mem_is_zeroEPKcm',
        'istrncpy': '_ZN11__sanitizer16internal_strncpyEPcPKcm'}


def strip(t):
    o, d, i = [], 0, 0
    while i < len(t):
        if t.startswith('(*', i):
            d += 1; i += 2; continue
        if t.startswith('*)', i) and d:
            d -= 1; i += 2; continue
        o.append(t[i] if d == 0 or t[i] == '\n' else ' ')
        i += 1
    return ''.join(o)


def main():
    lib, pin, twin, judged_p, out = sys.argv[1:6]
    e = ELFFile(open(twin, 'rb'))
    secs = {s.name: (s['sh_addr'], s['sh_addr'] + s['sh_size']) for s in e.iter_sections() if s['sh_addr']}
    syms = {}
    for s in e.get_section_by_name('.symtab').iter_symbols():
        if s['st_value'] and s.name:
            syms.setdefault(s.name, (s['st_value'], s['st_size']))
    by_addr = sorted((v, z, n) for n, (v, z) in syms.items() if z)
    keys = [x[0] for x in by_addr]

    def holder(a):
        i = bisect.bisect_right(keys, a)
        hit = [x for x in by_addr[max(0, i - 200):i] if x[0] <= a < x[0] + x[1]]
        return ('%s+0x%x' % (hit[-1][2][:60], a - hit[-1][0])) if hit else '-'

    loads = [s for s in e.iter_segments() if s['p_type'] == 'PT_LOAD']
    up = lambda a: (a + 0xfff) & ~0xfff
    img_lo, img_hi = loads[0]['p_vaddr'] & ~0xfff, up(loads[-1]['p_vaddr'] + loads[-1]['p_memsz'])
    rw = [s for s in loads if s['p_flags'] & 2]
    rw_lo = rw[-1]['p_vaddr'] & ~0xfff
    rw_len = up(rw[-1]['p_vaddr'] + rw[-1]['p_memsz']) - rw_lo
    ph_addr = loads[0]['p_vaddr'] + e.header['e_phoff']
    # the shadow offset: a lui + addi(w) pair in __asan_region_is_poisoned
    a0, z0 = syms['__asan_region_is_poisoned']
    tx = e.get_section_by_name('.text')
    code = tx.data()[a0 - tx['sh_addr']:a0 - tx['sh_addr'] + z0]
    md = capstone.Cs(capstone.CS_ARCH_RISCV, capstone.CS_MODE_RISCV64 | capstone.CS_MODE_RISCVC)
    consts = set()
    lui = {}
    for ins in md.disasm(code, a0):
        ops = [x.strip() for x in ins.op_str.split(',')]
        if ins.mnemonic in ('lui', 'c.lui'):
            lui[ops[0]] = int(ops[1], 0) << 12
        elif ins.mnemonic in ('addi', 'addiw', 'c.addi', 'c.addiw') and ops[0] in lui and len(ops) >= 2:
            src = ops[1] if len(ops) == 3 else ops[0]
            imm = int(ops[-1], 0)
            if src in lui:
                consts.add((lui[src] + imm) & 0xffffffffffffffff)
        elif ins.mnemonic in ('slli', 'c.slli') and ops[0] in lui:
            lui[ops[0]] = (lui[ops[0]] << int(ops[-1], 0)) & 0xffffffffffffffff
            consts.add(lui[ops[0]])
    consts |= set(lui.values())
    ab12 = open(os.path.join(lib, 'A', 'AB12.v')).read()
    rec = dict(re.findall(r'(\w+) := ([^;|]+?)(?=;\s*\w+ :=|\s*\|\})', ab12.replace('\n', ' ')))
    t = open(os.path.join(lib, 'A', 'AB1w.v')).read()
    st = strip(t)
    cells = re.findall(r"\bDefinition\s+([A-Za-z_][\w']*)\s*:\s*([^:=]+?)\s*:=\s*(.+?)\.(?=\s|$)", st)
    judged = {l.split('\t')[0] for l in open(judged_p).read().splitlines()[1:] if l.strip()}
    code_all = {}
    for dp, _, fn in os.walk(lib):
        for f in fn:
            if f.endswith('.v'):
                code_all[os.path.join(dp, f)] = strip(open(os.path.join(dp, f), errors='replace').read())
    rows = []
    for name, typ, val in cells:
        if name in judged:
            continue
        w = re.compile(r"(?<![\w'.])%s(?![\w'])" % re.escape(name))
        readers = sum(len(w.findall(c)) for c in code_all.values()) - 1
        v = val.strip()
        num = int(v, 0) if re.fullmatch(r'0x[0-9a-fA-F]+|\d+', v) else None
        claim, meas, note = '-', None, ''
        m = re.fullmatch(r'tfib_(\w+?)_(lo|hi)', name)
        if m and m.group(1) not in ('img', 'at_img', 'at_rw') and ('.' + m.group(1).replace('_rel_ro', '.rel.ro')) in secs:
            sn = '.' + m.group(1).replace('_rel_ro', '.rel.ro')
            claim = '%s %s' % (sn, 'start' if m.group(2) == 'lo' else 'end')
            meas = secs[sn][0 if m.group(2) == 'lo' else 1]
        elif name in ('tfib_entry', 'tfib_at_a_entry'):
            claim, meas = 'e_entry', e.header['e_entry']
        elif name == 'tfib_gp':
            claim, meas = '__global_pointer$', syms.get('__global_pointer$', (None,))[0]
        elif name in ('tfib_img_lo', 'tfib_at_img_lo'):
            claim, meas = 'the first PT_LOAD page (IMG_LO)', img_lo
            if v == 'IMG_LO':
                num, note = img_lo, 'by name: IMG_LO'
        elif name in ('tfib_img_hi', 'tfib_at_img_hi'):
            claim, meas = 'the image top (IMG_TOP)', img_hi
            if v == 'IMG_TOP':
                num, note = img_hi, 'by name: IMG_TOP'
        elif name == 'tfib_at_rw_lo':
            claim, meas = 'writable PT_LOAD page-down start', rw_lo
        elif name == 'tfib_at_rw_len':
            claim, meas = 'writable PT_LOAD page-rounded length', rw_len
        elif name == 'tfib_at_ph_addr_z':
            claim, meas = 'program headers address (PT_LOAD 0 vaddr + e_phoff)', ph_addr
        elif name == 'tfib_at_ph_ent_z':
            claim, meas = 'e_phentsize', e.header['e_phentsize']
        elif name == 'tfib_at_ph_num_z':
            claim, meas = 'e_phnum', e.header['e_phnum']
        elif name == 'tfib_at_shadow_off':
            sa = syms['__asan_shadow_memory_dynamic_address'][0]
            claim = 'the value of __asan_shadow_memory_dynamic_address (0x%x) after start-up' % sa
            ab01 = open(os.path.join(lib, 'A', 'AB01.v')).read()
            vals = set(int(x) for x in re.findall(r'a_off := %d \|\} 8 \(ELit (\d+)\)' % sa, ab01))
            meas = vals.pop() if len(vals) == 1 else None
            note = 'A/AB01.v hand-off states: KWord at 0x%x holds %s' % (sa, ', '.join('0x%x' % v for v in sorted(vals | ({meas} if meas is not None else set()))))
        elif re.fullmatch(r'tfib_at_x_(imemset|imemcpy|memset|memcpy|memiszero|istrncpy)', name):
            f = name[len('tfib_at_x_'):]
            claim, meas = 'start of %s' % SYMS[f], syms.get(SYMS[f], (None,))[0]
        elif name in ('tfib_at_x_sniff', 'tfib_at_sniff_tab', 'tfib_at_sniff_cell'):
            hits = sorted(n for n in syms if 'sniff' in n.lower())
            claim, meas = '0 = no sniff routine in the image', 0 if not hits else None
            note = 'symbols with "sniff": %s' % (hits[:3] or 'none')
        elif re.fullmatch(r'tfib_at_x_(envscan|pnscan)(_k)?', name):
            claim = 'an address in the scan routine the atable record names'
            meas = num if num is not None and holder(num) != '-' else None
        field = name[len('tfib_at_'):] if name.startswith('tfib_at_') else None
        recv = rec.get(field) if field else None
        if field == 'stops_more':
            a = [int(x, 16) for x in re.findall(r'0x[0-9a-f]+', v)]
            b = [int(x, 16) for x in re.findall(r'0x[0-9a-f]+', re.search(r'stops_more := \[(.*?)\]', ab12, re.S).group(1))]
            md.skipdata = True
            loops = sorted(ins.address for ins in md.disasm(tx.data(), tx['sh_addr'])
                           if ins.mnemonic in ('j', 'c.j') and ins.op_str.strip() in ('0', '0x0'))
            miss = [x for x in loops if x not in a]
            extra = [x for x in a if x not in loops]
            rows.append((name, '%d entries' % len(a), "the image's self-loop stops",
                         '%d in .text (A/AB12.v stops_more: %d, %s)' % (len(loops), len(b), 'the same set' if set(b) == set(loops) else 'a different set'),
                         'TRUE' if set(a) == set(loops) else 'FALSE', readers,
                         ('lacks %s' % ', '.join('0x%x (%s)' % (x, holder(x)) for x in miss) if miss else '') +
                         ('; not a self-loop: %s' % ', '.join('0x%x' % x for x in extra) if extra else '')))
            continue
        if field and recv is not None:
            rv = recv.strip()
            if typ.strip() == 'list Z':
                a = re.findall(r'0x[0-9a-f]+|\d+', v); b = re.findall(r'0x[0-9a-f]+|\d+', rv)
                note += (' | AB12 %s: %d entries, AB1w: %d; AB12 has %s that AB1w lacks' %
                         (field, len(b), len(a), [x for x in b if x not in a] or 'none'))
                verdict = 'TRUE' if a == b else 'FALSE'
                rows.append((name, v[:60], 'the atable field %s' % field, rv[:80], verdict, readers, note.strip(' |')))
                continue
            note += ' | AB12 %s := %s' % (field, rv)
            if meas is None and claim == '-':
                claim, meas = 'the atable field %s' % field, int(re.sub(r'%nat$', '', rv), 0) if re.fullmatch(r'0x[0-9a-fA-F]+|\d+', rv) else None
        if num is None and typ.strip() == 'nat':
            num = int(re.sub(r'%nat$', '', v))
        verdict = 'SEE-NOTE' if meas is None or num is None else ('TRUE' if meas == num else 'FALSE')
        if num is not None and claim.startswith('an address') and meas is not None:
            note += ' | %s' % holder(num)
        rows.append((name, v[:60], claim, '-' if meas is None else ('0x%x' % meas if meas > 999 else str(meas)), verdict,
                     readers, note.strip(' |')))
    with open(out, 'w') as o:
        o.write('cell\tvalue\tclaim (from its name)\tmeasured on fuzz_wire.asan\tverdict\treaders\tnote\tnext series\n')
        for r in rows:
            act = '-' if r[4] == 'TRUE' else ('STOP: read' if r[5] else
                  ('remove: incomplete (%s), unread' % r[3].split(' in ')[0] if 'self-loop' in r[2] else 'remove: unread'))
            if r[4] == 'FALSE' and 'self-loop' in r[2]:
                act = 'remove: incomplete (%s of %s), unread' % (r[1].split()[0], r[3].split()[0])
            o.write('\t'.join(map(str, r)) + '\t' + act + '\n')
    from collections import Counter
    print('ab1w_unjudged: %d cell(s) the classifier did not judge; %s; read %d' % (
        len(rows), dict(Counter(r[4] for r in rows)), sum(1 for r in rows if r[5] > 0)))


if __name__ == '__main__':
    main()
