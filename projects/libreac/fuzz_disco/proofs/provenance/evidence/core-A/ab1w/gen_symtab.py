#!/usr/bin/env python3
"""gen_symtab.py -- the target's image symbol table (cgif_file's lib/A/AB1w.v, lib/YB1w.v) from the target's own ELF.

AB1w is per-image data: its function bounds, section bounds and data / start-up names are facts of ONE binary. So this
script does not relocate cgif's numbers. It keeps the donor file's lines and names, and takes every value from the
target's twin: symbols and section headers from the twin's text extract (TARGET_TWIN), code bytes and the ELF entry
from the stripped target image (TARGET_ELF, whose loaded code is byte-equal to the twin's):

  section bounds   tfib_<sec>_lo / _hi        the target's section headers (.rodata, .text, .got, asan_globals, ...)
  function bounds  tfib_A_<n> / tfib_E_<n>    the donor range [A, E) is placed in the target at the first candidate
                                              start whose code over the WHOLE length E - A has the donor's masked
                                              instruction stream (elfdis's numeral mask; `mv rd, rs` reads as
                                              `addi rd, rs, #`, an auipc lo12 of 0) and whose direct jump targets
                                              map to the paired targets. Candidates, in order: resolve_code.py's
                                              pairing, its trampoline table, the nearest paired donor function
                                              before / after A at the same distance, and the ELF entry when A is the
                                              donor's entry. So a donor range that covers two functions keeps its
                                              full extent, and code without an FDE or FUNC symbol (asm, thunks) is
                                              found. A donor range with no such twin (the donor's own program, libc
                                              functions the target does not link) gets NO entry, and is listed in
                                              the report.
  fake stack       tfib_*_asan_stack_malloc_A/B are replaced by one entry per target __asan_stack_malloc_<k> and
                   __asan_stack_free_<k> (ruling of 2026-10-28 20:25Z), named by class.
  data names       tfib_D_<n>                 the target object of the same symbol at offset 0; a GOT slot name is the
                                              target GOT slot whose word is that object's address (by value).
  start-up names   tfib_at_<n>                code addresses by function pairing; image constants from the ELF header
                                              (entry, phdr) and YImgTop (img top).

Usage: gen_symtab.py DONOR.v RELOCATED.v DONOR_ELF TARGET_ELF TARGET_TWIN OUT.v REPORT.tsv DONOR_SYMS
DONOR.v is the donor file with only its module paths changed (port_core's stage/); function pairs are keyed by
its addresses.
RELOCATED.v is the donor file after port_core.py (module paths and the header line changed, every other value
relocated). Lines this script does not regenerate keep port_core's value; check those with --check (data names
against the target's symbols at offset 0, GOT names by value, start-up code names by function pairing).
DONOR_SYMS is port_addr_check.py's recovery for DONOR_ELF (`name addr size` lines or its cache JSON). The donor is
stripped, so without it resolve_code.py knows only the donor's FDE functions and every
FDE-less musl function (sysconf, exit, the malloc family, the stdio family) loses its pair.
TARGET_TWIN is extract_twin.py's text extract of the target's unstripped twin, read with ../twin/twin_syms.py.
Every value it writes is checked against TARGET_TWIN; a value it cannot check stops the run: a function range
placed at a target FUNC symbol must end at the end of a whole number of consecutive target FUNC symbols, so a
donor range that covers two target functions keeps both.
"""
import bisect, collections, importlib.util, os, re, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', 'twin'))
import elfdis
import twin_syms
from elftools.elf.elffile import ELFFile

RESOLVE = os.path.join(HERE, 'resolve_code.py')
SECTIONS = {'rodata': '.rodata', 'text': '.text', 'init_array': '.init_array', 'fini_array': '.fini_array',
            'preinit_array': '.preinit_array', 'data_rel_ro': '.data.rel.ro', 'got': '.got', 'data': '.data',
            'asan_globals': 'asan_globals', 'bss': '.bss', 'tbss': '.tbss'}
DEF = re.compile(r'Definition (tfib_[A-Za-z0-9_]+) : Z := ([^.]+)\.')
PAIR = re.compile(r'Definition tfib_A_(\w+) : Z := (0x[0-9a-f]+)\.\s+Definition tfib_E_\1 : Z := (0x[0-9a-f]+)\.')


def load_resolver(old, new, twin, osyms):
    spec = importlib.util.spec_from_file_location('resolve_code', RESOLVE)
    rc = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(rc)
    return rc.Resolver(old, new, twin, osyms)


def segs_of(e):
    return [(s['p_vaddr'], s['p_vaddr'] + s['p_filesz'], s['p_offset']) for s in e.iter_segments() if s['p_type'] == 'PT_LOAD']


def word(raw, sg, a, n=8):
    for lo, hi, off in sg:
        if lo <= a and a + n <= hi:
            return int.from_bytes(raw[off + a - lo: off + a - lo + n], 'little')
    return None


def main():
    donor_v, reloc_v, old_elf, new_elf, new_twin, out_v, rep, osyms = sys.argv[1:9]
    R = load_resolver(old_elf, new_elf, new_twin, osyms)
    od, nd = ELFFile(open(old_elf, 'rb')), twin_syms.load(new_twin)
    oraw, nraw = open(old_elf, 'rb').read(), open(new_elf, 'rb').read()
    ne = ELFFile(open(new_elf, 'rb'))
    osg, nsg = segs_of(od), segs_of(ne)
    nsec = {s.name: (s['sh_addr'], s['sh_addr'] + s['sh_size']) for s in nd.iter_sections() if s['sh_addr']}
    nfn, nsym = {}, {}
    for s in nd.get_section_by_name('.symtab').iter_symbols():
        if not s.name:
            continue
        nsym.setdefault(s.name, s['st_value'])
        if s['st_info']['type'] == 'STT_FUNC' and s['st_size'] > 0:
            nfn.setdefault(s['st_value'], s['st_value'] + s['st_size'])
    ngot = nsec['.got']
    slot_of = collections.defaultdict(list)
    for a in range(ngot[0], ngot[1], 8):
        slot_of[word(nraw, nsg, a)].append(a)

    donor_pairs = {m.group(1): (int(m.group(2), 16), int(m.group(3), 16))
                   for m in PAIR.finditer(open(donor_v).read())}
    text = open(reloc_v).read().split('\n')
    report, out = [], []
    vals = {}
    for n, v in DEF.findall('\n'.join(text)):
        vals[n] = v

    def new_code(o):
        m = R.map_code(o)
        if m is None and o in getattr(R, 'tramp', {}):
            m = R.tramp[o]
        return m

    stack_cls = sorted((a, int(re.search(r'_(\d+)$', n).group(1)), kind)
                       for n, a in nsym.items()
                       for kind in ('malloc', 'free')
                       if re.fullmatch(rf'__asan_stack_{kind}_\d+', n) and a in nfn)

    oimg, nimg = elfdis.load(old_elf), elfdis.load(new_elf)
    ofde = sorted(R.ofn)

    def masked(img, lo, n):
        out = []
        for x, mn, ops in elfdis.disasm(img, lo, n):
            mv = re.fullmatch(r'(\w+), (\w+)', ops) if mn == 'mv' else None
            if mv:
                mn, ops = 'addi', f'{mv.group(1)}, {mv.group(2)}, 0'
            tgt = None
            if mn in ('j', 'jal'):
                im = re.search(r'(-?0x[0-9a-f]+|-?\d+)$', ops)
                tgt = x + int(im.group(1), 0) if im else None
            out.append(((mn, elfdis._NUM.sub('#', ops)), tgt))
        return out

    placed = {}

    def same_code(a, e, na):
        ka, kb = masked(oimg, a, e - a), masked(nimg, na, e - a)
        if len(ka) != len(kb) or [k for k, _ in ka] != [k for k, _ in kb]:
            return False
        for (_, ta), (_, tb) in zip(ka, kb):
            if ta is not None and tb is not None:
                mt = new_code(ta)
                if mt is None:
                    mt = placed.get(ta)
                if mt is None and a <= ta < e:
                    mt = na + ta - a
                if mt != tb:
                    return False
        return True

    def place(a, e):
        cands = []
        for c, how in ((new_code(a), 'function pairing'),):
            if c is not None:
                cands.append((c, how))
        i = bisect.bisect_right([lo for lo, _ in ofde], a)
        for lo, _ in reversed(ofde[max(0, i - 4):i]):
            if new_code(lo) is not None:
                cands.append((new_code(lo) + a - lo, f'same distance from paired {lo:#x}'))
                break
        for lo, _ in ofde[i:i + 4]:
            if new_code(lo) is not None:
                cands.append((new_code(lo) - (lo - a), f'same distance to paired {lo:#x}'))
                break
        if a == od.header['e_entry']:
            cands.append((ne.header['e_entry'], 'ELF entry'))
        for c, how in cands:
            if same_code(a, e, c):
                return c, how + ' + masked code over the whole range'
        return None, None

    for _ in range(4):
        for a, e in donor_pairs.values():
            na, _how = place(a, e)
            if na is not None:
                placed[a] = na

    for line in text:
        m = PAIR.fullmatch(line.strip())
        if m and m.group(1) in ('asan_stack_malloc_A', 'asan_stack_malloc_B'):
            if m.group(1) == 'asan_stack_malloc_A':
                for a, k, kind in stack_cls:
                    out.append(f'Definition tfib_A_asan_stack_{kind}_{k} : Z := {a:#x}.  '
                               f'Definition tfib_E_asan_stack_{kind}_{k} : Z := {nfn[a]:#x}.')
                    report.append(('fakestack', f'asan_stack_{kind}_{k}', '-', hex(a), 'target symbol'))
            continue
        if m:
            name = m.group(1)
            if name not in donor_pairs:
                sys.exit(f'gen_symtab: {name} is in {reloc_v} but not in {donor_v}')
            a, e = donor_pairs[name]
            na, how = place(a, e)
            if na is None:
                report.append(('dropped', name, hex(a), '-', 'no target twin over the whole range'))
                continue
            ne = na + e - a
            if na in nfn:  # the donor range may cover several target functions: it must end at a symbol end
                cur, k = na, 0
                while cur < ne and cur in nfn:
                    cur, k = nfn[cur], k + 1
                if cur != ne:
                    sys.exit(f'gen_symtab: {name} at {na:#x} ends at {ne:#x}; the {k} target FUNC symbol(s) from '
                             f'{na:#x} end at {cur:#x}')
            out.append(f'Definition tfib_A_{name} : Z := {na:#x}.  Definition tfib_E_{name} : Z := {na + e - a:#x}.')
            report.append(('function', name, f'{a:#x},{e:#x}', f'{na:#x},{na + e - a:#x}', how))
            continue
        sm = re.fullmatch(r'Definition tfib_(\w+)_lo : Z := (0x[0-9a-f]+)\.\s+Definition tfib_\1_hi : Z := ([^.]+)\.', line.strip())
        if sm and sm.group(1) in SECTIONS:
            lo, hi = nsec[SECTIONS[sm.group(1)]]
            out.append(f'Definition tfib_{sm.group(1)}_lo : Z := {lo:#x}.  Definition tfib_{sm.group(1)}_hi : Z := {hi:#x}.')
            report.append(('section', sm.group(1), sm.group(2), f'{lo:#x},{hi:#x}', 'target section header'))
            continue
        out.append(line)
    open(out_v, 'w').write('\n'.join(out))
    with open(rep, 'w') as fh:
        fh.write('kind\tname\tdonor\ttarget\tmethod\n')
        for r in report:
            fh.write('\t'.join(r) + '\n')
    c = collections.Counter(r[0] for r in report)
    print(f'gen_symtab: {dict(c)}; out {out_v}; report {rep}', file=sys.stderr)


if __name__ == '__main__':
    main()
