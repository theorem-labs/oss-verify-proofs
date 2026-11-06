#!/usr/bin/env python3
"""Compare the image-bound definitions of an AB1w/YB1w file with the pin they claim to describe.

Checked: every `Definition tfib_<section>_lo/_hi` (section header start/end; img = page-rounded PT_LOAD hull),
tfib_entry, and the auxv values tfib_at_* (at_img_lo/hi = PT_LOAD hull, at_rw_lo/at_rw_len = page base / page-rounded
size of the last writable PT_LOAD, at_a_entry = e_entry, at_ph_addr_z = first PT_LOAD vaddr + e_phoff,
at_ph_ent_z = e_phentsize, at_ph_num_z = e_phnum).

usage: d9e0_secbounds.py FILE.v PIN [FILE.v PIN ...]
Prints one row per definition: file, line, name, file value, pin value, OK|DIFFERS, what was read from the pin.
"""
import re, sys
from elftools.elf.elffile import ELFFile

DEF = re.compile(r'Definition (tfib_[a-z0-9_]+) : Z := (0x[0-9a-fA-F]+|\d+)\.')


def pin_facts(pin):
    e = ELFFile(open(pin, 'rb'))
    secs = {s.name: (s['sh_addr'], s['sh_addr'] + s['sh_size']) for s in e.iter_sections() if s['sh_addr']}
    loads = [p for p in e.iter_segments() if p['p_type'] == 'PT_LOAD']
    lo = min(p['p_vaddr'] for p in loads) & ~0xfff
    hi = max((p['p_vaddr'] + p['p_memsz'] + 0xfff) & ~0xfff for p in loads)
    rw = [p for p in loads if p['p_flags'] & 2][-1]
    rw_lo = rw['p_vaddr'] & ~0xfff
    rw_hi = (rw['p_vaddr'] + rw['p_memsz'] + 0xfff) & ~0xfff
    h = e.header
    aux = {
        'tfib_at_img_lo': (lo, 'page-rounded PT_LOAD hull start'),
        'tfib_at_img_hi': (hi, 'page-rounded PT_LOAD hull end'),
        'tfib_img_lo': (lo, 'page-rounded PT_LOAD hull start'),
        'tfib_img_hi': (hi, 'page-rounded PT_LOAD hull end'),
        'tfib_at_rw_lo': (rw_lo, 'page base of the last writable PT_LOAD'),
        'tfib_at_rw_len': (rw_hi - rw_lo, 'page-rounded size of the last writable PT_LOAD'),
        'tfib_at_a_entry': (h['e_entry'], 'ELF header e_entry'),
        'tfib_entry': (h['e_entry'], 'ELF header e_entry'),
        'tfib_at_ph_addr_z': (min(p['p_vaddr'] for p in loads) + h['e_phoff'], 'first PT_LOAD vaddr + e_phoff'),
        'tfib_at_ph_ent_z': (h['e_phentsize'], 'ELF header e_phentsize'),
        'tfib_at_ph_num_z': (h['e_phnum'], 'ELF header e_phnum'),
    }
    return secs, aux


def main():
    args = sys.argv[1:]
    bad = n = 0
    for f, pin in zip(args[0::2], args[1::2]):
        secs, aux = pin_facts(pin)
        text = open(f, encoding='utf-8').read()
        for m in DEF.finditer(text):
            name, v = m.group(1), int(m.group(2), 0)
            line = text.count('\n', 0, m.start()) + 1
            if name in aux:
                want, what = aux[name]
            else:
                mm = re.fullmatch(r'tfib_([a-z0-9_]+?)_(lo|hi)', name)
                if not mm:
                    continue
                cand = ['.' + mm.group(1).replace('_', '.'), '.' + mm.group(1), mm.group(1)]
                sec = next((c for c in cand if c in secs), None)
                if sec is None:
                    print(f'{f}\t{line}\t{name}\t{v:#x}\t-\tNO-SECTION\tno section named {cand}')
                    bad += 1
                    n += 1
                    continue
                want = secs[sec][0] if mm.group(2) == 'lo' else secs[sec][1]
                what = f'section {sec} ' + ('start' if mm.group(2) == 'lo' else 'end')
            ok = 'OK' if v == want else 'DIFFERS'
            bad += ok != 'OK'
            n += 1
            print(f'{f}\t{line}\t{name}\t{v:#x}\t{want:#x}\t{ok}\t{what}')
    print(f'# definitions checked: {n}; differing: {bad}', file=sys.stderr)


if __name__ == '__main__':
    main()
