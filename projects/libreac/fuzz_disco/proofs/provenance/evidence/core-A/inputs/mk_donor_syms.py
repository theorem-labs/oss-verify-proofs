#!/usr/bin/env python3
"""mk_donor_syms.py SRC DONOR_PIN OUT

Writes the donor's recovered symbols (`name addr size` lines: the address checker's symbol recovery for the stripped
donor image) with one neutral header line. Every line of SRC that does not start with '#' is copied unchanged and in
order; the readers (gen_symtab.py, resolve_code.py, port_core.py) skip '#' lines. The script stops if SRC's header
does not name the sha256 of DONOR_PIN.
"""
import hashlib, sys


def main():
    src, pin, out = sys.argv[1:4]
    sha = hashlib.sha256(open(pin, 'rb').read()).hexdigest()
    lines = open(src).read().split('\n')
    head = [l for l in lines if l.startswith('#')]
    if not any(sha in l for l in head):
        sys.exit(f'mk_donor_syms: {src} does not name image sha256 {sha}')
    body = [l for l in lines if not l.startswith('#')]
    open(out, 'w').write('\n'.join([f'# symbols recovered for the stripped donor image; image sha256 {sha}'] + body))
    print(f'mk_donor_syms: {out}: {sum(1 for l in body if l.strip())} symbol lines')


if __name__ == '__main__':
    main()
