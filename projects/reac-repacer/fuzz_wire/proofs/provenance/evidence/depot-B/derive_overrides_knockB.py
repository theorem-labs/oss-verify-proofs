"""derive_overrides_knockB.py [--czone VALUE] [--files LIST] UNIT IMAGES LIBREAC_IMAGES STAGE UNIT_PIN_SHA256 UNIT_TWIN_SHA256
  > overrides-knockB.tsv 2> overrides-knockB-roles.tsv
port_core --override rows for the knock-donor files of a reac-repacer image-B core (donor libreac/fuzz_knock's release
88154566652a lib/AU), by role: the image-A core's derive_overrides_knock.py (image A of fuzz_wire) for image B and any unit. UNIT:
the unit (fuzz_wire); IMAGES: reac-repacer's result directory (bin/UNIT/UNIT.asan-ubsan, unstripped/UNIT/UNIT.asan-ubsan,
whose sha256 must be UNIT_PIN_SHA256 / UNIT_TWIN_SHA256); LIBREAC_IMAGES: libreac's (fuzz_knock.asan-ubsan pin
f834165f5002, twin 6b6e06f3c924). STAGE: the relocation run's stage/ (the donor text port_core relocates; line numbers are
the donor's); with --files LIST, STAGE is the normalised donor lib itself (mkdon.sh's, same lines) and the rows are for
the files LIST names (one per line, as port_core's --files). Each donor value is ASSERTED to be its role in fuzz_knock.asan-ubsan before the unit's value of that role is
read by symbol; the lines are found in STAGE's code (comments removed):
  B/YD3b.v  every code line holding the page of __sanitizer::stackStore (knock 0x170000 / 0x171000 as decimals): the page
            of the unit's stackStore (port_core leaves a page multiple that is no bound);
  B/YD3j.v  every code line of b2_mod_cells_kept (its statement and its proof, to Qed.) holding the window end
            0x131000 = knock's page_up(common_flags_dont_use + 0x105), the page above the last cell the lemma's rows
            read (common_flags + 0x104, one byte): the unit's page_up(common_flags_dont_use + 0x105) (port_core moves
            the statement's copy by symbol, as useCounts + 0xbc0, which is not that page, and leaves the proof's);
  --czone VALUE  every code line of STAGE/B/*.v holding knock's CZONE shadow bound 0x80050000 gets VALUE (the core
            owner's value; 0x80050000 keeps it).
The A rows that keep kNodesBlockSize (0x100000) have no B twin (port_core keeps it on image B). The rows go to stdout as
port_core reads them (no comment line); each row with its role goes to stderr (file, line, old, new, role)."""
import hashlib, os, re, sys
from elftools.elf.elffile import ELFFile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from depot_classify import decomment

KNOCK = ('f834165f5002e65398e68d514ab2a5a5b10e53144f0b41b93ebbc6f895290e82',
         '6b6e06f3c924663114d38bdec02a4ca4702e9612748fb239efe28aaf84f87773')


def syms(pin, twin, pins):
    for p, h in ((pin, pins[0]), (twin, pins[1])):
        if hashlib.sha256(open(p, 'rb').read()).hexdigest() != h:
            sys.exit('PIN MISMATCH %s' % p)
    st = ELFFile(open(twin, 'rb')).get_section_by_name('.symtab')
    return {s.name: (s['st_value'], s['st_size']) for s in st.iter_symbols() if s.name}


def code_lines(path):
    return decomment(open(path).read()).split('\n')


def main():
    args = sys.argv[1:]
    czone, flist = None, None
    while args[:1] in (['--czone'], ['--files']):
        if args[0] == '--czone':
            czone = args[1]
        else:
            flist = open(args[1]).read().split()
        args = args[2:]
    unit, imgs, lri, stage, upin, utwin = args

    def src(f):
        return os.path.join(stage, f if flist is None else f[len('B/'):])
    w = syms('%s/bin/%s/%s.asan-ubsan' % (imgs, unit, unit), '%s/unstripped/%s/%s.asan-ubsan' % (imgs, unit, unit),
             (upin, utwin))
    k = syms(lri + '/bin/fuzz_knock/fuzz_knock.asan-ubsan', lri + '/unstripped/fuzz_knock/fuzz_knock.asan-ubsan', KNOCK)
    out, roles = [], []

    def row(f, ln, old, new, why):
        out.append('%s\t%d\t%s\t%s' % (f, ln, old, new))
        roles.append('%s\t%d\t%s\t%s\t%s' % (f, ln, old, new, why))

    def lines_with(f, val, lo=0, hi=None):
        c = code_lines(src(f))
        return [i + 1 for i in range(lo, len(c) if hi is None else hi) if re.search(r'(?<![\w.])%s(?![\w.])' % re.escape(val), c[i])]
    s = '_ZN11__sanitizerL10stackStoreE'
    kp, wp = k[s][0] & ~0xfff, w[s][0] & ~0xfff
    assert (kp, kp + 0x1000) == (0x170000, 0x171000), k[s]
    why = ('the page of StackStore stackStore (the 4 KiB page [p, p + 0x1000) the store block must avoid): knock %#x in page '
           '%#x, %s %#x in page %#x; port_core left them (a page multiple that is no bound)' % (k[s][0], kp, unit, w[s][0], wp))
    for old, new in ((kp, wp), (kp + 0x1000, wp + 0x1000)):
        hits = lines_with('B/YD3b.v', '%d' % old)
        if not hits:
            sys.exit('derive_overrides_knockB: B/YD3b.v holds %d in no code line' % old)
        for ln in hits:
            row('B/YD3b.v', ln, '%d' % old, '%d' % new, why)
    s = '_ZN11__sanitizer21common_flags_dont_useE'
    page_up = lambda a: (a + 0xfff) & ~0xfff
    # the cells mod_cells / mnr_cells read: 2 GOT slots, PageSizeCached (8), common_flags_dont_use + 0x90 (8) and
    # + 0x104 (1); the last ends at common_flags_dont_use + 0x105, and the window ends at the page above it
    kend, wend = page_up(k[s][0] + 0x105), page_up(w[s][0] + 0x105)
    assert kend == 0x131000, k[s]
    c = code_lines(src('B/YD3j.v'))
    st = [i for i, l in enumerate(c) if re.match(r'\s*Lemma b2_mod_cells_kept\b', l)]
    if len(st) != 1:
        sys.exit('derive_overrides_knockB: B/YD3j.v has %d statements of b2_mod_cells_kept' % len(st))
    qed = next(i for i in range(st[0], len(c)) if re.search(r'\bQed\.', c[i]))
    why = ('the end of the frame-free window of b2_mod_cells_kept = page_up(common_flags_dont_use + 0x105), the page above '
           'the last cell its rows read (knock %#x + 0x105 -> %#x, %s %#x + 0x105 -> %#x): port_core moves the statement\'s '
           'copy by symbol (useCounts + 0xbc0, not that page) and leaves the proof-body copies' % (k[s][0], kend, unit, w[s][0], wend))
    hits = lines_with('B/YD3j.v', '0x131000', st[0], qed + 1)
    if not hits:
        sys.exit('derive_overrides_knockB: b2_mod_cells_kept holds 0x131000 in no code line')
    for ln in hits:
        row('B/YD3j.v', ln, '0x131000', '%#x' % wend, why)
    if czone:
        for f in sorted(os.listdir(os.path.join(stage, 'B')) if flist is None else flist):
            if f.endswith('.v'):
                for ln in lines_with('B/' + f, '0x80050000'):
                    row('B/' + f, ln, '0x80050000', czone, 'CZONE shadow bound: the core owner\'s value %s' % czone)
    print('\n'.join(out))
    print('file\tline\told\tnew\trole\n' + '\n'.join(roles), file=sys.stderr)


if __name__ == '__main__':
    main()
