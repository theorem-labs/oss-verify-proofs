#!/usr/bin/env python3
"""gen_exitW.py (reac-repacer/fuzz_wire, image B = asan-ubsan) -- relocate cgif_file_fuzzer's image-B exit-certificate
files lib/YE23.v (exit data), lib/YD1y.v (driver windows) and lib/YE37.v (x2 ranges) onto fuzz_wire.asan-ubsan.

Method of record: libreac/fuzz_decode's exit-driver relocation (EXITDRV.md + exitdrv.py) as the fuzz_uci image-B lane
carried it to image B (gen_exitB.py, sha256 441280f2f70e98529ef11dcf17678226dd280a506b1236294ed020fb0b2a61a0); this
file is that script with the target parameterised and with the n = 0 (no asan_globals) branches added. It runs on
either target: --target wire (the output) or --target uci (CONTROL C0: the same code must reproduce the fuzz_uci B
lane's three files byte for byte below their headers).
rule 24: no function proved. This tool only MOVES numerals; module paths are renamed afterwards by nsW.py (port_core's
rename_text). Every value comes from the target's pinned image BYTES or, to NAME an address, its unstripped twin's
.symtab; never by eye:

  code pc  : the identical cgif function that contains it (binmatch.cgif.asan-ubsan.json, the shared binmatch.py run
             unchanged by run_binmatch_wireB.py), moved by that function's delta (new = cgif - delta).
  data addr: the asan-ubsan data map cgif -> target (made by the image address-map tool (sha256 4d51ec1c0069) as
             port_core 0e4e065eab9f ran it; sha256 pinned below):
             new = new_lo + (cgif - old_lo); the new address is then NAMED in the twin (symbol, section, or a .got slot
             by the pointer it holds). A cell end one past a run = prev + 1.
  shadow   : shadow(a) = (a >> 3) + 0x7fff8000.  XW2's shadow disjuncts and YE37's x2_shw are GENERATED from the
             image's asan_globals descriptors: one [shadow(beg), shadow(beg + size_with_redzone)) per global, then the
             metadata [shadow(ag), shadow(ag + 64 n)), then (XW2 only) one range per run of ODR indicator bytes not in
             {0, -1}.
  segment  : YD1y's in_img / DRVW_rw bounds are the page-rounded PT_LOAD hull points of each image, by index.
  decimal  : YE23's 7 decimal address literals take the data rule and are written back in decimal.
  YE37     : for an image WITH descriptors, x2_rodata row bases by the data rule and pointer chunks read from the pin.
             For fuzz_wire (0 descriptors) the walk is MEASURED instead: walk_x2() executes asan.module_dtor from the
             pin, and the rows, the stack depth, the cellr cells and the shadow list are what that walk reads.

fuzz_wire.asan-ubsan has NO asan_globals section: 0 descriptors (cgif 3, decode 3, grant 13, fuzz_uci 1). Every
generator therefore takes its n = 0 branch; the line each one prints for that branch is in the log (grep 'n = 0').
Its .fini_array still holds asan.module_dtor (knock's, with 1 entry, does not), so the x2 walk EXISTS and is trivial:
module_dtor loads __start/__stop_asan_globals (both 0) and __asan_unregister_elf_globals returns at its first branch.

CONTROLS print first (CONTROLS section of the log); any failed check: exit 1 and nothing written. Fail-closed on its
inputs: every text it would write (the three files, with the donor's copied header lines, and numerals.md) passes
textguard.py (tools/, beside this directory in the slice; $W/tools in the lane) first; a forbidden token is exit 2 and
nothing is written.
Run:  python3 gen_exitW.py                       (writes $LT/exitdrv/out/{YE23,YD1y,YE37}.v + numerals.md)
      python3 gen_exitW.py --target uci          (control C0: reproduce the fuzz_uci B lane's three files)
      python3 gen_exitW.py --plant CG=UV         (negative control: forces cgif value CG -> UV, hex; d:CG=UV for a
                                                  decimal literal; writes nothing; exit 0 only if a check catches it)
      python3 gen_exitW.py --af0m YF0m.v         (adds the gates that need the unit's own YF0m)
"""
import argparse, bisect, difflib, hashlib, importlib.util, json, os, re, struct, subprocess, sys

sys.dont_write_bytecode = True


def need(name):
    v = os.environ.get(name)
    if not v:
        raise SystemExit('gen_exitW: set %s (source the lane env.sh)' % name)
    return v


# every machine-specific path comes from the lane environment; none is written here
HERE = os.path.dirname(os.path.abspath(__file__))
for _d in (os.path.join(HERE, '..', 'tools'), os.path.join(os.environ.get('W', ''), 'tools')):
    if os.path.isfile(os.path.join(_d, 'textguard.py')):
        sys.path.insert(0, _d)
        break
import textguard  # noqa: E402
LT = need('LT')
OVPI = need('HUB')
UCIREF = LT + '/exitdrv/uciref'    # snapshot of everything the fuzz_uci image-B lane supplies (its live directory is
                                   # rewritten by its owner); every file here is pinned by sha256 below
DONOR_REV, DONOR_REV2 = 'c8557374ad2e', '25e3d17bdb5059606131377a3722d585415ab5d6'
DECODE_REV = '7eb81ddb18679c904febe99207b1f7d526d27de3'    # decode B committed lib/B/{YE23,YD1y,YE37}.v
GRANT_REV = '4f87de75d6772f4c4d7a147cec9da775eaade18d'     # fuzz_grant B released lib/B/{YE23,YD1y,YE37}.v
A9CORE = 'a8fc5eedae69'                                    # the fuzz_uci image-A core commit (renderer control E2b)
CGIF = need('CB')
LR = need('LR')
DPIN, DUNS = LR + '/bin/fuzz_decode/fuzz_decode.asan-ubsan', LR + '/unstripped/fuzz_decode/fuzz_decode.asan-ubsan'
GPIN, GUNS = LR + '/bin/fuzz_grant/fuzz_grant.asan-ubsan', LR + '/unstripped/fuzz_grant/fuzz_grant.asan-ubsan'
UCI_PIN, UCI_UNS = need('U') + '/bin/fuzz_uci/fuzz_uci.asan-ubsan', need('U') + '/unstripped/fuzz_uci/fuzz_uci.asan-ubsan'
UCI_PINA, UCI_UNSA = need('U') + '/bin/fuzz_uci/fuzz_uci.asan', need('U') + '/unstripped/fuzz_uci/fuzz_uci.asan'

# --target: the image the files are written for.  'uci' is control C0 (reproduce the fuzz_uci B lane's output).
TARGETS = {
    'wire': dict(pin=need('UB'), uns=need('UBs'), name='fuzz_wire',
                 pin_sha='af4534831a4528320c7dc74ca3f64bb96e8232ed2e313f01126d10879f3417d6',
                 uns_sha='51eb4bef24252e4df6e11baa89f653d20d74e38ae684f61bc94f4fb339ac97c3',
                 binmatch=LT + '/exitdrv/binmatch/binmatch.cgif.asan-ubsan.json',
                 binmatch_sha='27dc4c8c2aeef1a0cdda4f470625f7c2fba64689da807cf5b8682609d85f1c3c',
                 datamap=LT + '/exitdrv/inputs/map.cgif2wire.asan-ubsan.json',   # named by role, not by its tool
                 datamap_sha='9d0220fa70c2232965483066f37b9c0e4bf8c571bcd273bfac07ecec0cc7dcff',
                 unit=LT + '/exitdrv/inputs/unitB', outdir=LT + '/exitdrv/out',
                 # measured facts this generator re-checks (lane measureB.py; T0.4 items 2 and 5)
                 main=0x7f758, text=(0x2ff5c, 0x67384), top=0x5f6000, ndesc=0,
                 hull=(0x10000, 0x5f6000), zero_shadow=[(0x10000, 0x5f6000)], shadow_cells={}, ref=None),
    'uci': dict(pin=UCI_PIN, uns=UCI_UNS, name='fuzz_uci',
                pin_sha='a1b86e424adde6f65d345459822690a6c21e9e606446b91b4ad25e9f3ef6e7fc',
                uns_sha='8d07ffcf594874884207465cc34ff9f3b1062f21f6d9b3622e0771fa76490b16',
                binmatch=UCIREF + '/binmatch.cgif.asan-ubsan.json',
                binmatch_sha='c59829512cef0e36b2602f2af12c561eb5538a5508eaf0af77fefad31f9c41ba',
                datamap=UCIREF + '/map.cgif2uci.asan-ubsan.json',
                datamap_sha='aeeee5afe6062584917ffee527ed34aade19512e8caa60e5a9fd2324d69e19a4',
                unit=UCIREF + '/unitB', outdir=LT + '/exitdrv/out-uci',
                main=0x7ee48, text=(0x2fbf0, 0x65fa0), top=0x5f4000, ndesc=1,
                hull=(0x10000, 0x5f4000),
                zero_shadow=[(0x10000, 0x20ca8), (0x20cc0, 0x9b9d0), (0x9ba10, 0x5f4000)],
                shadow_cells={x: 0xf9 for x in list(range(0x7fffc195, 0x7fffc198)) + list(range(0x8000b73a, 0x8000b742))},
                # C0: the fuzz_uci B lane's own outputs (gen_exitB.py 441280f2f70e), compared below their headers
                ref={'YE23': '27f4fa108e0c8c988e91afa9abd3c01e0a5ecda844144a47171d60e7f7c495f3',
                     'YD1y': '9338d848470c79edfd7b5828182fa4269309e9ba20d97069791f66ffe67e6a16',
                     'YE37': '5582074bd970c7a52d868a53a3eea6d2d442609d72be8c1a9da29de0f005c6dc'}),
}
AP = argparse.ArgumentParser()
AP.add_argument('--target', default='wire', choices=sorted(TARGETS))
AP.add_argument('--plant', action='append', default=[], help='CGIFHEX=NEWHEX: force one wrong value (control)')
AP.add_argument('--af0m', help="the unit's own YF0m.v: gates DRVW_not_owned, rodata_chk / shbyte_chk / cellr cells")
AP.add_argument('--refdir', default=LT + '/exitdrv/ref', help='C0 reference copies of the fuzz_uci B lane outputs')
ARGS = AP.parse_args()
T = TARGETS[ARGS.target]
PIN, UNS = T['pin'], T['uns']
PINA, UNSA = UCI_PINA, UCI_UNSA          # the fuzz_uci image-A pin: renderer control E2b only, never the output
BINMATCH, DATAMAP, UNIT = T['binmatch'], T['datamap'], T['unit']
SHA = {PIN: T['pin_sha'], UNS: T['uns_sha'],
       PINA: '6ea017c24525e6946fa06dc7e3075459ad2c5146d59af49873bf3c51a46e885d',
       UNSA: '56822e263d767986a76ec862cbfbee7571b0e64df2413ad18d7201205a7563fb',
       CGIF: '1c29845fe6058de6e1dbf3f6ec6abd566ea612d76b65ea5435d7ff77c63e08ef',
       DPIN: '5d05689fd5b196976890b91e68c113953d385775b9d811ef98c712b2cac7d4a9',
       DUNS: '6744989bb2e66ffa4fb48e042ecedff4a3b4ba2301f43c1217e76fd1b090d0a4',
       GPIN: 'fde52226dc48de254681156061de9263409c123ca0a0d6c5010ded4e17f602df',
       GUNS: '5a5ee7c02b4e2a1d1653dc0c256182c9b65c33dde3a7ddc98b9de2afffe7a417',
       BINMATCH: T['binmatch_sha'], DATAMAP: T['datamap_sha'],
       UCIREF + '/af0m.py': '238598b380f12c8942be11b554b5cbabe6db724ef8332835efcdacc42626758a',
       UCIREF + '/hsform.py': 'a93ebaea058faaeb14d35b1cdec31d6b4bcbe508ced124ccb1cf47e91d14adec'}
SHOFF = 0x7fff8000
TGT = T['name'] + ' B'          # the label every control line uses for the target image
U64M = (1 << 64) - 1
shadow = lambda a: (a >> 3) + SHOFF
FAIL = []
DRIVER_FILES = {'cli.c', 'adapter.c', 'wrap_getenv.c', 'wrap_mkstemp.c', 'wrap_getpid.c'}
DRIVER_GLOBALS = {'main', 'target_run', 'emit_printf', 'oft_exit_guard', 'target_alloc_init', 'target_alloc_count',
                  '__wrap_getenv', '__wrap_getpid', '__wrap_mkstemp'}   # T0.4 section 0: the same driver stream

def check(ok, what):
    if not ok:
        FAIL.append(what)
    return ok


def sha256(path):
    return hashlib.sha256(open(path, 'rb').read()).hexdigest()


def git_show(rev, path):
    r = subprocess.run(['git', '-C', OVPI, 'show', '%s:%s' % (rev, path)], capture_output=True, text=True, timeout=120)
    assert r.returncode == 0 and r.stdout, (rev, path, r.stderr)
    return r.stdout


def hx(v):
    return hex(v) if isinstance(v, int) else str(v)


# ---------------------------------------------------------------- ELF (image bytes; sections + .symtab when present)
class Elf:
    def __init__(self, path):
        self.path = path
        self.b = open(path, 'rb').read()
        assert self.b[:4] == b'\x7fELF'
        e_phoff = struct.unpack_from('<Q', self.b, 0x20)[0]
        e_phentsize, e_phnum = struct.unpack_from('<HH', self.b, 0x36)
        self.loads = []
        for i in range(e_phnum):
            o = e_phoff + i * e_phentsize
            p_type = struct.unpack_from('<I', self.b, o)[0]
            p_off, p_va, _, p_fsz, p_msz, _ = struct.unpack_from('<QQQQQQ', self.b, o + 8)
            if p_type == 1:
                self.loads.append((p_va, p_off, p_fsz, p_msz))
        self.loads.sort()
        shoff = struct.unpack_from('<Q', self.b, 0x28)[0]
        shent, shnum, shstr = struct.unpack_from('<HHH', self.b, 0x3a)
        sh = [struct.unpack_from('<IIQQQQIIQQ', self.b, shoff + i * shent) for i in range(shnum)]
        self.sec, self.syms, self.drv, self.allsym = {}, [], set(), {}
        strt = sh[shstr][4] if shnum else 0

        def nm(off, base):
            s = base + off
            return self.b[s:self.b.index(b'\0', s)].decode()
        for s in sh:
            if s[3]:
                self.sec[nm(s[0], strt)] = (s[3], s[5])
        for s in sh:
            if s[1] == 2:                                          # SHT_SYMTAB
                off, cnt, link = s[4], s[5] // s[9], sh[s[6]][4]
                cur = None
                for k in range(cnt):
                    name, info, _, _, val, size = struct.unpack_from('<IBBHQQ', self.b, off + k * s[9])
                    if (info & 0xf) == 4:                          # STT_FILE: locals that follow belong to it
                        cur = nm(name, link)
                        continue
                    if name:                                       # every named symbol, value 0 included
                        self.allsym.setdefault(nm(name, link), val)
                    if (info & 0xf) in (1, 2) and val and name:    # OBJECT / FUNC
                        n = nm(name, link)
                        self.syms.append((val, size, info & 0xf, n))
                        if ((info >> 4) == 0 and cur in DRIVER_FILES) or ((info >> 4) != 0 and n in DRIVER_GLOBALS):
                            self.drv.add(n)
        self.syms.sort()
        self.sym_lo = [x[0] for x in self.syms]

    def u(self, va, n):
        for p_va, p_off, p_fsz, p_msz in self.loads:
            if p_va <= va and va + n <= p_va + p_msz:
                return int.from_bytes(bytes(self.b[p_off + a - p_va] if a < p_va + p_fsz else 0
                                            for a in range(va, va + n)), 'little')
        return None

    def fileback(self, va, n=1):
        """True: every byte of [va, va+n) comes from the file; False: every byte is zero-fill; None: neither."""
        for p_va, p_off, p_fsz, p_msz in self.loads:
            if p_va <= va and va + n <= p_va + p_msz:
                if va + n <= p_va + p_fsz:
                    return True
                if va >= p_va + p_fsz:
                    return False
        return None

    def hull_points(self):
        segs = [(v & ~0xfff, (v + m + 0xfff) & ~0xfff) for v, o, f, m in self.loads]
        return [s[0] for s in segs] + [segs[-1][1]]

    def zero_suffix_start(self):
        p_va, p_off, p_fsz, p_msz = self.loads[-1]
        i = p_fsz
        while i > 0 and self.b[p_off + i - 1] == 0:
            i -= 1
        return p_va + i

    def section_of(self, a):
        for name, (lo, sz) in self.sec.items():
            if sz and lo <= a < lo + sz:
                return (name, a - lo)
        return None

    def names_at(self, a):
        """(names, offset) of the symbols that contain a (size > 0) or start at a; else the nearest one below."""
        i = bisect.bisect_right(self.sym_lo, a) - 1
        inside, start = [], None
        j = i
        while j >= 0 and j > i - 64:
            v, sz, t, n = self.syms[j]
            if (sz > 0 and v <= a < v + sz) or v == a:
                if start is None or v == start:
                    start = v
                    inside.append(n)
                elif v > start:
                    start, inside = v, [n]
            j -= 1
        if inside:
            return (frozenset(inside), a - start)
        if i >= 0:
            v = self.syms[i][0]
            return (frozenset(n for vv, sz, t, n in self.syms if vv == v), a - v)
        return (frozenset(), a)

    def enclosing(self, a):
        """decode's naming: the innermost sized symbol containing a, or a size-0 symbol at a."""
        i = bisect.bisect_right(self.sym_lo, a) - 1
        j = i
        while j >= 0 and j > i - 8:
            v, sz, t, n = self.syms[j]
            if sz > 0 and v <= a < v + sz:
                return (n, a - v)
            if sz == 0 and v == a:
                return (n, 0)
            j -= 1
        return None


def descriptors(E, ag, size):
    assert size % 64 == 0, size
    return [dict(beg=E.u(ag + 64 * i, 8), size=E.u(ag + 64 * i + 8, 8), swr=E.u(ag + 64 * i + 16, 8),
                 name=E.u(ag + 64 * i + 24, 8), mod=E.u(ag + 64 * i + 32, 8), dyn=E.u(ag + 64 * i + 40, 8),
                 loc=E.u(ag + 64 * i + 48, 8), odr=E.u(ag + 64 * i + 56, 8)) for i in range(size // 64)]


def odr_ranges(ds):
    """ODR indicator bytes the exit path writes 0 to (sb zero,0(a0) after `addi a1,a0,1; bgeu a1,s2(=2)`):
    indicators not in {0, -1}, merged into byte runs."""
    bs = sorted(d['odr'] for d in ds if d['odr'] not in (0, U64M))
    out = []
    for b in bs:
        if out and out[-1][1] == b:
            out[-1][1] = b + 1
        else:
            out.append([b, b + 1])
    return [tuple(r) for r in out]


def shadow_windows(E, ag, size):
    """(lo, n) per global [shadow(beg), shadow(beg + size_with_redzone)), then the metadata [shadow(ag), +64n/8).
    n = 0 branch: no global window at all, and the metadata window is the formula's own value at (ag, size) = (0, 0),
    i.e. the EMPTY window [shadow(0), shadow(0)) = (0x7fff8000, 0) -- one window, zero bytes."""
    ds = descriptors(E, ag, size)
    ws = [(shadow(d['beg']), shadow(d['beg'] + d['swr']) - shadow(d['beg'])) for d in ds]
    return ws + [(shadow(ag), shadow(ag + 64 * len(ds)) - shadow(ag))]


def xw2_shadow_line(E, ag, size):
    """n = 0 branch: one empty disjunct, `(0x7fff8000 <= a < 0x7fff8000).` (no global, no ODR range)."""
    parts = ['(%s <= a < %s)' % (hex(lo), hex(lo + n)) for lo, n in shadow_windows(E, ag, size)]
    parts += ['(%s <= a < %s)' % (hex(lo), hex(hi)) for lo, hi in odr_ranges(descriptors(E, ag, size))]
    return ' \\/ '.join(parts) + '.'


def byteset(ws):
    return {x for lo, n in ws for x in range(lo, lo + n)}


# ---------------------------------------------------------------- binmatch (identical cgif function map)
def load_funcs(path):
    d = json.load(open(path))
    assert d['build'] == 'asan-ubsan' and d['pinned_bytes_equal_unstripped'] is True, 'binmatch: pinned bytes != twin'
    fs = []
    for f in d['functions']:
        if f['status'] == 'identical' and f['cj_addr'] and f['fm_addr']:
            cj, fm = int(f['cj_addr'], 16), int(f['fm_addr'], 16)
            fs.append((cj, f['size'], cj - fm, f['name']))           # uci = cgif - delta
    fs.sort()
    return fs, [x[0] for x in fs], d


def code_reloc(pc):
    i = bisect.bisect_right(FLO, pc) - 1
    if i >= 0:
        cj, sz, delta, name = FS[i]
        if cj <= pc < cj + sz:
            return (pc - delta, name, pc - cj)
    return None


# ---------------------------------------------------------------- data map (asan-ubsan cgif -> fuzz_uci data runs)
def data_reloc(a):
    i = bisect.bisect_right(RLO, a) - 1
    if i >= 0 and RUNS[i]['old_lo'] <= a < RUNS[i]['old_hi']:
        return RUNS[i]['new_lo'] + (a - RUNS[i]['old_lo'])
    return None


def ptr_reloc(v):
    """the uci image of a cgif image POINTER value: code rule, section start/end rule, else data rule."""
    if is_code(v):
        r = code_reloc(v)
        return (r[0], 'binmatch %s+%d' % (r[1], r[2])) if r else (None, 'code outside identical functions')
    for edge in ('start', 'end'):                       # a section start wins over the end of the section before it
        for name, (lo, sz) in EC.sec.items():
            if sz and name in EU.sec and v == (lo if edge == 'start' else lo + sz):
                ul, us = EU.sec[name]
                return (ul if edge == 'start' else ul + us, 'section %s %s' % (name, edge))
    d = data_reloc(v)
    if d is not None:
        return (d, 'data map')
    d0 = data_reloc(v - 1)
    return (d0 + 1, 'data map: end = prev+1') if d0 is not None else (None, 'no data map image')


# ---------------------------------------------------------------- inputs
for p, h in SHA.items():
    assert sha256(p) == h, 'pin mismatch: %s' % p
EU, UU = Elf(PIN), Elf(UNS)              # the target image B: bytes / names
EUA, UUA = Elf(PINA), Elf(UNSA)          # fuzz_uci image A: the 8-word renderer control (E2b) only
EC = Elf(CGIF)                           # cgif donor image B (stripped; section headers present, no .symtab)
ED, UD = Elf(DPIN), Elf(DUNS)            # decode B: control + role identity only
EG, UG = Elf(GPIN), Elf(GUNS)            # grant B: control + driver-cell cross-check only
FS, FLO, BMJ = load_funcs(BINMATCH)
EMAP = json.load(open(DATAMAP))
assert EMAP['old']['sha256'] == SHA[CGIF] and EMAP['new']['sha256'] == SHA[PIN], 'data map is not cgif.B -> target B'
RUNS = sorted(EMAP['runs'], key=lambda r: r['old_lo'])
RLO = [r['old_lo'] for r in RUNS]
CG_TEXT = EC.sec['.text']
is_code = lambda a: CG_TEXT[0] <= a < CG_TEXT[0] + CG_TEXT[1]
is_shadow = lambda a: SHOFF <= a < 0x80010000
CG_LO, CG_HI = EC.hull_points()[0], EC.hull_points()[-1]
is_cg_img = lambda a: CG_LO <= a < CG_HI

N0 = []           # every line a generator prints for its n = 0 (no descriptor) branch; shown in CONTROLS

def agrange(E, U, tag):
    """(base, size) of the image's asan_globals descriptor array.
    n = 0 branch (fuzz_wire): the image has NO asan_globals section, so the array is EMPTY. Its base and end are the
    twin's __start_asan_globals / __stop_asan_globals (both 0); the .got cells asan.module_ctor / asan.module_dtor
    pass to __asan_(un)register_elf_globals are checked against them from the pin in the x2 walk (walk_x2)."""
    if 'asan_globals' in E.sec:
        return E.sec['asan_globals']
    st, sp = U.allsym.get('__start_asan_globals'), U.allsym.get('__stop_asan_globals')
    check(st == 0 and sp == 0, '%s: no asan_globals section, but the twin has __start/__stop_asan_globals = %s / %s'
          % (tag, hx(st), hx(sp)))
    N0.append('agrange(%s): NO asan_globals section; twin __start_asan_globals = %s, __stop_asan_globals = %s -> '
              'descriptor array (%s, %s), 0 descriptors' % (tag, hx(st), hx(sp), hex(0), hex(0)))
    return (0, 0)


AG = {'U': agrange(EU, UU, T['name'] + ' B'), 'C': EC.sec['asan_globals'], 'D': ED.sec['asan_globals'],
      'G': EG.sec['asan_globals']}

KEEP = {0x130: 'atexit region size = builtin+280 - finished_atexit (asserted equal in the target image)',
        0xffffffff: 'FILE.lock sentinel -1 (u32), read from the pin at F_STDIN+140 / F_STDERR+140'}
KEEP_DEC = {65536: 'stack window size 64 KiB (sp0 - 65536 / - 65536), image-independent',
            4194303: 'tid upper bound 2^22-1 (mkAF 1 4194303 0), not an address'}
HEX = re.compile(r'0x[0-9a-fA-F]+')
SMALL = re.compile(r"(?<![0-9A-Za-z_x.'])([0-9]{1,4})(?![0-9A-Za-z_])")
NUM = re.compile(r"0x[0-9a-fA-F]+|(?<![0-9A-Za-z_x.'])[0-9]{5,}(?![0-9A-Za-z_])")
DEC_NAME_A = {650296: 'A_GOT_canary', 664952: 'F_STDERR', 665192: 'F_STDOUT', 665432: 'F_STDIN',
              6131600: 'TFIB_TPX', 6262736: 'A_canary', 6264480: 'STDOUT_BUFA'}   # a9 / decode (image A)
END_A = {0x9df78: 0x9df68, 0x9ec78: 0x9ec68, 0x5d8655: 0x5d8654}                # a9: range ends (image A)
XW2_ANCHOR = 'Definition XW2 (a : Z) : Prop := '


# ---------------------------------------------------------------- donor text, XW2 lines, tokens
def body(text):
    """the text after the leading comment block(s) (copyright, SPDX, Modified, Generated headers)."""
    while text.startswith('(*'):
        text = text[text.index('*)') + 2:].lstrip('\n')
    return text


def xw2_lines(text):
    """the shadow part of XW2: the lines after the XW2 anchor line up to (not incl.) `Definition XW3`."""
    lines = text.split('\n')
    k = [i for i, l in enumerate(lines) if l.startswith(XW2_ANCHOR)]
    e = [i for i, l in enumerate(lines) if l.startswith('Definition XW3')]
    assert len(k) == 1 and len(e) == 1 and e[0] > k[0] + 1
    return '\n'.join(lines[k[0] + 1:e[0]])


def xw2_block(text):
    """the whole XW2 definition: the anchor line and the lines up to (not incl.) `Definition XW3`."""
    lines = text.split('\n')
    k = [i for i, l in enumerate(lines) if l.startswith(XW2_ANCHOR)][0]
    e = [i for i, l in enumerate(lines) if l.startswith('Definition XW3')][0]
    return '\n'.join(lines[k:e])


def mask_xw2(text):
    """n = 0 branch: the image registers no global and the exit writes nothing outside the walk's own stack, so XW2
    is `False` and the WHOLE definition is masked (the donor's two exit-cell disjuncts go with the shadow part)."""
    return text.replace(xw2_block(text) if not AG['U'][1] else xw2_lines(text), '@XW2SH@')


def xw2_bytes(text):
    return {x for a, b in re.findall(r'\((0x[0-9a-f]+) <= a < (0x[0-9a-f]+)\)', xw2_lines(text))
            if is_shadow(int(a, 16)) for x in range(int(a, 16), int(b, 16))}


def tokens(text):
    out = []
    for m in NUM.finditer(text):
        s = m.group(0)
        out.append(('h', int(s, 16)) if s.startswith('0x') else ('d', int(s)))
    return out


def pair(ta, tb, what, strict=True):
    if strict:
        check(len(ta) == len(tb), '%s: token count %d vs %d' % (what, len(ta), len(tb)))
    p, bad = {}, []
    for a, b in zip(ta, tb):
        if a[0] != b[0] or p.get(a, b) != b:
            bad.append((a, b, p.get(a)))
        p.setdefault(a, b)
    if strict:
        check(not bad, '%s: %d pairing mismatches %s' % (what, len(bad), bad[:4]))
    return p, len(bad)


def masknum(text):
    return NUM.sub('#', text)


def shape_diff(a, b):
    """lines that differ between a and b once every numeral (hex, decimal >= 5 digits) is masked."""
    la, lb = masknum(a).split('\n'), masknum(b).split('\n')
    out = []
    for op, i1, i2, j1, j2 in difflib.SequenceMatcher(None, la, lb, autojunk=False).get_opcodes():
        if op != 'equal':
            out.append((op, i1 + 1, i2, j1 + 1, j2, la[i1:i2], lb[j1:j2]))
    return out


# ---------------------------------------------------------------- roles (identity of a value in an image)
def target_role(E, U, t):
    ts = U.section_of(t)
    n, off = dname(U, t) if not (ts and ts[0] == '.text') else U.names_at(t)
    return ('code' if ts and ts[0] == '.text' else 'data', n, off)


XREF = {}


def xrefs(E, text):
    """{target: [pc of the lo instruction]} of every pc-relative data reference in .text, by a linear RV64GC decode:
    `auipc rd, hi` followed within 8 instructions by an addi / load / store (I- or S-type, also FP) whose base is rd
    (rd not written in between). Compressed instructions are stepped over (2 bytes)."""
    key = E.path
    if key in XREF:
        return XREF[key]
    lo, sz = text
    b = E.b
    p_va, p_off = [(v, o) for v, o, f, m in E.loads if v <= lo < v + f][0]
    off0 = p_off + lo - p_va
    ins = []
    a = 0
    while a < sz:
        h = b[off0 + a] | (b[off0 + a + 1] << 8)
        if h & 3 != 3:
            ins.append((lo + a, None))
            a += 2
            continue
        ins.append((lo + a, int.from_bytes(b[off0 + a:off0 + a + 4], 'little')))
        a += 4
    sx = lambda v, n: v - (1 << n) if v & (1 << (n - 1)) else v
    out = {}
    for i, (pc, w) in enumerate(ins):
        if w is None or w & 0x7f != 0x17:
            continue
        rd = (w >> 7) & 31
        hi = pc + sx(w & 0xfffff000, 32)
        for pc2, w2 in ins[i + 1:i + 9]:
            if w2 is None:
                continue
            op, rs1 = w2 & 0x7f, (w2 >> 15) & 31
            if op in (0x03, 0x07, 0x13) and rs1 == rd and (op != 0x13 or (w2 >> 12) & 7 == 0):
                out.setdefault(hi + sx(w2 >> 20, 12), []).append(pc2)
                if op != 0x07 and (w2 >> 7) & 31 == rd:
                    break
            elif op in (0x23, 0x27) and rs1 == rd:
                out.setdefault(hi + sx(((w2 >> 25) << 5) | ((w2 >> 7) & 31), 12), []).append(pc2)
            elif op not in (0x23, 0x27, 0x63) and (w2 >> 7) & 31 == rd:
                break
    XREF[key] = out
    return out


def xref_role(E, U, a, text):
    """the code that references a: [(function names, offset)] -- named by the twin (U) or, for cgif (no .symtab), by
    binmatch's identical function (name, offset)."""
    out = []
    for pc in sorted(xrefs(E, text).get(a, [])):
        if U is None:
            r = code_reloc(pc)
            out.append((frozenset({r[1]}), r[2]) if r else (frozenset({'?'}), pc))
        else:
            out.append(U.names_at(pc))
    return out


def xref_match(ra, rb):
    """same referencing code: equal counts, and each (names, off) of ra pairs with one of rb (same off, a common name)."""
    if len(ra) != len(rb):
        return False
    rest = list(rb)
    for n, o in ra:
        k = [i for i, (n2, o2) in enumerate(rest) if o2 == o and n & n2]
        if not k:
            return False
        rest.pop(k[0])
    return True


def xstr(r):
    return ', '.join('%s+%d' % ('/'.join(sorted(n)), o) for n, o in r) or 'none'


def dname(U, v):
    """(names, offset) of a data address, independent of the layout around it: (1) the symbols that contain v / start
    at v; else (2) a section that starts at v (e.g. asan_globals); else (3) one past the end of the sized symbol that
    ends at v (a cell end); else (4) the section and section offset. Never the nearest symbol below (its offset depends
    on the layout)."""
    if U.enclosing(v) is not None:
        return U.names_at(v)
    st = [n for n, (lo, sz) in U.sec.items() if sz and lo == v]
    if st:
        return (frozenset('<%s>' % n for n in st), 0)
    e = U.enclosing(v - 1)
    if e is not None:
        return (frozenset({e[0]}), e[1] + 1)
    s = U.section_of(v)
    return (frozenset({'<%s>' % s[0]}), s[1]) if s else (frozenset({'<no section>'}), v)


def ag_start(E, U):
    """where this image's asan_globals descriptor array BEGINS, and how that was read.
    n = 0 branch: with no asan_globals section the array is empty and begins one past the last byte of .data -- the
    address the donor's section start maps to (data map `cell end = prev + 1`)."""
    if 'asan_globals' in E.sec:
        return E.sec['asan_globals'][0], 'asan_globals section start'
    lo, sz = E.sec['.data']
    return lo + sz, '.data end (no asan_globals section: the empty array begins here)'


def role(E, U, v, kind):
    """code: function names+offset; hull: hull point index; .got: the pointer the slot holds (a 0 slot: the pointer
    of the slot before it); agstart: this image's own asan_globals array start; data: symbol names+offset (or
    section+offset, dname) and the section."""
    if kind == 'CODE':
        n, off = U.names_at(v)
        return ('code', n, off)
    if kind == 'SEG':
        hp = E.hull_points()
        return ('hull', hp.index(v) if v in hp else None)
    if kind == 'AGS':
        a, how = ag_start(E, U)
        return ('agstart', v == a, how)
    s = U.section_of(v)
    if s and s[0] == '.got':
        tgt = E.u(v, 8)
        if tgt == 0:
            return ('got0', target_role(E, U, E.u(v - 8, 8)))
        return ('got', target_role(E, U, tgt))
    n, off = dname(U, v)
    return ('data', n, off, s[0] if s else None, s[1] if s else None)


def roles_equal(a, b):
    if a[0] != b[0]:
        return False
    if a[0] == 'code':
        return bool(a[1] & b[1]) and a[2] == b[2]
    if a[0] == 'data':
        return bool(a[1] & b[1]) and a[2] == b[2] and a[3] == b[3]
    if a[0] in ('got', 'got0'):
        return a[1][0] == b[1][0] and bool(a[1][1] & b[1][1]) and a[1][2] == b[1][2]
    if a[0] == 'agstart':
        return a[1] is True and b[1] is True     # each value is ITS OWN image's asan_globals array start
    return a == b


def rstr(r):
    ns = lambda x: '/'.join(sorted(x))
    if r[0] == 'code':
        return 'code %s+%d' % (ns(r[1]), r[2])
    if r[0] == 'data':
        return 'data %s+%d [%s+%s]' % (ns(r[1]), r[2], r[3], hex(r[4]) if r[4] is not None else '?')
    if r[0] == 'got':
        return '.got slot -> %s %s+%d' % (r[1][0], ns(r[1][1]), r[1][2])
    if r[0] == 'got0':
        return '.got slot = 0, after the slot -> %s %s+%d' % (r[1][0], ns(r[1][1]), r[1][2])
    if r[0] == 'agstart':
        return 'asan_globals array start: %s, %s' % ('yes' if r[1] else 'NO', r[2])
    return 'hull point %s' % r[1]


def is_driver_role(r, U):
    names = set()
    if r[0] in ('code', 'data'):
        names = set(r[1])
    elif r[0] in ('got', 'got0'):
        names = set(r[1][1])
    return bool(names & U.drv)


# ---------------------------------------------------------------- maps (YE23 / YD1y)
def classify_and_map(vals_hex, vals_dec, is_d1y, dec_expect, dec_name):
    """cgif value -> (uci value, kind, rule).  Raises on an unmapped value."""
    m = {}
    hp_c, hp_u = EC.hull_points(), EU.hull_points()
    for v in sorted(vals_hex):
        if v in KEEP:
            m[('h', v)] = (v, 'CONST', KEEP[v])
        elif is_d1y and v in hp_c:
            i = hp_c.index(v)
            m[('h', v)] = (hp_u[i], 'SEG', 'page-rounded PT_LOAD hull point %d' % i)
        elif is_code(v):
            r = code_reloc(v)
            assert r, 'code pc %s outside every identical function' % hex(v)
            m[('h', v)] = (r[0], 'CODE', 'binmatch identical %s+%d (delta %s)' % (r[1], r[2], hex(v - r[0])))
        elif is_shadow(v):
            m[('h', v)] = (None, 'SHADOW', 'XW2 generator (asan_globals descriptors)')
        else:
            d = data_reloc(v)
            rule = 'data map'
            if d is None:
                d0 = data_reloc(v - 1)
                assert d0 is not None, 'data %s outside every data map run' % hex(v)
                d, rule = d0 + 1, 'data map: cell end = prev+1'
            if v == AG['C'][0]:          # the donor's asan_globals array start
                a, how = ag_start(EU, UU)
                check(d == a, 'asan_globals array start: data map gives %s, the image says %s (%s)' % (hx(d), hex(a), how))
                rule += '; the asan_globals array start = %s' % how
                if not AG['U'][1]:
                    N0.append('classify_and_map(%s): the donor asan_globals start %s maps to %s = %s'
                              % (hex(v), hex(v), hex(d), how))
            m[('h', v)] = (d, 'DRV' if is_d1y else 'DATA', rule)
    for v in sorted(vals_dec):
        if v in KEEP_DEC:
            m[('d', v)] = (v, 'CONST', KEEP_DEC[v])
        else:
            assert not is_d1y and v in dec_expect, 'unexpected decimal %d' % v
            d = data_reloc(v)
            assert d is not None, v
            m[('d', v)] = (d, 'DEC', 'data map (%s)' % dec_name[v])
    return m


def substitute(text, m):
    miss = []

    def rep(mo):
        s = mo.group(0)
        k = ('h', int(s, 16)) if s.startswith('0x') else ('d', int(s))
        if k in m and m[k][0] is not None:
            return hex(m[k][0]) if k[0] == 'h' else str(m[k][0])
        miss.append(s)
        return s
    return NUM.sub(rep, text), miss


REC = {'wire': 'WireSyms', 'uci': 'UciSyms'}
UNITPATH = {'wire': 'reac-repacer/fuzz_wire', 'uci': 'reac-repacer/fuzz_uci'}
# the generator clause of the Read-from line: the tool by its name and the sha256 of the file that ran (comment-formats
# row CL7b; the owner's ruling: a proof file cites no path, which may not resolve). The uci target is control C0 only,
# compared below its headers, so its clause stays as the fuzz_uci lane wrote it.
SELF_SHA12 = hashlib.sha256(open(os.path.abspath(__file__), 'rb').read()).hexdigest()[:12]
GENERATOR = {'wire': 'gen_exitW.py (sha256 %s; internal record)' % SELF_SHA12,
             'uci': 'provenance/evidence/startup-B/exitdrv/gen_exitB.py'}


def header(src, extra):
    """the two lane header lines. Header rule: no host path, no agent / lane name, no date, no clock time, no cold
    branch name; the donor unit by its repo-relative path, the donor commit as a bare sha, the image sha256s."""
    return ('(* Modified by Theorem Labs: copied from proofs/cgif/cgif_file_fuzzer/%s (commit 25e3d17bdb50, donor '
            'image sha256 1c29845fe605), with its module paths changed, its record name changed to %s and its '
            'addresses moved to %s\'s ASan+UBSan build by libreac/fuzz_decode\'s exit-driver method (code by '
            'binmatch\'s identical-function map, data by the image address map (map tool sha256 4d51ec1c0069) and '
            'symbol name, shadow by (a >> 3) + 0x7fff8000, '
            'segments by page-rounded PT_LOADs)%s. *)\n'
            '(* Read from: %s.asan-ubsan (the %s asan-ubsan pin) sha256 %s; unstripped twin sha256 %s; generator %s. *)\n'
            % (src, REC[ARGS.target], UNITPATH[ARGS.target], extra, T['name'], UNITPATH[ARGS.target],
               SHA[PIN], SHA[UNS], GENERATOR[ARGS.target]))


DATED = re.compile(r'\(\* Modified by Theorem Labs' + r', \d{4}-\d{2}(-\d{2})?: ')


def with_header(donor, hdr):
    """insert the two header lines after the donor's 3 leading comment lines (copyright, SPDX, Modified); the donor's
    own modification notice is UNDATED here (header rule: a committed comment carries no date)."""
    L = donor.split('\n')
    assert all(L[i].startswith('(*') and L[i].endswith('*)') for i in range(3)) and not L[3].startswith('(*')
    head = [DATED.sub('(* Modified by Theorem Labs: ', x) for x in L[:3]]
    return '\n'.join(head) + '\n' + hdr + '\n'.join(L[3:])


# ---------------------------------------------------------------- cells read from the pin (YE23)
CELL_RES = [
    re.compile(r'\((0x[0-9a-f]+|F_STD\w+ \+ \d+), (\d+)%N, (0x[0-9a-f]+|\d+|F_STD\w+)\)'),
    re.compile(r'YP09\.mkChunk \(?(0x[0-9a-f]+|F_STD\w+ \+ \d+)\)? \(CVal (\d+) \(SLit (0x[0-9a-f]+|\d+|\w+)\)\)'),
    re.compile(r'cellr (0x[0-9a-f]+|A_\w+) (\d+) \(SLit (0x[0-9a-f]+|\d+|\w+)\)'),
    re.compile(r'val_mem tfibsegs \(mrestrict \(w_H W\) m\) (0x[0-9a-f]+) (\d+) (0x[0-9a-f]+|\d+)')]


def cell_checks(text, consts, E):
    def ev(s):
        s = s.strip()
        if '+' in s:
            a, b = s.split('+')
            return consts[a.strip()] + int(b)
        if s in consts:
            return consts[s]
        return int(s, 16) if s.startswith('0x') else int(s)
    rows, seen = [], set()
    head = text[:text.index('Definition ss_exP ')]
    for rx in CELL_RES:
        for a, n, v in rx.findall(head):
            key = (ev(a), int(n), ev(v))
            if key in seen:
                continue
            seen.add(key)
            addr, size, val = key
            fb = E.fileback(addr, size)
            got = E.u(addr, size)
            if fb is True:
                ok = check(got == val, 'cell %s/%d: pin holds %s, file says %s' % (hex(addr), size, hx(got), hx(val)))
                rows.append((addr, size, val, 'PIN', hx(got), ok))
            else:
                ok = check(fb is False and got == 0, 'cell %s/%d: not in the zero-fill part' % (hex(addr), size))
                rows.append((addr, size, val, 'BSS', 'zero-fill (runtime exit state)', ok))
    return sorted(rows)


# ---------------------------------------------------------------- AF0m-form tables (Tfib_const / zero shadow / owned)
def af0m_tables(text):
    t = re.sub(r'\(\*.*?\*\)', '', text, flags=re.S)
    cells = []
    for name in ('Tfib_const_abs', 'Tfib_const_shadow'):
        if 'Definition %s' % name not in t:
            continue
        i = t.index('Definition %s' % name)
        cells += [(int(a, 0), int(w), int(v, 0)) for w, a, v in
                  re.findall(r'z(\d) \(ANum (0x[0-9a-fA-F]+|\d+)\) (0x[0-9a-fA-F]+|\d+)', t[i:t.index('].', i)])]
    zs = []
    if 'Definition Tfib_zero_shadow' in t:
        i = t.index('Definition Tfib_zero_shadow')
        zs = [(int(a, 16), int(eval(l))) for a, l in re.findall(r'\((0x[0-9a-f]+), ([^()]+?)\)', t[i:t.index('].', i)])]
    own = []
    if 'Definition Tfib_owned_static' in t:
        i = t.index('Definition Tfib_owned_static')
        own = [(int(a, 16), int(eval(l.strip()))) for a, l in re.findall(r'\((0x[0-9a-f]+), ([^)]+)\)', t[i:t.index('].', i)])]
    return cells, zs, own


def first_cell(cells, a):
    for c in cells:
        if c[0] == a:
            return c
    return None


# ---------------------------------------------------------------- the exit x2 walk, MEASURED on the pin
# Used for the n = 0 branch: with no descriptors the donor's x2_rodata rows are the ones the UNREGISTER LOOP reads,
# and that loop never runs. So nothing is relocated for YE37's rows: the walk is executed on the pin, instruction by
# instruction, and the rows / stack depth / cells are what it reads. capstone (5.0.7, the method's disassembler of
# record, as in C3b) decodes; every instruction is modelled explicitly and anything else REFUSES the run.
XREGS = ['zero', 'ra', 'sp', 'gp', 'tp', 't0', 't1', 't2', 's0', 's1', 'a0', 'a1', 'a2', 'a3', 'a4', 'a5', 'a6', 'a7',
         's2', 's3', 's4', 's5', 's6', 's7', 's8', 's9', 's10', 's11', 't3', 't4', 't5', 't6']
SP0 = 1 << 46                  # the walk's sp0: ss_x2's fact says 2^44 <= sp0 <= 2^47, 16-aligned
RA0 = (1 << 62) | 0x5a0        # sentinel return address: the walk ends when it jumps here
LOADW = {'lb': (1, True), 'lh': (2, True), 'lw': (4, True), 'ld': (8, False), 'lbu': (1, False),
         'lhu': (2, False), 'lwu': (4, False)}
STOREW = {'sb': 1, 'sh': 2, 'sw': 4, 'sd': 8}
M64 = (1 << 64) - 1


def _cs():
    import capstone
    return capstone.Cs(capstone.CS_ARCH_RISCV, capstone.CS_MODE_RISCV64 | capstone.CS_MODE_RISCVC), capstone.__version__


def _reg(s):
    s = s.strip()
    return s if s in XREGS else None


def _imm(s):
    s = s.strip()
    neg = s.startswith('-')
    v = int(s[1:] if neg else s, 0)
    return -v if neg else v


class Walk:
    """a concrete RV64 execution of one exit-path function on the pinned image.
    sp0 is symbolic only in the sense that the stack is a byte map anchored at SP0; every other value is the image's."""

    def __init__(self, E, U, tag):
        self.E, self.U, self.tag = E, U, tag
        self.cs, self.csver = _cs()
        self.regs = {r: 0 for r in XREGS}
        self.stack = {}                      # byte address -> byte (only [min_sp, SP0))
        self.loads, self.stores, self.trace = [], [], []
        self.min_addr = SP0
        self.refused = None

    def _ins(self, pc):
        raw = bytes(self.E.u(pc + i, 1) for i in range(4))
        n = 2 if (raw[0] & 3) != 3 else 4
        ins = list(self.cs.disasm(raw[:n], pc))
        if len(ins) != 1 or ins[0].size != n:
            self.refused = 'pc %s: capstone did not decode one %d-byte instruction' % (hex(pc), n)
            return None
        return ins[0]

    def _rd(self, a, w):
        if a < SP0 and a + w > SP0 - (1 << 20):          # the walk's own stack frame
            self.min_addr = min(self.min_addr, a)
            if not all(a + i in self.stack for i in range(w)):
                self.refused = 'read of uninitialised stack at %s/%d' % (hex(a), w)
                return 0
            return int.from_bytes(bytes(self.stack[a + i] for i in range(w)), 'little')
        v = self.E.u(a, w)
        if v is None:
            self.refused = 'load outside the image at %s/%d' % (hex(a), w)
            return 0
        self.loads.append((a, w, v))
        return v

    def _wr(self, a, w, v):
        if a < SP0 and a + w > SP0 - (1 << 20):
            self.min_addr = min(self.min_addr, a)
            for i in range(w):
                self.stack[a + i] = (v >> (8 * i)) & 0xff
            return
        self.stores.append((a, w, v))

    def run(self, pc, a0=None, a1=None, a2=None, fuel=400):
        self.regs['sp'], self.regs['ra'] = SP0, RA0
        for n, v in (('a0', a0), ('a1', a1), ('a2', a2)):
            if v is not None:
                self.regs[n] = v
        for _ in range(fuel):
            if self.refused:
                return None
            if pc == RA0:
                return self.min_addr
            i = self._ins(pc)
            if i is None:
                return None
            self.trace.append((pc, i.mnemonic, i.op_str))
            pc = self.step(i)
            if pc is None:
                return None
            self.regs['zero'] = 0
        self.refused = 'the walk did not return within %d instructions' % fuel
        return None

    def step(self, i):
        m, ops = i.mnemonic, [x.strip() for x in i.op_str.split(',')] if i.op_str else []
        nxt = i.address + i.size
        R, sx = self.regs, lambda v: v & M64

        def bad():
            self.refused = 'pc %s: `%s %s` is not modelled' % (hex(i.address), m, i.op_str)
            return None
        if m in ('nop', 'c.nop'):
            return nxt
        if m in ('mv', 'c.mv'):
            d, s = _reg(ops[0]), _reg(ops[1])
            if d is None or s is None:
                return bad()
            R[d] = R[s]
            return nxt
        if m in ('li', 'c.li'):
            d = _reg(ops[0])
            if d is None:
                return bad()
            R[d] = sx(_imm(ops[1]))
            return nxt
        if m in ('addi', 'addiw', 'add', 'addw', 'sub', 'subw', 'and', 'andi', 'or', 'ori', 'xor', 'xori',
                 'slli', 'srli', 'srai', 'sll', 'srl', 'sra'):
            d, s1 = _reg(ops[0]), _reg(ops[1])
            if d is None or s1 is None or len(ops) != 3:
                return bad()
            s2 = _reg(ops[2])
            b = R[s2] if s2 is not None else sx(_imm(ops[2]))
            a = R[s1]
            sa = a - (1 << 64) if a >> 63 else a
            if m in ('addi', 'add', 'addiw', 'addw'):
                r = a + b
            elif m in ('sub', 'subw'):
                r = a - b
            elif m in ('and', 'andi'):
                r = a & b
            elif m in ('or', 'ori'):
                r = a | b
            elif m in ('xor', 'xori'):
                r = a ^ b
            elif m in ('slli', 'sll'):
                r = a << (b & 63)
            elif m in ('srli', 'srl'):
                r = a >> (b & 63)
            else:                                    # srai / sra
                r = sa >> (b & 63)
            r = sx(r)
            if m.endswith('w') and m != 'sw':
                r = sx(r & 0xffffffff | (M64 << 32 if r & 0x80000000 else 0))
            R[d] = r
            return nxt
        if m in ('lui', 'c.lui'):
            d = _reg(ops[0])
            if d is None:
                return bad()
            R[d] = sx(_imm(ops[1]) << 12)
            return nxt
        if m == 'auipc':
            d = _reg(ops[0])
            if d is None:
                return bad()
            R[d] = sx(i.address + (_imm(ops[1]) << 12))
            return nxt
        if m in LOADW or m in STOREW:
            mm = re.fullmatch(r'(-?\w+)\((\w+)\)', ops[1])
            d, b = _reg(ops[0]), _reg(mm.group(2)) if mm else None
            if d is None or b is None:
                return bad()
            a = sx(R[b] + _imm(mm.group(1)))
            if m in LOADW:
                w, signed = LOADW[m]
                v = self._rd(a, w)
                if signed and v >> (8 * w - 1):
                    v = sx(v - (1 << (8 * w)))
                R[d] = v
            else:
                self._wr(a, STOREW[m], R[d])
            return nxt
        if m in ('beq', 'bne', 'blt', 'bge', 'bltu', 'bgeu', 'beqz', 'bnez'):
            if m.endswith('z'):
                s1, s2, off = _reg(ops[0]), 'zero', _imm(ops[1])
                m = m[:-1]
            else:
                s1, s2, off = _reg(ops[0]), _reg(ops[1]), _imm(ops[2])
            if s1 is None or s2 is None:
                return bad()
            x, y = R[s1], R[s2]
            sx1 = x - (1 << 64) if x >> 63 else x
            sy1 = y - (1 << 64) if y >> 63 else y
            take = {'beq': x == y, 'bne': x != y, 'blt': sx1 < sy1, 'bge': sx1 >= sy1,
                    'bltu': x < y, 'bgeu': x >= y}[m]
            return (i.address + off) if take else nxt
        if m in ('j', 'c.j', 'jal', 'c.jal'):
            if m in ('jal', 'c.jal') and len(ops) == 2:
                d, off = _reg(ops[0]), _imm(ops[1])
            else:
                d, off = ('ra' if m in ('jal', 'c.jal') else 'zero'), _imm(ops[0])
            if d is None:
                return bad()
            R[d] = nxt
            return i.address + off
        if m in ('ret', 'c.ret'):
            return R['ra']
        if m in ('jr', 'c.jr'):
            s = _reg(ops[0])
            return R[s] if s is not None else bad()
        if m in ('jalr', 'c.jalr'):
            mm = re.fullmatch(r'(-?\w+)\((\w+)\)', ops[-1])
            if mm:
                d = _reg(ops[0]) if len(ops) == 2 else 'ra'
                b, off = _reg(mm.group(2)), _imm(mm.group(1))
            else:
                d, b, off = ('ra' if len(ops) == 1 else _reg(ops[0])), _reg(ops[-1]), 0
            if d is None or b is None:
                return bad()
            t = sx(R[b] + off) & ~1
            R[d] = nxt
            return t
        return bad()


def group_rows(loads):
    """the walk's image loads as x2_rodata rows: one row per run of contiguous (address, width) reads."""
    rows, cells = [], sorted({(a, w, v) for a, w, v in loads})
    for a, w, v in cells:
        if rows and rows[-1][0] + rows[-1][1] == a:
            rows[-1][1] += w
            rows[-1][2].append((a - rows[-1][0], w, v))
        else:
            rows.append([a, w, [(0, w, v)]])
    return [(b, n, cs) for b, n, cs in rows]

# ---------------------------------------------------------------- YE37 (x2 ranges)
ROW = re.compile(r'\((0x[0-9a-f]+), (\d+), \[(.*?)\]\)', re.S)
CHK = re.compile(r'\((\d+), (\d+)%N, (0x[0-9a-f]+|\d+)\)')
SHW_RE = re.compile(r'Definition x2_shw : list \(Z \* Z\) := \[(.*?)\]\.')
HR_RE = re.compile(r'assert \(Hr : (0x[0-9a-f]+) <= lo /\\ lo \+ n <= (0x[0-9a-f]+) /\\ 0 <= n\)\.')


def rodata_block(text):
    i = text.index('Definition x2_rodata')
    j = text.index('].\n', i) + 2
    rows = [(m.start(), m.end(), int(m.group(1), 16), int(m.group(2)),
             [(int(o), int(w), int(v, 0)) for o, w, v in CHK.findall(m.group(3))]) for m in ROW.finditer(text, i, j)]
    return i, j, rows


def shw_list(text):
    return [(int(a, 16), int(n)) for a, n in re.findall(r'\((0x[0-9a-f]+), (\d+)\)', SHW_RE.search(text).group(1))]


def render_desc(base, ds, fields):
    """the globals-array row in the donor's layout: per descriptor `(o, 8%N, beg); (o+8, ..size); (o+16, ..swr);   (o+32,
    ..module_name);` then `(o+40, ..); (o+48, ..); (o+56, ..odr)`, only the donor's field offsets."""
    key = {0: 'beg', 8: 'size', 16: 'swr', 24: 'name', 32: 'mod', 40: 'dyn', 48: 'loc', 56: 'odr'}
    rv = lambda v: '0' if v == 0 else hex(v)
    lines = []
    for i, d in enumerate(ds):
        f1 = [o for o in fields if o <= 32]
        f2 = [o for o in fields if o > 32]
        c1 = ['(%d, 8%%N, %s)' % (64 * i + o, rv(d[key[o]])) for o in f1]
        s1 = '; '.join(c1[:-1]) + ';   ' + c1[-1] if len(c1) > 1 else c1[0]
        s2 = '; '.join('(%d, 8%%N, %s)' % (64 * i + o, rv(d[key[o]])) for o in f2)
        lines.append(s1 + ';')
        lines.append(s2 + (';' if i + 1 < len(ds) else ''))
    return '(%#x, %d, [%s])' % (base, 64 * len(ds), '\n'.join(lines))


ALL8 = [0, 8, 16, 24, 32, 40, 48, 56]   # the 8 words of an asan_globals descriptor
A9AE37 = 'proofs/reac-repacer/fuzz_uci/lib/A/AE37.v'   # the fuzz_uci image-A core's AE37 (renderer control E2b)


def render_desc8(base, ds):
    """the globals-array row stating ALL 8 descriptor words (the donor's YE37 text omits the +24 name cell: a
    donor-text gap, not an image difference), in the image-A layout of the fuzz_uci unit's lib/A/AE37.v (core
    a8fc5eedae69, control E2b below):
    per descriptor `(o, 8%N, beg); (o+8, ..size); (o+16, ..swr); (o+24, ..name);` then `(o+32, ..module_name);
    (o+40, ..); (o+48, ..); (o+56, ..odr)`."""
    key = {0: 'beg', 8: 'size', 16: 'swr', 24: 'name', 32: 'mod', 40: 'dyn', 48: 'loc', 56: 'odr'}
    rv = lambda v: '0' if v == 0 else hex(v)
    cell = lambda i, d, o: '(%d, 8%%N, %s)' % (64 * i + o, rv(d[key[o]]))
    lines = []
    for i, d in enumerate(ds):
        lines.append('; '.join(cell(i, d, o) for o in ALL8[:4]) + ';')
        lines.append('; '.join(cell(i, d, o) for o in ALL8[4:]) + (';' if i + 1 < len(ds) else ''))
    return '(%#x, %d, [%s])' % (base, 64 * len(ds), '\n'.join(lines))


def rewrite_row(rowtxt, newbase, newvals):
    m = re.match(r'\((0x[0-9a-f]+), ', rowtxt)
    out = '(%#x, ' % newbase + rowtxt[m.end():]
    it = iter(newvals)

    def rep(mo):
        v = next(it)
        return '(%s, %s%%N, %s)' % (mo.group(1), mo.group(2), hex(v) if mo.group(3).startswith('0x') else str(v))
    return CHK.sub(rep, out)


def block(text, start, end_marker, after=0):
    """[i, j) of the text from the line starting with `start` to the end of the first line starting with end_marker."""
    i = text.index('\n' + start, after) + 1
    j = text.index('\n' + end_marker, i) + 1
    j = text.index('\n', j) + 1
    return i, j


def form_blocks(text, decode_form):
    """the 3 shw blocks: S1 = x2_shbytes .. shbyte_chk; S2 = shbyte(s)_present lemmas; S3 = shw_ok."""
    if decode_form:
        s1 = block(text, 'Definition x2_shbytes', 'Definition shbyte_chk')
        s2 = block(text, 'Lemma shbyte_present', 'Qed.')
    else:
        s1 = block(text, 'Definition x2_shw_const', '| _ => false end) x2_shbytes.')
        a, _ = block(text, 'Lemma shbytes_present', 'Qed.')
        _, b = block(text, 'Lemma shbyte0_present', 'Qed.')
        s2 = (a, b)
    s3 = block(text, 'Lemma shw_ok', 'Qed.')
    return s1, s2, s3


def walk_controls(src, cag, plant):
    """the n = 0 MEASUREMENT: execute the exit x2 walk (asan.module_dtor) on the pin and check what it does.
    Returns (X2_STK, the .got row base the walk reads, {donor exit cell -> this image's address}). The file's rows
    are the donor's rows moved by the data rule (the agreed n = 0 form); this walk is the evidence that the
    unregister loop never runs, that the two .got cells hold 0, and that nothing outside the stack is written."""
    tab, rows_out = [], []
    pf = lambda k, d: plant.get(('h', k), d) if plant else d
    # ---- W1 the walk's entry: asan.module_dtor, in .fini_array[0] of both images, binmatch-identical to cgif's
    x2_c = int(re.search(r'Definition X2_PC : Z := (0x[0-9a-f]+)\.',
                         git_show(DONOR_REV2, 'proofs/cgif/cgif_file_fuzzer/lib/YE23.v')).group(1), 16)
    x2_pc = code_reloc(x2_c)
    dtor = UU.allsym.get('asan.module_dtor')
    fini_c, fini_u = EC.sec['.fini_array'], EU.sec['.fini_array']
    e0c, e0u = EC.u(fini_c[0], 8), EU.u(fini_u[0], 8)
    okw1 = check(x2_pc is not None and dtor is not None and x2_pc[0] == dtor == e0u and e0c == x2_c,
                 'YE37 n = 0: X2_PC / asan.module_dtor / .fini_array[0] disagree')
    print('  W1 x2 walk entry: cgif X2_PC %s = its .fini_array[0] %s; binmatch identical %s+%d -> %s = the twin\'s '
          'asan.module_dtor = this image\'s .fini_array[0] %s (%s holds %d entries, cgif %d): %s'
          % (hex(x2_c), hex(e0c), x2_pc[1] if x2_pc else '?', x2_pc[2] if x2_pc else 0, hex(dtor or 0), hex(e0u or 0),
             hex(fini_u[0]), fini_u[1] // 8, fini_c[1] // 8, 'PASS' if okw1 else 'FAIL'))
    # ---- W2 run it
    w = Walk(EU, UU, T['name'] + ' B')
    ended = w.run(dtor)
    check(w.refused is None, 'YE37 n = 0: the x2 walk refused: %s' % w.refused)
    check(ended is not None, 'YE37 n = 0: the x2 walk did not return to its caller')
    check(not w.stores, 'YE37 n = 0: the x2 walk writes outside its stack: %s' % w.stores)
    stk = pf('stk', SP0 - w.min_addr)
    check(stk == SP0 - w.min_addr and stk % 16 == 0,
          'YE37 n = 0: X2_STK %s does not cover the walk\'s own stack extent %s' % (hx(stk), hex(SP0 - w.min_addr)))
    print('  W2 x2 walk MEASURED on the pin (capstone %s): %d instructions, %d image loads, %d stores outside the '
          'stack, lowest byte written sp0 - %s = X2_STK %s'
          % (w.csver, len(w.trace), len(w.loads), len(w.stores), hex(SP0 - w.min_addr), hex(stk)))
    for pc, m, o in w.trace:
        print('     %-9s %s %s' % (hex(pc), m, o))
    # ---- W3 the two loaded cells are __start/__stop_asan_globals, and they are equal, so the callee returns at once
    rows = group_rows(w.loads)
    check(len(rows) == 1 and len(rows[0][2]) == 2, 'YE37 n = 0: the walk does not read exactly one 2-cell row')
    gotb, gotn, gotc = rows[0]
    gotb = pf(0x9ee98, gotb)
    vals = [v for o, ww, v in gotc]
    st, sp = UU.allsym.get('__start_asan_globals'), UU.allsym.get('__stop_asan_globals')
    okw3 = check(vals == [st, sp] == [0, 0], 'YE37 n = 0: the walk\'s two cells are not __start/__stop_asan_globals = 0')
    # the donor's own .got row has NO data map image (this map covers no .got run), so the row is named the way X1
    # names a data address: by the code that references it, moved through binmatch's identical-function map.
    cgot = cag_got(src)
    donor_got = data_reloc(cgot)
    pcs = xrefs(EC, EC.sec['.text']).get(cgot, [])
    mapped = {code_reloc(pc)[0] for pc in pcs if code_reloc(pc)}
    gotrefs = set(xrefs(EU, EU.sec['.text']).get(gotb, []))
    okw3b = check(bool(mapped) and mapped <= gotrefs and (donor_got in (None, gotb)),
                  'YE37 n = 0: the walk reads %s; the donor .got row %s is referenced at %s, moved %s, but this '
                  'image references %s there' % (hex(gotb), hex(cgot), [hex(p) for p in pcs],
                                                 sorted(map(hex, mapped)), sorted(map(hex, gotrefs))))
    print('  W3 the walk\'s one row %s/%d = the .got pair the dtor passes: [%s] = the twin\'s __start_asan_globals %s / '
          '__stop_asan_globals %s (equal -> __asan_unregister_elf_globals returns at its first branch).\n'
          '     The donor\'s own .got row %s has %s; it is referenced by cgif code at %s (binmatch-moved %s), and '
          'this image references %s at exactly those pcs (%s): %s'
          % (hex(gotb), gotn, ', '.join(hx(v) for v in vals), hx(st), hx(sp), hex(cgot),
             'data map image %s' % hex(donor_got) if donor_got is not None else 'NO data map image (no .got run in this map)',
             [hex(p) for p in pcs], sorted(map(hex, mapped)), hex(gotb), sorted(map(hex, gotrefs)),
             'PASS' if okw3 and okw3b else 'FAIL'))
    N0.append('x2_rodata row base: the .got pair has no data map run in this map, so it is named by the code that '
              'references it: cgif %s at %s -> this image %s at %s' % (hex(cgot), [hex(p) for p in pcs], hex(gotb),
                                                                       sorted(map(hex, mapped))))
    # ---- W4 the registration side: with start = stop the register call writes nothing, so the flag keeps its
    # zero-fill start-up value; both cellr cells are read from the pin, not carried over from cgif
    reg = UU.allsym.get('__asan_register_elf_globals')
    flag_c = [int(a, 16) for a, ww, v in re.findall(r'cellr (0x[0-9a-f]+) (\d+) \(SLit (\d+)\) true', src)]
    cel = [(int(a, 16), int(ww), int(v)) for a, ww, v in re.findall(r'cellr (0x[0-9a-f]+) (\d+) \(SLit (\d+)\) true', src)]
    cm = {}
    for a, ww, v in cel:
        cm[a] = pf(a, data_reloc(a))
        check(cm[a] is not None, 'YE37 n = 0: cellr %s has no data map image' % hex(a))
    flag, mu = cm[cel[0][0]], cm[cel[1][0]]
    wr = Walk(EU, UU, 'register')
    wr.run(reg, a0=flag, a1=0, a2=0)
    check(wr.refused is None, 'YE37 n = 0: the register walk refused: %s' % wr.refused)
    check(not wr.stores, 'YE37 n = 0: __asan_register_elf_globals(flag, 0, 0) writes %s' % wr.stores)
    cellv = []
    for (a, ww, v), ua in ((cel[0], flag), (cel[1], mu)):
        fb, got = EU.fileback(ua, ww), EU.u(ua, ww)
        ok = check(fb is False and got == 0, 'YE37 n = 0: cellr %s is not a zero-fill cell holding 0' % hex(ua))
        nv = pf('flagval', 0) if ua == flag else 0
        ok = check(nv == got, 'YE37 n = 0: cellr %s states %s, the start-up value is %s' % (hex(ua), hx(nv), hx(got))) and ok
        cellv.append((ua, ww, nv))
        print('  W4 cellr %-9s -> %-9s %-28s start-up value %d (cgif %d): zero-fill cell, pin holds %s: %s'
              % (hex(a), hex(ua), rstr(role(EU, UU, ua, 'DATA'))[:28], nv, v, hx(got), 'PASS' if ok else 'FAIL'))
        tab.append(('YE37', hex(a), 'CELLR', hex(ua), 'data map; %s; start-up value %d (zero-fill cell, pin %s; the x2 '
                    'walk writes nothing and the register call with start = stop writes nothing)'
                    % (rstr(role(EU, UU, ua, 'DATA')), nv, hx(got))))
    print('     W4 register walk: __asan_register_elf_globals(%s, 0, 0) ran %d instructions and wrote nothing outside '
          'its stack, so %s keeps its zero-fill value 0 (cgif registers 3 globals and its cell holds 1)'
          % (hex(flag), len(wr.trace), hex(flag)))
    N0.append('x2 walk MEASURED: %d instructions from asan.module_dtor %s; the two .got cells %s / %s hold 0 '
              '(= __start/__stop_asan_globals), __asan_unregister_elf_globals returns at its first branch, and the '
              'walk writes only %s stack bytes (X2_STK)'
              % (len(w.trace), hex(dtor), hex(gotb), hex(gotb + 8), hex(stk)))
    return stk, gotb, cm


def cag_got(src):
    """the donor's .got row: the row whose two cells are the donor's asan_globals start and end."""
    _, _, rows = rodata_block(src)
    hit = [b for b, n, cs in [(r[2], r[3], r[4]) for r in rows]
           if [v for o, w, v in cs] == [AG['C'][0], AG['C'][0] + AG['C'][1]]]
    assert len(hit) == 1, 'donor .got row (asan_globals start/end) not found: %s' % hit
    return hit[0]


def by_ref_reloc(a):
    """the target image's address for a cgif data address that NO data map run covers: the code that references it in
    cgif's .text, moved by binmatch, must reference exactly one address in the target's .text -- that address."""
    pcs = xrefs(EC, EC.sec['.text']).get(a, [])
    rev = {}
    for t_, ps in xrefs(EU, EU.sec['.text']).items():
        for p in ps:
            rev.setdefault(p, set()).add(t_)
    cand = set()
    for pc in pcs:
        r = code_reloc(pc)
        if r:
            cand |= rev.get(r[0], set())
    if len(cand) != 1:
        return None, 'no data map run and %d candidate(s) by reference' % len(cand)
    t_ = cand.pop()
    return t_, ('the code that references it: cgif %s -> this image %s (binmatch-moved)'
                % ([hex(p) for p in pcs], [hex(code_reloc(p)[0]) for p in pcs if code_reloc(p)]))


def gen_ye37(src, dec, gra, plant):
    """returns (text, table rows, controls printed).  src = cgif YE37 (full text)."""
    rows_out = []
    # ---- controls on the generators
    gw = {k: shadow_windows(E, *AG[k]) for k, E in (('C', EC), ('D', ED), ('G', EG), ('U', EU))}
    ok1 = check(gw['C'] == shw_list(src), 'YE37 x2_shw generator does not reproduce cgif\'s x2_shw')
    ok2 = check(gw['D'] == shw_list(dec), 'YE37 x2_shw generator does not reproduce decode B\'s x2_shw')
    ok3 = check(byteset(gw['G']) == byteset(shw_list(gra)), 'YE37 x2_shw generator: grant B byte set differs')
    print('  E1 x2_shw generator: cgif image -> donor list equal: %s; decode B pin -> decode list equal: %s; grant B pin'
          ' -> same shadow bytes as grant B\'s merged list (%d bytes): %s' % (ok1, ok2, len(byteset(gw['G'])), ok3))
    _, _, crow = rodata_block(src)
    cag = AG['C'][0]
    drow = [r for r in crow if r[2] == cag]
    check(len(drow) == 1, 'YE37: donor globals-array row not found')
    dtxt = src[drow[0][0]:drow[0][1]]
    fields = sorted({o % 64 for o, w, v in drow[0][4]})
    check(all(sorted(o % 64 for o, w, v in drow[0][4] if o // 64 == i) == fields for i in range(drow[0][3] // 64)),
          'YE37: donor descriptors do not all carry the same fields')
    rc = render_desc(cag, descriptors(EC, *AG['C']), fields)
    _, _, drows = rodata_block(dec)
    ddesc = [r for r in drows if r[2] == AG['D'][0]]
    rd = render_desc(AG['D'][0], descriptors(ED, *AG['D']), fields)
    okc = check(rc == dtxt, 'YE37 descriptor renderer does not reproduce the cgif row')
    okd = check(len(ddesc) == 1 and rd == dec[ddesc[0][0]:ddesc[0][1]], 'YE37 descriptor renderer: decode B row differs')
    print('  E2 globals-array row renderer (donor field offsets %s): cgif image -> donor row byte-equal: %s; decode B pin'
          ' -> decode row byte-equal: %s' % (fields, okc, okd))
    # E2b the 8-word renderer: the fuzz_uci image-A pin -> that unit's committed lib/A/AE37.v globals row, byte-equal
    # (the control behind the 8-word form). The A-vs-B word comparison is a fuzz_uci fact, so it runs on that target.
    a9t = git_show(A9CORE, A9AE37)
    _, _, arows = rodata_block(a9t)
    agA = EUA.sec['asan_globals']
    arow = [r for r in arows if r[2] == agA[0]]
    ra = render_desc8(agA[0], descriptors(EUA, *agA))
    oka = check(len(arow) == 1 and ra == a9t[arow[0][0]:arow[0][1]],
                'YE37 8-word renderer does not reproduce the fuzz_uci lib/A/AE37.v globals row')
    wA = [EUA.u(agA[0] + o, 8) for o in range(0, agA[1], 8)]
    wB = [EU.u(AG['U'][0] + o, 8) for o in range(0, AG['U'][1], 8)]
    okw = check(wA == wB, 'asan_globals words differ between the fuzz_uci A and B pins') \
        if T['name'] == 'fuzz_uci' else 'n/a (this target is %s)' % T['name']
    print('  E2b asan_globals MEASURED from each pin: fuzz_uci A %s+%s = [%s]; %s %s+%s = [%s]; identical words: %s. '
          '8-word renderer: fuzz_uci A pin -> %s %s globals row (:%d-%d) byte-equal: %s'
          % (hex(agA[0]), hex(agA[1]), ', '.join(map(hex, wA)), TGT, hex(AG['U'][0]), hex(AG['U'][1]),
             ', '.join(map(hex, wB)), okw, A9CORE, A9AE37, a9t[:arow[0][0]].count('\n') + 1 if arow else 0,
             a9t[:arow[0][1]].count('\n') + 1 if arow else 0, oka))
    # ---- form blocks: decode's patched form == grant B's (Hr masked); the donor's own blocks located
    dfb, gfb, cfb = form_blocks(dec, True), form_blocks(gra, True), form_blocks(src, False)
    dbl = [dec[a:b] for a, b in dfb]
    gbl = [gra[a:b] for a, b in gfb]
    mh = lambda s: HR_RE.sub('assert (Hr : @ <= lo /\\ lo + n <= @ /\\ 0 <= n).', s)
    okf = check([mh(x) for x in dbl] == [mh(x) for x in gbl], 'YE37 form: decode B and grant B shw blocks differ')
    print('  E3 shw_ok form: decode B (YE37-shbyte-A-form.patch applied, blob e84ab884) blocks S1 x2_shbytes..shbyte_chk '
          '(%d lines), S2 shbyte_present (%d), S3 shw_ok (%d) == grant B YE37 blocks (Hr numerals masked): %s'
          % tuple([x.count('\n') for x in dbl] + [okf]))
    # ---- n = 0: the walk is MEASURED first (evidence), then the rows are the donor's rows moved by the data rule
    # MINUS the descriptor-array row, which has no image here.
    n0 = AG['U'][1] == 0
    stk = wgot = None
    if n0:
        stk, wgot, cm_w = walk_controls(src, cag, plant)
    # ---- derive the rows
    out = src
    i, j, crow = rodata_block(src)
    pieces, last = [], i
    tab = []
    for (s, e, base, size, cs) in crow:
        pieces.append(src[last:s])
        last = e
        if base == cag and n0:
            pieces.append('@DROP@')
            tab.append(('YE37', hex(cag), 'ROW', '(dropped)', 'the asan_globals descriptor-array row: this image has '
                        'NO asan_globals section, so there is no such row and the unregister loop that reads it '
                        'never runs'))
            N0.append('x2_rodata: the descriptor-array row %s (%d descriptors in the donor) is DROPPED; the other %d '
                      'rows are the donor\'s, moved by the data rule' % (hex(cag), AG['C'][1] // 64, len(crow) - 1))
            continue
        if base == cag:
            ds = descriptors(EU, *AG['U'])
            pieces.append(render_desc8(AG['U'][0], ds))
            for di, d in enumerate(ds):
                for o in ALL8:
                    k = {0: 'beg', 8: 'size', 16: 'swr', 24: 'name', 32: 'mod', 40: 'dyn', 48: 'loc', 56: 'odr'}[o]
                    tab.append(('YE37', hex(cag + 64 * di + o) if di < len(descriptors(EC, *AG['C'])) and o in fields
                                else '- (not in cgif\'s text)' if o not in fields else '-',
                                'GDESC', hex(d[k]), 'fuzz_uci asan_globals %s descriptor %d +%d (%s), read from the pin'
                                % (hex(AG['U'][0]), di, o, k)))
            tab.append(('YE37', hex(cag), 'ROW', hex(AG['U'][0]), 'section asan_globals start (row size 64 x %d = %d)'
                        % (len(ds), 64 * len(ds))))
            rows_out.append((AG['U'][0], 64 * len(ds), 'GDESC', []))
            continue
        ub = data_reloc(base)
        how = 'data map'
        if ub is None:
            # no data map run covers this address (this map covers no .got run): name it the way X1 names a data
            # address, by the code that references it, moved through binmatch's identical-function map
            ub, how = by_ref_reloc(base)
        if plant and ('h', base) in plant:
            ub, how = plant[('h', base)], how + ' [PLANTED]'
        check(ub is not None, 'YE37 row %s: no data map image and no referencing code' % hex(base))
        nv, crs = [], []
        for o, w, v in cs:
            cfb_ = EC.fileback(base + o, w)
            ptr = cfb_ is True and EC.u(base + o, w) == v and CG_LO <= v < CG_HI
            rule = ''
            if ptr:
                uv = EU.u(ub + o, w)
                rv, rule = ptr_reloc(v)
                if n0 and v in (AG['C'][0], AG['C'][0] + AG['C'][1]):
                    # the donor pointer is its asan_globals start / end; this image has no such section, so the
                    # linker's __start_asan_globals / __stop_asan_globals are 0 and the pin holds 0 here
                    rv = UU.allsym.get('__start_asan_globals' if v == AG['C'][0] else '__stop_asan_globals')
                    rule = ('section asan_globals %s: ABSENT in this image, so the twin\'s __%s_asan_globals = %s'
                            % ('start' if v == AG['C'][0] else 'end',
                               'start' if v == AG['C'][0] else 'stop', hx(rv)))
                    N0.append('x2_rodata .got row %s +%d: the donor cell holds its asan_globals %s; this image has no '
                              'such section, so the cell is %s (pin) = the twin\'s symbol'
                              % (hex(ub), o, 'start' if v == AG['C'][0] else 'end', hx(EU.u(ub + o, w))))
                if plant and ('h', v) in plant:
                    uv = plant[('h', v)]
                check(uv == rv, 'YE37 row %s +%d: pin pointer %s != rule %s (%s)' % (hex(base), o, hx(uv), hx(rv), rule))
                kind, src_ = 'PTR', 'pin at %s+%d = %s; rule %s -> %s' % (hex(ub), o, hx(uv), rule, hx(rv))
            else:
                uv = v
                if cfb_ is True:
                    check(EC.u(base + o, w) == v, 'YE37 control: cgif pin at %s != %s' % (hex(base + o), hex(v)))
                ufb = EU.fileback(ub + o, w)
                if ufb is True:
                    check(EU.u(ub + o, w) == v, 'YE37 row %s +%d: uci pin holds %s, constant %s'
                          % (hex(base), o, hx(EU.u(ub + o, w)), hex(v)))
                    kind, src_ = 'CONST', 'image constant, uci pin at %s = %s' % (hex(ub + o), hx(EU.u(ub + o, w)))
                else:
                    check(ufb is False and cfb_ is False, 'YE37 row %s +%d: file/zero-fill class differs' % (hex(base), o))
                    kind, src_ = 'CONST', 'start-up value of a zero-fill (.bss) cell, kept (Tfib_const cell; gate below)'
            nv.append(uv)
            crs.append((o, w, v, uv, kind, rule))
            tab.append(('YE37', hex(v), kind, hx(uv), 'row %s +%d: %s' % (hex(ub), o, src_)))
        tab.append(('YE37', hex(base), 'ROW', hex(ub), '%s; %s' % (how, rstr(role(EU, UU, ub, 'DATA')))))
        pieces.append(rewrite_row(src[s:e], ub, nv))
        rows_out.append((ub, size, 'ROW', crs))
    pieces.append(src[last:j])
    out = src[:i] + ''.join(pieces) + src[j:]
    # ---- x2_shw (generated) and the shw form.  n = 0: the image registers no global and the walk touches no shadow
    # byte, so the list is EMPTY (no global window, no metadata window).
    shw = [] if n0 else gw['U']
    if n0:
        N0.append('x2_shw: 0 descriptors and no shadow byte touched by the walk -> `[]` (x2_shbytes = [] and '
                  'shbyte_chk is vacuously true)')
    out = SHW_RE.sub('Definition x2_shw : list (Z * Z) := [%s].' % '; '.join('(%#x, %d)' % w for w in shw), out, 1)
    nu, nc = len(shw) - 1, len(gw['C']) - 1
    for gi in range(nc if not n0 else 0):
        clo, cn = gw['C'][gi]
        if gi < nu:
            tab.append(('YE37', hex(clo), 'SHW', hex(shw[gi][0]), 'shadow window (shadow(beg), size_with_redzone/8 = %d) '
                        'of global %d, generated from the pin\'s asan_globals' % (shw[gi][1], gi)))
        else:
            tab.append(('YE37', hex(clo), 'SHW', '(removed)', 'cgif global %d window: this image has %d global(s)'
                        % (gi, nu)))
    if n0:
        for clo, cn in gw['C']:
            tab.append(('YE37', hex(clo), 'SHW', '(removed)', 'this image registers no global and its walk touches '
                        'no shadow byte: x2_shw is empty'))
    else:
        tab.append(('YE37', hex(gw['C'][-1][0]), 'SHW', hex(shw[-1][0]), 'shadow window (shadow(asan_globals), 64 x %d '
                    '/ 8 = %d) of the descriptor array' % (nu, shw[-1][1])))
    moved = {int(r[1], 16) for r in tab if r[2] in ('ROW', 'PTR', 'SHW') and r[1].startswith('0x')
             and (not r[3].startswith('0x') or int(r[1], 16) != int(r[3], 16))}
    cfb = form_blocks(out, False)
    for (a, b), new in sorted(zip(cfb, dbl), reverse=True):
        out = out[:a] + new + out[b:]
    if n0:
        # an empty window list: shw_ok's goal is `Forall _ (map shw_region [])`
        i_, j_ = block(out, 'Lemma shw_ok', 'Qed.')
        out = out[:i_] + ('Lemma shw_ok : forall ly S (H : word -> bool) mem E,\n'
                          'ARm B ly S (aview tfibsegs H mem) -> Forall (region_ok tfibsegs E (mrestrict H mem)) '
                          '(map shw_region x2_shw).\n'
                          'Proof.\nintros ly S H mem E HM. unfold x2_shw. cbn [map]. apply Forall_nil.\nQed.\n') + out[j_:]
        N0.append('shw_ok: x2_shw is empty, so the lemma is `unfold x2_shw. cbn [map]. apply Forall_nil.` (the A-form '
                  'window case and its Hr bound have nothing to range over)')
        tab.append(('YE37', 'Hr lo/hi', 'HR', '(removed)', 'the A-form window bound: x2_shw is empty, so shw_ok is '
                    'Forall_nil'))
    else:
        lo, hi = min(x for x, n in shw), max(x + n for x, n in shw)
        mh2 = HR_RE.search(out)
        tab.append(('YE37', 'Hr lo', 'HR', hex(lo), 'min lo of x2_shw (decode: %s)' % mh2.group(1)))
        tab.append(('YE37', 'Hr hi', 'HR', hex(hi), 'max lo+n of x2_shw (decode: %s)' % mh2.group(2)))
        out = HR_RE.sub('assert (Hr : %#x <= lo /\\ lo + n <= %#x /\\ 0 <= n).' % (lo, hi), out, 1)
    # ---- the two exit cells (cellr) by the data rule.  n = 0: the walk neither reads nor writes them, so the file
    # states NO exit cell: the two cellr regions, the MU0 premise, the two zi8 lemmas and the two proof bullets go.
    cel = [(int(a, 16), int(w), int(v)) for a, w, v in re.findall(r'cellr (0x[0-9a-f]+) (\d+) \(SLit (\d+)\) true', src)]
    cm = {}
    for a, w, v in cel:
        ua = data_reloc(a)
        if plant and ('h', a) in plant:
            ua = plant[('h', a)]
        cm[a] = ua
        tab.append(('YE37', hex(a), 'CELLR', '(removed)' if n0 else hex(ua),
                    ('data map -> %s (%s), but the walk never touches it: no cellr region, no MU0, no zi8 lemma'
                     % (hex(ua), rstr(role(EU, UU, ua, 'DATA')))) if n0 else
                    'data map; %s; value %d kept' % (rstr(role(EU, UU, ua, 'DATA')), v)))
    rest = out[out.index('Definition x2_regions'):]
    head = out[:out.index('Definition x2_regions')]
    rest = re.sub(r'\b0x[0-9a-f]+\b', lambda mo: hex(cm[int(mo.group(0), 16)]) if int(mo.group(0), 16) in cm
                  else mo.group(0), rest)
    out = head + rest
    if n0:
        out = out.replace('@DROP@;\n', '')
        check('@DROP@' not in out, 'YE37 n = 0: the dropped descriptor row left a marker')
        out = re.sub(r'Definition X2_STK : Z := \d+\.', 'Definition X2_STK : Z := %d.' % stk, out, 1)
        tab.append(('YE37', '272 (cgif)', 'STK', str(stk), 'X2_STK: the walk\'s own stack extent, measured on the pin'))
        out, n1_ = re.subn(r':: cellr 0x[0-9a-f]+ \d+ \(SLit \d+\) true\n', '', out)
        out, n2_ = re.subn(r'Hypothesis MU0 : [^\n]*\n', '', out)
        out, n3_ = re.subn(r'Lemma zi8_\w+ : wseg_ok[^\n]*\n', '', out)
        out, n4_ = re.subn(r'apply Forall_cons; \[\|apply Forall_cons; \[\|apply Forall_cons; \[\|apply Forall_app',
                           'apply Forall_cons; [|apply Forall_app', out)
        # the donor line closes 4 brackets: the split's [shw_ok | rodata_ok] and the 3 Forall_cons [|...]; with 2 of
        # those Forall_cons gone, 2 brackets close it (`]].`), not 1
        out, n5_ = re.subn(r'\]\]\]\]\.\n(\+ apply \(region_ok_stack)', r']].\n\1', out)
        i_ = out.index('+ unfold region_ok, cellr.')
        j_ = out.index('- apply pairwise_disjoint_of_extents', i_)
        out = out[:i_] + out[j_:]
        check((n1_, n2_, n3_, n4_, n5_) == (2, 1, 2, 1, 1),
              'YE37 n = 0: cellr removal hit %s (want 2, 1, 2, 1, 1)' % ((n1_, n2_, n3_, n4_, n5_),))
        out = out.replace('(x2_realizes B TB MU0)', '(x2_realizes B TB)')
        N0.append('x2_regions: no exit cell -> `stack :: map shw_region x2_shw ++ map ro_region x2_rodata`; the MU0 '
                  'premise, the 2 zi8 lemmas and the 2 cellr bullets are removed, so x2_realizes takes (B TB)')
        cel = []
    moved |= {a for a in cm if cm[a] != a} | {0x7fffc1b9, 0x20dc8}   # + cgif's x2_shw_const / shbyte0 range numerals
    return out, tab, rows_out, shw, cel, cm, dbl, moved


def proof_part(t):
    t = body(t)
    i = t.index('\nImport ListNotations.')
    return re.sub(r'\b(GrantSyms|UciSyms|DecodeSyms)\b', 'TfibSyms', t[i + 1:])


def unsplit(text, odr):
    """decode B's revision-1 YD1y split DRV_IVS window 3 around its ODR bytes; EXITDRV.md revision 2 keeps the donor's
    4 windows. For the position-for-position comparison only, join the two halves back."""
    for lo, hi in odr:
        text = re.sub(r'\((0x[0-9a-f]+), %s\); \(%s, ' % (hex(lo), hex(hi)), r'(\1, ', text)
        text = re.sub(r'\((0x[0-9a-f]+) <= a < %s\) \\/ \(%s <= a < ' % (hex(lo), hex(hi)), r'(\1 <= a < ', text)
    return text


# ---------------------------------------------------------------- main
def main():
    args = ARGS
    outdir = T['outdir']

    src = {}
    for nm, path in [('YE23', 'lib/YE23.v'), ('YD1y', 'lib/YD1y.v'), ('YE37', 'lib/YE37.v'),
                     ('AE23', 'lib/A/AE23.v'), ('AD1y', 'lib/A/AD1y.v')]:
        src[nm] = git_show(DONOR_REV2, 'proofs/cgif/cgif_file_fuzzer/' + path)
        check(src[nm] == git_show(DONOR_REV, 'proofs/cgif/cgif_file_fuzzer/' + path),
              'donor %s differs between %s and %s' % (path, DONOR_REV, DONOR_REV2[:12]))
    dec = {nm: git_show(DECODE_REV, 'proofs/libreac/fuzz_decode/lib/B/%s.v' % nm) for nm in ('YE23', 'YD1y', 'YE37')}
    gra = {nm: git_show(GRANT_REV, 'proofs/libreac/fuzz_grant/lib/B/%s.v' % nm) for nm in ('YE23', 'YD1y', 'YE37')}
    # the fuzz_uci image-A twins, read from the pushed core commit (sha256 9230d5e31dc0 / 28f9b37ad2fd), not from a
    # live directory another lane may rewrite
    a9 = {nm: git_show(A9CORE, 'proofs/reac-repacer/fuzz_uci/lib/A/%s.v' % an) for nm, an in (('YE23', 'AE23'), ('YD1y', 'AD1y'))}
    for nm, h in (('YE23', '9230d5e31dc019b7c47ec5621bf093748a5523ecededb080d18d1bf532b42997'),
                  ('YD1y', '28f9b37ad2fdc137ad7a5d73faad7d02b2a279ed97a8086bcd3a05b7d530a91c')):
        check(hashlib.sha256(a9[nm].encode()).hexdigest() == h, 'image-A control text %s: sha256 differs' % nm)
    cgif_yf0m = git_show(DONOR_REV2, 'proofs/cgif/cgif_file_fuzzer/lib/YF0m.v')

    print('== CONTROLS ==')
    # C1 donor pairing AE23<->YE23, AD1y<->YD1y; the B decimal literals named through it
    pe, n1 = pair(tokens(src['AE23']), tokens(src['YE23']), 'donor AE23<->YE23')
    pd, n2 = pair(tokens(src['AD1y']), tokens(src['YD1y']), 'donor AD1y<->YD1y')
    DEC_NAME = {pe[('d', k)][1]: v for k, v in DEC_NAME_A.items()}
    DEC_EXPECT = set(DEC_NAME)
    END = {pe[('h', k)][1]: pe[('h', v)][1] for k, v in END_A.items()}
    print('  C1 donor pairing AE23<->YE23 %d tokens, %d mismatches; AD1y<->YD1y %d tokens, %d mismatches; B decimal '
          'literals (named through the pairing) %s; B range ends %s'
          % (len(tokens(src['AE23'])), n1, len(tokens(src['AD1y'])), n2,
             ', '.join('%d=%s' % (k, v) for k, v in sorted(DEC_NAME.items())),
             ', '.join('%s=%s+%d' % (hex(k), hex(v), k - v) for k, v in sorted(END.items()))))
    # C2 hull points
    hp_c, hp_u, hp_d, hp_g = EC.hull_points(), EU.hull_points(), ED.hull_points(), EG.hull_points()
    dlit = sorted({v for k, v in tokens(src['YD1y']) if k == 'h'} & set(hp_c))
    check(hp_c == [0x10000, 0x30000, 0x9d000, 0x9f000, 0x5fb000] and dlit == hp_c, 'cgif B hull points != donor literals')
    print('  C2 page-rounded PT_LOAD hull points: cgif B %s (= donor YD1y literals %s) | decode B %s | grant B %s | '
          '%s %s' % ([hex(x) for x in hp_c], [hex(x) for x in dlit], [hex(x) for x in hp_d],
                     [hex(x) for x in hp_g], TGT, [hex(x) for x in hp_u]))
    for tag, E in (('cgif B', EC), (TGT, EU)):
        segs = [(v & ~0xfff, (v + m + 0xfff) & ~0xfff) for v, o, f, m in E.loads]
        ok = check(len(segs) == 4 and all(segs[i][1] == segs[i + 1][0] for i in range(3)),
                   '%s page-rounded PT_LOADs not 4 contiguous segments' % tag)
        print('     %s segments (= Asan[Ubsan]_segment_000..003 the in_img lemmas split on): %s contiguous: %s'
              % (tag, ' '.join('(%s,%s)' % (hex(a), hex(b)) for a, b in segs), ok))
    # C3 XW2 shadow generator: cgif B image -> donor line; decode B pin -> decode line; grant B -> same byte set
    gl = {k: xw2_shadow_line(E, *AG[k]) for k, E in (('C', EC), ('D', ED), ('G', EG), ('U', EU))}
    okc = check(gl['C'] == xw2_lines(src['YE23']), 'XW2 generator does not reproduce the cgif B donor line')
    okd = check(gl['D'] == xw2_lines(dec['YE23']), 'XW2 generator does not reproduce the decode B line')
    okg = check(byteset(shadow_windows(EG, *AG['G'])) == xw2_bytes(gra['YE23']), 'XW2 generator: grant B bytes differ')
    print('  C3 XW2 shadow generator: cgif B image -> donor line byte-equal: %s; decode B pin -> decode B line byte-equal'
          ' (ODR range included): %s; grant B pin -> the same shadow bytes as grant B\'s merged XW2 (%d bytes): %s'
          % (okc, okd, len(xw2_bytes(gra['YE23'])), okg))
    for tag, k, E in (('cgif B', 'C', EC), ('decode B', 'D', ED), ('grant B', 'G', EG), (TGT, 'U', EU)):
        ds = descriptors(E, *AG[k])
        print('     %-12s asan_globals %s+%s: %d descriptor(s)%s; ODR bytes written at exit: %s%s'
              % (tag, hex(AG[k][0]), hex(AG[k][1]), len(ds),
                 ' (NO asan_globals section: n = 0)' if not AG[k][1] else '',
                 [(hex(a), hex(b)) for a, b in odr_ranges(ds)] or 'none',
                 '' if len(ds) > 3 else ' %s' % ['beg %s size %s swr %s odr %s' % (
                     hex(d['beg']), hex(d['size']), hex(d['swr']), '-1' if d['odr'] == U64M else hex(d['odr']))
                     for d in ds]))
    print('     %s XW2 shadow line: %s' % (TGT, gl['U']))
    if not AG['U'][1]:
        N0.append('xw2_shadow_line on this image: 0 descriptors -> one EMPTY disjunct, `%s`; the file does not use '
                  'it, because XW2 is False here (no exit cell either)' % gl['U'])
    ODR_U = odr_ranges(descriptors(EU, *AG['U']))
    # C3b the ODR write in __asan_unregister_globals, disassembled from each pin (capstone, RV64GC)
    import capstone
    cs = capstone.Cs(capstone.CS_ARCH_RISCV, capstone.CS_MODE_RISCV64 | capstone.CS_MODE_RISCVC)
    for tag, E, U in (('decode B', ED, UD), (TGT, EU, UU)):
        fv, fz = [(v, sz) for v, sz, t, n in U.syms if n == '__asan_unregister_globals'][0]
        ins = list(cs.disasm(bytes(E.u(fv + i, 1) for i in range(fz)), fv))
        at = {i.address: i for i in ins}
        hit = [(a.address, b.address, int(b.op_str.split(',')[-1], 0) + b.address) for a, b in zip(ins, ins[1:])
               if a.mnemonic == 'addi' and a.op_str == 'a1, a0, 1' and b.mnemonic == 'bgeu' and b.op_str.startswith('a1, s2,')]
        s2 = [i for i in ins if i.mnemonic in ('addi', 'li', 'c.li') and i.op_str.replace(' ', '') in ('s2,zero,2', 's2,2')]
        ok = check(len(hit) == 1 and hit[0][2] in at and at[hit[0][2]].mnemonic == 'sb' and at[hit[0][2]].op_str == 'zero, 0(a0)'
                   and len(s2) >= 1, '%s: ODR write pattern not found in __asan_unregister_globals' % tag)
        print('  C3b %-10s __asan_unregister_globals %s: addi a1,a0,1 @%s; bgeu a1,s2 @%s -> %s `sb zero, 0(a0)`; s2 = 2 '
              '@%s (capstone %s): %s' % (tag, hex(fv), hex(hit[0][0]) if hit else '-', hex(hit[0][1]) if hit else '-',
                                         hex(hit[0][2]) if hit else '-', [hex(i.address) for i in s2],
                                         capstone.__version__, 'PASS' if ok else 'FAIL'))
    # C4 binmatch summary
    st = {}
    for f in BMJ['functions']:
        st[(f['kind'], f['status'])] = st.get((f['kind'], f['status']), 0) + 1
    print('  C4 binmatch %s vs cgif B (asan-ubsan): pinned bytes == twin: %s; %d functions; %s; jal pairs '
          'consistent %d, inconsistent %d' % (TGT, BMJ['pinned_bytes_equal_unstripped'], len(BMJ['functions']),
                                              ', '.join('%s/%s %d' % (k + (n,)) for k, n in sorted(st.items())),
                                              BMJ['jal_pairs_consistent'], BMJ['jal_pairs_inconsistent']))

    # ---- maps (YE23, YD1y)
    bodies = {nm: body(src[nm]) for nm in ('YE23', 'YD1y', 'YE37')}
    maps = {}
    for nm in ('YE23', 'YD1y'):
        t = mask_xw2(bodies[nm]) if nm == 'YE23' else bodies[nm]
        hv = {v for k, v in tokens(t) if k == 'h'}
        dv = {v for k, v in tokens(t) if k == 'd'}
        if nm == 'YE23':
            check(dv == DEC_EXPECT, 'YE23 decimal address literals: %s' % sorted(dv ^ DEC_EXPECT))
        else:
            check(dv == set(KEEP_DEC), 'YD1y decimals: %s' % sorted(dv))
        maps[nm] = classify_and_map(hv, dv, nm == 'YD1y', DEC_EXPECT, DEC_NAME)
    derived = {nm: dict(maps[nm]) for nm in maps}
    plant = {}
    for p in args.plant:                 # CG=NV hex, d:CG=NV for a decimal literal, or stk=N / flagval=N (YE37 n = 0)
        a, b = p.split('=')
        if a in ('stk', 'flagval'):
            plant[('h', a)] = int(b, 0)
            print('  PLANT %s -> %s' % (a, b))
            continue
        k = ('d', int(a[2:])) if a.startswith('d:') else ('h', int(a, 16))
        nb = int(b) if k[0] == 'd' else int(b, 16)
        plant[k] = nb
        for nm in maps:
            if k in maps[nm]:
                v, kind, rule = maps[nm][k]
                maps[nm][k] = (nb, kind, rule + ' [PLANTED, was %s]' % hx(v))
                print('  PLANT %s: %s -> %s (was %s)' % (nm, a, b, hx(v)))

    # ---- emit (texts in memory; written only if every check passes)
    outs, miss = {}, {}
    N0X = {'YE23': ('; the image has NO asan_globals section: it registers no global, the exit path\'s '
                    '__asan_unregister_elf_globals returns at its first branch, and the x2 walk writes nothing '
                    'outside its own stack, so XW2 is False (no exit cell and no shadow byte)'),
           'YD1y': ('; DRV_IVS is the donor\'s 4 windows, each end named in the unstripped twin, not split (the image '
                    'has no ODR indicator byte); window 1 ends where the asan_globals array would begin, at the end '
                    'of .data'),
           'YE37': ('; the image has NO asan_globals section, so the descriptor-array row is gone and the .got row '
                    'the walk reads holds __start_asan_globals / __stop_asan_globals = 0, 0; '
                    '__asan_unregister_elf_globals returns at its first branch, so the walk writes only its own '
                    'stack (X2_STK measured from it): x2_shw is empty and there is no exit cell, so x2_regions is '
                    'the stack window and the read-only rows; shw_ok takes the form of libreac/fuzz_decode\'s '
                    'YE37-shbyte-A-form.patch and of fuzz_grant B\'s lib/B/YE37.v, with the empty window list')}
    UCIX = {'YE23': ('; XW2\'s shadow windows are those of fuzz_uci.asan-ubsan\'s one registered global (MARGIN_MAX) '
                     'and of its descriptor array; its odr_indicator is -1, so the exit writes no ODR byte and XW2 '
                     'has no ODR range'),
            'YD1y': ('; DRV_IVS is the donor\'s 4 windows, each end named in the unstripped twin, not split (fuzz_uci '
                     'has no ODR indicator byte)'),
            'YE37': ('; the walk\'s globals array is fuzz_uci.asan-ubsan\'s 1 descriptor at 0x9b9d0 (MARGIN_MAX; all '
                     '8 descriptor words, the donor text omits the +24 name word), its shadow windows are that '
                     'global\'s and that array\'s; its odr_indicator is -1, so the exit writes no ODR byte and there '
                     'is no ODR region; shw_ok takes each shadow window byte from a constant shadow cell or a '
                     'Tfib_zero_shadow range (the form of libreac/fuzz_decode\'s YE37-shbyte-A-form.patch and of '
                     'fuzz_grant B\'s lib/B/YE37.v)')}
    EXTRA = N0X if not AG['U'][1] else UCIX
    XH = {nm: ('lib/%s.v' % nm, EXTRA[nm]) for nm in ('YE23', 'YD1y', 'YE37')}
    for nm in ('YE23', 'YD1y'):
        t = src[nm]
        if nm == 'YE23':
            t = t.replace(xw2_block(t) if not AG['U'][1] else xw2_lines(t), '@XW2SH@')
        t, miss[nm] = substitute(t, maps[nm])
        if nm == 'YE23':
            xw2new = (XW2_ANCHOR + 'False.') if not AG['U'][1] else gl['U']
            t = t.replace('@XW2SH@', xw2new)
            if not AG['U'][1]:
                N0.append('XW2 (YE23): 0 descriptors and the x2 walk writes nothing outside its own stack -> the '
                          'whole definition is `%s` (the donor\'s two exit-cell disjuncts and the shadow part go)'
                          % xw2new)
        outs[nm] = with_header(t, header(*XH[nm]))
        check(not miss[nm], '%s unmapped tokens %s' % (nm, miss[nm]))
    ye37, tab37, rows37, shw37, cel37, cm37, dbl, moved37 = gen_ye37(src['YE37'], dec['YE37'], gra['YE37'], plant)
    outs['YE37'] = with_header(ye37, header(*XH['YE37']))

    # ---- C5 role identity: donor position <-> decode B / grant B / fuzz_uci A <-> the target's output
    print('  C5 role identity (value in the reference image\'s pin/twin vs the %s value in its pin/twin):' % TGT)
    roles, xref = {}, {}
    refs = (('decode B', dec, ED, UD), ('grant B', gra, EG, UG), ('uci A', a9, EUA, UUA))
    for nm in ('YE23', 'YD1y'):
        tc = tokens(mask_xw2(bodies[nm]) if nm == 'YE23' else bodies[nm])
        tu = tokens(mask_xw2(body(outs[nm])) if nm == 'YE23' else body(outs[nm]))
        pcu, nbu = pair(tc, tu, '%s donor<->fuzz_uci' % nm)
        for tag, texts, E, U in refs:
            rt = texts[nm]
            if tag == 'decode B' and nm == 'YD1y':
                rt = unsplit(rt, odr_ranges(descriptors(ED, *AG['D'])))
            tr = tokens(mask_xw2(body(rt)) if nm == 'YE23' else body(rt))
            tcr, nodec = tc, False
            if tag == 'decode B' and nm == 'YE23' and len(tr) != len(tc):
                # decode B's committed YE23 (7eb81ddb186, shape round 3) names its 7 decimal literals (def_eq F_STDOUT
                # ...) instead of writing them: pair the hex numerals only; the decimals are checked against uci A / grant B
                tcr, tr, nodec = [t for t in tc if t[0] == 'h'], [t for t in tr if t[0] == 'h'], True
            # the a9 file pairs with the donor's image-A twin; that pairs with the image-B donor (C1), same positions
            pcr, nbr = pair(tcr, tr, '%s donor<->%s' % (nm, tag))
            nok = nrole = ndrv = ndrv_ok = nna = 0
            bad = []
            for k, (uv, kind, rule) in sorted(maps[nm].items()):
                if k not in pcr:
                    nna += 1
                    xref[(nm, k, tag)] = ('n/a', 'n/a', True, False)
                    continue
                rv = pcr[k][1]
                if kind == 'CONST':
                    ok = check(uv == k[1] == rv, '%s CONST %s moved (%s)' % (nm, k, tag))
                    xref[(nm, k, tag)] = ('const', 'const', ok, False)
                    continue
                rk = ('AGS' if k[1] == AG['C'][0] else 'CODE' if kind == 'CODE' else 'SEG' if kind == 'SEG' else 'DATA')
                if k[1] in END and kind == 'DATA':
                    lo = ('h', END[k[1]])
                    rr, ru = role(E, U, pcr[lo][1], rk), role(EU, UU, maps[nm][lo][0], rk)
                    ld, lu = rv - pcr[lo][1], uv - maps[nm][lo][0]
                    ok = roles_equal(rr, ru) and ld == lu == k[1] - END[k[1]]
                    sr, su = '%s, +%d (range end)' % (rstr(rr), ld), '%s, +%d (range end)' % (rstr(ru), lu)
                else:
                    rr, ru = role(E, U, rv, rk), role(EU, UU, uv, rk)
                    ok = roles_equal(rr, ru)
                    sr, su = rstr(rr), rstr(ru)
                drv = is_driver_role(ru, UU)
                nrole += 1
                nok += ok
                ndrv += drv
                ndrv_ok += drv and ok
                if tag == 'grant B':
                    if drv:     # the driver code is the same instruction stream in grant B and uci B (T0.4 s.0)
                        check(ok, '%s DRIVER cell %s: grant B %s %s / target %s %s' % (nm, hx(k[1]), hx(rv), sr, hx(uv), su))
                    if not ok:
                        bad.append((hx(k[1]), hx(rv), sr, hx(uv), su))
                else:
                    check(ok, '%s role mismatch %s: %s %s %s / target %s %s' % (nm, hx(k[1]), tag, hx(rv), sr, hx(uv), su))
                xref[(nm, k, tag)] = (sr, su, ok, drv)
                roles[(nm, k)] = su
            print('     %-4s vs %-10s: %d positions%s; pairing mismatches donor<->%s %d, donor<->target %d; roles equal '
                  '%d/%d; driver-side cells %d, equal %d%s'
                  % (nm, tag, len(tcr), ' (hex only)' if nodec else '', tag, nbr, nbu, nok, nrole, ndrv, ndrv_ok,
                     '; %d decimal key(s) n/a (named in decode B)' % nna if nna else ''))
            for b in bad:
                print('        differs (not a driver cell): cgif %s: grant B %s %s | target %s %s' % b)

    # ---- constants (the decimal literals' names) and the unit's definitions (port_core run, snapshot)
    dm = {DEC_NAME[k[1]]: v[0] for k, v in maps['YE23'].items() if k[0] == 'd'}
    consts = dict(dm)
    unitdefs = {}
    for f in ('YE2p.v', 'YE3m.v', 'YE22.v'):
        p = os.path.join(UNIT, f)
        if os.path.exists(p):
            for n, v in re.findall(r'Definition (F_STDOUT|F_STDERR|STDOUT_BUFA|A_GOT_canary|A_canary|A_GOT_CANARY) : Z := '
                                   r'(0x[0-9a-f]+|\d+|port_core_refused_[0-9a-f]+)\.', open(p).read()):
                unitdefs[n] = int(v, 0) if not v.startswith('port') else v
    print('  C6 YE23\'s by-reflexivity decimals vs the unit B definitions (port_core 0e4e stage-out snapshot inputs/unitB):')
    for n in ('F_STDOUT', 'F_STDERR', 'STDOUT_BUFA', 'A_GOT_canary', 'A_canary'):
        uv = unitdefs.get(n)
        if isinstance(uv, int):
            ok = check(uv == consts[n], 'unit %s = %s, YE23 asserts %s' % (n, hx(uv), hx(consts[n])))
            print('     %-12s YE23 %-10s unit %-10s %s' % (n, hex(consts[n]), hx(uv), 'PASS' if ok else 'FAIL'))
        else:
            print('     %-12s YE23 %-10s unit %s: NO VALUE IN THE UNIT FILE (open point)' % (n, hex(consts[n]), uv))
    if isinstance(unitdefs.get('A_GOT_CANARY'), int):
        check(unitdefs['A_GOT_CANARY'] == consts['A_GOT_canary'], 'YE22 A_GOT_CANARY')
        print('     A_GOT_CANARY (YE22) %s = A_GOT_canary: PASS' % hex(unitdefs['A_GOT_CANARY']))
    # ---- image facts
    F_STDIN = maps['YE23'][('h', [k for k, v in DEC_NAME.items() if v == 'F_STDIN'][0])][0]
    consts['F_STDIN'] = F_STDIN
    cdec = {v: k for k, v in DEC_NAME.items()}
    print('  C7 image facts (%s pin bytes; cgif B control in brackets):' % TGT)
    for nm_, f, cf in (('stdout', consts['F_STDOUT'], cdec['F_STDOUT']), ('stderr', consts['F_STDERR'], cdec['F_STDERR']),
                       ('stdin', F_STDIN, cdec['F_STDIN'])):
        print('     __%s_FILE %s .buf (FILE+88) = %s  [cgif %s .buf %s]' % (nm_, hex(f), hex(EU.u(f + 88, 8)),
                                                                     hex(cf), hex(EC.u(cf + 88, 8))))
    check(EU.u(consts['F_STDOUT'] + 88, 8) == consts['STDOUT_BUFA'], 'STDOUT_BUFA != __stdout_FILE.buf in the pin')
    check(EC.u(cdec['F_STDOUT'] + 88, 8) == cdec['STDOUT_BUFA'], 'cgif control: STDOUT_BUFA != cgif __stdout_FILE.buf')
    check(EU.u(consts['A_GOT_canary'], 8) == consts['A_canary'], 'A_GOT_canary does not hold A_canary in the pin')
    check(EC.u(cdec['A_GOT_canary'], 8) == cdec['A_canary'], 'cgif control: A_GOT_canary does not hold A_canary')
    print('     .got slot A_GOT_canary %s holds %s (= A_canary %s; __stack_chk_guard in the twin: %s) [cgif %s holds %s]'
          % (hex(consts['A_GOT_canary']), hex(EU.u(consts['A_GOT_canary'], 8)), hex(consts['A_canary']),
             UU.enclosing(consts['A_canary']), hex(cdec['A_GOT_canary']), hex(EC.u(cdec['A_GOT_canary'], 8))))
    tls_o, tls_n = EMAP['tls_anchor']['old']['builtin_tls'], EMAP['tls_anchor']['new']['builtin_tls']
    check(tls_o + 200 == cdec['TFIB_TPX'] and tls_n + 200 == consts['TFIB_TPX'], 'TFIB_TPX != builtin_tls+200')
    print('     TFIB_TPX = builtin_tls+200: data map TLS anchor builtin_tls %s -> %s; cgif %s; twin builtin_tls %s'
          % (hex(tls_n), hex(consts['TFIB_TPX']), hex(tls_o + 200),
             hex([v for v, sz, t, n in UU.syms if n == 'builtin_tls'][0])))
    a0 = maps['YE23'][('h', pe[('h', 0x5f8fe0)][1])][0]
    a1 = maps['YE23'][('h', pe[('h', 0x5f9110)][1])][0]
    check(a1 - a0 == 0x130, 'atexit region size changed')
    print('     atexit region [%s, %s) size %s (KEEP 0x130); finished_atexit %s / builtin %s in the twin'
          % (hex(a0), hex(a1), hex(a1 - a0), UU.enclosing(a0), UU.enclosing(a0 + 0x18)))
    agend = AG['U'][0] + AG['U'][1]
    print('     zero-fill start of the last PT_LOAD %s (%s); image end %s; main %s (twin)'
          % (hex(EU.zero_suffix_start()),
             ('= __stop_asan_globals %s' % hex(agend)) if AG['U'][1] else
             'n = 0: no asan_globals section; the .data end (where the empty array begins) is %s' % hex(ag_start(EU, UU)[0]),
             hex(hp_u[-1]), hex([v for v, sz, t, n in UU.syms if n == 'main'][0])))
    check([v for v, sz, t, n in UU.syms if n == 'main'][0] == T['main'], 'main != the lane measurement %s' % hex(T['main']))
    check(EU.sec['.text'] == T['text'] and hp_u[-1] == T['top'] and len(descriptors(EU, *AG['U'])) == T['ndesc'],
          '%s section facts differ from the lane measurement: .text %s, image end %s, %d descriptor(s)'
          % (TGT, EU.sec['.text'], hex(hp_u[-1]), len(descriptors(EU, *AG['U']))))
    print('     .text %s+%s; image end %s; %d asan_globals descriptor(s): all equal to the lane measurement'
          % (hex(EU.sec['.text'][0]), hex(EU.sec['.text'][1]), hex(hp_u[-1]), T['ndesc']))
    # ---- C8 cells read from the pin
    cells = cell_checks(body(outs['YE23']), consts, EU)
    npin = sum(1 for r in cells if r[3] == 'PIN')
    print('  C8 YE23 cells: %d distinct (addr,size,value); %d image-backed read from the pin (all equal: %s); '
          '%d in the zero-fill part (runtime exit state)' % (len(cells), npin, all(r[5] for r in cells if r[3] == 'PIN'),
                                                             len(cells) - npin))
    for addr, size, val, kind, got, ok in cells:
        print('     %-9s %d %-12s %-4s %s %s' % (hex(addr), size, hx(val), kind, got, '' if ok else 'FAIL'))
    # ---- C9 DRV_IVS (YD1y)
    dw = re.search(r'Definition DRV_IVS : list \(Z \* Z\) := \[([^\]]*)\]\.', outs['YD1y']).group(1)
    ivs = [(int(a, 16), int(b, 16)) for a, b in re.findall(r'\((0x[0-9a-f]+), (0x[0-9a-f]+)\)', dw)]
    check(len(ivs) == 4 and all(a < b for a, b in ivs) and all(ivs[i][1] <= ivs[i + 1][0] for i in range(3)),
          'DRV_IVS not 4 sorted disjoint windows')
    check(all(hp_u[2] <= a and b <= hp_u[-1] for a, b in ivs), 'DRV_IVS outside [rw lo, image end)')
    print('  C9 DRV_IVS %s: 4 sorted disjoint windows inside [%s, %s); ODR bytes: %s'
          % (['[%s, %s)' % (hex(a), hex(b)) for a, b in ivs], hex(hp_u[2]), hex(hp_u[-1]),
             ('none (%s)' % ('no asan global at all' if not AG['U'][1] else 'the registered global(s) have odr -1'))
             if not ODR_U else ODR_U))
    agname = 'asan_globals' if AG['U'][1] else '.data-end'
    want = [('oft_arg0', agname), ('__do_init.__initialized', '__do_fini.__finalized'),
            ('target_run.initialized', 'builtin_tls+112'), ('finished_atexit', 'exit.exit_lock')]
    for (a, b), (wa, wb) in zip(ivs, want):
        na = UU.enclosing(a)
        nb = (agname, 0) if b == ag_start(EU, UU)[0] else UU.enclosing(b)
        sa = na[0] if na and na[1] == 0 else '%s+%d' % na if na else '?'
        sb = nb[0] if nb and nb[1] == 0 else '%s+%d' % nb if nb else '?'
        ok = check(sa == wa and sb == wb, 'DRV_IVS window [%s, %s) named %s .. %s, want %s .. %s'
                   % (hex(a), hex(b), sa, sb, wa, wb))
        if b == ag_start(EU, UU)[0] and not AG['U'][1]:
            N0.append('DRV_IVS window 1 end: no asan_globals section -> %s = the end of .data, where the empty array '
                      'begins (the donor window ends at its asan_globals start)' % hex(b))
        print('     [%s, %s) = %s .. %s %s' % (hex(a), hex(b), sa, sb, 'PASS' if ok else 'FAIL'))
    for lo, hi in ODR_U:
        check(any(a <= lo and hi <= b for a, b in ivs), 'ODR bytes outside DRV_IVS')
    # C9b DRVW_not_owned gate (decode's drvivs.py): cgif B's YF0m owned list vs the donor windows (control); moved by
    # the data map vs the fuzz_uci B windows; --af0m when given.
    _, _, own_c = af0m_tables(cgif_yf0m)
    dw_c = re.search(r'Definition DRV_IVS : list \(Z \* Z\) := \[([^\]]*)\]\.', src['YD1y']).group(1)
    ivs_c = [(int(a, 16), int(b, 16)) for a, b in re.findall(r'\((0x[0-9a-f]+), (0x[0-9a-f]+)\)', dw_c)]

    def overlaps(own, wins):
        return [(hex(a), hex(n), '[%s, %s)' % (hex(lo), hex(hi))) for a, n in own for lo, hi in wins
                if a < hi and lo < a + n]
    bad_c = overlaps(own_c, ivs_c)
    check(own_c and not bad_c, 'control: cgif B YF0m meets the donor DRV_IVS')
    own_m, how, cg_only_own = [], {}, []
    for a, n in own_c:
        lo, hi = data_reloc(a), data_reloc(a + n)
        sc = EC.section_of(a)
        if lo is not None and hi is not None and hi > lo:
            own_m.append((lo, hi - lo))
            how['both ends'] = how.get('both ends', 0) + 1
        elif sc and sc[1] == 0 and EC.sec[sc[0]][1] == n and sc[0] in EU.sec:
            own_m.append(EU.sec[sc[0]])
            how['whole section ' + sc[0]] = how.get('whole section ' + sc[0], 0) + 1
        else:
            got_b = 0
            for r in RUNS:
                l2, h2 = max(a, r['old_lo']), min(a + n, r['old_hi'])
                if l2 < h2:
                    own_m.append((r['new_lo'] + l2 - r['old_lo'], h2 - l2))
                    got_b += h2 - l2
            how['run pieces'] = how.get('run pieces', 0) + 1
            if got_b == 0:
                cg_only_own.append((hex(a), hex(n), sc[0] if sc else None))
    bad_m = overlaps(own_m, ivs)
    check(not bad_m, 'cgif B owned list moved by the data map meets the target DRV_IVS')
    print('  C9b DRVW_not_owned gate: cgif B YF0m (%d owned entries) vs donor DRV_IVS: %d overlaps; cgif owned list moved '
          '(%s; no %s byte: %s) vs %s DRV_IVS: %d overlaps %s'
          % (len(own_c), len(bad_c), ', '.join('%s %d' % kv for kv in sorted(how.items())), TGT, cg_only_own, TGT,
             len(bad_m), bad_m))

    # ---- X1 by-reference check: the code that references a cgif data address (pc-relative auipc pairs in .text),
    # moved by binmatch, references the fuzz_uci value (the data map's own evidence, re-derived here per numeral)
    xc, xu_ = xrefs(EC, EC.sec['.text']), xrefs(EU, EU.sec['.text'])
    vals = [(nm, k[1], uv) for nm in ('YE23', 'YD1y') for k, (uv, kind, rule) in derived[nm].items()
            if kind in ('DATA', 'DRV', 'DEC')]
    vals += [('YE37', int(r[1], 16), int(r[3], 16)) for r in tab37 if r[2] in ('ROW', 'PTR', 'CELLR')
             and r[1].startswith('0x') and r[3].startswith('0x') and not is_code(int(r[1], 16))]
    nref = nok = 0
    for nm, cv, uv in sorted(set(vals), key=lambda x: (x[0], x[1])):
        pcs = xc.get(cv, [])
        if not pcs:
            continue
        nref += 1
        mapped = {code_reloc(pc)[0] for pc in pcs if code_reloc(pc)}
        unm = [hex(pc) for pc in pcs if not code_reloc(pc)]
        got = set(xu_.get(uv, []))
        extra = sorted(got - mapped)
        ok = check(mapped <= got, 'X1 %s %s -> %s: cgif refs %s moved %s do not all reference the target value '
                   '(target refs %s)' % (nm, hex(cv), hex(uv), [hex(p) for p in pcs], sorted(map(hex, mapped)),
                                         sorted(map(hex, got))))
        nok += ok
        print('     X1 %-4s %-9s -> %-9s cgif refs %d (moved %d%s) == target refs %d%s: %s'
              % (nm, hex(cv), hex(uv), len(pcs), len(mapped), ', not identical code %s' % unm if unm else '', len(got),
                 ', extra target refs in %s' % sorted({'/'.join(sorted(UU.names_at(p)[0])) for p in extra}) if extra else '',
                 'PASS' if ok else 'FAIL'))
    print('  X1 by-reference check: %d data numerals (of %d) have a direct pc-relative reference in cgif\'s .text; for %d '
          'the moved references all reference the target value' % (nref, len(set(vals)), nok))

    # ---- YE37 controls / gates
    print('  YE37 (x2 ranges):')
    _, _, cgrows = rodata_block(src['YE37'])
    ccells, czs, _ = af0m_tables(cgif_yf0m)
    cmiss = [(hex(b + o), w, hex(v)) for s_, e_, b, sz, cs_ in cgrows for o, w, v in cs_
             if first_cell(ccells, b + o) != (b + o, w, v)]
    check(not cmiss, 'control: a cgif YE37 x2_rodata cell is not the first Tfib_const cell of cgif YF0m: %s' % cmiss)
    cshb = [x for lo, n in shw_list(src['YE37']) for x in range(lo, lo + n)]
    czmiss = [hex(x) for x in cshb if not ((first_cell(ccells, x) or (0, 0))[1] == 1 or
                                           any(shadow(lo) <= x < shadow(lo) + n // 8 for lo, n in czs))]
    check(not czmiss, 'control: cgif shw bytes not covered by cgif YF0m: %s' % czmiss)
    ccel = [(int(a, 16), int(w), int(v)) for a, w, v in re.findall(r'cellr (0x[0-9a-f]+) (\d+) \(SLit (\d+)\) true',
                                                                    src['YE37'])]
    ccmiss = [c for c in ccel if first_cell(ccells, c[0]) != c]
    check(not ccmiss, 'control: cgif cellr cells not in cgif YF0m: %s' % ccmiss)
    print('  E4 control (the gates hold for cgif\'s own file): cgif YE37 x2_rodata %d cells are each the first '
          'Tfib_const cell of cgif YF0m at the address (width, value): %s; x2_shw %d bytes covered by a 1-byte const '
          'shadow cell or a Tfib_zero_shadow range: %s; cellr %d cells: %s'
          % (sum(len(r[4]) for r in cgrows), not cmiss, len(cshb), not czmiss, len(ccel), not ccmiss))
    # the target's start-up shadow facts by the frozen af0m (238598b380f1) functions, = the lane's T0.4 measurement
    spec = importlib.util.spec_from_file_location('af0m', UCIREF + '/af0m.py')
    sys.path.insert(0, UCIREF)
    af = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(af)
    hull = af.image_hull(PIN)
    scells, zr, _ = af.shadow_lists(PIN, hull)
    okt = check((scells, zr, hull) == (T['shadow_cells'], T['zero_shadow'], T['hull']),
                'af0m shadow facts differ from the lane measurement: hull %s, %d const cells, %d zero range(s)'
                % (hull, len(scells), len(zr)))
    shb = [x for lo, n in shw37 for x in range(lo, lo + n)]
    zmiss = [hex(x) for x in shb if not (x in scells or any(shadow(lo) <= x < shadow(hi) for lo, hi in zr))]
    check(not zmiss, '%s shw bytes not covered by the start-up shadow facts: %s' % (TGT, zmiss))
    print('  E5 %s start-up shadow (frozen af0m 238598b380f1 image_hull/shadow_lists): hull %s; const shadow %d '
          'cells %s; zero-shadow ranges %s; = the lane measurement: %s; x2_shw %s: %d byte(s), each a const cell or '
          'zero shadow: %s'
          % (TGT, [hex(x) for x in hull], len(scells), ['%s=%s' % (hex(k), hex(v)) for k, v in sorted(scells.items())],
             [(hex(a), hex(b)) for a, b in zr], okt, [(hex(a), n) for a, n in shw37], len(shb), not zmiss))
    if not shb:
        N0.append('shbyte_chk / E5 shadow coverage: x2_shw has no byte at all (the one window is empty), so the check '
                  'is vacuous: 0 shadow bytes to cover')
    for x in shb:
        print('     shadow byte %s: %s' % (hex(x), 'const cell %s' % hex(scells[x]) if x in scells else
                                           'zero shadow of %s' % [(hex(lo), hex(hi)) for lo, hi in zr
                                                                  if shadow(lo) <= x < shadow(hi)]))
    # provisional: port_core's own relocation of cgif's YF0m onto fuzz_uci B (parent lane, snapshot)
    pcells, pzs, pown = af0m_tables(open(os.path.join(UNIT, 'YF0m.v')).read())
    _, _, orows = rodata_block(outs['YE37'])
    pmiss = []
    for s_, e_, b, sz, cs_ in orows:
        for o, w, v in cs_:
            if first_cell(pcells, b + o) != (b + o, w, v):
                pmiss.append((hex(b + o), w, hx(v), first_cell(pcells, b + o)))
    for a, w, v in cel37:
        if first_cell(pcells, cm37[a]) != (cm37[a], w, v):
            pmiss.append(('cellr', hex(cm37[a]), first_cell(pcells, cm37[a])))
    print('  E6 PROVISIONAL (port_core 0e4e stage-out YF0m snapshot, not the unit\'s own YF0m): x2_rodata %d cells + '
          'cellr %d: not the first Tfib_const cell there: %d %s' % (sum(len(r[4]) for r in orows), len(cel37),
                                                                    len(pmiss), pmiss))
    if args.af0m:
        acells, azs, aown = af0m_tables(open(args.af0m).read())
        amiss = [(hex(b + o), w, hx(v), first_cell(acells, b + o)) for s_, e_, b, sz, cs_ in orows for o, w, v in cs_
                 if first_cell(acells, b + o) != (b + o, w, v)]
        amiss += [('cellr', hex(cm37[a])) for a, w, v in cel37 if first_cell(acells, cm37[a]) != (cm37[a], w, v)]
        amiss += [('shadow', hex(x)) for x in shb if not ((first_cell(acells, x) or (0, 0))[1] == 1 or
                                                          any(shadow(lo) <= x < shadow(lo) + n // 8 for lo, n in azs))]
        bad = overlaps(aown, ivs)
        print('  --af0m %s: rodata_chk / cellr / shbyte_chk misses %d %s; DRVW_not_owned overlaps %d %s'
              % (args.af0m, len(amiss), amiss, len(bad), bad))
        check(not amiss and not bad, '--af0m gates')
    # YE37 role identity: rows vs decode B / grant B (names), cellr names
    _, _, drows = rodata_block(dec['YE37'])
    _, _, grows = rodata_block(gra['YE37'])
    for tag, rr, E, U, rag, rtext in (('decode B', drows, ED, UD, AG['D'][0], dec['YE37']),
                                      ('grant B', grows, EG, UG, AG['G'][0], gra['YE37'])):
        if not AG['U'][1]:
            # n = 0: this image has no descriptor-array row, so the reference's is dropped and the remaining rows
            # are compared one for one as usual. The .got row's two cells are that image's asan_globals start / end
            # and 0 / 0 here, which the row loop checked against the twin's __start/__stop_asan_globals.
            drop = [r for r in rr if r[2] == rag]
            check(len(drop) == 1, 'YE37 n = 0: %s has no descriptor-array row at %s' % (tag, hex(rag)))
            print('  E7 (n = 0) YE37 vs %s: %s\'s descriptor-array row %s (%d descriptor(s)) is dropped; the other '
                  '%d rows are compared one for one:'
                  % (tag, tag, hex(rag), U.sec['asan_globals'][1] // 64, len(rr) - 1))
            rr = [r for r in rr if r[2] != rag]
        check(len(rr) == len(rows37), 'YE37: %s has %d rows, the target %d' % (tag, len(rr), len(rows37)))
        nb_ = 0
        for (ub, us, kind, ucs), (s2, e2, rb, rs, rcs) in zip(rows37, rr):
            if kind == 'GDESC':
                ok = rb == rag
                why = 'globals array: %s row %s %s = its asan_globals %s' % (tag, hex(rb), rs, hex(rag))
            else:
                absent = any(r_.startswith('section asan_globals') and 'ABSENT' in r_ for *_, r_ in ucs)
                if (UU.enclosing(ub) is None and (UU.section_of(ub) or ('',))[0] == '.rodata') or absent:
                    # an anonymous .rodata constant, or (n = 0) the .got slot that holds 0 because the section is
                    # absent: identity = the code that references it (twin-named function+offset), not the pointer
                    xr, xu = xref_role(E, U, rb, U.sec['.text']), xref_role(EU, UU, ub, UU.sec['.text'])
                    ok = xref_match(xr, xu) and bool(xu) and len(ucs) == len(rcs)
                    why = '%s %s referenced by %s / this image %s referenced by %s' % (
                        'the .got slot of the ABSENT asan_globals section' if absent else 'anonymous .rodata',
                        hex(rb), xstr(xr), hex(ub), xstr(xu))
                else:
                    ok = roles_equal(role(E, U, rb, 'DATA'), role(EU, UU, ub, 'DATA')) and len(ucs) == len(rcs)
                    why = 'base %s %s / uci %s %s' % (hex(rb), rstr(role(E, U, rb, 'DATA')), hex(ub),
                                                       rstr(role(EU, UU, ub, 'DATA')))
                for (o, w, cv, uv, ck, rule), (o2, w2, v2) in zip(ucs, rcs):
                    if ck == 'PTR' and rule.startswith('section '):
                        sname, se = rule.split()[1], rule.split()[2].rstrip(':')
                        lo_, sz_ = U.sec[sname]
                        okp = (o, w) == (o2, w2) and v2 == (lo_ if se == 'start' else lo_ + sz_)
                        why += '; +%d ptr %s / %s = section %s %s in each image' % (o, hex(v2), hex(uv), sname, se)
                    elif ck == 'PTR':
                        k = 'CODE' if (UU.section_of(uv) or ('',))[0] == '.text' else 'DATA'
                        okp = (o, w) == (o2, w2) and roles_equal(role(E, U, v2, k), role(EU, UU, uv, k))
                        why += '; +%d ptr %s %s / %s %s' % (o, hex(v2), rstr(role(E, U, v2, k)), hex(uv),
                                                             rstr(role(EU, UU, uv, k)))
                    else:
                        okp = (o, w, uv) == (o2, w2, v2)
                        why += '; +%d const %s / %s' % (o, hex(v2), hex(uv))
                    ok = ok and okp
            nb_ += not ok
            check(ok, 'YE37 row %s vs %s row %s: role or chunks differ (%s)' % (hex(ub), tag, hex(rb), why))
            print('     vs %-8s row %-9s %s: %s' % (tag, hex(ub), 'same' if ok else 'DIFFERENT', why[:400]))
        rc_ = [int(a, 16) for a in re.findall(r'cellr (0x[0-9a-f]+) \d+ \(SLit \d+\) true', rtext)]
        if not cel37:          # n = 0: this file states no exit cell at all
            okc = 'n/a (this file has no cellr cell; %s has %d)' % (tag, len(rc_))
        else:
            okc = len(rc_) == len(cel37) and all(roles_equal(role(E, U, a, 'DATA'), role(EU, UU, cm37[c[0]], 'DATA'))
                                                 for a, c in zip(rc_, cel37))
            check(okc, 'YE37 cellr vs %s' % tag)
        print('  E7 YE37 x2_rodata rows vs %s: %d rows, role/chunk mismatches %d; cellr roles equal: %s %s'
              % (tag, len(rows37), nb_, okc, [(hex(a), rstr(role(E, U, a, 'DATA'))) for a in rc_]))

    # ---- C10 no cgif-only address left
    cg_only = set()
    for nm in derived:
        for k, (uv, kind, rule) in derived[nm].items():
            if kind not in ('CONST',) and (is_cg_img(k[1]) or is_shadow(k[1])) and uv != k[1]:
                cg_only.add(k[1])
    for v in tokens(xw2_lines(src['YE23'])):
        if v[1] not in {t[1] for t in tokens(gl['U'])}:
            cg_only.add(v[1])
    cg_only |= moved37
    left = {}
    for nm in outs:
        for k, v in tokens(body(outs[nm])):
            if v in cg_only and not (nm == 'YE37' and v in {x for x, n in shw37}):
                left.setdefault(nm, set()).add(v)
    check(not left, 'cgif-only addresses left: %s' % {k: sorted(map(hex, v)) for k, v in left.items()})
    print('  C10 cgif-only addresses (%d distinct) left in the outputs: %s'
          % (len(cg_only), {k: sorted(map(hex, v)) for k, v in left.items()} or 'none'))
    # ---- C11 small decimals unchanged: donor == fuzz_uci (checked); decode B / grant B shown
    for nm in outs:
        sd = lambda t: sorted(SMALL.findall(proof_part(t)))
        if nm == 'YE37':
            print('  C11 YE37: small decimals donor %d / target %d / decode B %d / grant B %d (the shw form and the '
                  'globals row change them; see C12)' % tuple(len(sd(x)) for x in (src[nm], outs[nm], dec[nm], gra[nm])))
            continue
        ok = check(sd(src[nm]) == sd(outs[nm]), '%s small decimals (<5 digits) differ from the donor' % nm)
        print('  C11 %s: %d small decimal tokens (< 5 digits, from `Import ListNotations.` on): identical multiset in '
              'donor / %s: %s; decode B equal: %s; grant B equal: %s'
              % (nm, len(sd(src[nm])), TGT, ok, sd(src[nm]) == sd(dec[nm]), sd(src[nm]) == sd(gra[nm])))
    print('  C12 shape (every numeral masked; text from `Import ListNotations.` on; record names TfibSyms/GrantSyms '
          'identified) of each output vs decode B and grant B, differing line groups:')
    for nm in outs:
        for tag, texts in (('decode B', dec), ('grant B', gra)):
            sdiff = shape_diff(proof_part(texts[nm]), proof_part(outs[nm]))
            print('     %s vs %s: %d differing group(s)' % (nm, tag, len(sdiff)))
            for op, i1, i2, j1, j2, la, lb in sdiff:
                print('       %s ref %d-%d / target %d-%d' % (op, i1, i2, j1, j2))
                for l in la[:6]:
                    print('         - %s' % l[:170])
                for l in lb[:6]:
                    print('         + %s' % l[:170])

    # ---- numeral table
    rows = []
    for nm in ('YE23', 'YD1y'):
        cnt = {}
        for k in tokens(mask_xw2(bodies[nm]) if nm == 'YE23' else bodies[nm]):
            cnt[k] = cnt.get(k, 0) + 1
        for k, (uv, kind, rule) in sorted(maps[nm].items(), key=lambda kv: (kv[0][0] == 'd', kv[0][1])):
            if kind == 'SHADOW':
                continue
            xd = xref.get((nm, k, 'decode B'), ('', '', True, False))
            xg = xref.get((nm, k, 'grant B'), ('', '', True, False))
            xa = xref.get((nm, k, 'uci A'), ('', '', True, False))
            rows.append('| %s | %s | %d | %s | %s | %s | %s | %s | %s | %s |' % (
                nm, hex(k[1]) if k[0] == 'h' else str(k[1]), cnt[k], kind,
                hex(uv) if k[0] == 'h' else str(uv), rule, roles.get((nm, k), 'const'),
                'yes' if xd[2] else 'NO', ('yes' if xg[2] else 'differs: %s' % xg[0]) + (' (driver)' if xg[3] else ''),
                'yes' if xa[2] else 'NO'))
    lines = ['| file | cgif B | n | kind | %s | rule | %s source (pin/twin) | = decode B role | '
             '= grant B role | = uci A role |' % (TGT, TGT), '|---|---|---|---|---|---|---|---|---|---|'] + rows
    lines += ['', 'XW2 shadow line (YE23, generated):', '',
              '- cgif B: `%s`' % xw2_lines(src['YE23']), '- %s: `%s`' % (TGT, gl['U']), '',
              '| cgif B | %s | rule (%s source) |' % (TGT, TGT), '|---|---|---|']
    du, dc = descriptors(EU, *AG['U']), descriptors(EC, *AG['C'])
    for i, d in enumerate(dc):
        if i < len(du):
            lines.append('| %s | %s | shadow(global %d beg %s) |' % (hex(shadow(d['beg'])), hex(shadow(du[i]['beg'])), i,
                                                                     hex(du[i]['beg'])))
            lines.append('| %s | %s | shadow(global %d beg + size_with_redzone %s) |' % (
                hex(shadow(d['beg'] + d['swr'])), hex(shadow(du[i]['beg'] + du[i]['swr'])), i, hex(du[i]['swr'])))
        else:
            lines.append('| %s | (removed) | cgif global %d: %s has %d global(s) |' % (hex(shadow(d['beg'])), i,
                                                                                       TGT, len(du)))
            lines.append('| %s | (removed) | cgif global %d end |' % (hex(shadow(d['beg'] + d['swr'])), i))
    lines.append('| %s | %s | shadow(asan_globals %s) |' % (hex(shadow(AG['C'][0])), hex(shadow(AG['U'][0])),
                                                           hex(AG['U'][0])))
    lines.append('| %s | %s | shadow(asan_globals + 64 x %d) |' % (hex(shadow(AG['C'][0] + AG['C'][1])),
                                                                 hex(shadow(AG['U'][0] + AG['U'][1])), len(du)))
    lines += ['', 'YE37 (x2 ranges):', '', '| file | cgif B | kind | %s | source |' % TGT, '|---|---|---|---|---|']
    for r in tab37:
        lines.append('| %s | %s | %s | %s | %s |' % r)
    table = '\n'.join(lines) + '\n'
    print('\n== numeral table ==')
    print(table)

    print('== COUNTS ==')
    for nm in outs:
        for tag, t in (('donor', body(src[nm])), (T['name'], body(outs[nm]))):
            tk = tokens(t)
            print('  %s %-8s numerals: %d hex (%d distinct) + %d decimal >= 5 digits (%d distinct); %d small decimals; '
                  '%d lines' % (nm, tag, sum(1 for k in tk if k[0] == 'h'), len({k for k in tk if k[0] == 'h'}),
                                sum(1 for k in tk if k[0] == 'd'), len({k for k in tk if k[0] == 'd'}),
                                len(SMALL.findall(t)), t.count('\n')))
    print('== REQUIRES (cgif namespace; the lane\'s ns tool renames them) ==')
    for nm in outs:
        for frm, mods in re.findall(r'^From (\S+) Require(?: Import)?\s+([^.]*)\.', body(outs[nm]), re.M):
            print('  %s: From %s Require %s' % (nm, frm, ' '.join(mods.split())))

    # ---- G1 the XW2 / x2-windows cross-gate (the image-A exit-walk lane's run_ae37.sh rule): the ranges of YE23's
    # XW2 are exactly YE37's `cellr .. true` cells plus its x2_shw windows.
    xw2m = re.search(r'Definition XW2 \(a : Z\) : Prop := (.*?)\.\n', outs['YE23'], re.S).group(1)
    xw2r = sorted((int(a, 16), int(b, 16)) for a, b in re.findall(r'\((0x[0-9a-f]+) <= a < (0x[0-9a-f]+)\)', xw2m))
    y37c = [(int(a, 16), int(a, 16) + int(w)) for a, w in
            re.findall(r'cellr (0x[0-9a-f]+) (\d+) \(SLit \d+\) true', outs['YE37'])]
    y37s = [(a, a + n) for a, n in shw_list(outs['YE37'])]
    okg1 = check(xw2r == sorted(y37c + y37s), 'G1 XW2 != YE37 cellr + x2_shw')
    print('  G1 XW2 (YE23) as ranges %s == YE37 cellr %s + x2_shw %s: %s'
          % ([(hex(a), hex(b)) for a, b in xw2r], [(hex(a), hex(b)) for a, b in y37c],
             [(hex(a), hex(b)) for a, b in y37s], 'PASS' if okg1 else 'FAIL'))
    if not AG['U'][1]:
        N0.append('G1 cross-gate: XW2 is False (no range), and YE37 has no cellr cell and an empty x2_shw, so both '
                  'sides of the gate are the EMPTY set: it holds for n = 0')
    # ---- C0 control (--target uci): this code must reproduce the fuzz_uci B lane's three files below their headers
    if T['ref']:
        for nm in ('YE23', 'YD1y', 'YE37'):
            p = os.path.join(args.refdir, 'uciB.%s.v' % nm)
            rt = open(p).read()
            okr = check(sha256(p) == T['ref'][nm], 'C0: the reference copy %s is not the pinned one' % nm)
            okb = check(body(rt) == body(outs[nm]), 'C0: %s body differs from the fuzz_uci B lane output' % nm)
            print('  C0 control %s: reference sha256 %s pinned: %s; body (below the headers) byte-equal: %s'
                  % (nm, sha256(p)[:12], okr, okb))
    if N0:
        print('== n = 0 BRANCHES (the line each generator writes when the image has no descriptor) ==')
        for l in N0:
            print('  n = 0  ' + l)

    print('== RESULT ==')
    if FAIL:
        print('FAIL (%d):' % len(FAIL))
        for f in FAIL:
            print('  - ' + f)
    if args.plant:
        print('NEGATIVE CONTROL: %s' % ('CAUGHT (%d failed checks)' % len(FAIL) if FAIL else 'NOT CAUGHT'))
        sys.exit(0 if FAIL else 1)
    if FAIL:
        sys.exit(1)
    for nm in outs:
        textguard.refuse(outs[nm], '%s.v' % nm)
    textguard.refuse(table, 'numerals.md')
    os.makedirs(outdir, exist_ok=True)
    for nm in outs:
        open('%s/%s.v' % (outdir, nm), 'w').write(outs[nm])
    open(outdir + '/numerals.md', 'w').write(table)
    for nm in outs:
        print('  %s/%s.v sha256 %s' % (outdir, nm, sha256('%s/%s.v' % (outdir, nm))))
    print('PASS')



if __name__ == '__main__':
    main()
