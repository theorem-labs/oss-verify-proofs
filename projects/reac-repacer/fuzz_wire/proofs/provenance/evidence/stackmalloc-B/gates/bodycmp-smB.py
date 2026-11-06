#!/usr/bin/env python3
"""bodycmp-smB.py: the body compare of reac-repacer/fuzz_wire's image-B __asan_stack_malloc_0 / _1 files.

The kit is cmpkit 86da41d3ef68 (strictcmp3.py 65688e94214a, `cmp`); run with PYTHONDONTWRITEBYTECODE=1 from a copy of the
kit directory. It compares, fuzz_grant's unstripped twin (5a5ee7c02b4e) against fuzz_wire's (51eb4bef2425):

  1. the kit's own file check (sha256 of the nine members against its SHA256SUMS) and `drvcmp.py twins` for both images
     (each unstripped twin against its pin);
  2. FUNCTIONS: `strictcmp3.py cmp` over EVERY function the files' code table decodes: each row of fs_ranges in the
     relocated lib/B/Rt/YF0r.v, named by the sized FUNC symbol that holds its start in fuzz_wire's twin (NAME{STT_FILE}
     when several local functions carry the name), paired with the donor row of the same name and offset in fuzz_grant's
     twin (the donor's rows of the classes fuzz_wire does not link are listed as DROPPED: fuzz_wire's twin has no
     symbol of that name);
  3. RANGES: the kit's one compare (strictcmp3.tcmp, the function `cmp` calls) over exactly the bytes each fs_ranges row
     decodes (start, words * 4), the same pairs;
  4. PLANT: a copy of fuzz_wire's twin with one word flipped inside __asan_stack_malloc_0 and one inside
     __asan_stack_malloc_1 (bit 20 of the word at +0x4: an immediate bit; the low two bits stay 11), compared as in 2: both
     rows must be reported (not EQUAL / EQUAL-mod-pcrel).

  usage: bodycmp-smB.py KIT YF0r_relocated YF0r_donor OUTDIR
  env:   P (libreac's pinned image tree), R (reac-repacer's)
Writes OUTDIR/bodycmp-{kit,twins,functions,ranges,plant}.out; images are named by role and sha256, never by path.
A function row that is not clean is JUDGED (a line of bodycmp-functions.out) only when every differing target lies
outside the bytes the code table decodes of that function and those ranges compare clean; each such target is
measured (the address each side forms, its first bytes). A range row that stops inside its function and is only
UNMEASURED (an auipc whose consumer lies past the range) is PARTIAL when the whole function compares clean.
Exit 0: every row clean, both plants reported, every row paired; 2: the same except JUDGED function rows; 1: else."""
import hashlib, os, re, shutil, subprocess, sys, tempfile
from elftools.elf.elffile import ELFFile

KIT, YREL, YDON, OUT = sys.argv[1:5]
P, R = os.environ['P'], os.environ['R']
IMG = {
    'G': P + '/unstripped/fuzz_grant/fuzz_grant.asan-ubsan',
    'W': R + '/result/unstripped/fuzz_wire/fuzz_wire.asan-ubsan',
}
PIN = {
    'G': P + '/bin/fuzz_grant/fuzz_grant.asan-ubsan',
    'W': R + '/result/bin/fuzz_wire/fuzz_wire.asan-ubsan',
}


def sha(p):
    return hashlib.sha256(open(p, 'rb').read()).hexdigest()


NAMES = {}
for k, role in (('G', 'fuzz_grant.asan-ubsan twin'), ('W', 'fuzz_wire.asan-ubsan twin')):
    NAMES[IMG[k]] = '%s(%s)' % (role, sha(IMG[k])[:12])
for k, role in (('G', 'fuzz_grant.asan-ubsan pin'), ('W', 'fuzz_wire.asan-ubsan pin')):
    NAMES[PIN[k]] = '%s(%s)' % (role, sha(PIN[k])[:12])


def scrub(s, extra=()):
    for p, n in list(NAMES.items()) + list(extra):
        s = s.replace(p, n)
    return s


def run(cmd, extra=()):
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
    p = subprocess.run(cmd, cwd=KIT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, env=env)
    return p.returncode, scrub(p.stdout, extra)


class Syms:
    """sized FUNC symbols with the STT_FILE of each local one"""
    def __init__(self, path):
        e = ELFFile(open(path, 'rb'))
        self.f = []
        cur = None
        for s in e.get_section_by_name('.symtab').iter_symbols():
            t = s['st_info']['type']
            if t == 'STT_FILE':
                cur = s.name
            elif t == 'STT_FUNC' and s['st_size'] > 0:
                self.f.append((s['st_value'], s['st_size'], s.name, cur if s['st_info']['bind'] == 'STB_LOCAL' else None))
        self.count = {}
        for v, z, n, fl in self.f:
            self.count.setdefault(n, set()).add((v, z))

    def holder(self, a):
        c = sorted((z, v, n, fl) for v, z, n, fl in self.f if v <= a < v + z)
        if len({(v, z) for z, v, n, fl in c}) != 1:
            return None
        z, v, n, fl = c[0]
        q = n if len(self.count[n]) == 1 else '%s{%s}' % (n, fl)
        return q, v, z, a - v


def fs_ranges(path):
    s = open(path).read()
    m = re.search(r'Definition fs_ranges : list \(Z \* nat\) :=\s*\[(.*?)\]\.', s, re.S)
    return [(int(a, 16), int(n)) for a, n in re.findall(r'\((0x[0-9a-f]+), (\d+)%nat\)', m.group(1))]


os.makedirs(OUT, exist_ok=True)
bad = []
# 1. the kit and the twins
rc, o = run(['sha256sum', '-c', 'SHA256SUMS'])
kitid = hashlib.sha256(open(os.path.join(KIT, 'SHA256SUMS'), 'rb').read()).hexdigest()[:12]
open(os.path.join(OUT, 'bodycmp-kit.out'), 'w').write('# kit id (sha256 of SHA256SUMS) %s; sha256sum -c rc=%d\n%s' % (kitid, rc, o))
if rc or kitid != '86da41d3ef68':
    bad.append('kit')
tw = []
for k in ('G', 'W'):
    rc, o = run([sys.executable, 'drvcmp.py', 'twins', PIN[k], IMG[k]])
    tw.append('# drvcmp.py twins %s %s rc=%d\n%s' % (NAMES[PIN[k]], NAMES[IMG[k]], rc, o))
    if rc:
        bad.append('twins ' + k)
open(os.path.join(OUT, 'bodycmp-twins.out'), 'w').write(''.join(tw))

# 2. the pairs, from the code table
SG, SW = Syms(IMG['G']), Syms(IMG['W'])
rel, don = fs_ranges(YREL), fs_ranges(YDON)
pairs, rows = [], []
dkey = {}
for a, n in don:
    h = SG.holder(a)
    dkey[(h[0], h[3])] = (a, n, h)
for a, n in rel:
    h = SW.holder(a)
    if h is None:
        rows.append('UNPAIRED\twire row %#x %d: no unique FUNC symbol holds it' % (a, n)); bad.append('row %#x' % a); continue
    d = dkey.pop((h[0], h[3]), None)
    if d is None or d[1] != n:
        rows.append('UNPAIRED\twire row %#x %d (%s+%#x): no donor row of that name, offset and length' % (a, n, h[0], h[3]))
        bad.append('row %#x' % a); continue
    rows.append('PAIR\t%s+%#x\twire %#x..%#x (fn %#x size %d)\tgrant %#x..%#x (fn %#x size %d)\twords %d'
                % (h[0], h[3], a, a + 4 * n, h[1], h[2], d[0], d[0] + 4 * n, d[2][1], d[2][2], n))
    pairs.append((h[0], h[3], a, d[0], n))
for (q, off), (a, n, h) in sorted(dkey.items(), key=lambda x: x[1][0]):
    wn = q.split('{')[0]
    present = wn in SW.count
    rows.append('DROPPED\tgrant row %#x %d (%s+%#x): fuzz_wire twin %s' % (a, n, q, off, 'HAS a symbol of that name (not dropped!)' if present else 'has no symbol of that name'))
    if present:
        bad.append('dropped %s' % q)
fnlist = ','.join(dict.fromkeys(p[0] for p in pairs))
rc, o = run([sys.executable, 'strictcmp3.py', 'cmp', fnlist, 'W=' + IMG['W'], 'G=' + IMG['G'], 'W:G'])
clean, notclean = 0, []
for line in o.splitlines():
    f = line.split('\t')
    if len(f) > 7 and f[1] == 'W:G':
        if f[6] in ('EQUAL', 'EQUAL-mod-pcrel') and f[11] == '0':
            clean += 1
        else:
            notclean.append((f[0], f[6], f[11], int(f[2], 16), int(f[3], 16)))
FUNCS_OUT = ('# pairs from fs_ranges (relocated lib/B/Rt/YF0r.v vs the donor lib/B/Rt/YF0r.v)\n' + '\n'.join(rows) +
             '\n# strictcmp3.py cmp FNLIST W=<fuzz_wire twin> G=<fuzz_grant twin> W:G  rc=%d; clean rows %d of %d\n%s' % (rc, clean, len(pairs), o))

# 3. the decoded ranges, by the kit's tcmp
sys.path.insert(0, KIT)
sys.dont_write_bytecode = True
import strictcmp3 as sc  # noqa: E402
I = {'W': sc.Img(IMG['W']), 'G': sc.Img(IMG['G'])}
rr = ['range\twire\tgrant\tbytes\tverdict\t(pcrel, real, unmeasured)\ttarget-differ\twords-only']
fclean = {f[0] for f in (l.split('\t') for l in o.splitlines()) if len(f) > 11 and f[1] == 'W:G' and f[6] in ('EQUAL', 'EQUAL-mod-pcrel') and f[11] == '0'}
partial = []
for q, off, wa, ga, n in pairs:
    fb = []
    v, c, t3, diff = sc.tcmp(I, 'W', wa, 'G', ga, 4 * n, fb)
    vv = sc.verdict(v, diff)
    rr.append('%s+%#x\t%#x\t%#x\t%d\t%s\t%s\t%s\t%s' % (q, off, wa, ga, 4 * n, vv, c, diff if diff else 0, v))
    if vv in ('EQUAL', 'EQUAL-mod-pcrel'):
        continue
    # a range that stops inside its function can cut an auipc from its consumer: such a row is measured by the whole
    # function's compare when that compare is clean (and only then)
    if vv == 'UNMEASURED-target' and q in fclean and all(d[3] == 'unmeasured' for d in diff):
        partial.append('PARTIAL\t%s+%#x\tunmeasured only: %s; the whole function %s compares clean (bodycmp-functions.out)' % (q, off, diff, q))
    else:
        bad.append('range %#x %s' % (wa, vv))
open(os.path.join(OUT, 'bodycmp-ranges.out'), 'w').write('# strictcmp3.tcmp over each decoded range (kit %s)\n' % kitid + '\n'.join(rr + partial) + '\n')
RANGE_OK = {r.split('\t')[0] for r in rr[1:] if r.split('\t')[4] in ('EQUAL', 'EQUAL-mod-pcrel')}


def formed(k, fa, fz, at):
    """the address the auipc pair consumed at fa + at forms in image k (linear scan of the function's words)"""
    b = sc.frd(I[k], fa, fz)
    st, i = {}, 0
    while i < len(b):
        lo = b[i] | (b[i + 1] << 8)
        if lo & 3 != 3:
            i += 2; continue
        x = int.from_bytes(b[i:i + 4], 'little'); op, rd, rs1 = x & 0x7f, (x >> 7) & 31, (x >> 15) & 31
        if op == 0x17:
            st[rd] = fa + i + ((x & 0xfffff000) - (1 << 32 if x & 0x80000000 else 0))
        elif i == at and rs1 in st:
            imm = x >> 20
            return st[rs1] + (imm - 4096 if imm & 0x800 else imm)
        elif op in (0x33, 0x3b, 0x13, 0x1b, 0x03, 0x67, 0x6f, 0x37, 0x73, 0x2f):
            st.pop(rd, None)
        i += 4
    return None


# a function row that is not clean: JUDGED only when every differing target lies outside the bytes the code table
# decodes of that function and those ranges compare clean; each such target is measured (the address each side forms
# and its first bytes)
import ast  # noqa: E402
judged = []
for fn, verdict, dtxt, fw, fg in notclean:
    dif = ast.literal_eval(dtxt) if dtxt.startswith('[') else []
    dec = [(off, off + 4 * n, wa) for q, off, wa, ga, n in pairs if q == fn]
    rclean = all(r.split('\t')[0] in RANGE_OK for r in rr[1:] if r.split('\t')[0].startswith(fn + '+'))
    outside = dif and all(not any(lo <= int(d[0], 16) < hi for lo, hi, wa in dec) for d in dif)
    if not (outside and rclean):
        bad.append('function %s %s' % (fn, verdict)); continue
    fz = [x for x in SW.f if x[0] == fw][0][1]
    for d in dif:
        o = int(d[0], 16)
        aw, ag = formed('W', fw, fz, o), formed('G', fg, fz, o)
        bw, bg = sc.frd(I['W'], aw, 24) if aw else None, sc.frd(I['G'], ag, 24) if ag else None
        cw, cg = (bw.split(b'\0')[0] if bw else None), (bg.split(b'\0')[0] if bg else None)
        judged.append('JUDGED\t%s\t%s\tdiffering target +%#x (%s) lies outside the decoded range(s) %s, which compare %s;'
                      ' the target: wire %#x bytes %r (C string %r), grant %#x bytes %r (C string %r)'
                      % (fn, verdict, o, d[3], ', '.join('+%#x..+%#x' % (lo, hi) for lo, hi, wa in dec),
                         'clean' if rclean else 'NOT clean', aw or 0, bw, cw, ag or 0, bg, cg))
open(os.path.join(OUT, 'bodycmp-functions.out'), 'w').write(FUNCS_OUT + ''.join(j + '\n' for j in judged))

# 4. the plant
tmp = tempfile.mkdtemp()
pl = os.path.join(tmp, 'plant-wireB.elf')
shutil.copy(IMG['W'], pl)
e = ELFFile(open(IMG['W'], 'rb'))
text = e.get_section_by_name('.text')
b = bytearray(open(pl, 'rb').read())
log = []
for fn in ('__asan_stack_malloc_0', '__asan_stack_malloc_1'):
    v = [x for x in SW.f if x[2] == fn][0][0]
    off = text['sh_offset'] + (v + 4 - text['sh_addr'])
    w = int.from_bytes(b[off:off + 4], 'little')
    assert w & 3 == 3
    b[off:off + 4] = (w ^ (1 << 20)).to_bytes(4, 'little')
    log.append('# planted %s+0x4 (%#x): %#010x -> %#010x' % (fn, v + 4, w, w ^ (1 << 20)))
open(pl, 'wb').write(b)
psha = sha(pl)[:12]
rc, o = run([sys.executable, 'strictcmp3.py', 'cmp', '__asan_stack_malloc_0,__asan_stack_malloc_1', 'W=' + pl, 'G=' + IMG['G'], 'W:G'],
            extra=((pl, 'plant-wireB.elf(%s)' % psha),))
caught = 0
for line in o.splitlines():
    f = line.split('\t')
    if len(f) > 7 and f[1] == 'W:G':
        if f[6] in ('EQUAL', 'EQUAL-mod-pcrel') and f[11] == '0':
            bad.append('plant not caught %s' % f[0])
        else:
            caught += 1
if caught != 2:
    bad.append('plant rows %d' % caught)
open(os.path.join(OUT, 'bodycmp-plant.out'), 'w').write('\n'.join(log) + '\n# plant image sha256 %s; caught %d of 2\n%s' % (psha, caught, o))
shutil.rmtree(tmp)
print('bodycmp-smB: kit %s; pairs %d; function rows clean %d of %d, judged %d; range rows clean %d of %d (partial %d); plants caught %d of 2; not clean: %s'
      % (kitid, len(pairs), clean, len(pairs), len(judged), len(RANGE_OK),
         len(rr) - 1, len(partial), caught, bad or 'none'))
for j in judged:
    print(j)
# exit 0: every row clean; 2: clean except JUDGED function rows (each measured above); 1: anything else
sys.exit(1 if bad else 2 if judged else 0)
