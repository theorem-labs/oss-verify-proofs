#!/usr/bin/env python3
"""codedelta.py -- step 1 of the fuzz_transport re-pin dry run: every function of fuzz_transport's own program and of
libdiginet (every STT_FUNC symbol whose address lies in a DWARF compile unit under /src/libdiginet/), old pin vs patched
port build, plain and ubsan, compared by the fixed comparison kit (cmpkit = the kit's SHA256SUMS, sha256 4bbd3a74be89...,
strictcmp2.py 16982e3ef42b; checked by load_kit). Pairing: by name and compile unit; where one name has several copies in
one image, by address order inside the name (the copies are listed by address). Functions present on one side only are
listed as APPEARS / DISAPPEARS.

Verdict per pair:
  EQUAL            same size, every word equal, every pc-relative target the same symbol+offset (strictcmp2 rules)
  EQUAL-mod-pcrel  same size, only auipc / jal / lo12 immediates differ, and every such target is the same symbol+offset
  DIFFERENT@off    anything else; off = the first differing byte offset in the function (a real word difference, a
                   target that is not the same symbol+offset, an unmeasured word, a size / shape change: the first
                   raw byte that differs, or the shorter length when one is a prefix of the other)
Output: TSV on stdout (and the CSTR rows of strictcmp2 as comment lines). Read-only.
usage: codedelta.py --kit CMPKIT_DIR OLD_PLAIN NEW_PLAIN OLD_UBSAN NEW_UBSAN > codedelta.tsv
CMPKIT_DIR is the comparison kit (its SHA256SUMS sha256 4bbd3a74be89...; checked by load_kit before anything is read).
A module that imports this file calls load_kit(CMPKIT_DIR) first.
"""
import sys, os, hashlib, bisect, importlib.util, collections
from elftools.elf.elffile import ELFFile

KIT = sc = BC = None  # set by load_kit: the cmpkit directory, its strictcmp2 module, and strictcmp2's bytecmp (_bc)
CMPKIT_SHA = '4bbd3a74be89'
STRICT_SHA = '16982e3ef42b'

def sha(p):
    return hashlib.sha256(open(p, 'rb').read()).hexdigest()

def load_kit(kit):
    global KIT, sc, BC
    if not sha(os.path.join(kit, 'SHA256SUMS')).startswith(CMPKIT_SHA):
        raise SystemExit('codedelta: %s/SHA256SUMS is not cmpkit %s' % (kit, CMPKIT_SHA))
    for line in open(os.path.join(kit, 'SHA256SUMS')):
        h, f = line.split()
        if sha(os.path.join(kit, f)) != h:
            raise SystemExit('codedelta: %s does not match the cmpkit SHA256SUMS' % f)
    if not sha(os.path.join(kit, 'strictcmp2.py')).startswith(STRICT_SHA):
        raise SystemExit('codedelta: strictcmp2.py is not %s' % STRICT_SHA)
    _spec = importlib.util.spec_from_file_location('strictcmp2', os.path.join(kit, 'strictcmp2.py'))
    m = importlib.util.module_from_spec(_spec); _spec.loader.exec_module(m)
    KIT, sc, BC = kit, m, m._bc

def cu_of_pc(path):
    """{low_pc: compile unit name} of every DW_TAG_subprogram with code (pyelftools resolves DW_FORM_addrx); the CU name
    is relative to DW_AT_comp_dir (/src/libdiginet) for the project's own files, absolute for the oss-verify driver"""
    e = ELFFile(open(path, 'rb')); d = e.get_dwarf_info(); out = {}
    for cu in d.iter_CUs():
        a = cu.get_top_DIE().attributes
        name = a['DW_AT_name'].value.decode() if 'DW_AT_name' in a else '?'
        comp = a['DW_AT_comp_dir'].value.decode() if 'DW_AT_comp_dir' in a else ''
        full = name if name.startswith('/') else os.path.normpath(os.path.join(comp, name))
        for die in cu.iter_DIEs():
            if die.tag == 'DW_TAG_subprogram' and 'DW_AT_low_pc' in die.attributes:
                pc = die.attributes['DW_AT_low_pc'].value
                if pc: out.setdefault(pc, full)
    return out

def own_funcs(img, path):
    """[(name, cu, addr, size)] of the STT_FUNC symbols whose address is the low_pc of a subprogram of a /src/libdiginet/
    compile unit, and [(name, addr, size)] of the sized STT_FUNC symbols no subprogram starts at (unattributed)"""
    m = cu_of_pc(path); out = []; un = []
    for v, z, n, t in img.syms:
        if t != 'STT_FUNC' or z == 0: continue
        cu = m.get(v)
        if cu is None: un.append((n, v, z))
        elif cu.startswith('/src/libdiginet/'): out.append((n, cu, v, z))
    return out, un

def first_raw(b1, b2):
    for i, (x, y) in enumerate(zip(b1, b2)):
        if x != y: return i
    return min(len(b1), len(b2)) if len(b1) != len(b2) else None

def first_real(b1, b2):
    """the first word offset bytecmp counts real (or unmeasured), by bytecmp's own rule (cmp(), lines 157-177)"""
    w1, w2 = BC['words'](b1), BC['words'](b2); st = BC['flow_states'](w1); UNK = BC['UNKNOWN']
    for i, ((o, x, n), (_, y, _)) in enumerate(zip(w1, w2)):
        if x == y: continue
        if n == 4 and (x & 0x7f) == (y & 0x7f):
            op = x & 0x7f; rs1 = (x >> 15) & 31
            mask = 0x01fff07f if op in (0x23, 0x27) else 0x000fffff
            lo12 = op in (0x13, 0x03, 0x23, 0x67, 0x07, 0x27) and (x & mask) == (y & mask)
            j = st[i].get(rs1)
            if op in (0x17, 0x6f) and ((x >> 7) & 31) == ((y >> 7) & 31): continue
            if lo12 and j is not None and j >= 0: continue
        return o
    return None

def compare(I, ko, ao, zo, kn, an, zn):
    """-> (verdict, first differing offset or '', detail)"""
    bo, bn = sc.frd(I[ko], ao, zo), sc.frd(I[kn], an, zn)
    if bo is None or bn is None: return 'DIFFERENT', '', 'UNREADABLE'
    if zo != zn:
        return 'DIFFERENT', hex(first_raw(bo, bn)), 'SIZE %d vs %d' % (zo, zn)
    fb = []
    v, c, t3, diff = sc.tcmp(I, ko, ao, kn, an, zo, fb)
    if v in ('EQUAL', 'EQUAL-mod-pcrel') and not diff:
        return v, '', 'pcrel=%s targets=%s%s' % (c[0], t3, (' ' + sc.fb_text(fb)) if fb else '')
    if v == 'UNMEASURED' and not diff:
        return 'UNMEASURED', '', 'bytecmp UNMEASURED (pcrel,real,unk)=%s, every target the same symbol+offset' % (c,)
    offs = []
    if c is None: offs.append(first_raw(bo, bn))
    else:
        fr = first_real(bo, bn)
        if fr is not None: offs.append(fr)
        offs += [int(d[0], 16) for d in diff]
    off = min(o for o in offs if o is not None)
    det = '%s (pcrel,real,unk)=%s' % (v, c) + ('' if not diff else ' target-diffs=%d first=%s' % (len(diff), diff[0][:4]))
    return 'DIFFERENT', hex(off), det

def jt_settle(old, new, name, v, off, det):
    """a DIFFERENT verdict whose only differences are jump-table / .rodata targets (bytecmp EQUAL-mod-pcrel, real 0):
    the kit's jtcheck.py settles it when every entry is the same function-relative offset"""
    if not (v == 'DIFFERENT' and 'data-differs' in det and det.startswith('EQUAL-mod-pcrel') and ', 0, 0)' in det):
        return v, off, det
    import subprocess
    out = subprocess.run([sys.executable, os.path.join(KIT, 'jtcheck.py'), old, new, name], capture_output=True, text=True).stdout
    head = out.splitlines()[0] if out else ''
    if (head.startswith(name + '\tX ') and '\ttarget differs 0\t' in head and '\ttarget unmeasured 0\t' in head
            and '\tunpaired 0\t' in head and '   DIFF ' not in out and 'REAL' not in out):
        acc = [l.strip()[len('ACCEPT %s ' % name):] for l in out.splitlines()[1:] if l.strip().startswith('ACCEPT')]
        return 'EQUAL-mod-pcrel', '', 'jtcheck settled (kit jtcheck.py): %s; strictcmp2 alone: DIFFERENT@%s %s' % ('; '.join(acc), off, det)
    return v, off, det + ' | jtcheck: ' + head

def main():
    if len(sys.argv) != 7 or sys.argv[1] != '--kit':
        raise SystemExit('usage: codedelta.py --kit CMPKIT_DIR OLD_PLAIN NEW_PLAIN OLD_UBSAN NEW_UBSAN')
    load_kit(sys.argv[2])
    op, np_, ou, nu = sys.argv[3:7]
    paths = {'Oplain': op, 'Nplain': np_, 'Oubsan': ou, 'Nubsan': nu}
    I = {k: sc.Img(p) for k, p in paths.items()}
    print('# cmpkit %s (strictcmp2 %s) from %s' % (CMPKIT_SHA, STRICT_SHA, KIT))
    for k, p in paths.items(): print('# %s = %s sha256 %s' % (k, p, sha(p)))
    print('function\tbuild\tsource\told_addr\told_size\tnew_addr\tnew_size\tverdict\tfirst_diff_off\tdetail')
    counts = collections.Counter()
    for b in ('plain', 'ubsan'):
        ko, kn = 'O' + b, 'N' + b
        fo = collections.defaultdict(list); fn = collections.defaultdict(list)
        oo, uo = own_funcs(I[ko], paths[ko]); on, un = own_funcs(I[kn], paths[kn])
        for n, cu, v, z in oo: fo[(n, cu)].append((v, z))
        for n, cu, v, z in on: fn[(n, cu)].append((v, z))
        print('# %s unattributed sized STT_FUNC (no DWARF subprogram starts there): old %d %s; new %d %s'
              % (b, len(uo), ','.join(x[0] for x in uo), len(un), ','.join(x[0] for x in un)))
        rows = []
        for key in sorted(set(fo) | set(fn), key=lambda k: (k[1], k[0])):
            n, cu = key
            lo, ln = sorted(fo.get(key, [])), sorted(fn.get(key, []))
            for i in range(max(len(lo), len(ln))):
                tag = n if max(len(lo), len(ln)) == 1 else '%s#%d' % (n, i)
                src = cu.replace('/src/libdiginet/', '')
                if i >= len(ln):
                    rows.append((tag, b, src, hex(lo[i][0]), lo[i][1], '-', '-', 'DISAPPEARS', '', '')); continue
                if i >= len(lo):
                    rows.append((tag, b, src, '-', '-', hex(ln[i][0]), ln[i][1], 'APPEARS', '', '')); continue
                v, off, det = compare(I, ko, lo[i][0], lo[i][1], kn, ln[i][0], ln[i][1])
                v, off, det = jt_settle(paths[ko], paths[kn], n, v, off, det)
                rows.append((tag, b, src, hex(lo[i][0]), lo[i][1], hex(ln[i][0]), ln[i][1], v, off, det))
        for r in rows:
            counts[(b, r[7])] += 1
            print('\t'.join(str(x) for x in r))
        # the other functions (musl, compiler-rt, the oss-verify driver): paired by unique name, verdict counts
        oc = collections.Counter(); odiff = []
        bo = {}; bn = {}
        for vv, z, nm, t in I[ko].syms:
            if t == 'STT_FUNC' and z > 0: bo.setdefault(nm, []).append((vv, z))
        for vv, z, nm, t in I[kn].syms:
            if t == 'STT_FUNC' and z > 0: bn.setdefault(nm, []).append((vv, z))
        ownn = {k[0] for k in fo} | {k[0] for k in fn}
        for nm in sorted(set(bo) | set(bn)):
            if nm in ownn: continue
            if len(bo.get(nm, [])) != 1 or len(bn.get(nm, [])) != 1:
                oc['several copies or one side only: not paired by name'] += 1
                odiff.append('%s(copies %d/%d)' % (nm, len(bo.get(nm, [])), len(bn.get(nm, [])))); continue
            (a1, z1), (a2, z2) = bo[nm][0], bn[nm][0]
            v, off, det = compare(I, ko, a1, z1, kn, a2, z2)
            v, off, det = jt_settle(paths[ko], paths[kn], nm, v, off, det)
            oc[v] += 1
            if v not in ('EQUAL', 'EQUAL-mod-pcrel'): odiff.append('%s@%s(%s)' % (nm, off, det[:60]))
        print('# %s other functions (musl, compiler-rt, driver): %s; not EQUAL/EQUAL-mod-pcrel: %s'
              % (b, dict(oc), ', '.join(odiff) or 'none'))
    for (b, v), n in sorted(counts.items()): print('# summary %s %s %d' % (b, v, n))

if __name__ == '__main__':
    main()
