#!/usr/bin/env python3
"""mk_evidence_memchr.py IMAGE OUTDIR -- writes the evidence slice memchr-<IMAGE> (IMAGE = A or B) for fuzz_uci's memchr
contract: the code equality of fuzz_uci's memchr interceptor chain with fuzz_boxreg's released one, measured by
bytecmp + repin_check (cited, not shipped), with a planted control. Every table is written by this script; no host path,
machine name or date is written: an image is named by its file name and sha256.

Inputs, all from the environment (env.example.sh lists them):
  UCI_A, UCI_B         fuzz_uci.asan / fuzz_uci.asan-ubsan unstripped twins
  UCI_PIN_A, UCI_PIN_B the pinned (stripped) fuzz_uci images
  BOX_A, BOX_B         fuzz_boxreg.asan / .asan-ubsan unstripped twins
  BOX_PIN_A, BOX_PIN_B the pinned fuzz_boxreg images
  TOOLS                a directory holding bytecmp-7daa0e2a03d9.py and repin_check-9cbc3553c09e.py, the tools of record
                       (commit 8cd71d3a4bb) tools/bytecmp/7daa0e2a03d9/bytecmp.py and tools/repin_check/9cbc3553c09e/repin_check.py;
                       their sha256 must start with those names, else the run stops
The scripts drvcmp.py, closure.py and jtcheck.py beside this file are copied with the two tools into a temporary
directory and run there. WT_LIB (the unit's proofs/reac-repacer/fuzz_uci/lib) is read by memchr-local.py --check.
"""
import hashlib, os, shutil, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
FNS = ['__interceptor_trampoline_memchr', '___interceptor_memchr', 'memchr', '_ZN11__sanitizer15internal_memchrEPKvim']
JT = ['_ZN6__asan12ErrorGenericC1Ejmmmmbm', '_ZN6__asan9Decorator10ShadowByteEh', '_ZN6__asan16ErrorDescription5PrintEv',
      '_ZN11__sanitizer19GetHandleSignalModeEi', '_ZNK11__sanitizer13SignalContext8DescribeEv',
      '_ZN9libunwind10CFI_ParserINS_17LocalAddressSpaceEE20parseFDEInstructionsERS1_RKNS2_8FDE_InfoERKNS2_8CIE_InfoEmiPNS2_10PrologInfoE',
      '_ZN9libunwind17LocalAddressSpace11getEncodedPERmmhm', '_ZN9libunwind14EHHeaderParserINS_17LocalAddressSpaceEE17getTableEntrySizeEh',
      'sysconf', '__synccall', '__strftime_fmt_1']
PLANT_FN, PLANT_OFF = '___interceptor_memchr', 0x10


def sha(p):
    return hashlib.sha256(open(p, 'rb').read()).hexdigest()


def main():
    img, out = sys.argv[1], os.path.abspath(sys.argv[2])
    assert img in ('A', 'B')
    env = os.environ
    uci, box = env['UCI_' + img], env['BOX_' + img]
    upin, bpin = env['UCI_PIN_' + img], env['BOX_PIN_' + img]
    tools = env['TOOLS']
    tmp = tempfile.mkdtemp(prefix='mkev-')
    for f, pre in (('bytecmp-7daa0e2a03d9.py', '7daa0e2a03d9'), ('repin_check-9cbc3553c09e.py', '9cbc3553c09e')):
        if not sha(os.path.join(tools, f)).startswith(pre):
            raise SystemExit('mk_evidence_memchr: %s is not the tool of record' % f)
        shutil.copy(os.path.join(tools, f), tmp)
    for f in ('drvcmp.py', 'closure.py', 'jtcheck.py'):
        shutil.copy(os.path.join(HERE, f), tmp)
    # the planted control: one non-pc-relative word of the donor's interceptor changed in a copy
    sys.path.insert(0, tmp)
    from elftools.elf.elffile import ELFFile
    e = ELFFile(open(box, 'rb'))
    a = [s['st_value'] for s in e.get_section_by_name('.symtab').iter_symbols() if s.name == PLANT_FN][0] + PLANT_OFF
    off = [g['p_offset'] + a - g['p_vaddr'] for g in e.iter_segments()
           if g['p_type'] == 'PT_LOAD' and g['p_vaddr'] <= a < g['p_vaddr'] + g['p_filesz']][0]
    plant = os.path.join(tmp, 'plant.elf')
    b = bytearray(open(box, 'rb').read()); w0 = b[off:off + 4].hex(); b[off + 3] ^= 1; w1 = b[off:off + 4].hex()
    open(plant, 'wb').write(b)
    names = {uci: 'fuzz_uci.%s(unstripped, sha256 %s)' % (('asan', 'asan-ubsan')[img == 'B'], sha(uci)[:12]),
             box: 'fuzz_boxreg.%s(unstripped, sha256 %s)' % (('asan', 'asan-ubsan')[img == 'B'], sha(box)[:12]),
             upin: 'fuzz_uci.%s(pin, sha256 %s)' % (('asan', 'asan-ubsan')[img == 'B'], sha(upin)[:12]),
             bpin: 'fuzz_boxreg.%s(pin, sha256 %s)' % (('asan', 'asan-ubsan')[img == 'B'], sha(bpin)[:12]),
             plant: 'PLANT(fuzz_boxreg copy, %s+%#x %s -> %s)' % (PLANT_FN, PLANT_OFF, w0, w1), tmp + '/': ''}

    def run(args):
        r = subprocess.run([sys.executable] + args, cwd=tmp, capture_output=True, text=True, env=env)
        t = r.stdout + r.stderr
        for k in sorted(names, key=len, reverse=True):
            t = t.replace(k, names[k])
        if r.returncode:
            raise SystemExit('mk_evidence_memchr: %s failed:\n%s' % (args[0], t))
        return t

    os.makedirs(os.path.join(out, 'tables'), exist_ok=True)
    os.makedirs(os.path.join(out, 'scripts'), exist_ok=True)
    tabs = {
        'twins.txt': run(['drvcmp.py', 'twins', upin, uci, bpin, box]),
        'chain.tsv': run(['drvcmp.py', 'cmp', ','.join(FNS), 'U=' + uci, 'R=' + box, 'P=' + plant, 'U:R,P:R']),
        'closure.txt': run(['closure.py', uci, box, '___interceptor_memchr']) +
                       '== control: the planted copy against the donor\n' + run(['closure.py', plant, box, '___interceptor_memchr']),
        'jtcheck.tsv': run(['jtcheck.py', uci, box, ','.join(JT)]),
    }
    lr = subprocess.run([sys.executable, os.path.join(HERE, 'memchr-local.py'), env['WT_LIB'], '--check'],
                        capture_output=True, text=True)
    tabs['local.txt'] = lr.stdout + 'exit %d\n' % lr.returncode
    local_ok = lr.returncode == 0
    for k, v in tabs.items():
        open(os.path.join(out, 'tables', k), 'w').write(v)
    for f in ('mk_evidence_memchr.py', 'drvcmp.py', 'closure.py', 'jtcheck.py', 'memchr-local.py', 'env.example.sh', 'run.sh'):
        shutil.copy(os.path.join(HERE, f), os.path.join(out, 'scripts', f))
    shutil.rmtree(tmp)
    # verdict lines, read from the tables
    ch = [l.split('\t') for l in tabs['chain.tsv'].splitlines() if l and not l.startswith('#') and not l.startswith('fn\t')]
    ok = all(r[6] in ('EQUAL', 'EQUAL-mod-pcrel') and r[8] == '0' and r[11] == '0' for r in ch if r[1] == 'U:R')
    caught = any(r[0] == PLANT_FN and r[1] == 'P:R' and r[6] == 'DIFFERENT' for r in ch)
    jt_ok = all(l.split('\t')[3:5] == ['target differs 0', 'unpaired differing words 0'] for l in tabs['jtcheck.tsv'].splitlines() if l)
    man = ['# provenance/evidence/memchr-%s: fuzz_uci image %s memchr interceptor chain = fuzz_boxreg\'s released one' % (img, img), '',
           'Written by scripts/mk_evidence_memchr.py; not edited by hand. What a reader needs to re-derive why lib/%s/Rt/Memchr.v '
           'may port fuzz_boxreg\'s released walk (proofs/libreac/fuzz_boxreg/lib/%s/Rt/Memchr.v:562 memchr_icpt_realizesM, recipes '
           '88154566652a): the code of fuzz_uci\'s chain equals the donor\'s up to relocation. Tools cited, not shipped: '
           'the tools of record (commit 8cd71d3a4bb) tools/bytecmp/7daa0e2a03d9/bytecmp.py and tools/repin_check/9cbc3553c09e/repin_check.py. '
           'Generation logs are not here.' % (img, img), '',
           '## Verdict', '',
           '- chain (%s): %s' % (', '.join(FNS), 'EQUAL or EQUAL-mod-pcrel, real 0, target-differ 0' if ok else 'NOT EQUAL'),
           '- planted control: %s' % ('caught (DIFFERENT)' if caught else 'NOT CAUGHT'),
           '- jump / constant table members of the closure: %s' % ('target differs 0, unpaired differing words 0' if jt_ok else 'DIFFER'),
           '- the walk\'s `Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=` redefinitions, global in the donor, are '
           '`Local` in lib/{A,B}/Rt/{Memchr,MemchrChk}.v, so no importer inherits them: %s (memchr-local.py --check). With them '
           'Local, settings check global_settings v10 (439f8e3bd463) reports 0 ESCAPES over the ten memchr files; with them '
           'global it reported 4.' % ('0 global' if local_ok else 'GLOBAL REMAINS'),
           '', '## Files', '', '| file | kind | role |', '|---|---|---|',
           '| `scripts/env.example.sh` | config | every variable name the builder reads, without values |',
           '| `scripts/run.sh` | script | the run of record: builds memchr-A and memchr-B |',
           '| `scripts/mk_evidence_memchr.py` | script | this builder |',
           '| `scripts/drvcmp.py` | script | per-function compare (bytecmp cmp + repin_check target pass) and the twins check |',
           '| `scripts/closure.py` | script | direct-call closure compare |',
           '| `scripts/jtcheck.py` | script | jump-table / constant-table members of the closure |',
           '| `scripts/memchr-local.py` | script | makes the walk\'s global Zify redefinitions Local (only that word changes); --check verifies none is global |',
           '| `tables/twins.txt` | table | unstripped twin = pin, PT_LOAD bytes, both units |',
           '| `tables/chain.tsv` | table | the four chain functions, fuzz_uci : fuzz_boxreg, and the planted control |',
           '| `tables/closure.txt` | table | the interceptor\'s closure, and the planted control |',
           '| `tables/jtcheck.tsv` | table | the 11 table-carrying closure members |',
           '| `tables/local.txt` | table | memchr-local.py --check on the committed lib |']
    open(os.path.join(out, 'MANIFEST.md'), 'w').write('\n'.join(man) + '\n')
    if not (ok and caught and jt_ok and local_ok):
        raise SystemExit('mk_evidence_memchr: verdict failed, see %s' % out)
    print('mk_evidence_memchr: memchr-%s written' % img)


if __name__ == '__main__':
    main()
