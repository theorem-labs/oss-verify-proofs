import os
import sys
sys.path.insert(0, os.environ.get('REVCHECK_DIR') or sys.exit('set REVCHECK_DIR to the directory holding revcheck.py (NOTES.md, Commands)'))
import revcheck as rc

ROOT = os.environ.get('PIPELINE_ROOT') or sys.exit('set PIPELINE_ROOT to the pipeline libreac root (it holds bin/ and unstripped/)')
for k, p in [('asan', ROOT + '/unstripped/fuzz_boxreg/fuzz_boxreg.asan'),
             ('ubsan', ROOT + '/unstripped/fuzz_boxreg/fuzz_boxreg.asan-ubsan')]:
    e = rc.Elf(p)
    print('==', k, 'phoff', hex(e.phoff), 'phes', e.phes, 'phn', e.phn)
    for n, v in e.secs.items():
        for a, s in v:
            print('  %-18s %#x..%#x size %#x' % (n, a, a + s, s))
    print(' LOADS:')
    for L in e.loads():
        print('   ', L)
    print(' TLS:', e.tls)
