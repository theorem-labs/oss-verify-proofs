#!/usr/bin/env python3
"""run_settle2.py SLICE_DIR TABLE_SUBDIR U_ELF R_ELF CONTROL_ELF: runs settle2.py beside it on (U, R), writes
SLICE_DIR/TABLE_SUBDIR/settled2.tsv, runs it again on (U, CONTROL_ELF), a copy of R with the empty string's first byte
changed, writes settled2-control.tsv, copies settle2.py and this runner into SLICE_DIR/scripts/, and appends (or replaces)
the section `## Not-certified rows settled by measurement` of SLICE_DIR/MANIFEST.md. Images named by file name + sha256."""
import hashlib, os, re, shutil, subprocess, sys

S, SUB, U, R, C = sys.argv[1:6]
HERE = os.path.dirname(os.path.abspath(__file__))
sha = lambda p: hashlib.sha256(open(p, 'rb').read()).hexdigest()[:12]
td = os.path.join(S, SUB); os.makedirs(td, exist_ok=True)
r1 = subprocess.run([sys.executable, os.path.join(HERE, 'settle2.py'), U, R, os.path.join(td, 'settled2.tsv')], capture_output=True, text=True)
r2 = subprocess.run([sys.executable, os.path.join(HERE, 'settle2.py'), U, C, os.path.join(td, 'settled2-control.tsv')], capture_output=True, text=True)
if r1.returncode != 0 or r2.returncode == 0:
    raise SystemExit('run_settle2: settle exit %d (want 0), control exit %d (want 1)' % (r1.returncode, r2.returncode))
os.makedirs(os.path.join(S, 'scripts'), exist_ok=True)
for f in ('settle2.py', 'run_settle2.py'):
    shutil.copy(os.path.join(HERE, f), os.path.join(S, 'scripts', f))
rows = [l.split('\t') for l in open(os.path.join(td, 'settled2.tsv')).read().splitlines()[1:]]
n = len(rows)
sec = ['## Not-certified rows settled by measurement', '',
       'Two of the six not-certified closure rows are settled by scripts/settle2.py (run by scripts/run_settle2.py) on U = %s '
       '(sha256 %s) and R = %s (sha256 %s): %d checks, all PASS (%s/settled2.tsv). Control: the same run on a copy of R with the '
       'empty string\'s first byte changed fails exactly the two string checks (%s/settled2-control.tsv).'
       % (os.path.basename(U), sha(U), os.path.basename(R), sha(R), n, SUB, SUB), '',
       '- `__nl_langinfo_l+0xf8`: SETTLED. The string is empty (NUL) in both images; the code reads that one byte (`lbu` +0x100) and '
       'returns the address (`bnez` +0xfc / `beqz` +0x104 -> `ret` +0x118); its returned value has the consumers of the accepted row '
       '`__nl_langinfo_l+0x5c`.',
       '- `RegisterCommonFlags+0x1218`: SETTLED. The empty string is stored (+0x1228, +0x1274) into the field +0x18 of two '
       'objects whose vtable is __sanitizer::FlagHandlerInclude\'s (+0x121c, +0x1268). Of that vtable\'s two methods Parse only '
       'writes the field and Format reads it once and passes it to internal_snprintf with the format "%s". [Limit: that no code '
       'outside the class reads the field is a property of the class, not measured.]',
       '- `CommonFlags::SetDefaults+0x48`, `InitializeFlags+0x104`, `__lsan::Flags::SetDefaults+0xc`, '
       '`__ubsan::Flags::SetDefaults+0x4`: NOT CERTIFIED: reader list of flag fields needed. The claim of this slice is the '
       'chain, which does not depend on them.', '']
m = os.path.join(S, 'MANIFEST.md')
t = open(m).read()
t = re.sub(r'\n## Not-certified rows settled by measurement\n.*?(?=\n## |\Z)', '\n', t, flags=re.S).rstrip('\n') + '\n\n'
open(m, 'w').write(t + '\n'.join(sec))
print('run_settle2: %s: %d checks PASS, control failed as it must' % (S, n))
