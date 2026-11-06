#!/usr/bin/env python3
"""yd1j-x2.py YD1J: the image-B twin of the image-A core's AD1j change for a 0-descriptor image (fuzz_wire).

fuzz_wire registers no ASan global, so the start-up layer's lib/B/YE37.v states the exit walk of asan.module_dtor ->
__asan_unregister_elf_globals with start == stop (it reads no mu_for_globals cell) and its x2_realizes takes no MU0
argument. The relocated grant text of lib/B/YD1j.v still proves the cell lemma `mu0` and passes it:
`Let X2 : ... := x2_realizes B HB mu0.` This step removes the lemma `mu0` (its 2 lines; used only there) and the
argument, as the image-A core's lib/A/AD1j.v does. It writes no comment. Exit 1 unless each piece occurs exactly once."""
import re, sys

p = sys.argv[1]
t = open(p).read()
lemma = re.compile(r'Lemma mu0 : forall ly, cell_lookup \(Tfib_const ly\) \(ANum 0x[0-9a-f]+\) = Some \(ACell \(ANum 0x[0-9a-f]+\) 8 '
                   r'\(AV \(ANum 0\)\)\)\.\nProof\. intros ly\. vm_compute\. reflexivity\. Qed\.\n')
call = 'Let X2 : xret_realizes_noar tfibsegs B X2_PC XW2 XTRUE := x2_realizes B HB mu0.\n'
if len(lemma.findall(t)) != 1 or t.count(call) != 1:
    sys.exit(f'{p}: expected one mu0 lemma and one x2_realizes call with mu0')
t = lemma.sub('', t).replace(call, call.replace(' HB mu0.', ' HB.'))
if re.search(r'\bmu0\b', re.sub(r'\(\*.*?\*\)', '', t, flags=re.S)):
    sys.exit(f'{p}: mu0 is still used')
open(p, 'w').write(t)
print(f'{p}: lemma mu0 and its use in X2 removed')
