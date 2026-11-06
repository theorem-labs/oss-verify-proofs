#!/usr/bin/env python3
"""drvcmp.py -- KIT-SHAPED loader (the strictcmp review): the names strictcmp2.py, closure_strict2.py and
jtcheck_strict2.py take from the kit, with NO lax target pass (the kit exports none). Read-only.
  - class Img: lines 31-80 of the new repin_check.py (file sha256 4c05cadaeba3, frozen), read from `repin_check.py`
    beside this file (the kit's name) or, if absent, from `repin_check-4c05cadaeba3.py` (the kit's copy); class text
    sha256 checked below: syms / byname / res without
    STT_TLS, tlss / tlsz / tls(off), rd zero-filling past p_filesz up to p_memsz;
  - sx / targets / w_off: lines 209-231 of the same file (text identical to repin_check 9cbc3553c09e lines 188-209 and
    its w_off; sha256 checked below), over
  - bytecmp 1480ca2faea0 (tool registry commit 797e8971d27d, tools/bytecmp/1480ca2faea0; this file beside is that copy
    with its comments scrubbed, code above `base = {` identical; file sha256 checked below), everything above that line.
Exports: Img, _g = {'targets', 'sx', 'w_off', 'Img', ...}, _bc (the bytecmp namespace: words, cmp, auipc_states,
flow_states, WRITES_RD, CALLER_SAVED, ...), bc_words, bc_cmp, bc_states, sha(path), twins(a, b).
usage: drvcmp.py twins STRIPPED UNSTRIPPED ...   PT_LOAD byte equality of a stripped image and its unstripped twin (the
       old drvcmp.py fbbdb144ddfc `twins`, lines 30-40 and 61-65 there, same output)."""
import os, bisect, hashlib
from elftools.elf.elffile import ELFFile
HERE = os.path.dirname(os.path.abspath(__file__))
RC = next(p for p in (os.path.join(HERE, 'repin_check.py'), os.path.join(HERE, 'repin_check-4c05cadaeba3.py')) if os.path.exists(p))
BC = os.path.join(HERE, 'bytecmp-1480ca2faea0.py')
BC_SHA = '0ac2ec8db277b17e34a4a0e35804270157525dbacbc6b0283f95134dbfe129de'
CLASS_SHA = 'dd1087bf7ccc629ccf40be74816135397fda58bae2b33688d1ab08a52e0d5215'      # lines 31-80, newline-terminated
TARGETS_SHA = 'ffd62b28434a53eda148a644c25f6028a4006e94cc140f41049e53f3d20cce20'    # lines 209-231, newline-terminated

def sha(p):
    return hashlib.sha256(open(p, 'rb').read()).hexdigest()

if sha(BC) != BC_SHA: raise SystemExit('drvcmp.py: %s has sha256 %s, want %s' % (BC, sha(BC), BC_SHA))
_src = open(BC).read().split('\n')
_bc = {}
exec('\n'.join(_src[:[i for i, l in enumerate(_src) if l.startswith('base = {')][0]]), _bc)
bc_words, bc_cmp, bc_states = _bc['words'], _bc['cmp'], _bc['auipc_states']
_rl = open(RC).read().split('\n')
_cls, _tgt = '\n'.join(_rl[30:80]) + '\n', '\n'.join(_rl[208:231]) + '\n'
for name, text, want in (('class Img', _cls, CLASS_SHA), ('sx .. w_off', _tgt, TARGETS_SHA)):
    got = hashlib.sha256(text.encode()).hexdigest()
    if got != want: raise SystemExit('drvcmp.py: %s text of %s has sha256 %s, want %s' % (name, RC, got, want))
_g = dict(ELFFile=ELFFile, bisect=bisect, bc_words=bc_words, bc_cmp=bc_cmp, bc_states=bc_states)
exec(_cls, _g)
exec(_tgt, _g)
Img = _g['Img']

def twins(a, b):
    la = [(g['p_vaddr'], g['p_memsz'], g.data()) for g in ELFFile(open(a, 'rb')).iter_segments() if g['p_type'] == 'PT_LOAD']
    lb = [(g['p_vaddr'], g['p_memsz'], g.data()) for g in ELFFile(open(b, 'rb')).iter_segments() if g['p_type'] == 'PT_LOAD']
    same_hdr = [(x[0], x[1], len(x[2])) for x in la] == [(x[0], x[1], len(x[2])) for x in lb]
    nd = [v1 + i for (v1, _, d1), (v2, _, d2) in zip(la, lb) for i in range(min(len(d1), len(d2))) if d1[i] != d2[i]]
    note = [(s['sh_addr'], s['sh_size']) for s in ELFFile(open(b, 'rb')).iter_sections() if s.name == '.note.gnu.build-id'][0]
    out = [hex(x) for x in nd if not (0x10000 <= x < 0x10040 or note[0] <= x < note[0] + note[1])]
    print('%s %s | %s %s | PT_LOAD layout equal: %s | differing loadable bytes: %d, outside ELF header [0x10000,0x10040) '
          'and .note.gnu.build-id [%#x,%#x): %s'
          % (os.path.basename(a), sha(a)[:12], os.path.basename(b), sha(b)[:12], same_hdr, len(nd), note[0],
             note[0] + note[1], out))

if __name__ == '__main__':
    import sys
    if sys.argv[1:2] != ['twins']: raise SystemExit('usage: drvcmp.py twins STRIPPED UNSTRIPPED ...')
    a = sys.argv[2:]
    for i in range(0, len(a), 2):
        twins(a[i], a[i + 1])
