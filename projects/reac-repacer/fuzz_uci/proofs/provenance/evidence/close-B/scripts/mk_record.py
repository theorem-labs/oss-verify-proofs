#!/usr/bin/env python3
"""mk_record.py LOG SLICE_DIR -- writes SLICE_DIR/records/build.txt and SLICE_DIR/RECORD.md.
records/build.txt: from the cb build log LOG of record, its mode line (without the build host's cache path), its
per-image pin lines, every `cb: target` line, the rc line, and the About / Print Assumptions output of
lib/B/UciBClose.v (the lines from the first top's `About` output to the end of the Print Assumptions blocks), verbatim.
RECORD.md: the slice's record, its row table read from lib/B/UciBClose.v itself (each of the 18 rows with its line
and whether it is a Section Hypothesis or a Lemma), so the line numbers are the committed file's.
"""
import os
import re
import sys

ROWS = ['H_PROG_LLVMF', 'H_PROG_CNO', 'H_PROG_CV', 'H_PROG_CC', 'H_PROG_RUI', 'H_PROG_RHC_F', 'H_RT_STACK_MALLOC1',
        'H_RT_MEMCHR', 'H_KIT_AVIEW_EXT', 'H_KIT_AVIEW_SOME', 'H_LEAF_GLUE', 'HB_CELLS', 'HB_RO_RD_UNOWNED',
        'HB_ROM_NO_ERRNO', 'HB_CNO_UCTX', 'HB_CNO_UFIX', 'HB_CV_UFIX', 'HB_COST']
WAITS = {
    'H_PROG_LLVMF': 'the walk of lib/B/Prog/LLVMFuzzerTestOneInput_cg.v uci_llvmf_holds_stmt',
    'H_PROG_CNO': 'the walk of lib/B/Prog/check_no_overread_cg.v uci_check_no_overread_cg_holds_stmt',
    'H_PROG_CV': 'the walk of lib/B/Prog/check_value_cg.v uci_check_value_cg_holds_stmt',
    'H_PROG_CC': 'the walk of lib/B/Prog/check_clamp_cg.v uci_check_clamp_cg_holds_stmt',
    'H_PROG_RUI': 'the walk of lib/B/Prog/rp_uci_int_cg.v uci_rp_uci_int_holds_stmt',
    'H_PROG_RHC_F': 'the footprint walk of lib/B/Prog/rp_hot_clamp_F_c.v rp_hot_clamp_contract_F',
}
BY = {
    'H_PROG_LLVMF': 'lib/B/Prog/LLVMFuzzerTestOneInput_cgW.v uci_llvmf_holds (824090cba246)',
    'H_PROG_CNO': 'lib/B/Prog/check_no_overread_cgW.v uci_check_no_overread_cg_holds (e61d8b88c3d0)',
    'H_PROG_CV': 'lib/B/Prog/check_value_cgW.v uci_check_value_cg_holds (faf4885cf4dd)',
    'H_PROG_CC': 'lib/B/Prog/check_clamp_cgW.v uci_check_clamp_cg_holds (e5e90545d4c8)',
    'H_PROG_RUI': 'lib/B/Prog/rp_uci_int_cgW.v uci_rp_uci_int_holds (d3f024dc2e5)',
    'H_PROG_RHC_F': 'lib/B/Prog/rp_hot_clamp_FW.v rp_hot_clamp_holds_F (783ed4e623d)',
    'H_RT_STACK_MALLOC1': 'lib/B/Rt/YF0s.v:516 stack_malloc1_contract (evidence 135b5746fc67)',
    'H_RT_MEMCHR': 'lib/B/Rt/Memchr.v memchr_icpt_contract (43a6893892d7)',
    'H_KIT_AVIEW_EXT': 'lib/B/Prog/LeafCgClose.v H_KIT_AVIEW_EXT',
    'H_KIT_AVIEW_SOME': 'lib/B/Prog/LeafCgClose.v H_KIT_AVIEW_SOME',
    'H_LEAF_GLUE': 'lib/B/Prog/LeafCgClose.v H_LEAF_GLUE',
}


def main():
    log, sl = sys.argv[1], os.path.abspath(sys.argv[2])
    unit = os.path.dirname(os.path.dirname(os.path.dirname(sl)))
    close = os.path.join(unit, 'lib', 'B', 'UciBClose.v')
    L = open(log, errors='replace').read().split('\n')
    keep = [re.sub(r' dir=\S+', '', l) for l in L if l.startswith('cb-cache:') or l.startswith('cb: pin reac-repacer/')
            or l.startswith('cb: target') or l.startswith('cb: dune:') or re.match(r'^rc=\d+ wall=', l)]
    i0 = next(i for i, l in enumerate(L) if l.startswith('uci_B_TFIB_T_of_parts : '))
    i1 = next(i for i in range(i0, len(L)) if L[i].startswith('File "./proofs/'))
    os.makedirs(os.path.join(sl, 'records'), exist_ok=True)
    open(os.path.join(sl, 'records', 'build.txt'), 'w').write(
        'log: %s\n\n' % os.path.basename(log) + '\n'.join(keep) + '\n\n' + '\n'.join(L[i0:i1]) + '\n')
    C = open(close).read().split('\n')
    rows = []
    for r in ROWS:
        hits = [(i + 1, l) for i, l in enumerate(C) if re.match(r'^(Hypothesis|Lemma|Definition) %s\b' % r, l)]
        if len(hits) != 1:
            raise SystemExit('mk_record: row %s found %d times' % (r, len(hits)))
        n, l = hits[0]
        if l.startswith('Hypothesis'):
            rows.append('| %s | lib/B/UciBClose.v:%d | OPEN, Section hypothesis | waits for %s |' % (r, n, WAITS[r]))
        else:
            by = BY.get(r, 'lib/B/UciBFacts.v %s (computation at UciB)' % r)
            rows.append('| %s | lib/B/UciBClose.v:%d | DISCHARGED, %s | %s |' % (r, n, l.split()[0], by))
    out = ['# close-B: fuzz_uci image-B composition lib/B/UciBClose.v', '',
           'Written by scripts/mk_record.py; not edited by hand. Proves no function: lib/B/UciBClose.v proves',
           'Statements.asan_ubsan_agrees and Statements.asan_ubsan_halts (uci_asan_ubsan_agrees_of_parts,',
           'uci_asan_ubsan_halts_of_parts, through uci_B_TFIB_T_of_parts : UciBTFIB.TFIB_T) at the concrete record',
           'B := UciB (lib/B/YD2l.v:17), from the B core\'s closed walk lib/B/YD1q.v:173 tfib_srealizesX, whose slot',
           'lib/B/YCfn.v:140 is LIB_CONTRACT, proved from the 18 rows below and the CORE lemmas. Image A\'s twin is',
           'lib/A/UciClose.v (the same rows, names, order and composition).', '',
           '## The 18 rows (line numbers of the committed file)', '',
           '| row | where | status | by / waits for |', '|---|---|---|---|'] + rows + [
           '', '## Evidence of the CORE lemmas', '',
           'H_RT_MALLOC / H_RT_FREE: lib/B/UciBRtAlloc.v uciB_MALLOC / uciB_FREE, evidence provenance/evidence/uci-b-alloc',
           '(head 2c0a211766f5). H_RT_ASAN_MEMCPY: lib/B/YE2q.v asan_memcpy_realizes, evidence provenance/evidence/uci-b-memcpy',
           '(7af39d3f61cc). H_RT_STACK_MALLOC1: evidence provenance/evidence/stackmalloc1-B (head 135b5746fc67).',
           '', '## Build and Print Assumptions', '',
           'records/build.txt: the build log\'s mode, pin, target and rc lines and the About / Print Assumptions output',
           'of the tops, verbatim. The three tops rest on no Section hypothesis, only on PrimInt63.*, PrimString.*,',
           'PrimArray.array, functional_extensionality_dep and Classical_Prop.classic only.', '',
           '## Image measurements (run.sh)', '',
           'tables/dis-{A,B}.txt: RV64IM listings of the six program functions (pin words, twin names).',
           'tables/ubsan-traps-B.txt: every branch to UBSan\'s unimp in them; two need image-B premises (check_clamp',
           '0x7fa74 / 0x7fa78: pin mod 4 = 0; rp_hot_clamp 0x7fd40 and 0x7fd44 / 0x7fd48: a0 <> 0, a0 mod 4 = 0), the',
           'rest are refuted by the statements\' own premises (each statement header lists its traps).',
           'tables/s0-writes-{A,B}.txt: every write of s0 in the three functions whose call contexts the statements fix',
           '(B: LLVMFuzzerTestOneInput +0x34 `mv s0, a1` and the epilogue only, so CTX_check_no_overread = [[0x7f478]]).',
           'tables/cells-{A,B}.txt: the runtime cells, GOT words and REAL values of lib/{A,B}/AsanCells.v.', '',
           'The listing generator and its closure check are provenance/prog-gen/B (run.sh, closure.py, coqdep_closure.py).']
    open(os.path.join(sl, 'RECORD.md'), 'w').write('\n'.join(out) + '\n')


if __name__ == '__main__':
    main()
