# close-B: fuzz_uci image-B composition lib/B/UciBClose.v

Written by scripts/mk_record.py; not edited by hand. Proves no function: lib/B/UciBClose.v proves
Statements.asan_ubsan_agrees and Statements.asan_ubsan_halts (uci_asan_ubsan_agrees_of_parts,
uci_asan_ubsan_halts_of_parts, through uci_B_TFIB_T_of_parts : UciBTFIB.TFIB_T) at the concrete record
B := UciB (lib/B/YD2l.v:17), from the B core's closed walk lib/B/YD1q.v:173 tfib_srealizesX, whose slot
lib/B/YCfn.v:140 is LIB_CONTRACT, proved from the 18 rows below and the CORE lemmas. Image A's twin is
lib/A/UciClose.v (the same rows, names, order and composition).

## The 18 rows (line numbers of the committed file)

| row | where | status | by / waits for |
|---|---|---|---|
| H_PROG_LLVMF | lib/B/UciBClose.v:180 | DISCHARGED, Definition | lib/B/Prog/LLVMFuzzerTestOneInput_cgW.v uci_llvmf_holds (824090cba246) |
| H_PROG_CNO | lib/B/UciBClose.v:183 | DISCHARGED, Definition | lib/B/Prog/check_no_overread_cgW.v uci_check_no_overread_cg_holds (e61d8b88c3d0) |
| H_PROG_CV | lib/B/UciBClose.v:186 | DISCHARGED, Definition | lib/B/Prog/check_value_cgW.v uci_check_value_cg_holds (faf4885cf4dd) |
| H_PROG_CC | lib/B/UciBClose.v:188 | DISCHARGED, Definition | lib/B/Prog/check_clamp_cgW.v uci_check_clamp_cg_holds (e5e90545d4c8) |
| H_PROG_RUI | lib/B/UciBClose.v:190 | DISCHARGED, Definition | lib/B/Prog/rp_uci_int_cgW.v uci_rp_uci_int_holds (d3f024dc2e5) |
| H_PROG_RHC_F | lib/B/UciBClose.v:193 | DISCHARGED, Definition | lib/B/Prog/rp_hot_clamp_FW.v rp_hot_clamp_holds_F (783ed4e623d) |
| H_RT_STACK_MALLOC1 | lib/B/UciBClose.v:202 | DISCHARGED, Lemma | lib/B/Rt/YF0s.v:516 stack_malloc1_contract (evidence 135b5746fc67) |
| H_RT_MEMCHR | lib/B/UciBClose.v:208 | DISCHARGED, Lemma | lib/B/Rt/Memchr.v memchr_icpt_contract (43a6893892d7) |
| H_KIT_AVIEW_EXT | lib/B/UciBClose.v:214 | DISCHARGED, Lemma | lib/B/Prog/LeafCgClose.v H_KIT_AVIEW_EXT |
| H_KIT_AVIEW_SOME | lib/B/UciBClose.v:216 | DISCHARGED, Lemma | lib/B/Prog/LeafCgClose.v H_KIT_AVIEW_SOME |
| H_LEAF_GLUE | lib/B/UciBClose.v:218 | DISCHARGED, Lemma | lib/B/Prog/LeafCgClose.v H_LEAF_GLUE |
| HB_CELLS | lib/B/UciBClose.v:224 | DISCHARGED, Lemma | lib/B/UciBFacts.v HB_CELLS (computation at UciB) |
| HB_RO_RD_UNOWNED | lib/B/UciBClose.v:226 | DISCHARGED, Lemma | lib/B/UciBFacts.v HB_RO_RD_UNOWNED (computation at UciB) |
| HB_ROM_NO_ERRNO | lib/B/UciBClose.v:228 | DISCHARGED, Lemma | lib/B/UciBFacts.v HB_ROM_NO_ERRNO (computation at UciB) |
| HB_CNO_UCTX | lib/B/UciBClose.v:230 | DISCHARGED, Lemma | lib/B/UciBFacts.v HB_CNO_UCTX (computation at UciB) |
| HB_CNO_UFIX | lib/B/UciBClose.v:232 | DISCHARGED, Lemma | lib/B/UciBFacts.v HB_CNO_UFIX (computation at UciB) |
| HB_CV_UFIX | lib/B/UciBClose.v:234 | DISCHARGED, Lemma | lib/B/UciBFacts.v HB_CV_UFIX (computation at UciB) |
| HB_COST | lib/B/UciBClose.v:236 | DISCHARGED, Lemma | lib/B/UciBFacts.v HB_COST (computation at UciB) |

## Evidence of the CORE lemmas

H_RT_MALLOC / H_RT_FREE: lib/B/UciBRtAlloc.v uciB_MALLOC / uciB_FREE, evidence provenance/evidence/uci-b-alloc
(head 2c0a211766f5). H_RT_ASAN_MEMCPY: lib/B/YE2q.v asan_memcpy_realizes, evidence provenance/evidence/uci-b-memcpy
(7af39d3f61cc). H_RT_STACK_MALLOC1: evidence provenance/evidence/stackmalloc1-B (head 135b5746fc67).

## Build and Print Assumptions

records/build.txt: the build log's mode, pin, target and rc lines and the About / Print Assumptions output
of the tops, verbatim. The three tops rest on no Section hypothesis, only on PrimInt63.*, PrimString.*,
PrimArray.array, functional_extensionality_dep and Classical_Prop.classic only.

## Image measurements (run.sh)

tables/dis-{A,B}.txt: RV64IM listings of the six program functions (pin words, twin names).
tables/ubsan-traps-B.txt: every branch to UBSan's unimp in them; two need image-B premises (check_clamp
0x7fa74 / 0x7fa78: pin mod 4 = 0; rp_hot_clamp 0x7fd40 and 0x7fd44 / 0x7fd48: a0 <> 0, a0 mod 4 = 0), the
rest are refuted by the statements' own premises (each statement header lists its traps).
tables/s0-writes-{A,B}.txt: every write of s0 in the three functions whose call contexts the statements fix
(B: LLVMFuzzerTestOneInput +0x34 `mv s0, a1` and the epilogue only, so CTX_check_no_overread = [[0x7f478]]).
tables/cells-{A,B}.txt: the runtime cells, GOT words and REAL values of lib/{A,B}/AsanCells.v.

The listing generator and its closure check are provenance/prog-gen/B (run.sh, closure.py, coqdep_closure.py).
