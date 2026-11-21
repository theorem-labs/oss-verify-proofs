(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (52 recorded proofs replaced by written proofs (MOK_nonlazy, map_contains_true, map_has_true and 49 more); the munmap arm's destruct names aok's sixth conjunct (the range's subtraction); KI_acct_ok bounds the page count without rewriting the limit, which MOK now only bounds below (zstd_frame_info's proof)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import AcctCore ExecF ITreeA ModelX MmXfer NodesA.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import BackingAlgebra.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanCtrlProps AsanEmbed AsanInv AsanTotalCore AsanNodeSem AsanTotal.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import AProto ATsafeCore ATsafeEv.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ATsafeAlloc () := "C47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsI59OSSVerify5KrLib3Lib5ITree5itree00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufc59OSSVerify5KrLib5BothW;ATsafeAlloc3MOKC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00C4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedK47Corelib4Init9Datatypes4list01I47Corelib4Init5Logic2eq00C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State8vm_limitC56Stdlib6ZArith6BinInt1Z2leC59OSSVerify5KrLib2AS>BackingAlgebra<model_ivs_wfC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State7vm_mapsI59OSSVerify5KrLib4Spec7AsanInv4seps00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7AsanInv8entry_okC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topI47Corelib4Init5Logic3and00C59OSSVerify5KrLib4LibA8AcctCore=nonlazy_bytesC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State?vm_backing_usedC59OSSVerify5KrLib4LibA6MmXferEvm_backing_used_canonC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symI4ELinuxProcessSemantics?LinuxProcessSem5State5Model00K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib4Spec7AsanInv7LIMIT34C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00C46Stdlib5Lists4List2InC4ELinuxProcessSemantics?LinuxProcessSem5State<map_containsC46Stdlib5Lists4List7existsbI47Corelib4Init5Logic2ex00C46Stdlib5Lists4List>existsb_existsC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes4andbC59OSSVerify5KrLib2AS>BackingAlgebra1BC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib2AS>BackingAlgebra1SC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool=andb_true_iffC56Stdlib6ZArith6BinInt1Z6leb_leK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C4ELinuxProcessSemantics?LinuxProcessSem5State7map_hasC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbK47Corelib4Init9Datatypes4prod01C4ELinuxProcessSemantics?LinuxProcessSem2Fs9bv_eqb_eqC59OSSVerify5KrLib2AS>BackingAlgebra5iv_wfC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State;iv_subtractC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z2ltC47Corelib4Init9Datatypes3appI47Corelib4Init5Logic2or00C46Stdlib5Lists4List:in_app_iffC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z3maxC45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith6BinInt1Z3powK47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith6BinInt1Z8min_specC56Stdlib6ZArith6BinInt1Z3minK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr04K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z8max_specK47Corelib4Init9Datatypes4list02C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1N00K46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203C46Stdlib5Lists4List8nil_consC46Stdlib9micromega8ZifyInst7Inj_Z_ZK47Corelib4Init9Datatypes3nat01I47Corelib4Init5Logic5False00C59OSSVerify5KrLib2AS>BackingAlgebra6ivs_wfC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State=maps_subtractC59OSSVerify5KrLib2AS>BackingAlgebra?ivs_wf_cons_invC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01c59OSSVerify5KrLib5BothW;ATsafeAlloc>in_iv_subtractC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02C47Corelib4Init9Datatypes8list_indC4ELinuxProcessSemantics?LinuxProcessSem5State>page_in_rangesc59OSSVerify5KrLib5BothW;ATsafeAlloc@in_maps_subtractC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizeC56Stdlib6ZArith6BinInt1Z6moduloC4ELinuxProcessSemantics?LinuxProcessSem5State=lazy_interiorC59OSSVerify5KrLib2AS>BackingAlgebraElazy_interior_alignedC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3orbC46Stdlib4Bool4Bool;orb_false_rK47Corelib4Init9Datatypes4bool02C4ELinuxProcessSemantics?LinuxProcessSem5State;vm_reservedC59OSSVerify5KrLib4Spec7AsanInv;grant_modelC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State;vm_noaccessC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC59OSSVerify5KrLib2AS8AsanCeil:init_sp_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State<vm_start_brkC4ELinuxProcessSemantics?LinuxProcessSem5State6vm_brkC4ELinuxProcessSemantics?LinuxProcessSem5State<vm_mmap_baseC4ELinuxProcessSemantics?LinuxProcessSem5State:vm_init_spK4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps01C4ELinuxProcessSemantics?LinuxProcessSem5State;with_vmmapsC59OSSVerify5KrLib2AS>BackingAlgebra;iv_wf_introC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>BackingAlgebra;ivs_wf_consC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>BackingAlgebraEm_vm_lazy_with_vmmapsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>BackingAlgebraDm_vmmaps_with_vmmapsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State;region_freeC59OSSVerify5KrLib4Spec7AsanInv?region_free_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7AsanInv4wsepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7AsanInv@region_free_wsepC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec7AsanInv4seps02C1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02C59OSSVerify5KrLib2AS>BackingAlgebraMm_vm_materialized_with_vmmapsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>BackingAlgebra9sum_countC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib2AS>BackingAlgebra8iv_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7AsanInv=iv_count_le_SC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib4Spec7AsanInv>sum_count_consC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>BackingAlgebraCvm_backing_used_semC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>BackingAlgebra7coveredC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbI4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00c59OSSVerify5KrLib5BothW;ATsafeAllocAmap_contains_trueC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapBmmap_fixed_rw_nextC4ELinuxProcessSemantics?LinuxProcessSem5State?vm_forget_rangeC59OSSVerify5KrLib2AS>BackingAlgebra@maps_subtract_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>BackingAlgebraIm_vm_lazy_vm_forget_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>BackingAlgebraHm_vmmaps_vm_forget_rangeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateBpage_outside_rangeC46Stdlib5Lists4List6filterC59OSSVerify5KrLib2AS>BackingAlgebraQm_vm_materialized_vm_forget_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>BackingAlgebra;overlap_sumC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>BackingAlgebraHbacking_forget_commit_leC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7AsanInvEoverlap_sum_containedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8le_transC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_add_lazyC59OSSVerify5KrLib4Spec7AsanInv;fixed_modelC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7F_FIXEDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>BackingAlgebraEm_vm_lazy_vm_add_lazyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>BackingAlgebraDm_vmmaps_vm_add_lazyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>BackingAlgebraMm_vm_materialized_vm_add_lazyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>BackingAlgebraHbacking_recommit_lazy_leC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl:F_FIXNORESC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7AsanInv;seps_filterC1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms5flip2C59OSSVerify5KrLib4Spec7AsanInv<munmap_modelC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;ATsafeAlloc<map_has_trueC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8in_splitI46Stdlib7Sorting;Permutation;Permutation00C46Stdlib7Sorting;PermutationBPermutation_middleC46Stdlib7Sorting;Permutation?Permutation_symC46Stdlib5Lists4List;Forall_implC46Stdlib7Sorting;PermutationBPermutation_ForallC46Stdlib5Lists4List?Forall_cons_iffC59OSSVerify5KrLib4Spec7AsanInv?map_remove_permC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State:map_removeC59OSSVerify5KrLib4Spec7AsanInv9seps_permC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7AsanInv=seps_cons_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>BackingAlgebra=ivs_wf_filterC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;ATsafeAlloc<seps_filter'C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffC47Corelib7Program6Basics4implC46Stdlib5Lists4List=Forall_forallC47Corelib7Classes9MorphismsDiff_impl_subrelationC59OSSVerify5KrLib4LibA6MmXfer;incl_filterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>BackingAlgebraAmaps_subtract_semC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>BackingAlgebra6in_rngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>BackingAlgebra@sum_count_nonnegC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C46Stdlib4Bool4Bool>andb_false_iffC56Stdlib6ZArith6BinInt1Z6ltb_geC56Stdlib6ZArith6BinInt1Z6leb_gtC59OSSVerify5KrLib2AS>BackingAlgebra;covered_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7AsanInv@sum_count_ext_onC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7AsanInv>sum_count_permC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List6Exists00C47Corelib7Classes9MorphismsIiff_flip_impl_subrelationC56Stdlib6ZArith6BinInt1Z6to_natC59OSSVerify5KrLib2AS>BackingAlgebra=zcount_nonnegC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>BackingAlgebra6zcountC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8leb_specC59OSSVerify5KrLib2AS>BackingAlgebra:zcount_extC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC59OSSVerify5KrLib2AS>BackingAlgebra@zcount_and_splitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>BackingAlgebra?overlap_sum_nilC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;ATsafeAllocBiv_count_rng_splitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>BackingAlgebra@overlap_sum_consC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;ATsafeAlloc?iv_count_nonnegC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>BackingAlgebraBiv_count_in_rng_leC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>BackingAlgebra7B_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>BackingAlgebra7S_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00c59OSSVerify5KrLib5BothW;ATsafeAllocBoverlap_sum_nonnegC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC59OSSVerify5KrLib2AS>BackingAlgebra>sum_count_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>BackingAlgebraBzcount_const_falseC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega5Tauto8GFormula07C59OSSVerify5KrLib2AS>BackingAlgebraHiv_count_in_rng_disjointC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;ATsafeAllocCiv_count_in_rng_le0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;ATsafeAllocAoverlap_sum_splitC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes:comparison00C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap@mmap_noreserve_bc59OSSVerify5KrLib5BothW;ATsafeAlloc@overlap_sum_sepsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>BackingAlgebra@filter_length_leC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C59OSSVerify5KrLib2AS>BackingAlgebra=zcount_le_lenC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Z2Nat2idK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C59OSSVerify5KrLib2AS>BackingAlgebraHvm_backing_used_sem_mapsC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib6ZArith6BinInt1Z6ltb_ltC46Stdlib4Bool4Bool:orb_true_rC59OSSVerify5KrLib2AS>BackingAlgebra5in_ivC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>BackingAlgebra<zcount_falseC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof03C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC59OSSVerify5KrLib4LibA6NodesADmmap_fixed_span_replC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapGmmap_fixed_rw_span_nextc59OSSVerify5KrLib5BothW;ATsafeAllocFbacking_forget_span_leC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;ATsafeAllocMbacking_recommit_span_lazy_leC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA6alw_leC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF5fp_okC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC59OSSVerify5KrLib4LibA8AcctCore7page_okC1?~~~~~~~~~~~~~~~C57Corelib7BinNums6IntDef1Z6of_natC57Corelib7BinNums6IntDef1Z3addC4ELinuxProcessSemantics?LinuxProcessSem5State<page_base_ofC59OSSVerify5KrLib4LibA6ITreeA5fp_leC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC59OSSVerify5KrLib4LibA6ITreeA3alwC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List;existsb_appC56Stdlib6ZArith6BinInt1Z7div_posC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegc59OSSVerify5KrLib5BothW;ATsafeAlloc5pcostC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed:aembed_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed:aembed_visC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed4shadC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;ATsafeAlloc2GAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;ATsafeAlloc2KIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:ATsafeCore4abudC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List5NoDup00C59OSSVerify5KrLib4LibA5ExecF<footprint_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecFBfootprint_ok_fp_okC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib4LibA6ITreeA7acct_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7AsanInv9RESERVE34C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib4Spec9AsanEmbed9adec_mmapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode8errno_ofC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib6Decode8mmap_ans01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode8mmap_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode<mmap_addr_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State7eff_retC47Corelib4Init5Logic7f_equalK47Corelib4Init9Datatypes6option01K59OSSVerify5KrLib3Lib6Decode8mmap_ans02C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect01I59OSSVerify5KrLib3Lib6Decode8mmap_ans00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4respC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7PROT_RWC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect00I4ELinuxProcessSemantics?LinuxProcessSem5State7MemCopy00C59OSSVerify5KrLib4Spec9AsanTotal;mmap_len_idC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State?page_round_up_ZC59OSSVerify5KrLib4Spec;AsanNodeSem;mmap_len_eqC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C59OSSVerify5KrLib4Spec9AsanEmbed5shlenC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;div_le_monoc59OSSVerify5KrLib5BothW;ATsafeAlloc9shad_div8C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundc59OSSVerify5KrLib5BothW;ATsafeAlloc:shlen_div8C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z=add_le_mono_lC59OSSVerify5KrLib4Spec9AsanEmbed6ASHOFFC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses=eq_TransitiveC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC56Stdlib6ZArith6BinInt1Z7add_0_rC57Corelib7BinNums6PosDef3Pos3addC56Stdlib6ZArith6BinInt1Z7pos_subC46Stdlib;setoid_ring>Algebra_syntax8equalityC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC56Stdlib6ZArith6BinInt1Z9div_add_lC56Stdlib6ZArith6BinInt1Z8mul_commC46Stdlib;setoid_ring6Ncring;eq_notationC46Stdlib;setoid_ring6Ncring>ring_plus_compC56Stdlib6ZArith6BinInt1Z3oppC46Stdlib;setoid_ring>Ncring_initial4ZopsC46Stdlib;setoid_ring>Ncring_initial2ZrC59OSSVerify5KrLib4LibA6MmXfer6robustC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6NodesA6nsafeAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;ATsafeAlloc;MOK_nonlazyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6NodesA7nsafeA0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6NodesA6nslackC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes=nsafe_mmap_rwC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node0:C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes5nsafeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6NodesA<mmap_safeA_bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6NodesA?mmap_fixed_replC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;ATsafeAlloc;robust_roomC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;ATsafeAllocEnonlazy_fixed_repl_leC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;ATsafeAllocJnonlazy_fixed_span_repl_leC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;ATsafeAlloc<mmap_len_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6F_ANONC1?~~~~~~~~~~~~~~~C5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi9PROT_READC5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi:PROT_WRITEC5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi;MAP_PRIVATEC5ELinuxProcessSemantics?LinuxProcessSem3Sys4Uapi=MAP_ANONYMOUSC59OSSVerify5KrLib4LibA6NodesAEnsafeA0_mmap_fixed_rwC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap?mmap_fixed_rw_bC5ELinuxProcessSemantics?LinuxProcessSem3Sys7Syscall5w_is0C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7eqb_neqC59OSSVerify5KrLib3Lib5Nodes9w_is0_litC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;ATsafeAlloc<MOK_recommitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;ATsafeAllocOnonlazy_fixed_span_repl_lazy_leC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;ATsafeAlloc<NSAFEA_FIXEDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec;AsanNodeSem?mmap_len_boundsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node0;C1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap>munmap_free_okC59OSSVerify5KrLib3Lib5Nodes=munmap_safe_bC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9TASK_SIZEC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm7MadviseCmadvise_dontneed_okK59OSSVerify5KrLib3Lib5Nodes4node0=C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes>madvise_safe_bC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State:two_pow_64C45stdpp9bitvector;definitions7bv_wrapC46Stdlib6ZArith4Zdiv:Z_mod_multC56Stdlib6ZArith4Zdiv1Z>mod_mod_divideC45stdpp9bitvector;definitions@Z_to_bv_unsignedC59OSSVerify5KrLib3Lib6MStateCZ_to_bv_bv_unsignedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;ATsafeAllocDpage_base_of_alignedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;ATsafeAllocApage_base_of_selfC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;ATsafeAllocEpage_in_maps_subtractC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecFBpage_base_of_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:ATsafeCore;range_pagesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:ATsafeCore6aunionC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;ATsafeAlloc9MOK_grantC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;ATsafeAlloc=adec_mmap_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:ATsafeCore9aunion_leC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;ATsafeAlloc9shad_plusC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;ATsafeAlloc;shad_boundsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;ATsafeAlloc<shlen_boundsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6NodesA6fstepAC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC59OSSVerify5KrLib4LibA5ExecF3rngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AProto5fp_bwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA:fp_ok_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:ATsafeCore@range_pages_specC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:ATsafeCore?rng_fp_ok_unionC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AProto8fp_ok_bwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA<alw_le_transC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:ATsafeCore9aunion_inC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;ATsafeAlloc5GA_leC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:ATsafeCore:abud_unionC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC59OSSVerify5KrLib5BothW:ATsafeCoreBrange_pages_lengthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:ATsafeCore:pages_fromC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:ATsafeCoreApages_from_lengthC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_divC56Stdlib6ZArith4Znat5Nat2Z7inj_addC46Stdlib5Lists4List:length_appC59OSSVerify5KrLib5BothW:ATsafeCore9abud_monoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;ATsafeAlloc<pcost_nonnegC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AProto6fstepSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AProto=MAP_NORESERVEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7AsanInv3inWC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;ATsafeAlloc:MOK_commitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;ATsafeAlloc5shad8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA;alw_le_reflC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;ATsafeAllocCpage_notin_subtractC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF9rng_fp_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;ATsafeAlloc<shad_le_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl8K_REGIONC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7AsanInv4UWINC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_OFFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7AsanInv4FWINC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl@K_PTRARR_RESERVEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW8ATsafeEv4covGC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;ATsafeAllocBpage_in_ranges_appC1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool<orb_true_iffc59OSSVerify5KrLib5BothW;ATsafeAllocEpage_in_lazy_interiorC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;ATsafeAllocApage_base_of_pageC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;ATsafeAlloc;fp_ok_mono3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;ATsafeAlloc:MOK_munmapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:ATsafeCore5postTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:ATsafeCore2TSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:ATsafeCore=TS_unfold_visC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5ebindC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6NodesA6nstepAC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib3Lib5ITree3Exc3exc02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5enodeC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib3Lib5ITree3Exc3exc01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4bindC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF9footprintC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00c59OSSVerify5KrLib5BothW;ATsafeAlloc8TS_eventC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;ATsafeAlloc5gcostC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW;ATsafeAlloc5KPOSTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:ATsafeCore2EQC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List4inclC46Stdlib5Lists4List9incl_tran".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
Definition MOK (mo : Model) : Prop :=
  m_vm_materialized mo = []
  /\ LIMIT34 <= vm_limit (m_vmmaps mo)          (* [comment removed for export] *)
  /\ model_ivs_wf mo
  /\ seps (vm_maps (m_vmmaps mo))
  /\ Forall (entry_ok ATOP) (vm_maps (m_vmmaps mo))
  /\ alloc_top (m_vmmaps mo) = ATOP.      (* [comment removed for export] *)

Lemma MOK_nonlazy : forall mo, MOK mo -> nonlazy_bytes mo = vm_backing_used mo.
Proof. intros mo (M1 & _). symmetry. apply vm_backing_used_canon. exact M1. Qed.

(* [comment removed for export] *)
Lemma map_contains_true : forall l (a n : word),
  map_contains l a n = true -> exists e, In e l /\ B e <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= B e + S e.
Proof.
  intros l a n H. unfold map_contains in H. apply existsb_exists in H as (e & Hin & He).
  apply andb_true_iff in He as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  exists e. unfold B, S. auto.
Qed.

Lemma map_has_true : forall l (a n : word), map_has l a n = true -> In (a, n) l.
Proof.
  intros l a n H. unfold map_has in H. apply existsb_exists in H as ([b s] & Hin & He). cbn in He.
  apply andb_true_iff in He as [H1 H2]. apply bv_eqb_eq in H1. apply bv_eqb_eq in H2. subst. exact Hin.
Qed.

(* [comment removed for export] *)
Lemma in_iv_subtract : forall a sz lo hi q,
  iv_wf (a, sz) -> lo <= hi -> In q (iv_subtract a sz lo hi) ->
  B (a, sz) <= B q /\ B q + S q <= B (a, sz) + S (a, sz) /\ (B q + S q <= lo \/ hi <= B q).
Proof.
  intros a sz lo hi q Hwf Hlh Hin. unfold iv_wf, B, S in *. cbn [fst snd] in *.
  pose proof (bv_unsigned_in_range 64 a) as Ha. pose proof (bv_unsigned_in_range 64 sz) as Hs. unfold bv_modulus in Ha, Hs.
  unfold iv_subtract in Hin. cbv zeta in Hin. apply in_app_iff in Hin as [Hin|Hin].
  - destruct (Z.ltb_spec (bv_unsigned a) lo); [|destruct Hin]. destruct Hin as [<-|[]]. cbn [fst snd].
    rewrite unsigned_lit by lia. lia.
  - destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); [|destruct Hin]. destruct Hin as [<-|[]]. cbn [fst snd].
    rewrite !unsigned_lit by lia. lia.
Qed.

Lemma in_maps_subtract : forall l lo hi q,
  ivs_wf l -> lo <= hi -> In q (maps_subtract l lo hi) ->
  exists e, In e l /\ B e <= B q /\ B q + S q <= B e + S e /\ (B q + S q <= lo \/ hi <= B q).
Proof.
  induction l as [|[a sz] l IH]; intros lo hi q Hwf Hlh Hin; [destruct Hin|].
  apply ivs_wf_cons_inv in Hwf as [Ha Hl]. cbn [maps_subtract] in Hin. apply in_app_iff in Hin as [Hin|Hin].
  - exists (a, sz). split; [left; reflexivity|]. apply in_iv_subtract; assumption.
  - destruct (IH lo hi q Hl Hlh Hin) as (e & He & H). exists e. split; [right; exact He| exact H].
Qed.

(* [comment removed for export] *)
Lemma page_in_maps_subtract : forall l lo hi p,
  ivs_wf l -> lo <= hi ->
  page_in_ranges p (maps_subtract l lo hi) = true ->
  page_in_ranges p l = true /\ (bv_unsigned p + page_size <= lo \/ hi <= bv_unsigned p).
Proof.
  intros l lo hi p Hwf Hlh H.
  unfold page_in_ranges in *. apply existsb_exists in H as (q & Hin & Hp). cbv zeta in Hp.
  apply andb_true_iff in Hp as [P1 P2]. apply Z.leb_le in P1. apply Z.leb_le in P2.
  destruct (in_maps_subtract l lo hi q Hwf Hlh Hin) as (e & He & E1 & E2 & E3). unfold B, S in *.
  pose proof (bv_unsigned_in_range 64 p). assert (PS : 0 < page_size) by (unfold page_size; lia).
  split; [| lia].
  apply existsb_exists. exists e. split; [exact He|]. cbv zeta. apply andb_true_iff. split; apply Z.leb_le; lia.
Qed.

(* [comment removed for export] *)
Lemma page_in_lazy_interior : forall (a n p : word),
  bv_unsigned a mod page_size = 0 -> bv_unsigned n mod page_size = 0 -> 0 < bv_unsigned n -> bv_unsigned a + bv_unsigned n <= 2^64 ->
  page_in_ranges p (lazy_interior a n) = true ->
  bv_unsigned a <= bv_unsigned p /\ bv_unsigned p + page_size <= bv_unsigned a + bv_unsigned n.
Proof.
  intros a n p Hal Hnl Hn Hhi H. rewrite (lazy_interior_aligned a n Hal Hnl Hn Hhi) in H.
  unfold page_in_ranges in H. cbn [existsb fst snd] in H. rewrite Bool.orb_false_r in H.
  apply andb_true_iff in H as [P1 P2]. apply Z.leb_le in P1. apply Z.leb_le in P2. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma MOK_grant : forall mo z nZ,
  MOK mo -> z mod 4096 = 0 -> 0 < z -> z + nZ <= ATOP -> nZ mod 4096 = 0 -> 0 < nZ ->
  region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (Z_to_bv 64 z) (Z_to_bv 64 nZ) = true ->
  MOK (grant_model mo z nZ)
  /\ nonlazy_bytes (grant_model mo z nZ) <= nonlazy_bytes mo + nZ
  /\ m_vm_lazy (grant_model mo z nZ) = m_vm_lazy mo
  /\ vm_maps (m_vmmaps (grant_model mo z nZ)) = (Z_to_bv 64 z, Z_to_bv 64 nZ) :: vm_maps (m_vmmaps mo)
  /\ vm_limit (m_vmmaps (grant_model mo z nZ)) = vm_limit (m_vmmaps mo).
Proof.
  intros mo z nZ (M1 & M2 & M3 & M4 & M5 & M6) Hal Hz Hce Hnl Hn Hrf.
  atop_facts. pose proof M3 as (Wm & Wn & Wl & Wsp).
  assert (WF' : model_ivs_wf (grant_model mo z nZ)).
  { unfold model_ivs_wf, grant_model. model_proj. cbn [vm_maps vm_noaccess]. split; [| split; [exact Wn| split; [exact Wl| exact Wsp]]].
    apply ivs_wf_cons; [| exact Wm]. apply iv_wf_intro. cbn [fst snd]. rewrite !unsigned_lit by lia. lia. }
  assert (MOK' : MOK (grant_model mo z nZ)).
  { unfold MOK, grant_model. model_proj. cbn [vm_maps vm_limit]. split; [exact M1|]. split; [exact M2|]. split; [exact WF'|]. split; [| split; [| exact M6]].
    - constructor; [| exact M4]. rewrite region_free_app in Hrf. apply andb_true_iff in Hrf as [_ Hrf]. apply region_free_wsep. exact Hrf.
    - constructor; [| exact M5]. unfold entry_ok. cbn [fst snd]. rewrite !unsigned_lit by lia. atop_facts. repeat split; lia. }
  split; [exact MOK'|]. split; [| split; [reflexivity| split; reflexivity]].
  rewrite <- (vm_backing_used_canon _ M1). rewrite <- (vm_backing_used_canon (grant_model mo z nZ)) by (unfold grant_model; model_proj; exact M1).
  rewrite (vm_backing_used_sem _ WF'), (vm_backing_used_sem _ M3). unfold grant_model. model_proj. cbn [vm_maps vm_noaccess].
  rewrite sum_count_cons. pose proof (iv_count_le_S (fun x => negb (covered (vm_noaccess (m_vmmaps mo) ++ m_vm_lazy mo) x)) (Z_to_bv 64 z, Z_to_bv 64 nZ)) as IC.
  unfold S in IC. cbn [snd] in IC. rewrite unsigned_lit in IC by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma MOK_commit : forall mo a n,
  MOK mo -> 0 <= a -> 0 < n -> a + n < 2^64 ->
  map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 a) (Z_to_bv 64 n) = true ->
  MOK (fixed_model mo F_FIXED a n)
  /\ nonlazy_bytes (fixed_model mo F_FIXED a n) <= nonlazy_bytes mo + n
  /\ m_vm_lazy (fixed_model mo F_FIXED a n) = maps_subtract (m_vm_lazy mo) a (a + n)
  /\ vm_maps (m_vmmaps (fixed_model mo F_FIXED a n)) = vm_maps (m_vmmaps mo)
  /\ vm_limit (m_vmmaps (fixed_model mo F_FIXED a n)) = vm_limit (m_vmmaps mo).
Proof.
  intros mo a n (M1 & M2 & M3 & M4 & M5 & M6) Ha Hn Hhi Hmc. pose proof M3 as (Wm & Wn & Wl & Wsp).
  assert (Ua : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit; lia).
  assert (Un : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  destruct (map_contains_true _ _ _ Hmc) as (E & HinE & HE1 & HE2). rewrite ?Ua, ?Un in HE1. rewrite ?Ua, ?Un in HE2.
  unfold fixed_model, with_mmap_replacement, with_mmap_backing. change (mmap_noreserve_b (Z_to_bv 64 F_FIXED)) with false. cbv iota.
  rewrite !Ua, !Un.
  assert (WF' : model_ivs_wf (vm_forget_range a (a + n) (with_vmmaps (mmap_fixed_rw_next (m_vmmaps mo) (Z_to_bv 64 a) (Z_to_bv 64 n)) mo))).
  { unfold model_ivs_wf, mmap_fixed_rw_next. model_proj. cbn [vm_maps vm_noaccess]. rewrite ?Ua, ?Un.
    split; [exact Wm|]. split; [|split]; [apply maps_subtract_wf; [assumption| lia] | apply maps_subtract_wf; [assumption| lia] | exact Wsp]. }
  split; [| split; [| split; [| split]]].
  - unfold MOK, mmap_fixed_rw_next. model_proj. cbn [vm_maps vm_limit]. rewrite M1. cbn [List.filter].
    split; [reflexivity|]. split; [exact M2|]. split; [exact WF'|]. split; [exact M4| split; [exact M5| exact M6]].
  - rewrite <- (vm_backing_used_canon _ M1).
    rewrite <- vm_backing_used_canon by (model_proj; rewrite M1; reflexivity).
    eapply Z.le_trans. { apply backing_forget_commit_le; [exact M3| lia| reflexivity|]. unfold mmap_fixed_rw_next. cbn [vm_noaccess]. rewrite ?Ua, ?Un. reflexivity. }
    pose proof (overlap_sum_contained (vm_maps (m_vmmaps mo)) E a (a + n) M4 HinE HE1 HE2 ltac:(lia)). lia.
  - model_proj. reflexivity.
  - model_proj. reflexivity.
  - model_proj. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma MOK_recommit : forall mo a n,
  MOK mo -> 0 <= a -> 0 < n -> a + n < 2^64 -> a mod 4096 = 0 -> n mod 4096 = 0 ->
  map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 a) (Z_to_bv 64 n) = true ->
  MOK (fixed_model mo F_FIXNORES a n)
  /\ nonlazy_bytes (fixed_model mo F_FIXNORES a n) <= nonlazy_bytes mo
  /\ m_vm_lazy (fixed_model mo F_FIXNORES a n) = lazy_interior (Z_to_bv 64 a) (Z_to_bv 64 n) ++ maps_subtract (m_vm_lazy mo) a (a + n)
  /\ vm_maps (m_vmmaps (fixed_model mo F_FIXNORES a n)) = vm_maps (m_vmmaps mo)
  /\ vm_limit (m_vmmaps (fixed_model mo F_FIXNORES a n)) = vm_limit (m_vmmaps mo).
Proof.
  intros mo a n (M1 & M2 & M3 & M4 & M5 & M6) Ha Hn Hhi Hal Hnl Hmc. pose proof M3 as (Wm & Wn & Wl & Wsp).
  assert (Ua : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit; lia).
  assert (Un : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  unfold fixed_model, with_mmap_replacement, with_mmap_backing. change (mmap_noreserve_b (Z_to_bv 64 F_FIXNORES)) with true. cbv iota.
  rewrite !Ua, !Un.
  pose proof (lazy_interior_aligned (Z_to_bv 64 a) (Z_to_bv 64 n)) as HLI. rewrite !Ua, !Un in HLI.
  specialize (HLI ltac:(unfold page_size; lia) ltac:(unfold page_size; lia) Hn ltac:(lia)).
  assert (WF' : model_ivs_wf (vm_add_lazy (Z_to_bv 64 a) (Z_to_bv 64 n) (vm_forget_range a (a + n) (with_vmmaps (mmap_fixed_rw_next (m_vmmaps mo) (Z_to_bv 64 a) (Z_to_bv 64 n)) mo)))).
  { unfold model_ivs_wf, mmap_fixed_rw_next. model_proj. cbn [vm_maps vm_noaccess]. rewrite ?Ua, ?Un. rewrite HLI.
    split; [exact Wm|]. split; [apply maps_subtract_wf; [assumption| lia]|]. split; [| exact Wsp].
    apply ivs_wf_cons; [apply iv_wf_intro; rewrite Ua, Un; lia| apply maps_subtract_wf; [assumption| lia]]. }
  split; [| split; [| split; [| split]]].
  - unfold MOK, mmap_fixed_rw_next. model_proj. cbn [vm_maps vm_limit]. rewrite M1. cbn [List.filter].
    split; [reflexivity|]. split; [exact M2|]. split; [exact WF'|]. split; [exact M4| split; [exact M5| exact M6]].
  - rewrite <- (vm_backing_used_canon _ M1).
    rewrite <- vm_backing_used_canon by (model_proj; rewrite M1; reflexivity).
    pose proof (backing_recommit_lazy_le mo (mmap_fixed_rw_next (m_vmmaps mo) (Z_to_bv 64 a) (Z_to_bv 64 n)) (Z_to_bv 64 a) (Z_to_bv 64 n)) as BR.
    rewrite !Ua, !Un in BR. apply BR; auto; try (unfold page_size; lia); try lia.
    unfold mmap_fixed_rw_next. cbn [vm_noaccess]. rewrite ?Ua, ?Un. reflexivity.
  - model_proj. reflexivity.
  - model_proj. reflexivity.
  - model_proj. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma seps_filter' : forall f l, seps l -> seps (List.filter f l).
Proof. intros. apply seps_filter. assumption. Qed.

Lemma MOK_munmap : forall mo a n,
  MOK mo -> 0 <= a -> 0 < n -> a + n < 2^64 ->
  map_has (vm_maps (m_vmmaps mo)) (Z_to_bv 64 a) (Z_to_bv 64 n) = true ->
  MOK (munmap_model mo a n)
  /\ nonlazy_bytes (munmap_model mo a n) <= nonlazy_bytes mo
  /\ m_vm_lazy (munmap_model mo a n) = maps_subtract (m_vm_lazy mo) a (a + n)
  /\ (forall e, In e (vm_maps (m_vmmaps (munmap_model mo a n))) -> In e (vm_maps (m_vmmaps mo)))
  /\ vm_limit (m_vmmaps (munmap_model mo a n)) = vm_limit (m_vmmaps mo).
Proof.
  intros mo a n (M1 & M2 & M3 & M4 & M5 & M6) Ha Hn Hhi Hmh. pose proof M3 as (Wm & Wn & Wl & Wsp).
  assert (Ua : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit; lia).
  assert (Un : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  apply map_has_true in Hmh.
  (* [comment removed for export] *)
  destruct (in_split _ _ Hmh) as (l1 & l2 & EL).
  assert (HP : Permutation (vm_maps (m_vmmaps mo)) ((Z_to_bv 64 a, Z_to_bv 64 n) :: (l1 ++ l2))).
  { rewrite EL. apply Permutation_sym. apply Permutation_middle. }
  assert (HF2 : Forall (fun e : word * word => 0 < bv_unsigned (snd e)) (l1 ++ l2)).
  { assert (HF : Forall (fun e : word * word => 0 < bv_unsigned (snd e)) (vm_maps (m_vmmaps mo))).
    { eapply Forall_impl; [|exact M5]. intros e (He & _). exact He. }
    pose proof (Permutation_Forall HP HF) as X. apply Forall_cons_iff in X as [_ X]. exact X. }
  pose proof (map_remove_perm _ _ _ _ HP M4 ltac:(rewrite Un; lia) HF2) as HR.
  pose proof (seps_perm _ _ HP M4) as Hs2. apply seps_cons_inv in Hs2 as [Hfar Hs12].
  unfold munmap_model, with_mmap_destroyed. rewrite !Ua, !Un.
  set (h' := mkVmMapsFull _ _ _ _ _ _ _ _).
  assert (WF' : model_ivs_wf (vm_forget_range a (a + n) (with_vmmaps h' mo))).
  { unfold model_ivs_wf, h'. model_proj. cbn [vm_maps vm_noaccess].
    split; [unfold map_remove; apply ivs_wf_filter; exact Wm|]. split; [|split]; [apply maps_subtract_wf; [assumption| lia] | apply maps_subtract_wf; [assumption| lia] | exact Wsp]. }
  split; [| split; [| split; [| split]]].
  - unfold MOK, h'. model_proj. cbn [vm_maps vm_limit]. rewrite M1. cbn [List.filter].
    split; [reflexivity|]. split; [exact M2|]. split; [exact WF'|]. split; [| split; [| exact M6]].
    + unfold map_remove. apply seps_filter'. exact M4.
    + unfold map_remove. rewrite Forall_forall in *. intros e He. apply M5. apply (incl_filter _ _ _ He).
  - rewrite <- (vm_backing_used_canon _ M1).
    rewrite <- vm_backing_used_canon by (model_proj; rewrite M1; reflexivity).
    rewrite (vm_backing_used_sem _ WF'), (vm_backing_used_sem _ M3). unfold h'. model_proj. cbn [vm_maps vm_noaccess]. rewrite M1. cbn [List.filter length Z.of_nat Z.mul].
    destruct (maps_subtract_sem _ a (a + n) Wn ltac:(lia)) as (_ & _ & Cn).
    destruct (maps_subtract_sem _ a (a + n) Wl ltac:(lia)) as (_ & _ & Cl).
    rewrite (sum_count_perm _ _ _ HR). rewrite (sum_count_perm _ _ _ HP). rewrite sum_count_cons.
    pose proof (sum_count_nonneg (fun x => negb (covered (vm_noaccess (m_vmmaps mo) ++ m_vm_lazy mo) x)) [(Z_to_bv 64 a, Z_to_bv 64 n)]) as NN.
    rewrite sum_count_cons in NN. cbn [sum_count] in NN.
    rewrite (sum_count_ext_on _ (fun x => negb (covered (vm_noaccess (m_vmmaps mo) ++ m_vm_lazy mo) x)) (l1 ++ l2)); [lia|].
    intros e x He Hx. rewrite !covered_app, Cn, Cl.
    pose proof (proj1 (Forall_forall _ _) Hfar e He) as Hw. unfold wsep, B, S in Hw. cbn [fst snd] in Hw. rewrite Ua, Un in Hw.
    replace (in_rng a (a + n) x) with false.
    2:{ symmetry. unfold in_rng. apply andb_false_iff. unfold B, S in Hx. destruct Hw; [right; apply Z.ltb_ge| left; apply Z.leb_gt]; lia. }
    destruct (covered (vm_noaccess (m_vmmaps mo)) x), (covered (m_vm_lazy mo) x); reflexivity.
  - model_proj. reflexivity.
  - unfold h'. model_proj. cbn [vm_maps]. intros e He. unfold map_remove in He. apply (incl_filter _ _ _ He).
  - unfold h'. model_proj. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma iv_count_nonneg : forall P e, 0 <= iv_count P e.
Proof. intros. unfold iv_count. apply zcount_nonneg. Qed.

Lemma iv_count_rng_split : forall e lo m hi, lo <= m <= hi ->
  iv_count (in_rng lo hi) e = iv_count (in_rng lo m) e + iv_count (in_rng m hi) e.
Proof.
  intros e lo m hi Hm. unfold iv_count. rewrite (zcount_and_split (in_rng lo hi) (in_rng lo m)).
  f_equal.
  - apply zcount_ext. intros x _. unfold in_rng.
    destruct (Z.leb_spec lo x), (Z.ltb_spec x hi), (Z.ltb_spec x m); cbn; try reflexivity; lia.
  - apply zcount_ext. intros x _. unfold in_rng.
    destruct (Z.leb_spec lo x), (Z.ltb_spec x hi), (Z.ltb_spec x m), (Z.leb_spec m x); cbn; try reflexivity; lia.
Qed.

Lemma overlap_sum_split : forall l lo m hi, lo <= m <= hi ->
  overlap_sum l lo hi = overlap_sum l lo m + overlap_sum l m hi.
Proof.
  induction l as [|e l IH]; intros lo m hi Hm; [rewrite !overlap_sum_nil; lia|].
  rewrite !overlap_sum_cons, (IH lo m hi Hm), (iv_count_rng_split e lo m hi Hm). lia.
Qed.

Lemma overlap_sum_nonneg : forall l lo hi, 0 <= overlap_sum l lo hi.
Proof. intros. unfold overlap_sum. apply sum_count_nonneg. Qed.

Lemma iv_count_in_rng_le0 : forall p lo hi, lo <= hi -> 0 <= iv_count (in_rng lo hi) p <= hi - lo.
Proof. intros. split; [apply iv_count_nonneg| apply iv_count_in_rng_le; assumption]. Qed.

(* [comment removed for export] *)
Lemma overlap_sum_seps : forall l lo hi, seps l -> lo <= hi -> overlap_sum l lo hi <= hi - lo.
Proof.
  induction l as [|e l IH]; intros lo hi Hs Hlh; [rewrite overlap_sum_nil; lia|].
  apply seps_cons_inv in Hs as [Hf Hs]. rewrite overlap_sum_cons.
  set (a := B e). set (s := S e).
  pose proof (B_range e) as Ha. pose proof (S_range e) as Hsz. fold a in Ha. fold s in Hsz.
  set (m1 := Z.max lo (Z.min hi a)). set (m2 := Z.min hi (Z.max lo (a + s))).
  assert (Hm : lo <= m1 /\ m1 <= m2 /\ m2 <= hi) by lia.
  rewrite (overlap_sum_split l lo m1 hi) by lia. rewrite (overlap_sum_split l m1 m2 hi) by lia.
  rewrite (iv_count_rng_split e lo m1 hi) by lia. rewrite (iv_count_rng_split e m1 m2 hi) by lia.
  (* [comment removed for export] *)
  assert (MID : overlap_sum l m1 m2 = 0).
  { destruct (Z.eq_dec m1 m2) as [E|NE].
    - pose proof (overlap_sum_nonneg l m1 m2). unfold overlap_sum in *.
      pose proof (sum_count_mono (in_rng m1 m2) (fun _ => false) l ltac:(intros x Hx; exfalso; unfold in_rng in Hx; destruct (Z.leb_spec m1 x), (Z.ltb_spec x m2); cbn in Hx; try discriminate; lia)).
      assert (Z0 : sum_count (fun _ : Z => false) l = 0).
      { clear. induction l as [|q l IH2]; [reflexivity|]. rewrite sum_count_cons, IH2. unfold iv_count. rewrite zcount_const_false. lia. }
      lia.
    - unfold overlap_sum. clear IH Hs. induction l as [|q l IH2]; [reflexivity|].
      apply Forall_cons_iff in Hf as [Hq Hf]. rewrite sum_count_cons, (IH2 Hf).
      rewrite iv_count_in_rng_disjoint; [lia|]. unfold wsep in Hq. unfold B, S in *. lia. }
  (* [comment removed for export] *)
  assert (E1 : iv_count (in_rng lo m1) e = 0).
  { destruct (Z.eq_dec lo m1) as [E|NE].
    - pose proof (iv_count_in_rng_le0 e lo m1 ltac:(lia)). lia.
    - apply iv_count_in_rng_disjoint. fold a s. lia. }
  assert (E3 : iv_count (in_rng m2 hi) e = 0).
  { destruct (Z.eq_dec m2 hi) as [E|NE].
    - pose proof (iv_count_in_rng_le0 e m2 hi ltac:(lia)). lia.
    - apply iv_count_in_rng_disjoint. fold a s. lia. }
  pose proof (iv_count_in_rng_le e m1 m2 ltac:(lia)).
  pose proof (IH lo m1 Hs ltac:(lia)). pose proof (IH m2 hi Hs ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma nonlazy_fixed_repl_le : forall mo flags a n,
  MOK mo -> mmap_noreserve_b (Z_to_bv 64 flags) = false -> 0 <= a -> 0 <= n -> a + n < 2^64 ->
  nonlazy_bytes (fixed_model mo flags a n) <= nonlazy_bytes mo + n.
Proof.
  intros mo flags a n (M1 & M2 & M3 & M4 & M5 & M6) Hnr Ha Hn Hhi.
  assert (Ua : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit; lia).
  assert (Un : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  unfold fixed_model, with_mmap_replacement, with_mmap_backing. rewrite Hnr. rewrite !Ua, !Un.
  rewrite <- (vm_backing_used_canon _ M1).
  rewrite <- vm_backing_used_canon by (model_proj; rewrite M1; reflexivity).
  eapply Z.le_trans.
  { apply backing_forget_commit_le; [exact M3| lia| reflexivity|]. unfold mmap_fixed_rw_next. cbn [vm_noaccess]. rewrite ?Ua, ?Un. reflexivity. }
  pose proof (overlap_sum_seps (vm_maps (m_vmmaps mo)) a (a + n) M4 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma backing_forget_span_le : forall m h' lo hi e,
  model_ivs_wf m -> lo <= hi -> hi <= 2^64 ->
  B e = lo -> S e = hi - lo ->
  vm_maps h' = e :: maps_subtract (vm_maps (m_vmmaps m)) lo hi ->
  vm_noaccess h' = maps_subtract (vm_noaccess (m_vmmaps m)) lo hi ->
  vm_backing_used (vm_forget_range lo hi (with_vmmaps h' m))
  <= vm_backing_used m + (hi - lo).
Proof.
  intros m h' lo hi e Hwf Hlh Hhi HB HS Hmaps Hna.
  pose proof Hwf as (Wm & Wn & Wl & _).
  destruct (maps_subtract_sem _ lo hi Wm Hlh) as (Wm' & Smm & _).
  assert (He : iv_wf e) by (unfold iv_wf; lia).
  assert (Hwf' : ivs_wf (vm_maps (m_vmmaps (vm_forget_range lo hi (with_vmmaps h' m))))).
  { model_proj. rewrite Hmaps. apply ivs_wf_cons; [exact He | exact Wm']. }
  rewrite (vm_backing_used_sem_maps _ Hwf'), (vm_backing_used_sem _ Hwf).
  model_proj. rewrite Hmaps, Hna.
  destruct (maps_subtract_sem _ lo hi Wn Hlh) as (_ & _ & Cn).
  destruct (maps_subtract_sem _ lo hi Wl Hlh) as (_ & _ & Cl).
  pose proof (filter_length_le (page_outside_range lo hi) (m_vm_materialized m)).
  rewrite sum_count_cons, Smm.
  lazymatch goal with |- iv_count ?P e + _ + _ <= _ =>
    assert (E1 : iv_count P e <= hi - lo)
      by (unfold iv_count; rewrite HS; eapply Z.le_trans; [apply zcount_le_len|]; rewrite Z2Nat.id by lia; lia);
    assert (E2 : sum_count (fun x => P x && negb (in_rng lo hi x)) (vm_maps (m_vmmaps m))
                 <= sum_count (fun x => negb (covered (vm_noaccess (m_vmmaps m) ++ m_vm_lazy m) x)) (vm_maps (m_vmmaps m)))
      by (apply sum_count_mono; intros x; rewrite !covered_app, Cn, Cl;
          destruct (covered (vm_noaccess (m_vmmaps m)) x), (covered (m_vm_lazy m) x), (in_rng lo hi x); cbn; congruence)
  end.
  unfold page_size in *. nia.
Qed.

(* [comment removed for export] *)
Lemma backing_recommit_span_lazy_le : forall m h' (a n : word),
  model_ivs_wf m ->
  bv_unsigned a mod page_size = 0 -> bv_unsigned n mod page_size = 0 ->
  0 < bv_unsigned n -> bv_unsigned a + bv_unsigned n <= 2 ^ 64 ->
  vm_maps h' = (a, n) :: maps_subtract (vm_maps (m_vmmaps m)) (bv_unsigned a) (bv_unsigned a + bv_unsigned n) ->
  vm_noaccess h' = maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned a) (bv_unsigned a + bv_unsigned n) ->
  vm_backing_used (vm_add_lazy a n (vm_forget_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n) (with_vmmaps h' m)))
  <= vm_backing_used m.
Proof.
  intros m h' a n Hwf Hal Hnl Hpos Hend Hmaps Hna.
  pose proof Hwf as (Wm & Wn & Wl & _).
  set (lo := bv_unsigned a) in *. set (hi := (lo + bv_unsigned n)%Z) in *.
  assert (Hlh : lo <= hi) by (pose proof (bv_unsigned_in_range 64 n); lia).
  pose proof (lazy_interior_aligned a n Hal Hnl Hpos Hend) as Hli.
  destruct (maps_subtract_sem _ lo hi Wm Hlh) as (Wm' & Smm & _).
  assert (He : iv_wf (a, n)) by (unfold iv_wf, B, S; cbn [fst snd]; lia).
  assert (Hwf' : ivs_wf (vm_maps (m_vmmaps (vm_add_lazy a n (vm_forget_range lo hi (with_vmmaps h' m)))))).
  { model_proj. rewrite Hmaps. apply ivs_wf_cons; [exact He | exact Wm']. }
  rewrite (vm_backing_used_sem_maps _ Hwf'), (vm_backing_used_sem _ Hwf).
  model_proj. rewrite Hmaps, Hna, Hli.
  destruct (maps_subtract_sem _ lo hi Wn Hlh) as (_ & _ & Cn).
  destruct (maps_subtract_sem _ lo hi Wl Hlh) as (_ & _ & Cl).
  pose proof (filter_length_le (page_outside_range lo hi) (m_vm_materialized m)).
  rewrite sum_count_cons, Smm.
  lazymatch goal with |- iv_count ?P (a, n) + _ + _ <= _ =>
    assert (E1 : iv_count P (a, n) = 0)
      by (unfold iv_count; apply zcount_false; intros x Hx; unfold B, S in Hx; cbn [fst snd] in Hx;
          pose proof (bv_unsigned_in_range 64 n); rewrite Z2Nat.id in Hx by lia;
          rewrite !covered_app; unfold covered at 2; cbn [existsb]; unfold in_iv, B, S; cbn [fst snd]; unfold in_rng;
          replace (bv_unsigned a <=? x) with true by (symmetry; apply Z.leb_le; lia);
          replace (x <? bv_unsigned a + bv_unsigned n) with true by (symmetry; apply Z.ltb_lt; lia);
          cbn; rewrite ?Bool.orb_true_r; reflexivity);
    assert (E2 : sum_count (fun x => P x && negb (in_rng lo hi x)) (vm_maps (m_vmmaps m))
                 <= sum_count (fun x => negb (covered (vm_noaccess (m_vmmaps m) ++ m_vm_lazy m) x)) (vm_maps (m_vmmaps m)))
      by (apply sum_count_mono; intros x; rewrite !covered_app; unfold covered at 2; cbn [existsb]; fold (covered (maps_subtract (m_vm_lazy m) lo hi) x);
          rewrite Cn, Cl; destruct (in_iv (a, n) x), (covered (vm_noaccess (m_vmmaps m)) x), (covered (m_vm_lazy m) x), (in_rng lo hi x); cbn; congruence)
  end.
  unfold page_size in *. nia.
Qed.

(* [comment removed for export] *)
Lemma nonlazy_fixed_span_repl_le : forall mo flags a n,
  MOK mo -> mmap_noreserve_b (Z_to_bv 64 flags) = false -> 0 <= a -> 0 <= n -> a + n < 2^64 ->
  nonlazy_bytes (mmap_fixed_span_repl (Z_to_bv 64 flags) (Z_to_bv 64 a) (Z_to_bv 64 n) mo) <= nonlazy_bytes mo + n.
Proof.
  intros mo flags a n (M1 & M2 & M3 & M4 & M5 & M6) Hnr Ha Hn Hhi.
  assert (Ua : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit; lia).
  assert (Un : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  unfold mmap_fixed_span_repl, with_mmap_replacement, with_mmap_backing. rewrite Hnr. rewrite !Ua, !Un.
  rewrite <- (vm_backing_used_canon _ M1).
  rewrite <- vm_backing_used_canon by (model_proj; rewrite M1; reflexivity).
  eapply Z.le_trans.
  { apply (backing_forget_span_le mo _ a (a + n) (Z_to_bv 64 a, Z_to_bv 64 n));
      [exact M3| lia| lia| unfold B; cbn [fst]; exact Ua| unfold S; cbn [snd]; rewrite Un; lia| |];
      unfold mmap_fixed_rw_span_next; cbn [vm_maps vm_noaccess]; rewrite ?Ua, ?Un; reflexivity. }
  lia.
Qed.

Lemma nonlazy_fixed_span_repl_lazy_le : forall mo a n,
  MOK mo -> 0 <= a -> 0 < n -> a + n < 2^64 -> a mod 4096 = 0 -> n mod 4096 = 0 ->
  nonlazy_bytes (mmap_fixed_span_repl (Z_to_bv 64 F_FIXNORES) (Z_to_bv 64 a) (Z_to_bv 64 n) mo) <= nonlazy_bytes mo.
Proof.
  intros mo a n (M1 & M2 & M3 & M4 & M5 & M6) Ha Hn Hhi Hal Hnl.
  assert (Ua : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit; lia).
  assert (Un : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  unfold mmap_fixed_span_repl, with_mmap_replacement, with_mmap_backing. change (mmap_noreserve_b (Z_to_bv 64 F_FIXNORES)) with true. cbv iota.
  rewrite !Ua, !Un.
  rewrite <- (vm_backing_used_canon _ M1).
  rewrite <- vm_backing_used_canon by (model_proj; rewrite M1; reflexivity).
  pose proof (backing_recommit_span_lazy_le mo (mmap_fixed_rw_span_next (m_vmmaps mo) (Z_to_bv 64 a) (Z_to_bv 64 n)) (Z_to_bv 64 a) (Z_to_bv 64 n)) as BR.
  rewrite !Ua, !Un in BR. apply BR; auto; try (unfold page_size; lia); try lia.
  - unfold mmap_fixed_rw_span_next. cbn [vm_maps]. rewrite ?Ua, ?Un. reflexivity.
  - unfold mmap_fixed_rw_span_next. cbn [vm_noaccess]. rewrite ?Ua, ?Un. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma fp_ok_mono2 : forall lz lz' (A A' : alw),
  (forall p, page_in_ranges p lz' = true -> page_in_ranges p lz = true \/ A' p) ->
  alw_le A A' ->
  fp_le (fp_ok lz A) (fp_ok lz' A').
Proof.
  intros lz lz' A A' SUB LE b j H k Hk Hb.
  destruct (H k Hk Hb) as [NL | AL].
  - destruct (page_in_ranges (page_base_of (b + Z.of_nat k)) lz') eqn:E; [|left; exact E]. destruct (SUB _ E) as [E'|HA]; [congruence| right; exact HA].
  - right. apply LE, AL.
Qed.

(* [comment removed for export] *)
Lemma page_in_ranges_app : forall p l1 l2, page_in_ranges p (l1 ++ l2) = page_in_ranges p l1 || page_in_ranges p l2.
Proof. intros. unfold page_in_ranges. apply existsb_app. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pcost (len : Z) : Z := len / 4096 + len / 32768 + 4.
Fixpoint gcost (ga : list Z) : Z := match ga with [] => 0 | l :: ga' => pcost l + gcost ga' end.
Lemma pcost_nonneg : forall l, 0 <= l -> 0 <= pcost l.
Proof. intros. unfold pcost. pose proof (Z.div_pos l 4096). pose proof (Z.div_pos l 32768). lia. Qed.

(* [comment removed for export] *)
Definition GA (G : list (Z * Z)) (A : alw) : Prop :=
  forall g, In g G ->
    0 <= fst g /\ 0 <= snd g /\ fst g + snd g <= ATOP
    /\ (forall z, fst g <= z < fst g + snd g -> A (page_base_of z))
    /\ (forall z', shad (fst g) <= z' < shad (fst g + snd g) -> A (page_base_of z')).

Lemma GA_nil : forall A, GA [] A.
Proof.
ltac2:(KReplay.run1 (kr_t_ATsafeAlloc ()) ["CANSEC1"] "h01Ah11Hh21gh31zh42z'p;2p;1p;3p-1R0p10000p4p710p9P0p1000\R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001:p4p710p9P0g00J<R0p4p710p8p1002Ip4p70p10039p4p710R1p8p1003Wp4p70P1p8p1004Ep4p710P1p8p103Xap4p7210P1p8p103Y_p4p7210P1p8p1005;p4p70P1p8g00?fj2<Tg00:1j1;TP0j39Tg00ROj33Tg00<Yj21Tg00Rlj36Tg00ODj24Tg00@Fj18Tg00ZSj22Tg00COj20Tg03S0j17Tg03Z]j15Tg03[Uj2:Tg03U?g00I^R0/<0R1f0R2%;1R3591g01A?g019WR1f2R49300R5'1A6004R4,111454p,2rc#8'1f3R49300R5/12A6004,45R4,22'0f5f1#7O1R1[^30%55/12%54,22'0P1[^40'0'0'0'0P2n010000000W1W21:32eW0o"). Qed.
Lemma GA_le : forall G A A', GA G A -> alw_le A A' -> GA G A'.
Proof.
  intros G A A' H LE g Hg. destruct (H g Hg) as (H1 & H2 & H3 & H4 & H5).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; intros; apply LE; auto.
Qed.

Section Ops.
Variable NMAX : nat.
Variables SB PA : Z.
Variable Abase : alw.
Let NMAXZ : Z := Z.of_nat NMAX.
(* [comment removed for export] *)
Hypothesis HRES : NMAXZ * 4096 <= RESERVE34.
(* [comment removed for export] *)
Hypothesis ABASE_SH : forall z',
  ((exists c, 1 <= c <= 31 /\
      (shad (SB + c * K_REGION) <= z' < shad (SB + c * K_REGION + UWIN)
       \/ shad (SB + c * K_REGION + K_FREEARR_OFF) <= z' < shad (SB + c * K_REGION + K_FREEARR_OFF + FWIN)))
   \/ shad PA <= z' < shad (PA + K_PTRARR_RESERVE)) -> Abase (page_base_of z').
Hypothesis HSB : 0 <= SB /\ SB + K_SPACE_SIZE <= ATOP.
Hypothesis HPA : 0 <= PA /\ PA + K_PTRARR_RESERVE <= ATOP.

Definition KI (b : Z) (G : list (Z * Z)) (A : alw) (k : Z) (mo : Model) : Prop :=
  MOK mo /\ 0 <= b /\ nonlazy_bytes mo + RESERVE34 <= LIMIT34 /\ alw_le Abase A /\ GA G A /\ abud A k /\ 0 <= k.   (* [comment removed for export] *)

Lemma KI_acct_ok : forall b G A k mo, KI b G A k mo -> k <= NMAXZ -> acct_ok NMAX (fp_ok (m_vm_lazy mo) A) A mo.
Proof.
  intros b G A k mo (M & Hb & HN & _ & _ & (L & ND & HL & HAL) & Hk) Hkc. pose proof M as (_ & M2 & _).
  split; [apply footprint_ok_fp_ok|]. split.
  - exists L. split; [exact ND|]. split; [| exact HAL]. subst NMAXZ. lia.
  - unfold page_size. subst NMAXZ. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma adec_mmap_ret : forall len rsp z, adec_mmap ATOP len PROT_RW rsp = Some z -> bv_unsigned (eff_ret rsp) = z.
Proof.
  intros len rsp z H. unfold adec_mmap in H. change (PROT_RW =? 0) with false in H. cbv iota in H.
  unfold dec_mmap in H. destruct rsp as [r ws zs us cs ci].
  destruct ws; [|discriminate]. destruct zs as [|[a n] zs].
  - destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct (errno_of r); discriminate.
  - destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate].
    match type of H with (match (if ?c then _ else _) with _ => _ end) = _ => destruct c; [|discriminate] end. cbn [eff_ret]. injection H as <-. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mmap_len_lit : forall len, 0 < len < 2^63 -> len mod 4096 = 0 -> page_round_up_Z (bv_unsigned (Z_to_bv 64 len)) = len.
Proof. intros len H1 H2. rewrite mmap_len_eq by lia. apply mmap_len_id; lia. Qed.

Lemma shad_div8 : forall a, shad a = 2147450880 + a / 8.
Proof. intros. unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.
Lemma shlen_div8 : forall l, shlen l = l / 8.
Proof. intros. unfold shlen. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.
Lemma shad_bounds : forall a, 0 <= a <= 2^47 -> 2147450880 <= shad a <= 2147450880 + 2^44.
Proof.
  intros a Ha. rewrite shad_div8. pose proof (Z.div_pos a 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_mono a (2^47) 8 ltac:(lia) ltac:(lia)). change (2^47/8) with (2^44) in H0. lia.
Qed.
Lemma shlen_bounds : forall l, 0 <= l -> 0 <= shlen l <= l.
Proof. intros l Hl. rewrite shlen_div8. pose proof (Z.div_pos l 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound l 8 l ltac:(lia) ltac:(lia)). lia. Qed.
Lemma shad_le_mono : forall a b, a <= b -> shad a <= shad b.
Proof. intros. unfold shad. rewrite !Z.shiftr_div_pow2 by lia. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. Qed.
Lemma shad_plus : forall a n, a mod 8 = 0 -> shad (a + n) = shad a + Z.shiftr n 3.
Proof.
  intros a n Ha. unfold shad. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
  pose proof (Z.div_mod a 8 ltac:(lia)). rewrite Ha, Z.add_0_r in H.
  rewrite H at 1. rewrite Z.mul_comm, Z.div_add_l by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma robust_room : forall mo x, MOK mo -> x + RESERVE34 <= LIMIT34 -> robust NMAX x (vm_limit (m_vmmaps mo)).
Proof.
ltac2:(KReplay.run1 (kr_t_ATsafeAlloc ()) ["CANSEC1"; "Ops"] "h01Hh14__x1h24__x2h34__x3h44__x4h54__x5h62Hxh72M2h82_Hh93_H0h:7__arithh;4__ffh<8__varmaph=5__with>4cstrh?2moh@1xp;1p;3p;2p;4p;7p;8p-1R0p10000p4p710p9P0p1000\R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001:p4p710p9P0p10022p4p710p8p1002Ip4p70p10039p4p710R0p8p1003Wp4p70P0p8p1004Ep4p710P0p8p103Xap4p7210P0p8p103Y_p4p7210P0p8p1005;p4p70P0p8g0061j1lTg006kj10Tg007Pj1UTg007nj1kTg008Qj1PTg0091j1QTg00:1j1MTg00:Qj35Tg00:kj12Tg00;bj16Tg00<Yj21Tg00=5j1DTg00>8j1<Tg00>nj1?Tg00?fj2fTg00@Fj1^Tg00A<j1\Tg00B6j3CTg00BWj1BTg00ODj28Tg04GQj3NTg00COR0j29Tg01eHj1XTg01hnj2ITg00ZSj2WTg01Omj1VTg00h\j13Tg00_Hj1GTg01gfj1TTg00e1j1FTg00ePj2=Tg015Gj3ETg0160j2RTg0137j3STg00f9j2JTg00fWj1jTg00g5j4LTg00gSj1iTg00h1j1gTg00iAj2:Tg00jij3OTg00jGj1eTg0107j2]Tg01hKj3_Tg00l0j2`Tg00`aj2aTg00lRj2bTg00m>j3[Tg00m]j4cTg01D[j3dTg016\j4ZTg017Gj7YTg0193j8hTf0R1#0#0#0#0p=>f2R2f1R3/91'9p=7%31#3#3#3p=4%01#0p=H%01#0#0#0#0#0#0#0p=;g00I^R4P3g01?8P1CZp=@P3g01<RR5g01=1R6P6g01=QR7P1g01>XFYp=Af3R8P5P6P6P7P2P3P1Ghp=Kg00GJ%l3P0g00H@R5#0R9#0R:#>R;#U#kR<#PR=%Q2%M<R>35g00HeR?%22R@#6'1%D2%<@RA#?1f<<R<p,2rcRB#^RC#\RD;CA%B@=54C3737g03b>R@,82/1?p,4NMAXRAf4RE#2#67N8[P1%QE=5=>f5R>#2R=#6,1?%D>%<=RF#?AC<DF%B==54C3737P0f6R0#2R=#6,1?%D0%<=RF#?AC<DF%B==54C'937180@/1?f7f8#2#6R05NA[P111?0f9R0#D%20R=#<RF#?AC<DF%B==54C'937180@/1?f:R0%XAR=g01I:'I'8f;#2#6RF'1RD1WF0%VB%35RB#3#4#4#4RF#0#4#4#0#H#>#;#;#G/1C%3F#4#4#0#H#>#;#;#G,1C'9%TAg019WRA/1=g01;?RCg01@`RF#FR0#FR<#F,=41=4<1=401=4F5E45E45E4g01:S'R%MC3S%PCP4P41J4EP2P41J4>P>%j4CLCLP31J48CL%i4%g4RC1:45R51:4:R:5O4%39#0,:4RF'@,AC%e6R6PC1:4BRB,@F,ACP6PC1:49%H;#>#GR;,]45_4R9/@:,ACP6AO459/@B,ACCKCKCK1`C7P1P2g00SIRCg00SiR7'a1b12=5C7dA[4A3Ccb;b<b=X14X24X34X44X541818/1E11>81I8;/1>1IE;,88/1>[[[^14^24^34^44^54P1P?P@f>#2#6P=f=P8P>p,4HRESO8b:b>b0PDe3dW6W9W7P3P1O2n2001000000121000000W0W8P3P1O2n2001000000121000000W0X@4W?o"). Qed.

Lemma nsafeA_grant : forall b G A k mo len,
  KI b G A k mo -> 0 < len < 2^41 -> len mod 4096 = 0 -> vm_backing_used mo + len + RESERVE34 <= LIMIT34 ->
  nsafeA NMAX (NMmap 0 len PROT_RW F_ANON) mo.
Proof.
  intros b G A k mo len HK Hlen Hal HR. pose proof HK as (M & Hb & HN & _). pose proof M as (M1 & M2 & _). pose proof (MOK_nonlazy mo M) as NLZ.
  split.
  - cbn [nsafeA0]. unfold mmap_safeA_b.   (* [comment removed for export] *)
pose proof (nsafe_mmap_rw 0 len mo ltac:(lia) (place_declined_b_null _ _ _)) as X. cbn [nsafe] in X.
    change PROT_RW with (PROT_READ + PROT_WRITE). change F_ANON with (MAP_PRIVATE + MAP_ANONYMOUS). exact X.
  - cbn [nslack]. rewrite (mmap_len_lit len) by lia. cbv zeta. split.
    + right. apply robust_room; [exact M| lia].
    + split.
      * change (mmap_fixed_repl (Z_to_bv 64 F_ANON) (Z_to_bv 64 0) (Z_to_bv 64 len) mo) with (fixed_model mo F_ANON 0 len).
        apply robust_room; [exact M|]. pose proof (nonlazy_fixed_repl_le mo F_ANON 0 len M eq_refl ltac:(lia) ltac:(lia) ltac:(lia)). lia.
      * (* [comment removed for export] *)
        apply robust_room; [exact M|]. pose proof (nonlazy_fixed_span_repl_le mo F_ANON 0 len M eq_refl ltac:(lia) ltac:(lia) ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma NSAFEA_FIXED : forall a len flags mo,
  (flags = F_FIXED \/ flags = F_FIXNORES) -> 0 < len -> len mod 4096 = 0 -> 0 < a -> a mod 4096 = 0 -> a + len <= ATOP ->
  alloc_top (m_vmmaps mo) = ATOP ->      (* [comment removed for export] *)
  region_free (vm_reserved (m_vmmaps mo)) (Z_to_bv 64 a) (Z_to_bv 64 len) = true ->
  map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 a) (Z_to_bv 64 len) = true ->
  nslack NMAX (NMmap a len PROT_RW flags) mo ->
  nsafeA NMAX (NMmap a len PROT_RW flags) mo.
Proof.
  intros a len flags mo Hfl Hlen Hal Ha Haal Hce Htop Hrf Hmc Hsl. split; [| exact Hsl].
  atop_facts.
  assert (Hlen2 : len < 2^47) by lia.
  pose proof (nsafeA0_mmap_fixed_rw a len flags mo) as X. cbv zeta in X. rewrite (mmap_len_lit len) in X by lia.
  change PROT_RW with (PROT_READ + PROT_WRITE). apply X.
  - destruct Hfl as [E | E]; rewrite E; vm_compute; reflexivity.
  - rewrite w_is0_lit by lia. apply Z.eqb_neq. lia.
  - exact Ha.
  - unfold page_size. exact Haal.
  - rewrite Htop. lia.
  - left. split; [exact Hrf | exact Hmc].
Qed.

Lemma nsafeA_fixed : forall b G A k mo a len flags,
  KI b G A k mo -> (flags = F_FIXED \/ flags = F_FIXNORES) -> 0 < len < 2^41 -> len mod 4096 = 0 ->
  0 < a -> a mod 4096 = 0 -> a + len <= ATOP ->
  region_free (vm_reserved (m_vmmaps mo)) (Z_to_bv 64 a) (Z_to_bv 64 len) = true ->
  map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 a) (Z_to_bv 64 len) = true ->
  vm_backing_used mo + len + RESERVE34 <= LIMIT34 ->                 (* [comment removed for export] *)
  nsafeA NMAX (NMmap a len PROT_RW flags) mo.
Proof.
  intros b G A k mo a len flags HK Hfl Hlen Hal Ha Haal Hce Hrf Hmc HR. pose proof HK as (M & Hb & HN & _). pose proof M as (M1 & M2 & _ & _ & _ & M6).
  pose proof (MOK_nonlazy mo M) as NLZ.
apply NSAFEA_FIXED; auto; try lia.
  cbn [nslack]. rewrite (mmap_len_lit len) by lia. cbv zeta.
  change (mmap_fixed_repl (Z_to_bv 64 flags) (Z_to_bv 64 a) (Z_to_bv 64 len) mo) with (fixed_model mo flags a len).
  atop_facts. destruct Hfl as [-> | ->].
  - split; [| split].
    + right. apply robust_room; [exact M| lia].
    + apply robust_room; [exact M|]. pose proof (nonlazy_fixed_repl_le mo F_FIXED a len M eq_refl ltac:(lia) ltac:(lia) ltac:(lia)). lia.
    + apply robust_room; [exact M|]. pose proof (nonlazy_fixed_span_repl_le mo F_FIXED a len M eq_refl ltac:(lia) ltac:(lia) ltac:(lia)). lia.   (* [comment removed for export] *)
  - split; [| split].
    + left. reflexivity.
    + apply robust_room; [exact M|]. destruct (MOK_recommit mo a len M ltac:(lia) ltac:(lia) ltac:(lia) Haal Hal Hmc) as (_ & X & _). lia.
    + apply robust_room; [exact M|]. pose proof (nonlazy_fixed_span_repl_lazy_le mo a len M ltac:(lia) ltac:(lia) ltac:(lia) Haal Hal). lia.   (* [comment removed for export] *)
Qed.

Lemma nsafeA_munmap : forall mo a len,
  0 < len <= 2^40 -> 0 <= a -> a mod 4096 = 0 -> a + mmap_len len <= ATOP ->
  map_has (vm_maps (m_vmmaps mo)) (Z_to_bv 64 a) (Z_to_bv 64 (mmap_len len)) = true ->
  nsafeA NMAX (NMunmap a len) mo.
Proof.
  intros mo a len Hlen Ha Haal Hce Hmh. atop_facts. pose proof (mmap_len_bounds len ltac:(lia)) as ML. split; [| exact I].
  cbn [nsafeA0 nsafe]. unfold munmap_safe_b. rewrite (unsigned_lit a) by lia. unfold page_size. rewrite Haal.
  rewrite w_is0_lit by lia. replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb orb Z.eqb].
  rewrite mmap_len_eq by lia.
  rewrite Hmh. destruct (TASK_SIZE <? a + mmap_len len); reflexivity.   (* [comment removed for export] *)
Qed.

(* [comment removed for export] *)
Lemma nsafeA_madvise : forall mo a len,
  0 < len <= 2^40 -> 0 <= a -> a mod 4096 = 0 -> a + mmap_len len <= 2^47 ->
  madvise_dontneed_ok (m_vmmaps mo) (Z_to_bv 64 a) (Z_to_bv 64 (mmap_len len)) = true ->
  nsafeA NMAX (NMadvise a len) mo.
Proof.
  intros mo a len Hlen Ha Haal Hce Hok. pose proof (mmap_len_bounds len ltac:(lia)) as ML. split; [| exact I].
  cbn [nsafeA0 nsafe]. unfold madvise_safe_b. rewrite (unsigned_lit a) by lia. unfold page_size. rewrite Haal.
  rewrite w_is0_lit by lia. replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb Z.eqb].
  rewrite mmap_len_eq by lia. rewrite Hok. destruct (two_pow_64 <=? a + mmap_len len); reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma page_base_of_aligned : forall y, bv_unsigned (page_base_of y) mod 4096 = 0.
Proof.
  intros y. unfold page_base_of, page_size. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  rewrite Z.mod_mod_divide by (exists 4503599627370496; reflexivity). apply Z_mod_mult.
Qed.

Lemma page_base_of_self : forall p : word, bv_unsigned p mod 4096 = 0 -> page_base_of (bv_unsigned p) = p.
Proof.
  intros p Hp. unfold page_base_of, page_size.
  replace (bv_unsigned p / 4096 * 4096) with (bv_unsigned p) by (pose proof (Z.div_mod (bv_unsigned p) 4096 ltac:(lia)); lia).
  apply Z_to_bv_bv_unsigned.
Qed.

Lemma page_base_of_page : forall y, page_base_of (bv_unsigned (page_base_of y)) = page_base_of y.
Proof. intros. apply page_base_of_self. apply page_base_of_aligned. Qed.

(* [comment removed for export] *)
Lemma fp_ok_mono3 : forall lz lz' (A A' : alw),
  (forall y, page_in_ranges (page_base_of y) lz' = true -> page_in_ranges (page_base_of y) lz = true \/ A' (page_base_of y)) ->
  alw_le A A' ->
  fp_le (fp_ok lz A) (fp_ok lz' A').
Proof.
  intros lz lz' A A' SUB LE b j H k Hk Hb.
  destruct (H k Hk Hb) as [NL | AL].
  - destruct (page_in_ranges (page_base_of (b + Z.of_nat k)) lz') eqn:E; [|left; exact E]. destruct (SUB _ E) as [E'|HA]; [congruence| right; exact HA].
  - right. apply LE, AL.
Qed.

(* [comment removed for export] *)
Lemma page_notin_subtract : forall l lo len z,
  ivs_wf l -> 0 <= len -> lo <= z < lo + len -> 0 <= lo -> lo + len <= 2^64 ->
  page_in_ranges (page_base_of z) (maps_subtract l lo (lo + len)) = false.
Proof.
  intros l lo len z Hwf Hlen Hz Hlo Hhi.
  destruct (page_in_ranges (page_base_of z) (maps_subtract l lo (lo + len))) eqn:E; [|reflexivity]. exfalso.
  apply page_in_maps_subtract in E as [_ E]; [| exact Hwf| lia].
  pose proof (page_base_of_range z ltac:(lia)). unfold page_size in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma step_grant : forall b G A k mo len z rsp,
  KI b G A k mo -> 0 < len < 2^41 -> len mod 4096 = 0 -> len <= b ->
  vm_backing_used mo + len + RESERVE34 <= LIMIT34 ->                  (* [comment removed for export] *)
  z mod 4096 = 0 -> 0 < z -> z + len <= ATOP ->
  region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (Z_to_bv 64 z) (Z_to_bv 64 len) = true ->
  adec_mmap ATOP len PROT_RW rsp = Some z ->
  let A' := aunion A (range_pages z len ++ range_pages (shad z) (shlen len)) in
  let mo' := grant_model mo z len in
  fstepS (NMmap 0 len PROT_RW F_ANON) rsp (fp_ok (m_vm_lazy mo) A) (fp_ok (m_vm_lazy mo') A')
  /\ alw_le A A'
  /\ KI (b - len) ((z, len) :: G) A' (k + pcost len) mo'.
Proof.
ltac2:(KReplay.run1 (kr_t_ATsafeAlloc ()) ["CANSEC1"; "Ops"] "p'0h07__sat10h17__sat14h27__sat16h34__x1h47__sat15h54cstrh69heq_NMAXZh77__sat12h87__arithh97__sat11h:7__sat13h;6__sat9h<4__p1h=4__x2h>4__ffh?8__varmaph@5__withA4__x3hB7__sat17hC1zhD2H0hE7__sat18hF5cstr0hG2HahH4__x4hI1ahJ4__p2hK1HhL6__sat3hM4__x5hN4__x6hO4__x7hP2HyhQ7__sat19hR5cstr1hS1yhT2H1hU6__sat1hV6__sat2hW1xhX2z'hY1AhZ2H2h[3RPLh\2_Hh]3_H0h^6__sat0h_1lh`2zhha2H8hb2H9hc4__p3hd4__p4he6__sat5hf1ghg2l'hh1ni001nhi2A'hj2E0hk1Ghl3H10hm3H11hn3H12ho2H3hp2H4hq2H5hr2H6hs2H7ht3HABhu3HBUhv3HGAhw2HKhx2HNhy2HRhz2Hbh{3Hceh|4Hdech}2Hgh~2Hki014Hlali023Hlbi034Hleni043Hrfi052Hzi064Hzali072LEi083LZ'i091Mi0:2M'i0;2NEi0<3NL'i0=3NLZi0>3RETi0?3SH8i0@3SHIi0A2SLi0B3SZ0i0C3_H1i0D7__sat20i0E7__sat21i0F6__sat4i0G1bi0H1ki0I3leni0J2moi0K3mo'i0L1pi0M3rspi0N1si0O2z9i0P1ep%0p%1p%2p&0p&1p&2p;2p;1p;5p;3p;4p;:p;6p;8p;7p;<p-1R0p10000p4p710p9P0p1000\R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001:p4p710p9P0g00J<R0p4p710p8p1002Ip4p70g0039R1p4p710R2p8p1003Wp4p70P2p8p1004Ep4p710P2p8p103Xap4p7210P2p8p103Y_p4p7210P2p8p1005;p4p70P2p8g00?fk216Tg008Qk10FTg03\Nk50LTg006kj16Tg00_Hj1KTg00h\j1FTg00`Dk203Tg01J2j2ATg00<YS00j22Tg00Djk10eTg00ODS01j21k10tTg00@Fk11tTg007Pk10=Tg007nk11cTg00:kj1<Tg01N6k10qTg00>8j1_Tg00Zoj3^Tg00]?j2>Tg01]Hk31LTg03c9k11CTg03c[k41ATg03iQk21@Tg00:Qj3PTg052\j2;Tg03Z]j14Tg044Oj1=Tg053]k21;Tg01O0j37Tg0061j1|Tg00Cjj1@Tg03O1j2bTg03[Uk20STg03]Gk20@Tg01Omk11rTg04I?k21eTg01eHR2j1UTg01gfj1\Tg030ck20ATg031Kk30?Tg03Caj2:Tg031ok20pTg00`aj2tTg00:1k11STg00gSk11QTg00h1k11PTg00iAk20|Tg00jGk11ITg00l0k21GTg00lRk21ETg00m>k31DTg00m]k41BTg0107k20mTg00COS02j25Tg00ZSj2?Tg054Ym:1?Tg01Qej19Tg055Yk41>Tg03h>k10ITg00Lgj2rTg056]k21=Tg00fWk11<Tg03DRk31:k20oTg03E3S03j23k10rTg01hnj2TTg03W4j2NTg00e1k107Tg00ePk20kTg00nOk119Tg00nmk218Tg00oNk30jTg01hKk30UTg04kCk225Tg057\k324Tg010Zk30DTg058\k217Tg059^k223Tg03Ohj2eTg00]eS04j28k10sTg03Wek10bTg05:ak41{Tg05;Xk21zTg041Gk10`Tg05<6k305Tg05<ik11xTg03Skk21wTg01G6k21vTg05=`k61uTP0j3ETg00[LS05k20RTg00[fk41sTg03S0k10^Tg05>[k50OTg01D[k313Tg05?ak812Tg04T1k30~Tg00QZk40\Tg01F:k30}Tg05@fk21pTg01Pkk11oTg01SXk11nTg01TSk11kTg00;bk10WTg01UHk11jTg01VCk11iTg01W<k81hTg01X3k21fTP1k60>Tg00idk30HTg05A`k51dTg05B]k40xTg0129k60wTg05C\k71bTg01dhj2VTg05DXk41aTg05EXk21`Tg05Eok40uTg02kTk21\Tg02l4k10MTg02lMS06k21[Tg02^KR1k10YTg02bOk80KTg03VSk21YTg045Hk51XTg00\bk20JTg00aak11WTg014bm<1TTg012Uk21ZTg018Ok71]Tg03`[k41RTg05G7k21^Tg05H7k21_Tg03EPk211Tg03F7k20{Tg03F^k20nTg03GDk20yTg03Gjk20zTg043Fk20GTg043fk31gTg05I>k51OTg05I_k21NTg05JBk31lTg05Jak51MTg05K`k21mTg00Ulk40fTg0137k30XTg04Llk40_Tg05Lck40]Tg00f9k21KTg00g5k40BTg00jik31JTg016\j4wTg017Gk706Tg0193k802Tg00kLk61HTg017kk70aTg032Pk61yTg015Gk31FTg0160k21}Tg00ROk31~Tg00Rlk320Tg013Wm<15Tg019WR0f0R3'?p=Cf2R4f1R5/?3'5p>0N%63#6p=sg00I^R6?P30p=Bg03b>S07,13g00HeS08'2p=p1145/23p=xg00SIR7g00SiR87P3p>0c1203p=0f4R9f3R:+0S20@45/53'5p=j1b45/53p>0h1553,54p>0EP6P6P4P5H0f>0X:3p=X&0b3,15p=Yf7R;f6R<'bf5R=/89P:P4P5P3I0L'5p=fP0P<g03mXS09g04U4S0:H0_P=%99/e:%94/e5H0]/53p=d1205/53p=Z20@451203'5p>14%F3#Fp>10%F3#F#F#Fp>09%63#6#6#6p>0[%63#6#6#6#6#6#6#6p>0C1253,54p=qAP653p=L1t63p=y1A53,20p=G21K63p=uP6P4P5P3H0Bp=a20|63p=JB1J653p=DP4g01<RR>g01=1R?P?g01=QR@P6P5g01?8RAP3Cwg01>XRBK06p=HP:P>P?P?P@P4P5P3L02p=lP4P>P?P?P@P6P5g01;kRCP3CwPBK06p=iP5P>P?P?P@P3J1Hp=vP4P>P?P?P@P5P3K0ap=o1153,24p=WP9P:P4P5H0f%_360X=p=c&0W5&0W35P6p=hAP:45/53p=S1245/53p=`%_5=P43p>0l20m63p=gP4P>P?P?P@P6P5g01>1RDP3CwPBK06p=~P5P>P?P?P@P3J1yp>0V1353,20p=R20k63p>08B1F653p=Ig01;?REg01:S-1}5<0X3p=kP6P9P:P6P4P5P3H0BH0Bp>0iP6P6P9P:P4H0BP5P3H0Bp=MP6P5PDP3Cwp>0gP<P>P?P?P@P=P9P:P>P?P?P@P4P5P3L02L02p=QP9P>P?P?P@P:P>P?P?P@P4PBK06P5P3L02p>0TP6P9P:P4P5P3J0wp>0:P6P5PAP3Cwp>0dP:P>P?P?P@P4P5P>P?P?P@P3PBK06K0ap>0<P=P>P?P?P@P9P>P?P?P@P6P:PAP4CwPBK06P5P3L02p=]P=P>P?P?P@P9P>P?P?P@P:P4K0aP5P3L02p={P0P3Q09Q0:H0_p>22P9P:P41e53H0]p>21P0P:Q09Q0:H0_P4P5P3H0]p>1|12:41?53'5p=OP6P5PCP3Cwp>0QP6P9P:P4P5P3J0>p>0;%95/e3p>1qP<P=P9P:P4P5P3H0\H0\p=zP6P6P5P3H0fp>0PB1~663p>00B20663p>011345/13p>04%U5/23p=m1;53,V4p=[%U3,20p=nP6P6P=P9P:P4P5P3L0Kp>0ZP6g03?cS0;P6P6P1P9P2P:g03IRP4P5P3N<15p>1VQ0;P6P6P6P2P2P=P9P:P4P5P3N<15p>1UAP653,54p>0v1V53#Up=}21666R2$0Fg03U?R1g00GJRCg03leP;P<P=P9P:I0L%C:S0<g00H@S0=#6RB#KRA%FBS0>#6RD#6#FS0?#KRF+03RG80N:%6BS0@#6RH#6S0A#sRI#6#sRJ#6#sS0B#KRK,A9#Bf:S0C,2=&0e;/1<#p1A<K#B%C;S0Df8S0Ef9S0Fp,2rcRL$1tRM3x&0=IRN$1cRO016OS0Gf;S0H#<RP$0q%_P3^Q0F,>NQ0C,>N41L$0c&1C6PMQ0HQ09Q0FH1AQ0C-1@63Pf?S0IQ0Hf<S0J';Q0H#4Q0J#=';5^O+1;P1f>S0KQ0Jf=37PCQ0HfCS0LfBS0MfAS0Nf@S0OQ0II0LQ02Q0O#|fDRC#0R1Q0O#@#pp,5AbaseRPQ0MQ0LQ0MQ0MQ0NQ0N#0Dj40h40EQ0OQ0KQ0NQ0LQ0NQ0IQ0O37RQP:Q0LP:fES0PQ0OP2Q0IQ0OPCCXP:Q0MQ0O'YPQGfFdP3Q0M#|fGRQQ0L#@#pQ0P,bPfFS0QQ0PQ0PPCP1Dj40E'ZQ02fHS0R#0R1%@C#pQ0Q,bPPQQ0QQ0QQ0PQ0P#0Dj40EPCQ0MQ0PPQQ0PQ0L;7CRRP;PQP;fIS0SPCP2Q0LPCQ0RCXP;Q0Q/YCPRGfFdP3fJS0T#0%@Q#pQ0S,bPQ0TQ0SQ0SQ0RP1Dj40EQ02Q0R#@#pQ0TfKR1Q0TQ0TQ0SQ0S#0Dj60hPQ0RQ0QQ0SP1Q0SQ0R77QRRQ0HP1Q0HfMS0UQ0RP2PQQ0RfLRCCXQ0HQ0TQ0R'YPRGfFdP3Q0T#@#pQ0UfNS0VQ0UQ0UPC%0CDj60hPQ02Q0V,bPfORRQ0VQ0VQ0UQ0U#0DjPCQ0TQ0UPRQ0U?71CRSQ0IPRQ0IfQRTPCP2P1PCfPR1CXQ0IQ0V/YCPSGfFdP31bP1fRS0WPTPTP1%01DjQ02fSRSQ0W+0SQ0W@14TTP1Q0VPTPSA7TR1RCQ0LPSQ0LfUS0XP1P2PRP1fTS0YCXQ0LQ0W/Y1PCGfFdP3Q0XQ0Y+0SQ0XQ0YQ0Y414Q02fVRCQ0X+0@Q0X#0Q0YQ0WQ0XfWRRQ0XQ0Y77SRUPQPRPQfYRVQ0YP2PSQ0YfXS0ZCXPQQ0Y,YCPUGfFdP3Q0Z00@RQ0Z#0&1rLQ0=#FS0[#FS0\#FRL$10S0]#F$09$09RU#6$09$09#6#s$0[$0C$0C#K/2MS0^%FURU$09$09#6#s$0[$0C$0C#KRS7qMQ0Q-1eV%@V&0eV'LfZRWQ0ZPVPQPTP1p,4NMAXRT#URQ#yp,5NMAXZ/LQRXeRYPX%\TRT%0QRQ20AAFRZ%CAS0_%0F%CG[R[[R\%0AR]g036UR^B0?AF5UWGRF%0GS0`\^^G]R_f\R`/:KRa%0`%0KRbf^Rc/GK[[Rd1:cKRe%0cf`Rf/GK\b[RgP:g037MS0a20p0A'tQ0_eS0bO1RhP[&1SERi&0FERE%u4S0c%u:Rj7a5S0d&1Q6Rk&1P6RlQ0=-0|6Rm%JBRB'DS0eQ0[#JS0f5HlS0g&1I?RnQ0gCl21Gl@RoP3P41t7821E34$0cdB1D605H1BR8b>b?b@X36X=6XA6S0h1135S0i/241154S0j/2:S0k[^36^=6^A6S0lP3PMfaR7PfPRO4b8bLb^bUbVbLb5b6Q0YPYPXPTPQPZP\PFP_PaPdPePgPhP[p-0RgPiPE%u5S0mPkPl20m60Re=ilmS0n1vl:S0o5olS0pPnQ0nClPoP8b>b?b@X36W<S0q%C3S0r/55Rd%C5S0s[^36^<gS0tP31?7GP7f]RaO3b8bLb^bUbVbLb5b6Q0VN:1?Q0Z=7WVRR#|%@R%@W;WVQ0G$0FRp%9R%9WPp%<RRR#_Q0GPOPOQ0Z,>N1>NVRq%<WRrEc1hRrCSCS40EQ02f[Rr?7VWRR#|%@R%@r/1WPp%9R%9rPp%<RRR#_Q0GPOPOPq1>NW%<rRqEc1hRqCSCS3`PrPVP`PcA7`WrRqQ0VPcQ0VPfPrP2PWPrf_RRCXQ0V1YarPqGfFdP3A7ar`#|A7c`aRr#@%@c/1aPp%9r%9cPp%<rRr#_Q0GPOPO1>N`1>NaR`%<cRqEc1hrqCSCS3`Q02A7RacRq#@%@R;WcPp%9q%9RPp%<qRq#_Q0GPOPOP`1>Nc%<RR`Ec1hq`CSCSPRPaPffbRaA7fcRR`Q0WPaQ0WfdS0uPRP2PcPRfcRqCXQ0W1Y7RP`GfFdP3A77Rf#@%@7;WfPpA7af7RR#9%9aPp%<RRR#_Q0GPOPO1>Nf1>N7Rf%<aR`Ec1hR`CSCSQ02A7q7aR`#9%9q5PpPp%<`R`#_Q0GPOPOPf1>Na%<qRfEc1h`fCSPqP7Q0uffR7Q0u?7aqRfPCP7PCfhS0vPqP2PaPqfgRaCXPCfeRC/YqPfGfFdP3Q0u97Cq#9%9C5PpPpQ0u=77C#<Rf#_Q0GPOPOQ0u,>N1>NCR`%<7RREc1hfRCSQ02A7aC7#<RRQ0GPOPOP`1>N7%<aR`Ec60lp1hR`PaPCQ0vfjS0wQ0v?77aR`PWQ0wPWflRRPaP2P7PafkRfCXPWfiS0x/YaP`GfFdP3Q0xQ0v77a#<Q0GPOPO1>NaQ0v,>NQ0x#<Ec60lpQ0wQ0vQ0x37#<Q0w#<'hQ0wQ0vQ0xPcH1>Q0v$0I,rNQ0x'LfnR`Q0w/;fQ0w#4%=f';5^O+1=1b`cPYPXPTPQPZP\PFP_foRc/:K%0cfqRW/GK\b[1:WK%0WfsRr/GK\b[PhP[PiPE&1<6RsPk%gKS0y=~le-0VlPoP8b>b?b@%BKS0zg01A?S0{[P3b8bLb^bUbVbLb5b6:1:fK13fKRt,TK1AfK'1,LfPYPXPTPQPZP\PFP_fpRu/:K%0ufrRv/GK\b[1:vKS0|%0vRwftRx/GK\b[Ry1NvK1RxK\b\wP9Q0bO1P[g01@`Rw$07Rz$07R{$07R|$07S0}$08S0~&08{R{20k6wS10'I'IS11Q0=$19-186RwQ0~60j6B0j6w{Q10'I'I/ki'kPEPsP4Aaj9sS12P5PsP9PsP9%u9S13I0iDMPkPlPlQ0y>0U6m%JLS14'D-0gBPnPlAileBS15PnPlQ14=~lePnPl%JDS169ileS171vl<RD5olS18Pn%KJRJ#g:0U6m%KHRH#gS1960U6=~lBClFQI0TPoP8b>b?b@X36X=6XA6XH6X<g1TK3/1:,L5%C4S1:%B=%C=S1;/5;S1<1T9J/TH/L=[[[[^36^=6^A6^H6^<gP3fvRL/?GfuRw/AKR}PLPw13wKQ0FfmP`PvO9b8bebUbVbLc0Fbeb5b6bD1TtJ/TH/Lf13RK/TJRJ/TH1A3H#BXC6225JHPRP3I0:bD:24fR11fR#4%4f%=R'1'LRfePfPYPXPTPQQ0>#FRf$10RJ#KRt-0AAS1=Q0_%0t203AtR~#C[S1>[S1?B0?At5V^XG]S1@%0~\^^G]S1APZP\PFP_Q0|Py1:xK%0xS0|1GLK\b[PhP[P<Q0bO1RyQ1>Q0~&08|S1B&08zQ10'IS1C'I'I/kiPEPsP:Q0cP5PjP:PsP:PsDMDMPkPlPl1vl=S1DQ0[#6S1E#JRz%gSS1F5HlPnPlPlQ0@#FS1G#JS1H,DmPzPnPlQ0nPnPlQ1H9ileS1I=olDPnPlAHlemS1JPl%gAS1K&0=J60D6S1L-0dmH0<FQE]E{PoP8b>b?b@X36X=6XA6X<gXJgAq:5S115:S1M/24Q1:Q1<129~,Z9[[[[^36^=6^A6^<g^JgP3fxRJ/?GQ0^PJPMfwRzP1P`PcPxO9b8b1b7b;b0b9b7b:b1b5b6-17R%6U#s$0[$0C#KS1N%4RRRQ1N%6fS1O#6S1P#KRf-03ARU'1S1Q,2R3`PYPXPTPQ20AAfRRQ0_%0f%CU[R1[R|B0?Af5V^XG]Rf%0US1R\^^G]RUPZP\PFP_1:rK%0rS1S%0}\b[1:wKS1T%0wS1U1GzK\b[S1VPhP[PyP1PiPEQ0mPkPlQ0pPnQ1JClPoP8b>b?b@X36X<gS0p%05S1W\d^36^<gS1XP3fyS1Y/?GQ1YPwO3b8b1b7b;b0b9b7b:b1b5b6-23`%=`Rd12d`'Z11`cRd#4R}%KIRI-03ARt,23XC6PYPXPTPQQ1=Q1?Q1@Q1APRP|PfPUPZP\PFP_1:LKS1A%0LS1@1GJK\b[S1?1:JKS1=%0JfzS1Z/GK\b[S1[PhP[PyP1Q0FQ0bO1RhQ1>Q1C,I{Q0~Q1BQ10'I'I/kiS1B'kPEQ0cAas:jS1C7a5S1>PkPlPlQ1DPlQ0\#JRjQ1F+0dH0<S1FPnPlQ0e=HljS1\PnPlQ0nPnPlQ15=olDS15PnPlQ0e9HleS1]PlQ0eQ1L+0dH0<FQFQPoP8b>b?b@X36X=6XA6X<gXJgAq:4SS1LQ0kQ1:%C9S1^/5;S1_119=S1`#0S1aQ1`;q~[[[[^36^=6^A6^<g^JgP3f}R~/?GQ0^PMP~f|S1bQ0XPrPxQ1YO9b8b2b1b7b;b0b9b7b:b1b4b2b5b6-17dQ1NQ1Q,2}7`}PYPXPTPQPRP|PfPUPZP\PFP_Q1TQ1V1:zKS1c%0zQ1Y/GK\b[S1d20AAIR}Q0_%0I%Ct[Rd[RSB0?AI5V^XG]RI%0tS1e\^^G]RDP5Q0bO1RjPdPyP[PhP1PiPEQ0mPkPlPlQ0oQ1N#gS1fQ1KQ1P$0=60D6'D9HlmPnQ1K>0D6NS1P9HlmE{PoP8b>b?b@X36X<gQ1Q9q53125t[^36^<gP3Q1Nf~R{,1~#4S1g'2Q1gQ0KO3b8b2b1b0b;b0b9b7b:b1b4b2b5b6bD%4`%=c'1S1gP4I0:Q1g/2t&22uS1gP`%9WS1h/erS1iA7WcuS1j#9PqI21S1k1brqS1l18wuS1mP2PcPuPxCXS1nPq&0buS1o,1vS1pQ1jI0LS1q'5PpQ1hPWPc%9vS1r/exQ0u,e3H1|X_pQ1gP`Q1iQ1h/eqR`H1{Q0:g05M[+1z#BS0:Q09g04Umg04Vh'15P6S09&0Iu,rNS1gg01I:Rp'A#BS0u%9xS1s/e7R7&0IW,rNS1t#41>Nr,rN$0`S1u#=405[[[S1v&1x`S1w'5Q1i01w`Q09&0Ic,rN/Ap#BS1i%9rRp/eCQ1g1>Nv,rN$0`S1x405[[Q1hQ1hPrPqQ1r-1v3$0cP3WDZ0LOP9J1uQ09Q1iPWQ1u:0573XC6PvB057v3XC6PpPwPWPv1;WvS1r%4W%=vS1y';S1z5^OPYPXPTPQPRP|PfPUPZP\PFP_Q1cQ1dQ1Y/:KS1{Q1Y#0f{S1|/GK\b[S1}P}PSPIPDPjPdPyP[PhP1PiPEQ0mPkPlQ0nPnQ1JClPoP8b>b?b@X36S1~Q0rQ1W[^36S20P3p+01@RpPzO2b8b2b1b0b;b0b9b7b:b1b4b2b5b6PYPXPTPQPRP|PfPUPZP\PFP_Q1cQ1dQ1{Q1}P}PSPIPDPjPdPyP[PhP1Q1BPEQ1>PkPlQ1FPnPlQ1\PnPlQ0nPnPlQ15PnQ0eQ1P5HlS1PFQFQPoP8b>b?b@X36X=6XA6X<gXJgQ1LQ0kQ1:Q1_Q1`/2t[[[[^36^=6^A6^<g^JgP3p+01AS1L/?GS0kQ0^PMQ1LPpQ0ZPLPzQ1bO9b8b2b1b0b;b0b9b7b:b1b4b2b5b6PvP3P311vrCOg01?_p4p710S0^&0F3R7&0F5RCQ02A^:459E:3AE95:AE954+0RR`[AE:34AE:35+0RA^9:49E95[S02A^=9:9E=4\`P:P4P5P3H1sP3n2001000000120000000XI4WgW_WYS1_Q0^Q02^I4^gC^_7]YS0^P3PO1;xwS02%4xS1`%=w';S0e&0^4S15Q15Q025EOQ15Q0e5EOPxPwP4PYPXPTPQPRP|PfPUPZP\PFP_Q1Z/:KS1\Q1Z#0S1FQ1b/GK\b[S1>Q1b/:KS21Q1b#0S221G{K\b[S23P}PSPIPDPjPdPyP[PhP1Q1~Q20P3p+01CR7Q1ZO2b8b2b1b0b;b0b9b7b:b1b4b2b5b6PYPXPTPQPRP|PfPUPZP\PFP_Q1\Q1>Q21Q23P}PSPIPDPjPdPyP[PhP1PiPEQ0dPkPlPlAHlmBPlQ0f,Dm-0QBH0<RCPnPCClPoP8b>b?b@X36X=6XA6S0dP3P5P51134COP5P4P4Q1MCO[^36^=6^A6S1MP3p+01DRCQ0OP7Q0IO4b8b2b1b0b;b0b9b7b:b1b4b2b5b6I0O413O5bDWPXS6L12Q1xPYPXPTPQQ0]#KR`-0AAS1xQ0_%0`203A`S24#C[S25[S0_B0?A`5V^XG]S26Q24#0\^^G]S27PRP|PfPUPZP\PFP_Q1{Q1}Q1|/:KS28Q1|#0S291G~K\b[S2:P}PSPIPDPjPdPyP[PhP1Q0JQ0bO1S2;Q25PiPEQ0mPkPlPlQ0nQ1KQ0?$0=60D69ilmPnPlQ0nPlQ1KQ0]$0=60D6-0QmH0<E{PoP8b>b?b@X36S0]Q0r@0N3GQ0sQ2480N5[^36S24P3PCPpO2b8bEb2b1b0b;b0b9b7b:b1b4b2bBbEb5b6PYPXPTPQPRP|PfPUPZP\PFP_Q1cQ1dQ1{Q1}P}PSPIPDPjPdPyP[PhP1PiPEPsP:Q1CP5Q0cP:PsP:PsDMDMPkPlPlPlPeQ1HPnPlPlPeQ0yPnQ1JE]E]PnPlQ0\#6#J9ilePnPlA~lmeS0\PnPlQ1IQ1D5olPnQ0\FQFQPoP8b>b?b@X36X=6XA6X<gS1IQ1W%04S1D\b[Q0<%B4Q1^/5<%B9[[[[^36^=6^A6^<gS0<P3Q0kPpQ1LQ1L/AKS0kP<PzQ1|Q1bO8b8b2b1b0b;b0b9b7b:b1b4b2b5b660~vI0;Q1gP;I0;W]W\H0\Q1vQ1wQ0:Q09Q0uPv21qwaR`%431>Nx,rN$0`#=405XC6Pr%4rS1w%=3605`XC6Q1sPL%4vR`%=rS1s1;vrQ1s,;`S1v5^OPYPXPTPQPRP|PfPUPZP\PFP_Q1=Q1[Q1\Q1>P}PSPIPDPjPdPyP[PhP1PiPEQ0mPkPlPlQ1f=HlmQ0oPnQ1JE{PoP8b>b?b@X36X<gS1iQ1N?`35Q1W[^36^<gS1gP3Q1L#4R`Q1Q'2P`Q0LO3b8b2b1b0b;b0b9b7b:b1b4b2b5b6PYPXPTPQPRP|PfPUPZP\PFP_Q1=Q1[Q1\Q1>P}PSPIPDPjPdPyP[PhP1PiPEQ0c?a5sS0cPkPlQ1PPnQ1PClPoP8b>b?b@X36X=6Q0i/2tQ0j/2t[^36^=6P3p+01BRt#=P`Q0NO3b8b2b1b0b;b0b9b7b:b1b4b2b5b6Q1wP3P3Q1w%=xS0j'1COQ1_Q0^P3PO1;wLS0i%4wS1P%=LS1^';S1HQ15Q15Q0i5EOQ15Q1H5EOQ1PQ1^P4PYPXPTPQPRP|PfPUPZP\PFP_Q28Q2:1:~KS1C%0~S0s1GpK\b[S0rP}PSPIPDPjPdPyP[PhP1Q1iQ1gP3%4CS0?Q1Q'2Q0?Q0QO3b8S0Qb2b1b0b;b0b9b7b:b1b4b2b5b6PYPXPTPQPRP|PfPUPZP\PFP_Q28Q2:Q1CQ0rP}PSPIPDPjPdPyP[PhP1Q0dQ1MP3p+01ER`#=S2<Q0OQ0?Q0IO4b8b2b1b0b;b0b9b7b:b1b4b2b5b6I0O40}O5bDWPXS6L12Q1uPYPXPTPQQ1xQ0_Q26Q27PRP|PfPUPZP\PFP_Q1\Q1>Q21Q23P}PSPIPDPjPdPyP[PhP1Q2;Q25Q0]Q24P3P`Q1LO2b8bEb2b1b0b;b0b9b7b:b1b4b2bBbEb5b6PYPXPTPQPRP|PfPUPZP\PFP_Q1=Q1[Q1\Q1>P}PSPIPDPjPdPyP[PhP1Q1IQ0<P31?tGQ1LPt1AtKS0<P<PJQ1bP~O8b8b2b1b0b;b0b9b7b:b1b4b2b5b660~rI0;Q1tQ0EI0;Y0CW]W\Q1h01pqFz%<WS1h$0qQ0GPOPO1>Nc1>NuQ1hEcQ1h$1oQ1h$1nQ1h$1kQ1h$0WQ1h$1jQ1h$1iL1h01fW#9Q0HJ0>Q1keQ1lQ1qP9Q1j#|Q1m#0S1mQ1j#@#pS1j1bPqS1qQ1n00SqS1nQ1p-0@qS1lQ1p#0S1k'5S1h'5S0G'5S0:'5RN'5Q0LQ1mPNPYPXPTPQPRP|PfPUPZP\PFP_Q1TQ1VQ1cQ1dP}PSPIPDPjPdPyP[PhP1PiPEQ0cPkPlPlPBPmPnB0H6mB9HleE]PoP8b>b?b@X36X=61253S1m1854#0[^36^=6P3P{PCPJO3b8b2b1b0b;b0b9b7b:b1b4b2b5b6Q1jQ0:PYPXPTPQPRP|PfPUPZP\PFP_Q1TQ1VQ1cQ1dP}PSPIPDPjPdPyP[PhP1Q0}$07S0}$08S0:Q11'I/kiPE%u;S11P;PsP;PsDMS1jP4Q13?a;sS09P5PsP;%u=S0uP:%u<S1t9as;DMDMPkPlPlPmQ0A#JS0AQ16'DPnPlPlQ0AQ1E#FS1E#JS1I+0gPnPlPlQ14-0QePnPlPlQ1IQ16'D/DBQ0fPnPlPlQ17Q0F,vlS14PnQ0gE{E]I0TI0TE]PoP8b>b?b@X36X=6XA6XH6XM6XN6XO6X<gAW3<:1L;=Q0D11;<?x9=Q0DQ0H'511=<S0g/2;[[[[[^36^=6^A6^H6^M6^N6^O6^<gP31?{GS24%@pP~&0epP{Q08Q07A7p~{#@Q0UQ0XPwPzQ1ZO=b8b2b1b0b;b0b9b7b:b1b4b2b5b6Q1qQ0GPPPrPqQ0WP9I1dQ1nQ1hP2PuPWPwCX9E23Q0520PWv=P25AE25L&004RP&014RN11PN&00:RNP3P3&01:,1NS05COQ0v&0^5RPO1S0v[^C6%4NP3P3Q05#4COQ0v[^X6'57`M'Z'ZP320Pvr=P24P220PrxS0v&003S05&013RNQ05/1N&005RNP3P3&015,1NS05COQ0wPPO1S0w[^C6%4NP3P3Q05#4COQ0w[^X6'57`M'Z'ZXf2Q1SQ0|AxrxMS1SPxP3P311xwRNCOS0wQ0xPPO1S0x[^C6S05Q1`P3P3%4NCOS1hQ0x[^X6S0G'5S1q'5RN'5PYPXPTPQPRP|PfPUPZP\PFP_Q1{Q1}Q28Q2:P}PSPIPDPjPdPyP[PhP1Q1~Q20P3PtQ1YO2b8b2b1b0b;b0b9b7b:b1b4b2b5b6Q0|PNPYPXPTPQPRP|PfPUPZP\PFP_Q1{Q1}Q28Q2:P}PSPIPDPjPdPyP[PhP1Q0pQ1XP31?7GP7P{O3b8b2b1b0b;b0b9b7b:b1b4b2b5b6Q1SQ1qPYPXPTPQPRP|PfPUPZP\PFP_Q1{Q1}Q28Q2:P}PSPIPDPjPdPyP[PhP1Q0hQ0lP3PMP7PtPJO4b8b2b1b0b;b0b9b7b:b1b4b2b5b6Q05Q0GQ0wQ1YQ0iQ1H5^OPPQ1_Q0^P3PO1;LzS1H%4LS0G%=z';RPQ15Q15Q1H5EOQ15=EOPPLPzP4PYPXPTPQPRP|PfPUPZP\PFP_Q21Q231:{KS05%0{Q0k#0\b[S0kP}PSPIPDPjPdPyP[PhP1Q1~Q20P3P`Q1bO2b8b2b1b0b;b0b9b7b:b1b4b2b5b6PYPXPTPQPRP|PfPUPZP\PFP_Q21Q23Q05Q0kP}PSPIPDPjPdPyP[PhP1Q0dQ1MP3p+01FRNQ0OP`Q0IO4b8b2b1b0b;b0b9b7b:b1b4b2b5b6I0O413O5bDH0xWPXS6Q1h11wL#4Q0GP4P4P3COXC6P3Q1PQ1^'1S1^Q0FI0:Q1PP5P5Q1^COQ1ZQ1H=^OPQ15Q1_Q0^P3PO1;zJS0^%4zRP%=JS1_';S15&0^:S1^Q1^Q0^5EOQ1^Q155EOPPQ1_P:PYPXPTPQPRP|PfPUPZP\PFP_Q1CQ0r1:pKS1_%0pS1^Q0<#0\b[S15P}PSPIPDPjPdPyP[PhP1Q1iQ1gP3%4NS1gQ1Q'2Q1gQ0RO3b8b2b1b0b;b0b9b7b:b1b4b2b5b6PYPXPTPQPRP|PfPUPZP\PFP_Q1CQ0rQ1_Q15P}PSPIPDPjPdPyP[PhP1Q0dQ1MP3p+01GS1M#=Q0NQ1gQ0IO4b8b2b1b0b;b0b9b7b:b1b4b2b5b6I0O40}O5bDH0xbPWPXS6FzFzQ0v$00S1hQ0v$01S0vQ1hQ0v'120PxwS0v$00S1hP3P3Q1hQ0v$01'1S0vCOQ0x[^C6Q1h#4P3P3Q0v#4COQ0x[^X6'57`M'Z'ZeP:P3J0wWDP3O1AE24zPJPzPaQ0WQ0EP:P3K1bW}P3O1n200100000021100010000WDXf2Q1neQ1lQ1kPq1;cuS1k%4c%=u';S1l5^ORq,VOS1n#U,1vQ1pPrPvPqQ0TH1aQ0;Q1k,VOS0TQ1l,VOS1p+1`S0WQ0;%U3S0x1YrWRq5xrWhQ0T#UR2Q1p#U'1Axr3qXC6PcPuPYPXPTPQPRP|PfPUPZP\PFP_Q1TQ1VQ1cQ1dP}PSPIPDPjPdPyP[PhP1Q1~Q20P3P~PwO2b8b2b1b0b;b0b9b7b:b1b4b2b5b6PYPXPTPQPRP|PfPUPZP\PFP_Q1TQ1VQ1cQ1dP}PSPIPDPjPdPyP[PhP1Q0qQ0tP3Q24P{Q1ZO3S24b8b2b1b0b;b0b9b7b:b1b4b2b5b6H0u13uK=W2A%=WS0t01\0Q0t#BR2&0M2+1[Q06Q1y#BR2&0M2Q1v,VOQ0B#6#s#KR2>04rA'mP3Q1s#BS1sP6P0Q1`=[O3B04w2AS0B'mXC6Q0;Q1w/10Q0=#KRr'8S0=/3KS1vQ1w/3KRc'8Rq/1rS1y$0YS06Q0;Q0xQ0B'2WhQ1w/8rS0q/3KRa/8cS20$0t&0tqPrPrP6P6\6RMQ01Q01Q20PqPM\6RqQ01't&0saQ1v$0sPcPcP6PMQ04Q04PaQ1vQ04,tqQ0q$0rQ0=$0rPKPKP6PMQ03Q03Q0qQ0=Q03,tqPYPXPTPQQ0i,VORq#\S0i%nqS03PRP|PfPUPZP\PFP_Q1\Q1>Q21Q231N~KS0=Q0s1RpK\b[S0sP}PSPIPDPjPdP;Q0bO1S0qP[Q0CQ0bO1S04P1PiPEQ0mPk%grS1v:0H6mS011DmeQ1v60H65~lPoP8b>b?b@X36183rRq1130/8r'L^36P3Q0?O1b8bBb4b0b;b0b9b7b:b1b4b2bBbFb5b6L0K%yKJ0ZL0K%ycJ0ZL0K%yrJ0ZQ20/1rQ1y'LQ1`/8r/3KQ1`/3KS1y'8/1r&0Y3B04L2AS20'mXC621Yw2Q1U%C21Rz2[[Q1P/8rRMQ1PPKPYPXPTPQQ0^,VORa#\S0^%naS1UPRP|PfPUPZP\PFP_Q21Q23Q05Q0k1NpKS1~Q1^13tKS0v#0\b[S1^P}PSPIPDPjPdQ0qP[Q04P1PiPEPsPkQ0y9ilePoP8b>b?b@%CKRaP3b8S0ybBb4b0b;b0b9b7b:b1b4b2bBbFb5b6PYPXPTPQQ0^Q1UPRP|PfPUPZP\PFP_Q21Q23Q05Q0kQ1~Q1^P}PSPIPDPjPdQ0qP[Q04P1PiPEQ0mPkQ01=HlmPoP8b>b?b@X3612q3^36P3Q1gO1b8bBb4b0b;b0b9b7b:b1b4b2bBbFb5b6I1X13MKQ1P/3K'2PYPX18Pr/3K13PK'8/1rRM$0YS1g#US0113J2S1U/1ARq'220J0MS0^/2qP6P6Q00P3XW6S1hQ00Q1m$1WXS6XW6Q01Q0^Q1hQ1hQ0;Q0x#yWWQ1gQ0^Q1h20J03XW6PMPM%yMI1VJ1UPqPq%yqN<1TPTPQQ1Y9[OJRq#\S1h%nqS0^Q1Y#4Rq/8r/3K13qK'8/1rRq-1Z0%Cq20J0qRM<0vq%BM9`q0+0RQ1Z#4Rq/8r/3K13qK'8/1r-0J0P6Q1b/N2S1gQ22%02S0;1R{2[[S22Q1b#4Rq/NK%0q%4{/RK\b[PRP|PfPUPZP\PFP_1:tK%0tS0x1ACKRq#0\b[%47/8rRM/NK%0M%4`/8r/RK\b[1:`K%0`Q1M/AKS01#0\b[1NNK%0Np+01HRM/RK\b[P}PSPIPDPjPdQ0EQ0bO1S1mP[Q0HQ0bO1S00P1Q0}$07$08S0}Q0:Q10'I'IQ0}Q0:Q0~Q10'I'I'I/ki'kPEQ09?a;sP4PsP:Q1tP;Q0u?a;sDMP5PsP;Q119as;P;PsI0iDMPkPlPlPlPeQ16PnPlPlPe%g2PnAHleBS16E]E]PnPlPlP>P?P?P@PlQ14PlQ1E#6#JR@Q1E#F#JR?60H6Q1v'D-0gmH0<Q0C,vlQ0\5olK1]PnPlPlP@P?PnPlPlQ1fQ1O#J5HlQ0H,vlPnPlQ0A9ileS0APnPlQ17Q0J,vl5olPnQ1K,DB9HlmS17FQE{E]FQPoP8b>b?b@X36X=6XA6XH6XM6XN6XO6X<gXJgXcgXdgQ1DQ0;%0:[[Q0E18<;/1r80v5Q0F%B5'5+0RQ0E,2;Q1NQ0J7`;Q0DQ0DQ0I'5AW<;A[[[[[[^36^=6^A6^H6^M6^N6^O6^<g^Jg^cg^dgP3p+01MR</?Gp+01LR?#4R@Q1Q'218@r/3KS1Q13@KS0D'8/1rR>/20%C>Q0DQ1QP@P?P<13<2Q0OQ0IQ0NQ0PQ0VPCp+01IR@OAb8bQbBb9b0b9b7b:b1b4b2bBbEbQc0Dc0Ec0ObbbFb5H1Rb6bZbTQ1`/10/8r/3KQ1y'8/1rP3I0:bT1TcKRcQ06+1^,VOQ06-1_cJ0>Q1w=[O0B04x2A'meQ0jP3J0>WjP3O1Q1s$0MQ1wQ0jPYPXPTPQQ0iQ03PRP|PfPUPZP\PFP_Q1\Q1>Q21Q23Q0=Q0sP}PSPIPDPjPdQ0qP[Q04P1Q0QbBb4b0b;b0b9b7b:b1b4b2bBbFb5b6PYPXPTPQQ0iQ03PRP|PfPUPZP\PFP_Q1\Q1>Q21Q23Q0=Q0sP}PSPIPDQ1L00oKQ0z$0MRcQ0v,TKQ0<'1,Lt[211tK1A7KRr#0S0<@0NrK\a20{7K1?K0Rr1?Kq?qq0[20nCKQ0z13`KS0v#B[20y`KQ0z1ANK/LN[g0371Rq20zNKR>eP>20oNKQ1MQ1M/3K,TKQ01'1'L\cQ1M011K1AMKRc1?cK'Z\a20{MK1A@KRM,?K?qM0\r20n@KQ0zp+01JR@/3K#B[20y@KQ0zp+01KRr/AK/Lr[Pq20zrKRqePqP9Q0a20p0K'tPaeRaO11A?KR?1??K'ZQ0HPaO1p+01N/AKRa1?aK'ZP4P^Q0OP3P5O2XI]Q1e^I]Q0NQ0bO1PdP=P^Q0RP3P5O2XI]Q0`^I]Q0SQ0bO1P[Q0EP^Q0UP3P5O2XI]Q1R^I]Q0VQ0bO1P1PiPEQ0mPkPlQ0\-0VlPnPlQ1JQ0o5olPnQ0nFQPoP8b>b?b@X36X<g%B3Q0{[Q1W/54Q1:[[^36^<gP3p+01YR]#=R^/2]P^Q0YPVO4b8bBb2b`b4b1b`b0b;b`bZba%=<#CebnbmblbbbabsbrbqbpbobZbTb;b0b9b7b:b1b4b2bBbFb5b6H0uQ1wQ0j5[OR<#URVQ0j/3K;WAQ0[#KR^-03A,3wR]Q1P/;3,}ORaQ20'2XC620Gw^S20133K=WaAXC6P3P]PYPXPTPQQ1H,VORa#\%na20GJ^9[OPRa#\%naPRP|PfPUPZP\PFP_Q21Q23Q05Q0kQ1~Q1^P}PSPIPD20G7^Ra/NK%0a20G`^/RK\b[P4Q0bO1PdQ1mP[Q00P1PiPEPsPk%g^9HlePoP8b>b?b@%0^P3b8bEb2b9b;b0b9b7b:b1b4b2bBbEbRbFb5b6:1gw^S0bI0:Q1`=[O]B04]KA'm13LHR]/3KQ0G13zH5[ORz#UR^?W3AXC6P31THK,3LRwPLPHPKPYPX%\zS0G%0^S1`PTPQQ1hQ0^Q1Z/NHR^Q1F%0HRzQ1b/RH[[RaPRP|PfPUPZP\PFP_Q05Q0kQ1L/:KR?Q1L#0Q0<\b[R01NtKRqQ0x1RCK\b[RM137HRc/NKR>%0c13`H/RK\b[RcP}PSPIPDPjPdQ1mP[Q00P1PiPEPsPkQ19=~le-0VlPoP8b>b?b@%BHQ0{[P3b8bEb2b0b;b0b9b7b:b1b4b2bBbEbQbRbFb5b6PYPXQ0GQ1`PTPQQ1hQ0^P^PaPRP|PfPUPZP\PFP_Q05Q0kP?P0PqPMP>PcP}PSPIPDPjPdQ1mP[Q00P1Q0ybEb2b0b;b0b9b7b:b1b4b2bBbEbQbRbFb5b6I1OI0:Q1P=[O]11wA'mPYPX13JH9[OPRP#\%nPPTPQQ1YQ1Z5[ORP#\%nPQ1|/NHQ291R~H\z[Q1gQ22PRP|PfPUPZP\PFP_P?P01:7K%071G`K\b[1NCK%0C1RNK\b[P}PSPIPDPjPdQ0qP[Q04P1PiPEQ0cPkPlQ17PnQ17ClPoP8b>b?b@X36X=6AW35AAW54A[^36^=6P313r2%4@13rH';,}OQ0LO3b8bBb4b0b;b0b9b7b:b1b4b2bBbEbQbRbFb5b6b[b[Q20Q0bI0;Q0e,VOQ0B'meb[Y0;P3O1n200110N00021110P11100c0N%4uQ0t5[OB04W2A'mPYPXPTPQ%\<%0VQ02,VORV#\%nV1NL2Q1@Q0;Q1U#0[[PRP|PfPUPZP\PFP_Q1\Q1>Q21Q23Q0=Q0sP}PSPIPDPjPdQ0qP[Q04P1Q1BPEQ13P4PsP5PsP=Q1tP:Q1jDMDMPkPlPlQ0fQ0>#JR:Q1K'DPnPlPlPBQ0@#JR=Q1K'DPnPlPlQ1G#F#J-0QePnPlPlQ1I9ileQ14PnQ0f,DB,Dm1D=:Q0@#KR=#g'D,Dm5HlE{I0TE]E]PoP8b>b?b@X36X=6XA6XH6XM6XN6XO6X<gAW49ARAQ0E#CRmQ0C,5mQ0gQ0E,1;/1=,195x9[[\A[^36^=6^A6^H6^M6^N6^O6^<gP31?`GPCP`13`2Q0vQ0?Q2<';,}O1;C`,}OQ1MQ0MQ0LQ1|Q1LO<b8bBb4b0b;b0b9b7b:b1b4b2bBbEbRbFb5b6Q1r,}OQ1z,}O'11Yxv5xxebTbDQ0W#UQ0TQ1p+1NI0;Q1nQ1kQ1l61lOJ0>I1MPYPXPTPQPRP|PfPUPZP\PFP_Q1TQ1VQ1cQ1dP}PSPIPDPjPdPyP[PhP1Q0pQ1XQ24b8b2b1b0b;b0b9b7b:b1b4b2b5b6-1muQ1o#0PYPXPTPQPRP|PfPUPZP\PFP_Q1AQ1?Q1=Q1[P}PSPIPDPjPdPyP[PhP1Q1BPEQ13P9PsP9PsDMP4Q12P5PsDMPkPlQ16PnPlQ1JPnPlQ0APnPlQ18PnQ1]FQFQPoP8b>b?b@X36X=6XA6XH6X<gQ1WQ1WQ1;Q1<Q1a[[[[^36^=6^A6^H6^<gP31?pGP{Pp&0bpPtQ0KQ0ZPLQ1|O9b8b2b1b0b;b0b9b7b:b1b4b2b5b6bDFzFzFzFzc0@c0Ac0Bc0?c07c0>W]W\P5P3O2n2001000000121000000WDY08P5P3O2n2001000000121000000WDY0<P5P3O2n2001000000121000000WDY0:P5P3O2n2001000000121000000bIc0=bKW~WuP5P3O2n2001000000121000000WKWvP5P3O2n2001000000121000000WKWtP5P3O2n2001000000121000000WKWxP5P3O2n2001000000121000000WKWzP5P3O2n2001000000121000000WKY09P5P3O2n2001000000121000000bKc0KbiW|Y04W{Y05Y06WyY02Y01Y03WwY0MXC6Z0I6Y0JZ0H6WYWkZ0G6o"). Qed.

Lemma shad8 : forall a len, a mod 4096 = 0 -> shad (a + len) = shad a + shlen len.
Proof.
  intros a len Ha. unfold shlen. apply shad_plus. replace a with (a / 4096 * 512 * 8); [apply Z_mod_mult|].
  pose proof (Z.div_mod a 4096 ltac:(lia)). lia.
Qed.

Lemma step_commit : forall b G A k mo a len rsp,
  KI b G A k mo -> 0 < len < 2^41 -> len mod 4096 = 0 -> len <= b ->
  vm_backing_used mo + len + RESERVE34 <= LIMIT34 ->                  (* [comment removed for export] *)
  0 < a -> a mod 4096 = 0 -> a + len <= ATOP -> inW SB PA a len ->  (* [comment removed for export] *)
  map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 a) (Z_to_bv 64 len) = true ->
  adec_mmap ATOP len PROT_RW rsp = Some a ->
  let mo' := fixed_model mo F_FIXED a len in
  fstepS (NMmap a len PROT_RW F_FIXED) rsp (fp_ok (m_vm_lazy mo) A) (fp_ok (m_vm_lazy mo') A)
  /\ KI (b - len) G A k mo'.
Proof.
ltac2:(KReplay.run1 (kr_t_ATsafeAlloc ()) ["CANSEC1"; "Ops"] "p'0h07__sat13h17__sat11h24__x1h34__p1h47__arithh57__sat10h64cstrh79heq_NMAXZh84__x2h97__sat12h:7__sat14h;6__sat9h<2H0h=4__x3h>4__ffh?8__varmaph@5__withA7__sat15hB2HahC1chD4__p2hE4__x4hF4__x5hG1HhH7__sat16hI4__x6hJ4__x7hK2_HhL6__sat2hM1zhN3_H0hO6__sat1hP4__x8hQ2H1hR2HphS2P1hT2P2hU6__sat0hV6__sat3hW2HyhX3SZ1hY3_H1hZ6__sat4h[1yh\1Ah]1Gh^3HABh_3HBUh`3HGAha2HKhb2HNhc2HRhd2HWhe4Haalhf2Hbhg2Hchh3Hcehi4Hdechj2Hkhk4Hlalhl3Hlbhm4Hlenhn3Hmcho3LZ'hp1Mhq2M'hr3NL'hs3NLZht3REThu3SH8hv2SLhw3SZ0hx2Wlhy3_H2hz3_H3h{3_H4h|6__sat5h}1ah~2a0i001bi011ki021li033leni042moi053mo'i061pi073rspi081xp%0p%1p&0p&1p;2p;1p;5p;4p;3p;8p;7p;6p;9p-1R0p10000p4p710p9P0p1000\R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001:p4p710p9P0p10022p4p710p8p1002Ip4p70g0039R0p4p710R1p8p1003Wp4p70P1p8p1004Ep4p710P1p8p103Xap4p7210P1p8p103Y_p4p7210P1p8p1005;p4p70P1p8g00?fk20`Tg008Qk10ITg03\Nk50DTg006kj17Tg00_Hj1JTg00h\j1;Tg00`Dk207Tg01J2j2iTg00<Yj20Tg00Djk10RTg00ODj21Tg00@Fk113Tg05NZk410Tg00:kj13Tg00>8j19Tg007Pk108Tg00]?k206Tg00JSk30rTg03c9k10nTg03c[k40mTg03iQk20kTg00:Qj3CTg0061j1lTg00Cjj1<Tg03O1j2_Tg03[Uj2fTg03]Gk20;Tg01Omk11FTg007nk11=Tg0091k10_Tg00:1k10]Tg00;bj1|Tg00=5j1zTg00>nk10=Tg00A<k112Tg01A\j1KTg01Pkk10CTg01Qej18Tg01R]j1uTg00COR1j24Tg03Ohj2LTg04I?k20uTg01eHk10tTg00`ak20OTg01gfk10sTg03Caj2=Tg030ck205Tg031Kk304Tg031ok20qTg00gSk10pTg00h1k10oTg0107k202Tg00iAk20YTg00jGk10lTg00l0k20jTg00lRk20iTg00m>k30hTg00m]k40gTg00ZSj2:Tg00e1j1mTg00ePk20XTg00fWk10fTg010Zk300Tg05OOk80eTg055Yk40dTg03h>k10@Tg00Lgj2WTg05PPk30cTg03Z]j15Tg044Oj1PTg058\k20VTg059^k20bTg00]ek20TTg05:ak41HTg05;Xk21GTg01BYk30HTg041Gk10STg05<6j3}Tg05<ik11ETg03Skk21CTg01G6j2hTg050Nk71BTg00[LS00j2pTg05QLk11?Tg05=`k61>Tg03S0k11<Tg05RHm91;Tg01D[k30GTg05SRk70^Tg04T1k30ZTP0k603Tg00QZj4MTg00nOk118Tg00nmk217Tg00oNk316Tg0129k615Tg05TKj3{Tg00R5k40[Tg01F:k30QTg05@fk211Tg00idk30~Tg02<Ck414Tg04Llk40FTg05Lck40JTg00B6k30}Tg00BWk119Tg00f9k20|Tg016\j4xTg017Gj7wTg0193j8tTg00kLk60{Tg017kk70PTg015Gk30zTg0160k20yTg0137k31@Tg00g5k40<Tg00jik30xTg01hnk21DTg00KjS01k20wTg019WR0f0R2':p=Gf2R3f1R4/:2'4p>0N%72#7p=v%72#7#7#7p>0Ag00I^R5?C20p=ng03b>S02,12g00HeS03'0p=dg00SIS04g00SiR67C2p=oP3g02=@S05P4P2H14p=61002p=220;341002'4p=a1442,43p=Df5R7f4R8+0Tf3R9P3P4P2I0Dp=Af7R:f6R;g03mXS06Q05H0FP7%88/L9%83/L4H0J/42p=E20;34/42p>0U1f34/42p>0K%;2#;#;#;p=~%72#7#7#7#7#7#7#7p>0?1042,43p=gB0}893&194=C52'4p=]1034/42p>0E&0=4/42p>09P;P7Q06Q05H0FP8P9%83/L4H0J/42p>0vAC542p=r1i42,00p=@20|52p=cP3g01<RR<g01=1R=P=g01=QR>P5P4g01;kR?P2Cxg01>XR@Fwp=UP3P<P=P=P>P5P4g01?8RAP2CxP@Fwp=FP9P<P=P=P>P3P4P2Gtp>0MP4P<P=P=P>P2J0{p=bP3P<P=P=P>P4P2K0Pp>0B20X52p=qB0z542p=Hg01:S-0y2p=sg01;?RB@1@42p=kP5P8P9P5P3P4P2H0<H0<p=j20Y52p=?P5P4PAP2Cxp>0LP9P<P=P=P>P3P4P<P=P=P>P2P@FwK0Pp>01B0x542p=\P;P<P=P=P>P7P8P9P<P=P=P>P3P4P2GtGtp=^1142:0H93p=Z%|4%|25C5p=`AC934/42p=N%94=C32p>0WP5P5P8P9P3H0<P4P2H0<p=IP7P<P=P=P>P8P<P=P=P>P5P9PAP3CxP@FwP4P2Gtp=OP7P<P=P=P>P8P<P=P=P>P9P3K0PP4P2Gtp=T10931042'4p=>P4P2Q06Q05H0Fp>0aP8P9P31L42H0Jp>1JP8P9Q06Q05H0FP3P4P2H0Jp>1IP5P3P4P2H0<p=R1p42,43p>1A10931:42'4p=BP5P4P?P2Cxp>0>P5P4g01>1P2Cxp=yP4P<P=P=P>P2P@Fwp>1:P8P<P=P=P>P9P<P=P=P>P3P@FwP4P2Gtp=eg05UN-1D2,14p=Sg05VI,12p=Xg05W?,12p=Qg05X?,12p=Y1093/44/p2,48p=V20w52p=[1442,p3p>0:1434/p2p>0\20`55$0Ig03U?g00GJR@g03leP:P;P7P8P9I0D%G3S07g00H@S08#7R<#JR?%;<RA#7S09#7#;S0:#JRC+07RD80N3%7<S0;#vS0<#vRE#v$0A#JRF,i9#nf:RG,08&0R:/17#d%G:S0=f8RH/iF#nf9RI/1Hp,2rcRJ$13RK'0p,2SBRLp,2PARMPGPIH10f<S0>#3#9&08ERNf;RO+06206NG40r#o&0n5PKPOQ06PGH0mQ0>-0k53Cf>S0?f=S0@Q0>36P@POfCR@fBRPfAS0Af@RQf?S0BI0DP1%lQfDS0C#2RR%<Q#dp,5AbaseRS/_P1f@PQ0AQ0A5aP3D3DPQQ0BQ0?Q0AP@Q0AQ0B76QRTP@fERUQ0BQ0CP@PPPTEAGEP2%lPfGRT#2%<@#d1_SUfFRV/fUQ0C>0UUR3D3DP1fHS0D#2RRQ0C#<#d1_SVAaVUU:0KTV3DQ0CP@PPPUPTQ0C=6U@RWPTfIRXP@Q0DPTPVPWEAGEP2fJRW#2%<T#d1_SXQ0D>0UXR:0KWX3DP1Q0D#<#d1_SWfKS0E/fWAaWXX3DQ0DPTPVPXQ0EQ0D=6XTRRQ0EfMRYPTfLS0FQ0EPWPREAGEP2%<W#d1_SYfNS0G/fYQ0FQ0F5aY3DP1Q0G,_SfOS0HQ0GQ0G?aYY40KQ0FQ0EPWPYQ0HQ0FQ0E56YRWQ0HfQRRQ0EfPRTQ0HQ0GPWEAGEP21_STfRRWAaRTT80KRP1fSRZ/fWAaWRRPTQ0HQ0GPRPZQ0H96RTRTPZfUR[Q0HfTR\PZPWPTEAGEP21f[\Aa[\\P1fVS0I00;[%2[P\PZPWP[fWRWA6[\ZR\PWfYRTPZfXRZPWQ0IP\EAGEP220;ZW%2Z&1FJQ08#;S0J#;S0K#;S0L#;S0M#;S0N#;#~#~RJ#7#~#~#7#v$0A$0?$0?#J/0KS0O%;JRJ#~#~#7#v$0A$0?$0?#JRW7gKPV%lTP1&1=NS0P$0IRVfZR\$0_Q0P$0]R]3CQ03%3\R^#|%z\%9^R_$0=Q0PQ0P+0`R`&12KRaP_P^PKD]3D40EP\PTPZf[RZf]R^A6Z\TRZP^f_R\PTf^RTP^f\R_PZEAGEP2&0__=CV]Q03%3^R]#|%z^%9]RV$0=P`PaPVP]PKD]3D40EP1Q03%3TR]#|'0%zT%9]RV$0=P`PaPVP]PKD]3DPTP^P_P\faR_A6\T^RTP_fcR]P^fbS0QP_f`R^PTEAGEP2Q03%3^#|'0%z_%3_RT#9RV$0=P`PaPVPTPKD]3DP1Q0Q#zQ0Q#3RT#9RVP`PaPVPTPKD]+09Q0QP_P^P]feRTQ0Q=6]_R]PTfgRVP_ffS0RPTfdRZP]EAGEP2%zZP1%3TR]#9#K&0C]#K%8T#K%u]3DQ0R#3R]#9RbP`PaPbP]PKD]+09Q0RPTPZPVfiRZQ0R=6VTR]PZfkRbPTfjS0SPZfhRTP]EAGE[P2%3V#9#K%3TRV$0C#K%8T#K%uV3DP1%3ZRV$0C#K%8Z#K%uV'4Q0S#3RV#9R]P`PaP]PVPKD]+09Q0SPZPTPbfmRVQ0S=6bZR]PVfoS0TPZfnRZPVflRcP]EAGE[P2%3b$0C#K%8c#K%3c#u'4P1%8V#K%3V#u%3ZRb#9R]P`PaP]PbPKD]+09PZPVPcQ0T#8RcfqRb'LQ0T?6ZVRZPbfsR]PVfrRdPbfpS0UPZEAK0v[P2%KcQ0U#3#u%3bRc#9RZP`PaPZPcPKD]+0920ud\%<d&0Rd'rP]PdPbP^p,4NMAXR^$0tR\-0O5p,5NMAXZ/r\RceRZPc&0s^R^%2\R\ftRa/=FRe%2a%2FRffvRg/@F[[Rh205?CRi%G?S0V%2C%GD[Rj[Rk%2?Rlg036URmB04?C4UWBRC%2D\m^BlRn1=gFRo%2gfxRp/@F\f[RqP3g037M20q0?+0OQ0VeRrO1RsPj&0]BRt&0IBRB%c4S0W&0p5Ru&0o5Rv20250RwQ08-0Y5Rx5UvS0X&0l=R=AFvwxS0YH0M20jv>R>P2P3Q0400O620i23#odB0h504H0gR0b>b?b@X25S0Z%G2S0[%24S0\[^25S0]P2fzR6PdO2b4bLbUbObLbVb6b7PZPcP^P\PePhPiPkPCPnPoPqPsPjp-0RyPtPBQ0WPuPvQ0X1bv9S0^60BvS0_P=Q0XH0MP>P0b>b?b@X25W3Q0[/44S0`%G4S0a[^25^3yP2fyRz/:DPzPgO3b4bLbUbObLbVb6b7PZPcP^P\PePhPiPkPCPnPoPq%JERE-05?S0bQ0V%2E207?ES0c#G[S0d[S0eB04?E4VmXBlS0fQ0c#2\m^BlS0gP4PrO1S0hQ0dP7PrO1REPjg01@`Rq#mRo#mS0i#mRh#mS0j#qS0k%qhS0l20X5qS0m'H'H#s/ktS0nPB%c3S0oP4&0f5RqP9%c9S0pDjS0qPuPvPv1bv7S0rPvQ0K#?Rh2025WRe+0LH01S0sP=Pv%?<R<,\xR{=FvhS0tP=PvQ0XP=PvAUvw<S0u1bv;Rh60BvS0vP=2025?S0w>005NS0x9Uv{F^F^P>P0b>b?b@X25X85X=5X3yXDyAg93WS0y1143S0z/09S0{Q07%G8S0|/4:S0}1187S0~Q0c':[[[[^25^85^=5^3y^DyP2f|R|/:DQ0OPKP|f}R}P[P]fuR[PzO9b4bZbObUbObLbVbZb|b6b7Q0RL0eA6]dbR~#l%<~%<]/1b'0&0I`R`%8~%8]PdPdPbCZP`%3~R~#9%3]Rb#91`~bCNCN3DP1A6a]dRb#l%<b%<a/1dP`%8b%8aP]P]PdCZP`%3bRb#9%3aR~#91`b~CNCN40EPaP]PdP[fwR~A6[a]RbP~PzP]PpP~PgPbEAGEP2A6g[a#lA6~g[Ra#<%<~/1[P`%8a%8~PgPgP[CZP`%3aRa#9%3~R[#91`a[CNCN40EP1A6p~gR[#<%<p/1g'0P`%8[%8pP~P~PgCZP`%3[R[#9%3pRa#91`[aCNCNPpP~PgPzf{RaA6zp~R[PaP}P~P|PaP6P[EAGEP2A66zp#<%<6/1p'0P`A6a6zRp#8%8aP6P6PzCZP`%3pRp#9%3aRz#91`pzCNCNP1A6|a6Rz#8%8|PaPaP6CZ5C`P`%3zRz#9%3|Rp#91`zpCNP|PaP6P}p+01@R6A6}|aRpP6p+01BRzPap+01AR[P6f~R~PpEAGEP2A6~}|#8%8~P}P}P|CZ5C`P`A66~}#3R}#9%36R|#91`}|CNP1A6[6~#3R|%3[R}#960W`1`|}P[P6P~Pzp+01DR~A6z[6R}P~p+01FR|P6p+01ER6P~p+01CRpP}EAGEP2A6pz[#3%3p#960W`A6~pz#3%3~'`PpPzP~PgH0d&0@z,WN/r~B0c6~a116~#5%56%P~'1'rPZPcP^P\p+01HR6/=F%26p+01JRa/@F\f[%;AS10#;S11#;RA#JRz-05?S12Q0V%2z207?zRg#G[S13[S14B04?z4VmXBlS15%2g\m^BlS16PiPkPCPnp+01LRz/=F%2zp+01NRp/@F\f[PsPjPEQ13Q0kQ0l%qoQ0m'HS17'H'H#s/ktPBPqP9Q0oP4Q0pP9PqP9PqDIDIPuPvPvQ0rQ0J#7S18#?Ro=FveP=PvPvQ0;#;#?S0;,\xPoP=PvQ0XP=PvQ0;9UvwS19>0BvhP=PvQ0YPvQ0w&08A6005S1:-0LxH01F^EOETP>P0b>b?b@X25X85X=5X3yXDyAg94W1149/03Q07%G7S1;/4:%28?g8g[[[[^25^85^=5^3y^DyP2p+01PRW/:DQ0OPWPKp+01QRAPTp+01GS1<p+01IRTp+01MRhO9b4b0b1b;b5b1b9b0b:b6b7-0V|%7J#v$0A$0?#JS1=%5|RJPJQ1=Q10#7S1>#7S1?#JRJ-07?Ro'1S1@C>PZPcP^P\1=TF%2Tp+01KRe/@F\f[205?JR[Q0V%2J%Go[R}[RbB04?J4VmXBlRJ%2o\m^BlRoPiPkPCPn1=hFS1A%2hp+01OR]/@F\f[S1BPsPjPEP}PtPBQ0WPuPvQ0_P=Q0YH0MP>P0b>b?b@X25X3yS0_Q0`Q0\[^25^3yS0`P21:ADPAPpO3b4b0b1b;b5b1b9b0b:b6b7-0b|%P|S1C#2Q1C;g|Q1<,16S1CPZPcP^P\1=aF%2a1@zF\f[Q12Q14Q15Q16P[PbPJPoPiPkPCPn1=WF%2Wp+01RR|/@F\f[PsPjPEP}PHPrO1S16Q13Q0i#qS0iQ17'H#sQ0n'kPBQ0qPuPvQ0sP=PvQ0tP=PvQ0XP=PvQ0vP=PvAFvw{PvQ1:-0L{H01F^F^P>P0b>b?b@X25X85X=5X3yXDyQ0yQ0{Q07Q0}Q0~#2Q0~;gg[[[[^25^85^=5^3y^DyP2p+01URg/:DS1:Q0OPKPgp+01VRrPVPzPpP|O9b4bAb0b1b;b5b1b9b0b:bAbHb6b7+0VQ1=Q1C#5RVPVQ1@C>20aT6RVQ1<%8aS1C/LzS17A6aT6S13#8S15PzI1J20Tp6S14PhPzPeQ13I0DP`Q1CPTPTP6CZS12PaPTP6%8eS1D/Lh1L2hI1IZ02`PVQ1<Q17Q12/LzRVH1HQ05g05M[+1G#nS05Q06g04Umg04Vh'15C5S06&0@T,WNS1<g01I:R`'i#nS1E%8hS1F11zeS1G80HzS1H/L]S1I&0@a,WNS1J#5206Ne,WN$0SS1K#P3}[[[S1L&1EVS1M'4Q1701CVQ06&0@6,WN/i`#nS17%8zR611eaRV80HeS1N/LpQ1<206Na,WN$0SS1O3}[[Q1CQ12PzPzQ0PQ1DPaPaPTCZ,h2#oP6PePVP4Q0EPZPcP^P\Q1AQ1BP[PbPJPoPiPkPCPn1=AFS0E%2Ap+01SRT/@F\f[S1DPsPjPEP}PtPBQ0o?R4qS1CPuPvPvQ0u1bv8P=AFvx{ETP>P0b>b?b@X25X85X3yQ0a/43Q0z,04[^25^85^3yP2Q1:PgPrP|O4b4b0b1b;b5b1b9b0b:b6b7P2K1B1h46#o1WN4R6/1`/0e10V641AP1Q1F,h3#o1WN3R6/1`/0zQ1G/06'p%8pR6,h9#oP2%8]S1F,h8#o1WN7RV/1`/0]11]pS0u/0V'pP4WKWRP4P2O2n2001000000120000000bRWRY06&1?zJ1>Q06Q17P5PeQ1IQ1K7}2XM5P5PaQ1I?}z2XM5Q1NPpPePaPZPcP^P\Q1AQ1BP[PbPJPoPiPkPCPnQ0EQ1DPsPjPEP}Q0ZQ0]P2PrPpO2b4b0b1b;b5b1b9b0b:b6b7PZPcP^P\Q1AQ1BP[PbPJPoPiPkPCPnQ0EQ1DQ0bQ0eQ0fQ0gQ0hQ0dPEPjQ16P}Q0nPBQ0qPuPvQ0sP=PvQ0tP=PvQ0XP=PvQ0vP=Q0x9Fv{S0xF^F^P>P0b>b?b@X25X85X=5X3yXDyS0vQ0yQ0{Q07Q0}Q0~Q0c'0S0~[[[[^25^85^=5^3y^DyS0yP2p+01XRV/:DQ0OPKPVp+01YR`Q0UP]PAPgO9b4bAb0b5b;b5b1b9b0b:bAbHb6b7PzP2P2Q1GCBQ04&1<4S1GP6PhPhPzCZS0U'hg01MVS0{3CPWQ1GO1P6PhPzP4PYPZPcP^P\1=]FS07%2]1@AF\f[S0}P[PbPJPoPiPkPCPn1=TFS0c%2T1igFS0t#2\f[S0sPsPjPEP}Q0_Q0`P2p+01WS0`/:DQ0`p+01TRYO3b4b0b1b;b5b1b9b0b:b6b7P2PZPcP^P\Q07Q0}P[PbPJPoPiPkPCPnQ0cQ0sPsPjPEP}Q0ZQ0]P2PVPWO2b4b0b1b;b5b1b9b0b:b6b7PZPcP^P\Q07Q0}P[PbPJPoPiPkPCPnQ0cQ0sQ0bQ0eQ0fQ0gQ0hQ0dPEPjQ16P}Q0vQ0yP2p+01ZR6/:DQ0OPKP6p+01[S0OPdPAPTQ0`O9b4bAb0b5b;b5b1b9b0b:bAbHb6b7N91;40GWWX[5K0^Q1OPZPcP^P\Q1AQ1BQ0N#JRd-05?S1OQ0V%2d207?dRK#G[S0y[S0VB04?d4VmXBlS0v%2K\m^BlS0]P[PbPJPoPiPkPCPnQ0cQ0sPsPjPEP}Q16Q0yPtPBQ0WPuPvPvQ0XQ0wQ0:$0860059UvxP=PvQ0XPvQ0wQ0N$086005-0>xH01ETP>P0b>b?b@X25S0NQ0[@0N2DQ0a@0N4K[^25S0aP2PVPgO2b4bAb0b1b;b5b1b9b0b:bAbHb6b7PZPcP^P\Q1AQ1BP[PbPJPoPiPkPCPnQ0EQ1DPsPjPEP}PtPBPqP4Q0oQ0p7R9P9PqDjPuPvPvPvPwQ0;P=PvPvPw2025FP=Q0YEOEOP=PvQ18#;S0;#?S0o9UvwP=Pv1yxw-1:vRKP=PvQ19Q0r60BvP=PKF^F^P>P0b>b?b@X25X85X=5X3yS19Q0\%23\f[%G9%n3Q0|/4;%n8[[[[^25^85^=5^3yS0|P2Q1:PrPgQ0tP9PpPAP|O8b4b0b1b;b5b1b9b0b:b6b760ZaJ03Q1<P;J03WNWKCMQ1LQ1MQ05Q06Q1EP5PzQ0U/LWRa%52206Nz,WN$0S#P3}XM5P5Pe%5hRN%P25}aXM5Q1HP]%5z%PePZPcP^P\1=pFS1H%2p1@WF\f[S0UP[PbPJPoPiPkPCPn1=|FS1M%2|1@YF\f[S1LPsPjPEP}PtPBQ0WPuPvPvQ1=-025Ra=FvxQ0^P=Q0YETP>P0b>b?b@X25X3yQ1=/02RK/44Q0\[^25^3yP2Q0`#5RlQ1@'0PlPQO3b4b0b1b;b5b1b9b0b:b6b7PZPcP^P\Q1HQ0UP[PbPJPoPiPkPCPnQ1MQ1LQ0bQ0eQ0fQ0gQ0hQ0dPEPjQ16P}Q0kQ08$18-175Q0l6165Q0m'H'HS0l#s/ktPBPqP3Q0p?R7qP4PqP7%c7S0p?R7qP7%c8S0d9Rq7DIDIPuPvPv1bv:Q09#;#?RlQ0wQ1?$086005,\a5FvP=PvPv1yl{P=PvPvQ0L#?-0>wP=PvPvQ09#?S099UvwS0L1bvHP=Q0xETDeDeETP>P0b>b?b@X25X85X=5XE5XF5X3yXDyQ1@9g78Q0z,r7Q1;Q1;/4IQ0~[[[[^25^85^=5^E5^F5^3y^DyP21:`DQ1=116`S1;#5Rl'0PlP6P`%P`%56Q0AQ0CP|PrO;b4bAb0b5b;b5b1b9b0b:bAbHb6b7PNP2P2%Pz,1NCBQ04Q1GQ1F11phRN80Hp'hQ0{3CPAQ1GO1Q0TQ1Gp,8ABASE_SHP4P5%5NQ1@9gK2XM5P7%5p%Ph'1RKPHJ15Q1=PKPKQ1@C>Q00Q08#JS08P2P2Q0M#JS0MC>RK1SL2RNPW11W]S1@%XNRl'0%QNS1=PWQ1@Q1=#YS1GC>DVXC5#[PMP]Q0ug05Y5,1MRaC>PK%5NS0uP8%5lRm,:8Q1=#5S0TP8P8Q1G#5S0{CBDVXC5#[%5MRd/09%5aR?,:940:P~PKPNPA11AWS04/0lQ1=PAQ04Q1GC>DVXC5#[Q01P5PKPNP|11|AR~/0lQ1=P|P~Q1GC>DVXC5PKQ0uP;1:;mQ0TP;P;Q0{CBDVXC5#[10d71:7?40:S01P2PKPNPY11YTS1F/0lQ1=PYQ1FQ1GC>DVP1Q08P4P4Q0MC>1SL4Rl/0g11gYRN%Xl'0%QlRlPgPN%YlC>40\PKQ0uPG1:GmQ0TPGPGQ0{CBDVXC5#[10dI1:I?40:P2Q08P9P9Q0MC>1SL8Rl/0VQ0`,1VRN%Xl'0%QlRlPVPN%YlC>40\Q001SL7RlP`11`VRV%XlC>%QlRlP`PV%YlC>PKQ0uQ0?Q0?/:mQ0TQ0?Q0?Q0{CBDVXC5#[Q0@,0dQ0@/:?40:P21SL;S0?P6Q1;Q0?#XC>P11SL:S00Q0O'0Q0O/16S1GQ00#X'0PKQ0uPQ1:QmQ0TPQPQQ0{CBDVXC5#[Q0B,0dQ0B/:?40:S0BP21SLIS1=p+01]RQ'0p+01^S0A/1QS0~1SLGS0z#X'0PKQ0uP@1:@mQ0TP@P@Q0{CBDVXC5S0x#[S0wPdPPPPP?CBS1?P5Q0xPOQ08POPOQ0MC>S0M1SLOR@#5RlPPPP%X@#5CBS08%Q@S0h#5S0gPPPPQ0h#Y#5CBS0f'pS0eP:Q08Q0fp+01_RV={@4%5VS0b,0lp+01`/1VS0\Q0>,SLS0Y#XRl;{4Q0\#5S0^%5l'0PZPcP^P\p+01cRl/=FS0W%2lp+01e/@F\f[S17P[PbPJPoPiPkPCPnp+01gRl/=FS1<%2lp+01i/@F\f[S0tPsPjPEP}Q0j#mRl#mR@#q%qlS0jQ0m'H'H#s%m@#qQ0l'H#s/kt'kS0lPBQ0p?RHqS1:?RHqP3PqPH%c:S0rPHPqDIP4PqPH%c;S1DPHPqDIS0EP9%cHS1B9Rq8PHPqDjDIPuPvPvQ18#7S18#;#?S1AQ0J#?R@P=PvPvPxQ0;#7#?RlP=PvPvAFvl<Q0;#;#?RN,\lR~9Uv<P=PvPvQ1A/y~P=PvPvQ0<#?S0<-0>wP=PvPvQ10#?9Uvw1bvGP=PvAFvx<Pv20><@H01ETDeS10DeETEOEOP>P0b>b?b@X25X85X=5XE5XF5XI5XJ5XP5X3y1073104:PHP9P911HICB11IG,rH%GHR~Q0@,4~P;P:P:PHCB[[[[[[^25^85^=5^E5^F5^I5^J5^P5^3yS0@P2p+01kR~/:DS1A%P~S0;p+01lS0J#5S0[Q0J/1~#5S0XQ0JP~Q0D,SLRL#X#5Q0H%5LPOQ0>Q0GQ0Ip+01dS0Dp+01hS0:O?b4b0b1b;b5b1b9b0b:b6b7bQb<40GCMH0[40GWTWSP4P2O2n2001000000121000000W<P2O1Q0?#QS0?P6Q1;Q0?#YC>P1Q00#QS00Q0O'0Q1GQ00#Y'0Q0BP2Q1=#Q/0QQ0~Q0z#Q#Y'0Q0wQ1?P5Q0xPOQ0MQ0eP:Q08Q0fQ0h?{V4Q0gQ0b'0Q0\Q0Y#Q#YS0Y;{4Q0^Q0Y#5'0PZPcP^P\Q0WQ17P[PbPJPoPiPkPCPnQ1<Q0tPsPjPEP}Q0lPBQ1:PHPqPHQ1BDjP3Q0EP4PqP9Q0r9Rq8PHPqDjDIPuPvPvPlP@P=PvPvPxPNP=PvPvAFvN<Q0K#7S0K#7#?,\NRN9Uv<P=PvPv1ylNP=Q10DeETEOEOP>P0b>b?b@X25X85X=5XE5XF5XI5XJ5XP5X3yQ0@P2Q1AQ0;Q0[Q0XQ0JP~%QLRL#Y#5Q0H%5LPOQ0>Q0GQ0IQ0DQ0:O?b4b0b1b;b5b1b9b0b:b6b7bQb<40QCMH0[40GWTWSP4P2O2n2001000000121000000W<P2O1n200100000021100011000W<WgP4P2O2n2001000000121000000W<XC5P4P2O2n2001000000121108000W<P2O1PMPWQ1@PaC>P110MAQ04/0aQ01P210MTQ1F/0aPKQ0uPI1:ImQ0TPIPIQ0{CBDVXC5#[PdPHPHP?CBA{Mg4%5g,0d11rgRM?{a4%5M/0?PZPcP^P\1=`F%2`Q0O/@F\f[P[PbPJPoPiPkPCPn1=QF%2Q1@VF\f[PsPjPEP}Q0lPBQ0pPHQ1BPHPqDIP3PqPHQ1DPHPqDjP4PqP9Q0dPHQ0r?RHqDjDIPuPvPvQ1>#?RHP@P=PvPvPxQ11#?RVP=PvPvAFvV<Q18#7#?,\VRV9Uv<P=PvPv1yHVP=Q10DeETEOEOP>P0b>b?b@X25X85X=5XE5XF5XI5XJ5XP5X3yQ0@P2p+01aRV/:D%PVp+01bRH#511HV#5PHPVP?PUPdPOQ0>Q0CQ0FP6Q0AO?b4b0b1b;b5b1b9b0b:b6b7bQb<40QWTWSP4P2O2n2001000000121000000W<P2O1n200100000021100011000bXO2O240QWWX[5K0^Q1KPZPcP^P\Q1HQ0UQ1OQ0VQ0vQ0]P[PbPJPoPiPkPCPn1=YF%2Y1irFR6#2\f[PsPjPEP}Q16Q0yQ0NQ0aP2P`PrO2b4bAb0b1b;b5b1b9b0b:bAbHb6b7PZPcP^P\Q1HQ0UP[PbPJPoPiPkPCPnQ1MQ1LPsPjPEP}Q19Q0|P21:rDQ0`PrP6P9P]P|PTO8b4b0b1b;b5b1b9b0b:b6b760ZeJ03Q1JP:J03WYWNWKQ12011zCMCMQ15PGJ03Q13#lQ14#2RGQ13#<#dR|1_SzRS1fhzR]20;zeR6%2eRr'4Rd'4RU'4R?'4RV'4PPPGPVPZPcP^P\1=eFRe1@hF\f\rRfP[PbPJPoPiPkPCPnQ07Q0}PsPjPEP}PtPBQ1CPuPvPvP<PxP=B0~5x<9FvwEOP>P0b>b?b@X25X85104220T43#2[^25^85P2PTP`PpO3b4b0b1b;b5b1b9b0b:b6b7P|P?PZPcP^P\PePfP[PbPJPoPiPkPCPnQ07Q0}PsPjPEP}Q0jQ0kQ0iQ0m'H'H'H#s/ktPBQ0rP:PqP:PqDIP3Q0dQ1D7R:P4PqP:Q0pP9PqDIDIPuPvPvPxQ0<Q09'\P=PvPvQ0<Q0o'yP=PvPvQ0K#?-0>wP=PvPvQ0oQ09'\/\<P@P=PvPvQ0L1bvIP=AFv{@ETEODeDeEOP>P0b>b?b@X25X85X=5XE5XF5XI5XJ5X3y11;9,021r:7Q0=11:;/18/07Q0=/4O117;/0:[[[[[^25^85^=5^E5^F5^I5^J5^3yP21:TD%<gPY&0RgPTQ03Q02A6gYT#<PXPRPzPhPWO=b4b0b1b;b5b1b9b0b:b6b7PSPUQ0SP]PdQ0RP6PrQ0QP_CMCMCMCMCMCMCMbXbvbwbubtWNWKP4P2O2n2001000000121000000W<WoP4P2O2n2001000000121000000W<WrP4P2O2n2001000000121000000W<WqP4P2O2n2001000000121000000b~bsW{WzWxP4P2O2n2001000000121000000W<WyP4P2O2n2001000000121000000W<WYP4P2O2n2001000000121000000W<P4P2O2n2001000000121000000W<WNP4P2O2n2001000000121000000W<WKP4P2O2n2001000000121000000b<bGWjW_P4P2O2n2001000000121000000WGW`P4P2O2n2001000000121000000WGW^P4P2O2n2001000000121000000WGWbP4P2O2n2001000000121000000WGWfP4P2O2n2001000000121000000WGWpP4P2O2n2001000000121000000bGc05WiWnWdWhWeWBWcWlWkWmWaY07Z035X}5Y04Z015W\W]Z005o"). Qed.

Lemma step_recommit : forall b G A k mo a len rsp,
  KI b G A k mo -> 0 < len < 2^41 -> len mod 4096 = 0 ->
  0 < a -> a mod 4096 = 0 -> a + len <= ATOP -> covG G a len ->
  map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 a) (Z_to_bv 64 len) = true ->
  adec_mmap ATOP len PROT_RW rsp = Some a ->
  let mo' := fixed_model mo F_FIXNORES a len in
  fstepS (NMmap a len PROT_RW F_FIXNORES) rsp (fp_ok (m_vm_lazy mo) A) (fp_ok (m_vm_lazy mo') A)
  /\ KI b G A k mo'.
Proof.
  intros b G A k mo a len rsp HK Hlen Hlal Ha Haal Hce HCG Hmc Hdec mo'. subst mo'.
  pose proof HK as (M & Hb & HN & HAB & HGA & HBU & Hk). atop_facts. pose proof M as (_ & _ & (_ & _ & Wl & _) & _).
  destruct (MOK_recommit mo a len M ltac:(lia) ltac:(lia) ltac:(lia) Haal Hlal Hmc) as (M' & NL' & LZ' & _ & _).
  pose proof (adec_mmap_ret _ _ _ Hdec) as RET.
  destruct HCG as (g & Hg & Hg0 & Hg1 & Hg2). destruct (HGA g Hg) as (G1 & G2 & G3 & G4 & G5).
  assert (Ua : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit; lia).
  assert (Un : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
  assert (INA : forall y, a <= y < a + len -> A (page_base_of y)).
  { intros y Hy. apply G5. lia. }
  split.
  - rewrite LZ'. split; [split|split].
    + apply fp_ok_mono3; [| apply alw_le_refl]. intros y Hy. rewrite page_in_ranges_app in Hy. apply Bool.orb_true_iff in Hy as [Hy|Hy].
      * right. apply page_in_lazy_interior in Hy; rewrite ?Ua, ?Un in *; try (unfold page_size; lia).
        rewrite <- page_base_of_page. apply INA. unfold page_size in Hy. lia.
      * left. apply page_in_maps_subtract in Hy as [Hy _]; [exact Hy| exact Wl| lia].
    + intros _ _. rewrite RET. rewrite (mmap_len_lit len) by lia. apply rng_fp_ok; [lia| lia|].
      intros y Hy. right. apply INA. exact Hy.
    + intros HNR. exfalso. vm_compute in HNR. discriminate.
    + apply fp_ok_bw.
  - split; [exact M'|]. split; [lia|]. split; [lia|]. split; [exact HAB|]. split; [exact HGA|]. split; [exact HBU| exact Hk].
Qed.

Lemma step_munmap : forall b G A k mo a len rsp,
  KI b G A k mo -> 0 < len <= 2^40 -> 0 <= a -> a + mmap_len len <= ATOP ->
  map_has (vm_maps (m_vmmaps mo)) (Z_to_bv 64 a) (Z_to_bv 64 (mmap_len len)) = true ->
  let mo' := munmap_model mo a (mmap_len len) in
  fstepS (NMunmap a len) rsp (fp_ok (m_vm_lazy mo) A) (fp_ok (m_vm_lazy mo') A)
  /\ KI b G A k mo'.
Proof.
  intros b G A k mo a len rsp HK Hlen Ha Hce Hmh mo'. subst mo'. pose proof (mmap_len_bounds len ltac:(lia)) as ML.
  pose proof HK as (M & Hb & HN & HAB & HGA & HBU & Hk). atop_facts. pose proof M as (_ & _ & (_ & _ & Wl & _) & _).
  destruct (MOK_munmap mo a (mmap_len len) M ltac:(lia) ltac:(lia) ltac:(lia) Hmh) as (M' & NL' & LZ' & _ & _).
  split.
  - assert (LE : fp_le (fp_ok (m_vm_lazy mo) A) (fp_ok (m_vm_lazy (munmap_model mo a (mmap_len len))) A)).
    { apply fp_ok_mono; [| apply alw_le_refl].
      rewrite LZ'. intros p Hp. apply page_in_maps_subtract in Hp as [Hp _]; [exact Hp| exact Wl| lia]. }
    split; [| exact LE]. cbn [fstepA]. intros b0 j Hb0 _. exact (LE _ _ Hb0).   (* [comment removed for export] *)
  - split; [exact M'|]. split; [lia|]. split; [lia|]. split; [exact HAB|]. split; [exact HGA|]. split; [exact HBU| exact Hk].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma TS_event : forall {R} n (d : resp -> option Z) (f : Z -> itree node (exc R)) RNG A mo Q,
  acct_ok NMAX RNG A mo -> nsafeA NMAX n mo ->
  (forall rsp mo' evs, nstepA n mo rsp mo' evs ->
     exists z RNG' A', d rsp = Some z /\ fstepS n rsp RNG RNG' /\ alw_le A A' /\ TS NMAX RNG' A' (f z) mo' Q) ->
  TS NMAX RNG A (ebind (enode n d) f) mo Q.
Proof.
  intros R n d f RNG A mo Q HA HS HK. unfold ebind, enode. cbn [bind]. apply TS_unfold_vis.
  split; [exact HA|]. split; [exact HS|].
  intros rsp mo' evs Hst. destruct (HK rsp mo' evs Hst) as (z & RNG' & A' & Hd & HF & HL & HT).
  exists RNG', A'. rewrite Hd. cbn [bind]. split; [exact HF|]. split; [exact HL| exact HT].
Qed.

Lemma gcost_nonneg : forall ga, Forall (fun l => 0 <= l) ga -> 0 <= gcost ga.
Proof. induction ga as [|l ga IH]; intros H; cbn; [lia|]. apply Forall_cons_iff in H as [H1 H2]. pose proof (pcost_nonneg l H1). specialize (IH H2). lia. Qed.

(* [comment removed for export] *)
Definition KPOST {R} (RP : list (Z * Z) -> R -> Prop) (Post : R -> Model -> Prop) (G : list (Z * Z)) (KCAP : Z) : postT (exc R) :=
  EQ (fun r RNG' A' mo' => exists G' b' k', RP G' r /\ Post r mo' /\ KI b' G' A' k' mo' /\ k' <= KCAP /\ incl G G' /\ RNG' = fp_ok (m_vm_lazy mo') A').

Lemma KPOST_mono_G : forall {R} RP Post (G G1 : list (Z * Z)) KCAP (r : exc R) RNG A mo,
  incl G G1 -> KPOST RP Post G1 KCAP r RNG A mo -> KPOST (R:=R) RP Post G KCAP r RNG A mo.
Proof.
  intros R RP Post G G1 KCAP [|r] RNG A mo HI H; cbn in *; [exact I|].
  destruct H as (G' & b' & k' & H1 & H2 & H3 & H4 & H5 & H6). exists G', b', k'. repeat (split; [assumption|]).
  split; [eapply incl_tran; eauto| exact H6].
Qed.

(* [comment removed for export] *)
Theorem TS_aembed : forall {R} (t : AM R) (RP : list (Z * Z) -> R -> Prop) Post ga G b A k KCAP mo,
  atotal (aok34 (ATOP:=ATOP) (SBc:=SB) (PAc:=PA)) (apost ATOP) t mo Post -> evq SB PA RP ga G b t -> KI b G A k mo ->
  Forall (fun l => 0 <= l) ga -> k + gcost ga <= KCAP -> KCAP <= NMAXZ ->
  TS NMAX (fp_ok (m_vm_lazy mo) A) A (aembed ATOP t) mo (KPOST RP Post G KCAP).
Proof.
  intros R t. induction t as [r | e k0 IH]; intros RP Post ga G b A k KCAP mo HT HE HK Hga Hk HKC.
  - rewrite aembed_ret. pose proof (gcost_nonneg ga Hga). apply TS_ret_ok.
    + eapply KI_acct_ok; [exact HK| lia].
    + cbn in HT, HE. exists G, b, k. split; [exact HE|]. split; [exact HT|]. split; [exact HK|]. split; [lia|]. split; [apply incl_refl| reflexivity].
  - cbn [atotal] in HT. destruct HT as [[Hok Hroom] HT]. pose proof (gcost_nonneg ga Hga) as GC0.
    assert (HAT : atop_ok ATOP) by (unfold atop_ok, AsanInv.ACEIL, AsanInv.ATOP_MAX; atop_facts; lia).
    pose proof (asan_node_sound ATOP HAT e mo Hok) as (n & d & En & Hans & _ & _).
    pose proof HK as (M & Hb & HN & HAB & HGA & HBU & Hk0).
    destruct e as [t0|b0|a len prot flags|a len|a l p|a len|w]; cbn [aok] in Hok; try contradiction.
    + (* [comment removed for export] *)
      destruct Hok as (-> & Hlen & Htop & Hc). cbn [aev_node] in En. injection En as <- <-.
      cbn [evq] in HE. destruct HE as (_ & _ & Hlal & HE).
      rewrite aembed_vis. cbn [aev_tree].
      assert (ML : mmap_len len = len) by (apply mmap_len_id; lia).
      cbn [room34] in Hroom. rewrite ML in Hroom. destruct Hroom as [HR HWf].   (* [comment removed for export] *)
      destruct HE as [(-> & -> & HE)|[(-> & HAP & Hlb & HE)|(-> & HCG & HE)]].
      * (* [comment removed for export] *)
        rewrite Z.eqb_refl in Hc. destruct Hc as (_ & Hbud & Hgap).
        destruct ga as [|l0 ga']; [destruct HE|]. destruct HE as (<- & Hlb & HE). cbn [gcost] in Hk. apply Forall_cons_iff in Hga as [_ Hga].
        pose proof (pcost_nonneg len ltac:(lia)). pose proof (gcost_nonneg ga' Hga).
        apply TS_event.
        -- eapply KI_acct_ok; [exact HK| lia].
        -- eapply nsafeA_grant; [exact HK| lia| exact Hlal| exact HR].
        -- intros rsp mo' evs Hst. destruct (Hans rsp mo' evs Hst) as (_ & z & Hd & Hpost).
           pose proof Hpost as Hpost'. cbn [apost] in Hpost. rewrite Z.eqb_refl in Hpost. rewrite ML in Hpost.
           destruct Hpost as (Z1 & Z2 & Z3 & Z4 & ->).   (* [comment removed for export] *)
           destruct (step_grant b G A k mo len z rsp HK ltac:(lia) Hlal Hlb HR Z1 Z2 Z3 Z4 Hd) as (HF & HL & HK').
           eexists z, _, _. split; [exact Hd|]. split; [exact HF|]. split; [exact HL|].
           eapply TS_EQ_mono.
           ++ eapply (IH z RP Post ga' ((z, len) :: G) (b - len) _ (k + pcost len) KCAP).
              ** apply HT. exact Hpost'.
              ** specialize (HE z). rewrite is_err_small in HE by (unfold TWO64; atop_facts; lia). exact HE.
              ** exact HK'.
              ** exact Hga.
              ** lia.
              ** exact HKC.
           ++ intros x RNG' A'' mo'' _ HP. apply (KPOST_mono_G RP Post G ((z, len) :: G) KCAP (Ok x)); [| exact HP]. intros g Hg. right; exact Hg.
      * (* [comment removed for export] *)
        destruct (Z.eqb_spec a 0) as [->|Hnz]. { destruct Hc as (Hc & _). exfalso. revert Hc. cbv. discriminate. }
        destruct Hc as (_ & Ha & Haal & Hce & Hrf & Hmc & _). rewrite ML in Hce, Hrf, Hmc.
        apply TS_event.
        -- eapply KI_acct_ok; [exact HK| lia].
        -- eapply nsafeA_fixed; [exact HK| left; reflexivity| lia| exact Hlal| exact Ha| exact Haal| exact Hce| exact Hrf| exact Hmc| exact HR].
        -- intros rsp mo' evs Hst. destruct (Hans rsp mo' evs Hst) as (_ & z & Hd & Hpost).
           pose proof Hpost as Hpost'. cbn [apost] in Hpost. replace (a =? 0) with false in Hpost by (symmetry; apply Z.eqb_neq; exact Hnz).
           rewrite ML in Hpost. destruct Hpost as (-> & ->).
           destruct (step_commit b G A k mo a len rsp HK ltac:(lia) Hlal Hlb HR Ha Haal ltac:(exact Hce) (HWf eq_refl) Hmc Hd) as (HF & HK').
           eexists a, _, A. split; [exact Hd|]. split; [exact HF|]. split; [apply alw_le_refl|].
           eapply (IH a RP Post ga G (b - len) A k KCAP).
           ++ apply HT. exact Hpost'.
           ++ specialize (HE a). rewrite is_err_small in HE by (unfold TWO64; atop_facts; lia). exact HE.
           ++ exact HK'.
           ++ exact Hga.
           ++ exact Hk.
           ++ exact HKC.
      * (* [comment removed for export] *)
        destruct (Z.eqb_spec a 0) as [->|Hnz]. { destruct Hc as (Hc & _). exfalso. revert Hc. cbv. discriminate. }
        destruct Hc as (_ & Ha & Haal & Hce & Hrf & Hmc & _). rewrite ML in Hce, Hrf, Hmc.
        apply TS_event.
        -- eapply KI_acct_ok; [exact HK| lia].
        -- eapply nsafeA_fixed; [exact HK| right; reflexivity| lia| exact Hlal| exact Ha| exact Haal| exact Hce| exact Hrf| exact Hmc| exact HR].
        -- intros rsp mo' evs Hst. destruct (Hans rsp mo' evs Hst) as (_ & z & Hd & Hpost).
           pose proof Hpost as Hpost'. cbn [apost] in Hpost. replace (a =? 0) with false in Hpost by (symmetry; apply Z.eqb_neq; exact Hnz).
           rewrite ML in Hpost. destruct Hpost as (-> & ->).
           destruct (step_recommit b G A k mo a len rsp HK ltac:(lia) Hlal Ha Haal ltac:(exact Hce) HCG Hmc Hd) as (HF & HK').
           eexists a, _, A. split; [exact Hd|]. split; [exact HF|]. split; [apply alw_le_refl|].
           eapply (IH a RP Post ga G b A k KCAP).
           ++ apply HT. exact Hpost'.
           ++ exact (HE a).
           ++ exact HK'.
           ++ exact Hga.
           ++ exact Hk.
           ++ exact HKC.
    + (* [comment removed for export] *)
      destruct Hok as (Hlen & Ha & Haal & Hce & Hmh & Hsub). cbn [aev_node] in En. injection En as <- <-.
      cbn [evq] in HE.
      rewrite aembed_vis. cbn [aev_tree]. apply TS_event.
      * eapply KI_acct_ok; [exact HK| lia].
      * eapply nsafeA_munmap; eauto.
      * intros rsp mo' evs Hst. destruct (Hans rsp mo' evs Hst) as (_ & z & Hd & Hpost).
        pose proof Hpost as Hpost'. cbn [apost] in Hpost. destruct Hpost as (-> & ->).
        destruct (step_munmap b G A k mo a len rsp HK Hlen Ha Hce Hmh) as (HF & HK').
        eexists 0, _, A. split; [exact Hd|]. split; [exact HF|]. split; [apply alw_le_refl|].
        eapply (IH 0 RP Post ga G b A k KCAP).
        -- apply HT. exact Hpost'.
        -- exact (HE 0).
        -- exact HK'.
        -- exact Hga.
        -- exact Hk.
        -- exact HKC.
    + (* [comment removed for export] *)
      destruct Hok as (Hlen & Ha & Haal & Hce & Hcan & Hmok). cbn [aev_node] in En. injection En as <- <-.
      cbn [evq] in HE.
      rewrite aembed_vis. cbn [aev_tree]. apply TS_event.
      * eapply KI_acct_ok; [exact HK| lia].
      * eapply nsafeA_madvise; eauto.
      * intros rsp mo' evs Hst. destruct (Hans rsp mo' evs Hst) as (_ & z & Hd & Hpost).
        pose proof Hpost as Hpost'. cbn [apost] in Hpost. destruct Hpost as (-> & ->).
        eexists 0, _, A. split; [exact Hd|]. split; [apply fstepS_id; exact I|]. split; [apply alw_le_refl|].
        eapply (IH 0 RP Post ga G b A k KCAP).
        -- apply HT. exact Hpost'.
        -- exact (HE 0).
        -- exact HK.
        -- exact Hga.
        -- exact Hk.
        -- exact HKC.
Qed.
End Ops.
End CANSEC1.
