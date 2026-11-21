(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (56 recorded proofs replaced by written proofs (all_chunks_init_cache, qbatches_init_cache, CH_init_cache and 53 more); adds seps_In_wsep, seps_maps_subtract_exact, ami_region_free_within, ami_maps_resv_cons; AMI's bound on the reserved ledger's entries, false with the vDSO pair, replaced by the fact that the mappings miss the reserved ledger, kept by AMI_grant and AMI_munmap). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation FinFun.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import AcctCore.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import BackingAlgebra.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanCtrlProps SizeHist.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AsanInv () := "C47Corelib4Init5Logic7eq_rectC47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapI47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3appC35stdpp8fin_maps;map_to_listC35stdpp4base6LookupC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_ind_rI35stdpp8fin_maps6FinMap00C35stdpp8fin_maps7MapFoldC35stdpp8fin_maps:map_insertC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base6InsertC35stdpp4base<PartialAlterC35stdpp4base5MergeC35stdpp4base;RelDecisionI35stdpp4gmap4gmap00I35stdpp9countable9Countable00C35stdpp4base4fmapC35stdpp8fin_maps:map_eq_iffC46Stdlib5Lists4List8map_consC46Stdlib5Lists4List7existsbC35stdpp4gmap;gmap_lookupC35stdpp4gmap:gmap_emptyC35stdpp4gmapBgmap_partial_alterC35stdpp4gmap9gmap_foldK47Corelib4Init5Logic2eq01I47Corelib7Numbers7BinNums1Z00C59OSSVerify5KrLib4Spec8AsanCtrl=ALLOC_TOP_MINC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateBtarget_alloc_limitC4ELinuxProcessSemantics?LinuxProcessSem5StateBsource_alloc_limitI47Corelib4Init5Logic2eq00C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01c59OSSVerify5KrLib4Spec7AsanInv7LIMIT34C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7AsanInv5LIMITC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7AsanInv4zlenC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthI47Corelib4Init9Datatypes4list00c59OSSVerify5KrLib4Spec7AsanInv:all_chunksC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6achunk00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6abatch00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6aclass00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6astate00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7AsanInv8qbatchesC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00c59OSSVerify5KrLib4Spec7AsanInv2CHC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7a_cinitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl9set_cinitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl:init_cacheC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat02C47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List2InC56Stdlib6ZArith6BinInt1Z6of_natI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C47Corelib4Init5Logic3iffK47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC46Stdlib5Lists4List:in_map_iffI47Corelib4Init5Peano2le00C47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2ltC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z3maxC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K47Corelib7Numbers7BinNums8positive02C46Stdlib9micromega;ZifyClasses;rew_iff_revK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqK47Corelib7Numbers7BinNums1Z01K47Corelib4Init9Datatypes3nat01C47Corelib7Classes?RelationClasses>iff_TransitiveK47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201c59OSSVerify5KrLib4Spec7AsanInv7CLASSESC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib5Lists6Finite9InjectiveC46Stdlib5Lists4List9seq_NoDupC46Stdlib5Lists6FiniteCInjective_map_NoDupI46Stdlib5Lists4List5NoDup00C46Stdlib5Lists4List;ForallPairsC46Stdlib5Lists4ListKNoDup_map_NoDup_ForallPairsC59OSSVerify5KrLib4Spec8AsanCtrl7get_clsC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02K47Corelib4Init5Logic2or01C47Corelib4Init9Datatypes8list_indC46Stdlib5Lists4List:fold_rightC56Stdlib6ZArith6BinInt1Z3subC47Corelib4Init5Logic3notC59OSSVerify5KrLib4Spec8AsanCtrl7put_clsC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04C47Corelib4Init5Logic6eq_symC59OSSVerify5KrLib4Spec=AsanCtrlProps:get_put_neC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7AsanInv=fold_csum_extC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec=AsanCtrlProps:get_put_eqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7AsanInv:In_CLASSESC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7AsanInv=fold_csum_putC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7AsanInv4csumC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7AsanInv=NoDup_CLASSESC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7AsanInvAcls_mapped_bytes'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_nresC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega7EnvRing5PExpr05c59OSSVerify5KrLib4Spec7AsanInv8csum_putC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7AsanInv<commit_bytesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7AsanInv?csum_init_cacheC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7AsanInv6vc_clsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7AsanInv2VCC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7AsanInv5FAINVC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrlCc_mapped_free_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=c_mapped_userC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_MAPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec=AsanCtrlPropsBget_cls_init_cacheC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z=add_le_mono_rc59OSSVerify5KrLib4Spec7AsanInv7csum_leC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_appC56Stdlib6ZArith4Znat5Nat2Z8inj_succc59OSSVerify5KrLib4Spec7AsanInv:is_prim_ofC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6filterc59OSSVerify5KrLib4Spec7AsanInv8zlen_appC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:filter_appc59OSSVerify5KrLib4Spec7AsanInv4cntPC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7AsanInv9zlen_consC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7AsanInv;zlen_nonnegC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<flat_map_appc59OSSVerify5KrLib4Spec7AsanInv4secsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7AsanInv6sec_ofC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7AsanInv7qchunksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl8b_chunksC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7AsanInv5zsumcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl:chunk_sizeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7AsanInv4bsumC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6b_sizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbc59OSSVerify5KrLib4Spec7AsanInv6nbatchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_BATCH_CLASSC1?~~~~~~~~~~~~~~~I46Stdlib7Sorting;Permutation;Permutation00K46Stdlib7Sorting;Permutation;Permutation01K46Stdlib7Sorting;Permutation;Permutation02K46Stdlib7Sorting;Permutation;Permutation03C46Stdlib7Sorting;Permutation@Permutation_reflC46Stdlib7Sorting;PermutationAPermutation_transC46Stdlib7Sorting;Permutation?Permutation_indc59OSSVerify5KrLib4Spec7AsanInv;filter_permC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;PermutationBPermutation_lengthC46Stdlib7Sorting;PermutationDPermutation_flat_mapI47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib4Spec8AsanCtrl6a_liveC1?~~~~~~~~~~~~~~~C35stdpp4base6lookupC47Corelib4Init9Datatypes3sndC35stdpp4base6insertK47Corelib4Init9Datatypes4prod01C35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap;gmap_finmapC35stdpp8fin_mapsBmap_to_list_insertC46Stdlib7Sorting;Permutation?Permutation_mapC59OSSVerify5KrLib4Spec8AsanCtrl8set_liveC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7AsanInv;live_chunksC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableK47Corelib4Init9Datatypes6option01C35stdpp8fin_maps:map_deleteC35stdpp4base6deleteC46Stdlib7Sorting;PermutationGPermutation_EquivalenceC47Corelib7Classes?RelationClassesEEquivalence_SymmetricC35stdpp8fin_mapsBmap_to_list_deleteC47Corelib7Classes?RelationClasses8symmetryK47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C59OSSVerify5KrLib2AS>BackingAlgebra8iv_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>BackingAlgebra9sum_countC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7AsanInv>sum_count_consC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>BackingAlgebra1BC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>BackingAlgebra1SC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>BackingAlgebra=zcount_nonnegC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>BackingAlgebra=zcount_le_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>BackingAlgebra6zcountC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>BackingAlgebra7S_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powc59OSSVerify5KrLib4Spec7AsanInv=iv_count_le_SC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Z2Nat2idC59OSSVerify5KrLib2AS>BackingAlgebraAzcount_const_trueC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State:live_bytesC59OSSVerify5KrLib2AS>BackingAlgebraDlive_bytes_sum_countC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses3injC59OSSVerify5KrLib2AS>BackingAlgebra:zcount_extC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZC59OSSVerify5KrLib2AS>BackingAlgebra@sum_count_nonnegC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>BackingAlgebra=sum_count_appC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedc59OSSVerify5KrLib4Spec7AsanInv4wsepC1?~~~~~~~~~~~~~~~i59OSSVerify5KrLib4Spec7AsanInv4seps00C1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;PermutationBPermutation_Forallk59OSSVerify5KrLib4Spec7AsanInv4seps02C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List?Forall_cons_iffc59OSSVerify5KrLib4Spec7AsanInv8wsep_symC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02k59OSSVerify5KrLib4Spec7AsanInv4seps01C1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List6Exists00c59OSSVerify5KrLib4Spec7AsanInv=seps_cons_invC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State;region_freeK47Corelib5Lists7ListDef6Forall01C47Corelib4Init9Datatypes4andbC46Stdlib4Bool4Bool=andb_true_iffC4ELinuxProcessSemantics?LinuxProcessSem5State:iv_overlapC47Corelib4Init9Datatypes4negbC46Stdlib4Bool4Bool=negb_true_iffC46Stdlib4Bool4Bool>andb_false_iffC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_geK47Corelib4Init9Datatypes4bool02C46Stdlib5Lists4List8in_splitC59OSSVerify5KrLib2AS>BackingAlgebra;overlap_sumC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>BackingAlgebra6in_rngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>BackingAlgebraHiv_count_in_rng_disjointC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;PermutationBPermutation_middleC46Stdlib7Sorting;Permutation?Permutation_symc59OSSVerify5KrLib4Spec7AsanInv9seps_permC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:Forall_appC59OSSVerify5KrLib2AS>BackingAlgebraBiv_count_in_rng_leC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClassesFEquivalence_TransitiveC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC4ELinuxProcessSemantics?LinuxProcessSem2Fs9bv_eqb_eqC59OSSVerify5KrLib3Lib8PropExec;bv_eqb_reflC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State:map_removeC46Stdlib5Lists4List>existsb_existsC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z6leb_leC4ELinuxProcessSemantics?LinuxProcessSem5State<map_containsC4ELinuxProcessSemantics?LinuxProcessSem5State7map_hasC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z2geC45stdpp9bitvector;definitions7Z_to_bvK46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8min_specC56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00C46Stdlib4Bool4Bool;andb_true_rC4ELinuxProcessSemantics?LinuxProcessSem5State;iv_subtractK46Stdlib9micromega=RingMicromega3Op204C59OSSVerify5KrLib2AS>BackingAlgebra6ivs_wfC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State=maps_subtractC46Stdlib4Bool4Bool:andb_assocC59OSSVerify5KrLib2AS>BackingAlgebra5iv_wfC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7AsanInvGiv_subtract_region_freeC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith:ZArith_dec;Z_le_gt_decC56Stdlib6ZArith6BinInt1Z2gtK46Stdlib9micromega=RingMicromega3Op206c59OSSVerify5KrLib4Spec7AsanInv;noacc_clearC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7AsanInvIregion_free_maps_subtractC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7AsanInv5LS_LOC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7AsanInv5LS_SZC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7AsanInv5HS_LOC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7AsanInv5HS_SZC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8with_fdsC4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedC4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_reservedc59OSSVerify5KrLib4Spec7AsanInv8entry_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State7vm_mapsC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_noaccessC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyc59OSSVerify5KrLib4Spec7AsanInv7atop_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topC47Corelib4Init5Logic7and_indc59OSSVerify5KrLib4Spec7AsanInv3AMIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>BackingAlgebra7coveredC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7AsanInv5STARTC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8vm_limitc59OSSVerify5KrLib4Spec7AsanInv4wentC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7AsanInv6EAGER0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7AsanInv5RTOT0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7AsanInv4LEN0C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00c59OSSVerify5KrLib4Spec7AsanInv6RES_HIC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7AsanInv2PmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;a_space_begC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;a_ptr_arrayC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7AsanInv4rcovC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7AsanInv6PTR_SZC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7AsanInv7PRIM_SZC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7AsanInv5KHIGHC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7AsanInv6GAP_LOC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7AsanInv6GAP_SZC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7AsanInv4TOT0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>BackingAlgebra<model_ivs_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8AsanCeil:init_sp_okC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List=Forall_forallC47Corelib4Init5Logic5proj1C56Stdlib6ZArith6BinInt1Z6moduloC4ELinuxProcessSemantics?LinuxProcessSem5State:vm_init_spc59OSSVerify5KrLib4Spec7AsanInv5ACEILC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7AsanInv8ATOP_MAXC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_loC59OSSVerify5KrLib2AS>BackingAlgebraCvm_backing_used_semC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State?vm_backing_usedC59OSSVerify5KrLib4LibA8AcctCore=nonlazy_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA8AcctCoreEvm_backing_used_splitC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizec59OSSVerify5KrLib4Spec7AsanInv5zsum2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7AsanInv:AMI_ivs_wfC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7AsanInvAsum_count_le_liveC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7AsanInv?live_bytes_wentC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7AsanInv>sum_count_permC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7AsanInvAnonlazy_sum_countC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7AsanInv;grant_modelC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State<vm_start_brkC4ELinuxProcessSemantics?LinuxProcessSem5State6vm_brkC4ELinuxProcessSemantics?LinuxProcessSem5State<vm_mmap_baseK4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps01C4ELinuxProcessSemantics?LinuxProcessSem5State;with_vmmapsc59OSSVerify5KrLib4Spec7AsanInv?region_free_appC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7AsanInv@region_free_wsepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>BackingAlgebra5in_ivC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3orbC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapBmmap_fixed_rw_nextC4ELinuxProcessSemantics?LinuxProcessSem5State?vm_forget_rangeC4ELinuxProcessSemantics?LinuxProcessSem5StateBpage_outside_rangeC59OSSVerify5KrLib2AS>BackingAlgebra@maps_subtract_wfC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7AsanInvDnoacc_clear_subtractC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>BackingAlgebraAmaps_subtract_semC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>BackingAlgebra;covered_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>BackingAlgebraEm_vm_lazy_with_vmmapsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>BackingAlgebraDm_vmmaps_with_vmmapsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>BackingAlgebraIm_vm_lazy_vm_forget_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>BackingAlgebraHm_vmmaps_vm_forget_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>BackingAlgebra>sum_count_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>BackingAlgebra?sum_count_or_leC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7AsanInv=sum_count_subC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7AsanInvEoverlap_sum_containedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8le_transC59OSSVerify5KrLib2AS>BackingAlgebraMm_vm_materialized_with_vmmapsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>BackingAlgebraQm_vm_materialized_vm_forget_rangeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State;vm_add_lazyc59OSSVerify5KrLib4Spec7AsanInv;fixed_modelC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7F_FIXEDC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00C59OSSVerify5KrLib2AS>BackingAlgebraElazy_interior_alignedC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State=lazy_interiorC59OSSVerify5KrLib2AS>BackingAlgebra;ivs_wf_consC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7AsanInv<covered_consC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>BackingAlgebraEm_vm_lazy_vm_add_lazyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>BackingAlgebraDm_vmmaps_vm_add_lazyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>BackingAlgebraMm_vm_materialized_vm_add_lazyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl:F_FIXNORESC1?~~~~~~~~~~~~~~~C47Corelib7Program6Basics4implC47Corelib7Classes9Morphisms5flip2C47Corelib7Classes9MorphismsDiff_impl_subrelationC46Stdlib5Lists4List;incl_filterC47Corelib7Classes9MorphismsIiff_flip_impl_subrelationc59OSSVerify5KrLib4Spec7AsanInv<munmap_modelC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_assocC46Stdlib5Lists4List7map_appC46Stdlib5Lists4List;Forall_implc59OSSVerify5KrLib4Spec7AsanInv?map_remove_permC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7AsanInv;seps_filterC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6leb_gtc59OSSVerify5KrLib4Spec7AsanInv@sum_count_ext_onC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition AIMG_HI : Z := 0x6a6000.        (* [comment removed for export] *)
Definition RES_HI : Z := 0x7fff7000.       (* [comment removed for export] *)
Definition ACEIL : Z := 0x7fff7f800000.    (* [comment removed for export] *)
Definition ATOP_MAX : Z := 0x7FFFFF800000. (* [comment removed for export] *)
Definition KHIGH : Z := 0x10007fff8000.    (* [comment removed for export] *)
Definition LS_LO : Z := 0x7fff7000.        (* [comment removed for export] *)
Definition LS_SZ : Z := 0x10000000.
Definition GAP_LO : Z := 0x8fff7000.       (* [comment removed for export] *)
Definition GAP_SZ : Z := 0x20000000000.
Definition HS_LO : Z := 0x2008fff7000.     (* [comment removed for export] *)
Definition HS_SZ : Z := 0xdfff0001000.
Definition PRIM_SZ : Z := 0x2000011000.    (* [comment removed for export] *)
Definition PTR_SZ : Z := 0x800000.         (* [comment removed for export] *)
Definition EAGER0 : Z := 2^25.             (* [comment removed for export] *)
Definition TOT0 : Z := 2^45.               (* [comment removed for export] *)
Definition RTOT0 : Z := 2^30.              (* [comment removed for export] *)
Definition LEN0 : Z := 32.                 (* [comment removed for export] *)
Definition LIMIT : Z := 0x8000000000.      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition SECM : Z := 2^33 - 2^30.
(* [comment removed for export] *)
Definition NOPS : Z := 128.
Definition VC0 : Z := 31 * 0x40000.
(* [comment removed for export] *)
Definition VCMAX : Z := VC0 + 2^19 * (2 * NOPS + 2) + 2^20.
Definition UWIN : Z := 2^27 + 2^24.
Definition FWIN : Z := 2^25.
Definition inW (sb pa a len : Z) : Prop :=
  (exists c, 1 <= c <= 31 /\
     ((sb + c * K_REGION <= a /\ a + len <= sb + c * K_REGION + UWIN)
      \/ (sb + c * K_REGION + K_FREEARR_OFF <= a /\ a + len <= sb + c * K_REGION + K_FREEARR_OFF + FWIN)))
  \/ (pa <= a /\ a + len <= pa + K_PTRARR_RESERVE).
(* [comment removed for export] *)
Definition RESERVE34 : Z := 2^33 - 2^29.
Definition CBROOM : Z := 0x400000000 - 2^25 - (2^33 - 2^30) - (2^33 - 2^29).   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition LIMIT34 : Z := 0x400000000.      (* [comment removed for export] *)

Lemma ACEIL_eq : ACEIL = ALLOC_TOP_MIN.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanInv ()) [] "p;2p-1R0p10000p4p710p9P0p1000Mp4p710p9P0p10010p4p710p9P0p1001\R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1002:p4p710p9P0p1002Xp4p7210p9P0p10035p4p710p9P0p1003mp4p710p8P0p1004DR1p4p710p8P0P1p4p7210p8P0p1004`p4p710p8P0p1005AR1p4p710p8P0P1p4p7210p8P0p1005^p4p710p8P0p1006;R1p4p710p8P0P1p4p7210p8P0p1006XR1p4p710R2p8P0P1p4p7210p8p1006lp4p710p1007Ip4p710R0p8p1007gR3p4p73101R4p1008AR5p4p73110p8P4p1008ZR6p4p73110p8P4p10096p4p710p8P4p1009IR7p4p7201p8P4p1009[p4p7201p8P4P1p4p73110p8P4p1009mR1p4p73110p8P4p100:AR8p4p73110p8P4p100:[p4p7201p8P3p4p710R4P5p4p710p8P4P6p4p710p8P4p100:nR6p4p710R5p8P4P6p4p7210R6p8P4P2p8P4P1p4p710p8P4P8p4p710p8p100;GR8p4p710R4p100;[p4p710p8P4P5p8P4P6p8P4p100<9p4p73110p8P8p4p741110R8p100<Kp4p73101p8p100<gp4p7210P0p8p100=Dp4p710P0p8p100=`p4p741110R0P3p4p7511100R4p8P4P0p8p100>9p4p741110R0P3p4p76111100R4p8P4P0p8p100>Qp4p741110R0P3p4p771111100R4p8P4P0p8p100?1p4p741110R0P3p4p7:1111111100R3p8P3P0p8P7p4p7200R7P8p8P8P7p8g00?Hj20Tg00?bg00@@'0o"). Qed.
(* [comment removed for export] *)
Definition atop_ok (ATOP : Z) : Prop := ACEIL <= ATOP <= ATOP_MAX.
Lemma LIMIT_eq : LIMIT = target_alloc_limit.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanInv ()) [] "p;2g00?Hj20Tg00?bg00A@'0o"). Qed.
Lemma LIMIT34_eq : LIMIT34 = source_alloc_limit.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanInv ()) [] "p;2g00?Hj20Tg00?bg00BA'0o"). Qed.
Lemma LIMIT34_le_LIMIT : LIMIT34 <= LIMIT.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanInv ()) [] "p'0h01Hh11eh21xi001cp;3p;6p;2g00CBj33Tg00C\j62Tg00D8j20Tg00DWj21Tg00E3R0g00EYR1g00F?R233P0P1P0p-0f0R1g00FeR3g00GBP3n011000003000000X10g00G^P2P1E2P31031b0W2g00H:g00I3'1do"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition is_prim_of (c : Z) (ch : achunk) : bool := match ch with CPrim c' _ => c' =? c | CSec _ _ _ => false end.
Definition sec_of (ch : achunk) : list (Z * Z) := match ch with CSec mb ms _ => [(mb, ms)] | CPrim _ _ => [] end.

Definition zlen {A} (l : list A) : Z := Z.of_nat (length l).
Definition cntP (c : Z) (l : list achunk) : Z := zlen (List.filter (is_prim_of c) l).
Definition secs (l : list achunk) : list (Z * Z) := flat_map sec_of l.

Definition live_chunks (st : astate) : list achunk := map snd (map_to_list (a_live st)).
Definition qchunks (bs : list abatch) : list achunk := flat_map b_chunks bs.
Definition qbatches (pb : list abatch) (st : astate) : list abatch := pb ++ a_qloc st ++ a_qglob st.
Definition all_chunks (pc : list achunk) (pb : list abatch) (st : astate) : list achunk :=
  pc ++ live_chunks st ++ qchunks (qbatches pb st).
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition CH (pc : list achunk) (pb : list abatch) (st : astate) : list (Z * Z) := secs (all_chunks pc pb st).

Definition nbatch (c : Z) (bs : list abatch) : Z := if c =? K_BATCH_CLASS then zlen bs else 0.

Fixpoint zsumc (l : list achunk) : Z := match l with [] => 0 | ch :: l' => chunk_size ch + zsumc l' end.
Fixpoint bsum (bs : list abatch) : Z := match bs with [] => 0 | b :: bs' => b_size b + bsum bs' end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition chunk_wf (ATOP : Z) (ch : achunk) : Prop :=
  match ch with
  | CPrim c n => 0 <= n <= 64512 /\ c = class_id (needed_size n)
  | CSec mb ms n => 64512 < n <= 536871936 /\ ms = sec_map_size n /\ mb mod 4096 = 0 /\ 0 < mb   (* [comment removed for export] *)
                   /\ (mb + ms <= LS_LO \/ (KHIGH <= mb /\ mb + ms <= ATOP))
  end.

Definition batch_wf (b : abatch) : Prop :=
  b_count b = zlen (b_chunks b) /\ b_count b <= Q_BATCH /\ b_size b = Q_BATCH_BYTES + zsumc (b_chunks b)
  /\ Forall (fun ch => 0 <= chunk_size ch <= Q_MAX) (b_chunks b).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition LMAX (c : Z) : Z :=
  if c =? 1 then 32 * (2 * HB + 6) else if c =? 2 then 64 * (HB + 4) else 2^28.
Definition SMAX : Z := HB / 16127 + 4.       (* [comment removed for export] *)

Definition LSBYTES : Z := 5 * HB + 4 * 536871936.     (* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint secbytes (l : list achunk) : Z :=
  match l with [] => 0 | CSec _ _ n :: l' => n + secbytes l' | CPrim _ _ :: l' => secbytes l' end.

Definition live_budget (st : astate) : Prop :=
  (forall c, 1 <= c <= 31 -> size_of_class c * cntP c (live_chunks st) <= LMAX c)
  /\ zlen (secs (live_chunks st)) <= SMAX
  /\ secbytes (live_chunks st) <= LSBYTES.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition cls_inv (pc : list achunk) (pb : list abatch) (st : astate) (c : Z) : Prop :=
  let r := get_cls st c in
  0 <= c_allocated_user r /\ c_allocated_user r <= c_mapped_user r /\ c_mapped_user r <= K_FREEARR_OFF
  /\ c_mapped_user r - c_allocated_user r <= 2 * K_USER_MAP
  /\ c_mapped_user r mod K_USER_MAP = 0
  /\ 0 <= c_mapped_free_array r <= K_FREEARR_MAX /\ c_mapped_free_array r mod K_FREEARR_MAP = 0
  /\ 0 <= c_num_freed r /\ 0 <= c_count r <= max_count st c
  /\ c_allocated_user r = size_of_class c * (cntP c (all_chunks pc pb st) + nbatch c (qbatches pb st) + c_count r + c_num_freed r).

Definition AINV (ATOP : Z) (pc : list achunk) (pb : list abatch) (st : astate) : Prop :=
  (forall c, 1 <= c <= 31 -> cls_inv pc pb st c)
  /\ Forall (chunk_wf ATOP) (all_chunks pc pb st)
  /\ Forall batch_wf (qbatches pb st)
  /\ a_qloc_bytes st = bsum (a_qloc st) /\ a_qglob_bytes st = bsum (a_qglob st)
  /\ a_nsec st = zlen (CH pc pb st)
  /\ (a_nres st = 0 \/ a_nres st = K_CHUNKS_BLOCK)
  /\ (forall id ch, (a_live st) !! id = Some ch -> (id < a_next st)%N)
  /\ a_space_beg st mod 65536 = 0 /\ 0 < a_space_beg st /\ a_ptr_array st mod 4096 = 0 /\ 0 < a_ptr_array st
  /\ live_budget st.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition went (e : Z * Z) : word * word := (Z_to_bv 64 (fst e), Z_to_bv 64 (snd e)).

(* [comment removed for export] *)
Definition Pm (mo : Model) (x : Z) : bool := negb (covered (vm_noaccess (m_vmmaps mo) ++ m_vm_lazy mo) x).

(* [comment removed for export] *)
Definition wsep (p q : word * word) : Prop :=
  bv_unsigned (fst p) + bv_unsigned (snd p) <= bv_unsigned (fst q) \/ bv_unsigned (fst q) + bv_unsigned (snd q) <= bv_unsigned (fst p).
Inductive seps : list (word * word) -> Prop :=
| seps_nil : seps []
| seps_cons : forall p l, Forall (wsep p) l -> seps l -> seps (p :: l).

Definition entry_ok (ATOP : Z) (e : word * word) : Prop :=
  0 < bv_unsigned (snd e) /\ bv_unsigned (fst e) mod 4096 = 0 /\ bv_unsigned (snd e) mod 4096 = 0
  /\ bv_unsigned (fst e) + bv_unsigned (snd e) <= ATOP.

(* [comment removed for export] *)
Definition CLASSES : list Z := map Z.of_nat (seq 1 31).
Definition csum (f : aclass -> Z) (st : astate) : Z := fold_right (fun c acc => f (get_cls st c) + acc) 0 CLASSES.
Definition cls_mapped_bytes' (r : aclass) : Z := c_mapped_user r + c_mapped_free_array r.
Definition commit_bytes (st : astate) : Z := csum cls_mapped_bytes' st + 8 * a_nres st.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rcov (P : list (word * word)) (iv : Z * Z) : Prop :=
  exists e, In e P /\ bv_unsigned (fst e) <= fst iv /\ snd iv <= bv_unsigned (fst e) + bv_unsigned (snd e).

(* [comment removed for export] *)
Definition START (RESV : list (Z * Z)) (ATOP : Z) (L0 R : list (word * word)) (st : astate) : Prop :=
  (exists pb0, In (went (pb0, PRIM_SZ)) L0 /\ pb0 <= a_space_beg st /\ a_space_beg st + 2^37 + 2^12 <= pb0 + PRIM_SZ
               /\ KHIGH <= pb0 /\ pb0 + PRIM_SZ <= ATOP)
  /\ In (went (a_ptr_array st, PTR_SZ)) L0 /\ a_ptr_array st + PTR_SZ <= ATOP
  /\ region_free R (Z_to_bv 64 (a_ptr_array st)) (Z_to_bv 64 PTR_SZ) = true   (* [comment removed for export] *)
  /\ In (went (LS_LO, LS_SZ)) L0 /\ In (went (GAP_LO, GAP_SZ)) L0 /\ In (went (HS_LO, HS_SZ)) L0
  /\ zlen L0 <= LEN0 /\ live_bytes L0 <= TOT0
  /\ Forall (rcov (R ++ L0)) RESV.

(* [comment removed for export] *)
Definition noacc_clear (na : list (word * word)) : Prop :=
  region_free na (Z_to_bv 64 LS_LO) (Z_to_bv 64 LS_SZ) = true
  /\ region_free na (Z_to_bv 64 HS_LO) (Z_to_bv 64 HS_SZ) = true.

Definition AMI (RESV : list (Z * Z)) (ATOP : Z) (ch : list (Z * Z)) (st : astate) (mo : Model) : Prop :=
  m_vm_materialized mo = []
  /\ LIMIT34 <= vm_limit (m_vmmaps mo)            (* [comment removed for export] *)
  (* LPS 727298f3: the mappings miss the reserved ledger (it holds the vDSO pair above the stack, so no bound on its entries) *)
  /\ (forall e, In e (vm_maps (m_vmmaps mo)) -> region_free (vm_reserved (m_vmmaps mo)) (fst e) (snd e) = true)
  /\ zlen (vm_reserved (m_vmmaps mo)) <= LEN0 /\ live_bytes (vm_reserved (m_vmmaps mo)) <= RTOT0
  /\ Forall (entry_ok ATOP) (vm_maps (m_vmmaps mo))
  /\ ivs_wf (vm_noaccess (m_vmmaps mo))
  /\ ivs_wf (m_vm_lazy mo)
  /\ seps (vm_maps (m_vmmaps mo))
  /\ (atop_ok ATOP /\ alloc_top (m_vmmaps mo) = ATOP)      (* [comment removed for export] *)
  /\ noacc_clear (vm_noaccess (m_vmmaps mo))                (* [comment removed for export] *)
  /\ exists L0, Permutation (vm_maps (m_vmmaps mo)) (L0 ++ map went ch)
       /\ START RESV ATOP L0 (vm_reserved (m_vmmaps mo)) st
       /\ sum_count (Pm mo) L0 <= EAGER0 + commit_bytes st.

(* [comment removed for export] *)
Definition grant_model (mo : Model) (z nZ : Z) : Model :=
  with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps mo)) ((Z_to_bv 64 z, Z_to_bv 64 nZ) :: vm_maps (m_vmmaps mo))
                 (vm_noaccess (m_vmmaps mo)) (vm_start_brk (m_vmmaps mo)) (vm_brk (m_vmmaps mo)) (vm_limit (m_vmmaps mo))
                 (vm_mmap_base (m_vmmaps mo)) (vm_init_sp (m_vmmaps mo))) mo.

Definition fixed_model (mo : Model) (flags addr nZ : Z) : Model :=
  with_mmap_replacement (Z_to_bv 64 flags) (Z_to_bv 64 addr) (Z_to_bv 64 nZ)
     (with_vmmaps (mmap_fixed_rw_next (m_vmmaps mo) (Z_to_bv 64 addr) (Z_to_bv 64 nZ)) mo).

Definition munmap_model (mo : Model) (addr nZ : Z) : Model :=
  with_mmap_destroyed (Z_to_bv 64 addr) (Z_to_bv 64 nZ)
     (mkVmMapsFull (vm_reserved (m_vmmaps mo)) (map_remove (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr))
        (maps_subtract (vm_noaccess (m_vmmaps mo)) addr (addr + nZ))
        (vm_start_brk (m_vmmaps mo)) (vm_brk (m_vmmaps mo)) (vm_limit (m_vmmaps mo))
        (vm_mmap_base (m_vmmaps mo)) (vm_init_sp (m_vmmaps mo))) mo.


(* [comment removed for export] *)
Definition INV (RESV : list (Z * Z)) (ATOP : Z) (pc : list achunk) (pb : list abatch) (st : astate) (mo : Model) : Prop :=
  AINV ATOP pc pb st /\ AMI RESV ATOP (CH pc pb st) st mo.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma all_chunks_put : forall pc pb c r st, all_chunks pc pb (put_cls c r st) = all_chunks pc pb st.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanInv ()) [] "h01ch12pbh22pch31rh42stp;1p;3p;2p100Ijp4p710p100J`p4p710p8g00K@j10Tg00K`j32Tg00?Hj21Tg00L\#0R0g00MW#0g00?bg00NRg00OMf4f3f032,10W4W3W0W1W2o"). Qed.
Lemma qbatches_put : forall pb c r st, qbatches pb (put_cls c r st) = qbatches pb st.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanInv ()) [] "h01ch12pbh21rh32stp;1p;2g00K@j12Tg00PHj21Tg00?Hj20Tg00MW#2R0g00?bg00NRg00OMf3f0'1,00W3W2W0W1o"). Qed.
Lemma CH_put : forall pc pb c r st, CH pc pb (put_cls c r st) = CH pc pb st.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanInv ()) [] "h01ch12pbh22pch31rh42stp;1p;2p;3g00K@j10Tg00QBj23Tg00Qbj32Tg00?Hj21Tg00L\#0g00MW#0g00?bR0g00NRg00OM1300#0f4f3f032'1W4W3W0W1W2o"). Qed.
Lemma all_chunks_init_cache : forall pc pb st, all_chunks pc pb (init_cache st) = all_chunks pc pb st.
Proof. intros. unfold init_cache. destruct (a_cinit st); reflexivity. Qed.
Lemma qbatches_init_cache : forall pb st, qbatches pb (init_cache st) = qbatches pb st.
Proof. intros. unfold init_cache. destruct (a_cinit st); reflexivity. Qed.
Lemma CH_init_cache : forall pc pb st, CH pc pb (init_cache st) = CH pc pb st.
Proof. intros. unfold init_cache. destruct (a_cinit st); reflexivity. Qed.
Lemma all_chunks_set_nres : forall pc pb v st, all_chunks pc pb (set_nres v st) = all_chunks pc pb st.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanInv ()) [] "h02pbh12pch22sth31vp;1p;3p;2g00K@j10Tg00K`j32Tg00?Hj21Tg00L\#0R0g00MW#0g00?bg00OMf3f2f032,10W2W3W0W1o"). Qed.
Lemma all_chunks_set_nsec : forall pc pb v st, all_chunks pc pb (set_nsec v st) = all_chunks pc pb st.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanInv ()) [] "h02pbh12pch22sth31vp;1p;3p;2g00K@j10Tg00K`j32Tg00?Hj21Tg00L\#0R0g00MW#0g00?bg00OMf3f2f032,10W2W3W0W1o"). Qed.

(* [comment removed for export] *)
Lemma In_CLASSES : forall c, In c CLASSES <-> 1 <= c <= 31.
Proof.
  intros c. unfold CLASSES. rewrite in_map_iff. split.
  - intros (n & <- & Hn). apply in_seq in Hn. lia.
  - intros Hc. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia.
Qed.
Lemma CLASSES_nodup : List.NoDup CLASSES.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanInv ()) [] "h04__x1h14__x2h21Eh37__arithh44__ffh58__varmaph65__with71ah81bh94cstrh:5cstr0h;1xh<1yp;1p;2p;3p;<p;4p;7p;8p;6g00VIj11Tg00Vhj2;Tg00W[R0j13Tg00CBj30j16Tg01Alj2?Tg01BOj3=Tg00?Hj24Tg00iZl<:Tg00`>j18Tg00DWj29Tg00k;j1XTg00kYj2UTg00l:j27Tg00lcj3ITg00mLj3HTg00n5j2GTg00`cj1@Tg00naj3ATg00K@j1BTg00aCj2>Tg00oAj1CTg00o_j4DTg00aaj1ETg00b?j1FTg00cMj25Tg010=j1<Tg00dSj4JTg012hj7KTg00e>j1LTg0140j8MTg00e`j2NTg00fBj2OTg00fnj3PTg00gMj4QTg010bj4RTg01Blj3STg01CLj2TTg01Cjj6WTg01DTj2VTf0R1#1#1p=Y%11#1#1#1p=2g016AR2g00?bR3P0g01<XR4#1R5%Y5#2#2#2#2#2#2#2R6';f1R7#3R8%31503R9f2R:=027%3:R;=038P2P3%62P0%63A02711?715=9X<2X;2P:P;143;P7P81438M<:%8:R8g01<:R9/9;R;P8P;g01>MR;g01=hR8#X,U317355I317345H3g01?`'G%@;3A%B;P31>3:P7%C3CD%E3%F3R;g019NR4g019mR<P<g01:MR=P;P4P<P<P=P31538g01@L%<8,53CJg01:mFKR8%L<P8GM1N;=P1P:g00UIR=g00UiR;'41O1:=0=;dAP397CQb4b5b6X03X13A0317A037:[^03^13P1f4#3f5#3f3O3b3b:b9CRW2X82X72AS230e1T65EWg01A3,V3eo"). Qed.
Lemma NoDup_CLASSES : List.NoDup CLASSES.
Proof. unfold CLASSES. apply (List.NoDup_map_NoDup_ForallPairs Z.of_nat). intros x y Hx Hy E. lia. apply List.seq_NoDup. Qed.

Lemma fold_csum_ext : forall (f : aclass -> Z) st st' l,
  (forall c, In c l -> get_cls st' c = get_cls st c) ->
  fold_right (fun c acc => f (get_cls st' c) + acc) 0 l = fold_right (fun c acc => f (get_cls st c) + acc) 0 l.
Proof.
  induction l as [|c l IH]; intros H; cbn; [reflexivity|]. rewrite H by (left; reflexivity). rewrite IH; [reflexivity|]. intros; apply H; right; assumption.
Qed.

Lemma fold_csum_put : forall (f : aclass -> Z) st c r l,
  List.NoDup l -> In c l ->
  fold_right (fun c' acc => f (get_cls (put_cls c r st) c') + acc) 0 l
  = fold_right (fun c' acc => f (get_cls st c') + acc) 0 l - f (get_cls st c) + f r.
Proof.
  induction l as [|c0 l IH]; intros Hnd Hin; [destruct Hin|]. cbn. inversion Hnd; subst.
  destruct Hin as [->|Hin].
  - rewrite get_put_eq. rewrite (fold_csum_ext f st (put_cls c r st)); [lia|]. intros c' Hc'. apply get_put_ne. congruence.
  - rewrite get_put_ne by congruence. rewrite IH by assumption. lia.
Qed.

Lemma csum_put : forall f st c r, 1 <= c <= 31 -> csum f (put_cls c r st) = csum f st - f (get_cls st c) + f r.
Proof. intros. unfold csum. apply fold_csum_put; [apply NoDup_CLASSES| apply In_CLASSES; lia]. Qed.

Lemma csum_init_cache : forall f st, csum f (init_cache st) = csum f st.
Proof. intros. unfold init_cache. destruct (a_cinit st); reflexivity. Qed.

Lemma commit_bytes_put : forall st c r, 1 <= c <= 31 ->
  commit_bytes (put_cls c r st) = commit_bytes st - cls_mapped_bytes' (get_cls st c) + cls_mapped_bytes' r.
Proof. intros. unfold commit_bytes. rewrite csum_put by assumption. cbn [a_nres put_cls set_cls]. lia. Qed.
Lemma commit_bytes_init_cache : forall st, commit_bytes (init_cache st) = commit_bytes st.
Proof. intros. unfold commit_bytes. rewrite csum_init_cache. unfold init_cache. destruct (a_cinit st); reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition vc_cls (r : aclass) : Z := c_mapped_user r + c_mapped_user r / 8 + K_FREEARR_MAP.
Definition VC (st : astate) : Z := csum vc_cls st + 8 * a_nres st.
Definition FAINV (st : astate) : Prop :=
  forall c, 1 <= c <= 31 -> 0 <= c_mapped_free_array (get_cls st c) <= c_mapped_user (get_cls st c) / 8 + K_FREEARR_MAP
                            /\ 0 <= c_mapped_user (get_cls st c).

Lemma VC_put : forall st c r, 1 <= c <= 31 -> VC (put_cls c r st) = VC st - vc_cls (get_cls st c) + vc_cls r.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanInv ()) [] "h04__x1h14__x2h24__x3h34__x4h47__arithh54__ffh68__varmaph75__with81ch91rh:2sth;1zp;1p;2p;3p;4p;7p;5p;6g00YIj19Tg00DWj2BTg00Ygj15Tg00X;j2ETg01P\j2;Tg01F@j2?Tg01XFR0j18Tg01Hoj21Tg00^5j20Tg010=j1:Tg01Iej3=Tg01STj17Tg01TMj23Tg00CBj32Tg00`cj1STg00K@j1RTg00aCj2ATg00oAj1QTg00o_j4>Tg00aaj1PTg00b?j1OTg00cMj26Tg01J_j3<Tg00d0j34Tg00bjj2JTg01Tjj3ITg00dSj4HTg012hj7GTg00e`j2FTg00?Hj2KTg00fBj2LTg00fnj3DTg00gMj4MTg01UMj5NTg007Ij6CTg01Y>j1@Tg00OMg00?bR1g00NRg01=hR2#9f1R3'B%52R4#5#5#5#9,B3'EP1f3R5,;0R6f2R7,?5#8R8'1%83R9'0R:f0R;%:2R<#:R=#:#9R>f4R?9=57#7'3'01;0?R@%7?RA,3>'01??5#8RB'1%87RC'0521X;1g01>MRD#S%RDP1P11A1?P7%Q1C>P31A15C>%P1%O1R?g019Ng019mRDPDg01:MRDP11612R2161<R<5<11614R45411J1>161=5I1R=541g01@LA412==<1<=414CHg01:mFG1F?DP;P7g00UIRDg00UiR?'K1L;7=2D?dg01<:=D13CMb5b6b7X01X11X21X3111;3/0713>5R?'010;?/13/07521^01^11^21^31P;PAPCPBP@O4b4A=735R@#7,3>,0:%75,3>,06/18/09521e1;0@P0P5P7P3P;DNEC%@@%@5/18/09521eUW9W8W:o"). Qed.
Lemma VC_init_cache : forall st, VC (init_cache st) = VC st.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanInv ()) [] "p'0h01bi001bh12sth21zp;2p;1p;3p;6g01P\j24Tg010=j15Tg00YIj1=Tg00TLj16Tg01STj11Tg01TMj20Tg00^5j22Tg00CBj33Tg00RVj1<Tg00SPj2;Tg00?Hj28Tg01WEj29Tg007Ij6:Tg01Y>j17Tg00OMR0g00?bR1g01XFR2f0R3'4R4g01=h#5#5#5#=R5f1R6#6#1'0,231426%16,05'2R6531X21%<3g00UIR7P7f2R8,42R9P7P0P3P8g00Ui/;8n0100000020000#1,05'2%18,05,29531P31816R6P6n0110000020000b0%63R6#1,05,24%13,05,24531e14261923E:%76%73531eW1o"). Qed.
Lemma FAINV_put : forall st c r, 1 <= c <= 31 -> FAINV st ->
  0 <= c_mapped_free_array r <= c_mapped_user r / 8 + K_FREEARR_MAP -> 0 <= c_mapped_user r -> FAINV (put_cls c r st).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanInv ()) [] "p'0h03Hc'h12c'h22HFh32Hch42Hrh52Huh62NEh71ah81ch91ei001eh:1rh;1si011sh<2sti021np;1p;2p;3p;4p;6p;7p;5g00YIj1=Tg00DWj28Tg00Ygj19Tg01Z2j1@Tg01Zij16Tg01[oj12Tg010=j1<Tg01\oj24Tg00^5j23Tg01]Lj2ATg00CBj3;Tg01ILj1>Tg01]lR0j2FTg01Iej37Tg01F@j25Tg00X;j2:Tg011Mj4ETg01M_j3DTg007Ij6?Tg00C\j7CTg01K^j5BTf2R1f1R2f0R3'8':p=1g01<:/83p=0g00OMg00?bR4g00NRR5g01=hR6#=R7/82%96#9#9#9#=R8712f3R9#@%61R:#0%21%<6#<#<#=R6'4g01^LR;'371:%29#01873?138R:f7R</A2A;4<2R=%>='FP0f8R0=;41R1%>1f9R1f:R=770/59R0#6R>#0%20R0/46/3;71>%00':P3A;419R0P4P=f<R>f;R?f=37/52R2#6R@#0%22R2/46/3;71@%02':^0:X14187=?1=8P5P=%63R8#0%23R7/46/3;718%07':X75R7%6=R8#0%2=R:/46/3;718%0:P<f6R:CEA7?=>/5?AD>?=E?W0f4R>P3P9FCW9P3O1%>0P515?>P7P<P>P9O2A7=1?/5>P?P=P>P1P3DBE?W6P3O1n200110100021010010102b;W0X14f5?7>:#@eW5W4W2W3W:W8W<o"). Qed.
Lemma FAINV_init_cache : forall st, FAINV st -> FAINV (init_cache st).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanInv ()) [] "h01Hh12Hch21ah31ch42stp;1p;2p;6g01Z2j16Tg00YIj14Tg00DWj20Tg00Ygj11Tg00X;j23Tg01F@j27Tg01Zij1<Tg01[oj1;Tg010=j12Tg01\oj2:Tg00^5j28Tg00TLj15Tg01_Lj29Tg007Ij6=Tg00OMf0R0#6g00?bg01=hR1#4/00%11#1#1#1#4,00'3g00NRR2f3R3f1R4'7g01<:R5%<0R6'0%;0R7%21#2#2#4':g01^L'8,06'31057'3X22f2P4P0O2%53/741934E=W1W3%54#6eW0W4o"). Qed.

Lemma csum_le : forall f g st, (forall c, 1 <= c <= 31 -> f (get_cls st c) <= g (get_cls st c)) -> csum f st <= csum g st.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanInv ()) [] "p'0h01ch13acch21li001lh32H0h42Hlh52IHh67__arithh74__ffh88__varmaph95__with:4__x1h;4__x2h<4__x3h=4__x4h>1ah?1Gh@1HhA2HchB1fhC1ghD2sthE1xi012Ini021bi032l'p;1p;2p;3p;4p;5p;7p;8g00YIj1HTg00DWj20Tg00Ygj18Tg00X;R0j2;Tg01F@j23Tg00K@R1j1FTg00WDj34Tg00^5j21Tg00`cj1=Tg00oAj1LTg00aaj1JTg00b?j1ITg00bjj2[Tg00e`j2VTg00?Hj2DTg00fBj2UTg00CBj37Tg00fnj3TTg00gMj4STg00naj3ATg00jaj2PTg01GTj3OTg01G:j3NTg00VIj1?Tg00l:j2:Tg00mLj3>Tg00n5j2MTg00aCj2@Tg00o_j4<Tg00cMj25Tg00e>j1KTg010=j1GTg00d0j3BTg01Gnj5QTg01Naj1RTg01P\j2ETg01HPj5ZTg00dSj4YTg012hj7XTg0140j8WTg00?bR2P2f1R3g01<:R4f0R5DZp=2P2P3g018gP5CYp=9P3g019NR6g019mR7P7g01:MR8P5g01:mFXp=6f3R9P6P7P7P8f2R6P3P5GWp=Cg00NRP2]ER:g00OMg01=hR;#HR</05%8;R=#8#8#8#HR>,05';R?f4R@1363RAO1P9PAO1'0[^02%F2RAP2A425310<3103>';RB[^02RCf8RDf6RE/33RFO1/15X12X02/23f7RGPFO1/15X12X02/23'0[X2A%=2RF9425PB[^02g01>MRH#=RI%FHRJ%L2RK%J2RL%I2RM1[24RN/9N'61VM8R8P5P6g00UIRNg00UiRO'D1U56=7NOdAT243CSROb7b8b91044P5b6PGf5R4/33RNO1/15X12X02RP/2FPEPNO1/15X12X02RN/2F'0eW4f9RF13G3RQO1/15X12X02/23PDPQO1/15X12X02/23'0\CAA296RQ9425PB[^02P4P9P5P9A7299p-0RR^2A^>2P1P2PRP5g00FeA7239P@P9P5O2'Pn10110000020020102103X2AX>2p?1001101P9P6O21D293OO2O2PD13E9RRO1PGPRO1'0P6A425@P9P3A72E3A4234;N5O2UX02O1f;RR13F3RGO1/15X12X02/29f:R1PGO1/15X12X02/29'0g01<XRG#?RS#?,:21:2S1:2G5>25>2g01?`'M=AHIPJP2P21@2@P6PKC<P31@29C<PLPM152;RL152=R='9,6M%K7R7PM%G;R;,52RK%G;,52R;'9,6MP7AB2LKAB2=;'9,6MCCCCP8POb7b8b9X:2X;2X<2X=21056106@116911@4'0[[^:2^;2^<2^=2P5f<13R3R@O1/15X12X02/24P113FEREO1f=P@O1/15X12X02/24PRPEO1P6P3O6b6b5b3P113D3RDO1/15X12X02/2QPFPDO1/15X12X02/2Q'0eW4W5X2AX02P5DQW212P312N3'0\C^2AP5g01A3RAA425ARCP0PB\CRCA423ARA\?10<6106>';\A%R5P3n2001000000120000000X02PC^02P5P6P3O2b3WAX02O2b?1E931E63'0eW@WDXC:WBo"). Qed.

Lemma commit_le_VC : forall st, FAINV st -> commit_bytes st <= VC st.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanInv ()) [] "h01Hh14__x1h24__x2h34__x3h44__x4h51mh61nh71ph82H0h92H1h:2H2h;2HFh<2Hch=7__arithh>4__ffh?8__varmaph@5__withA1ahB1chC2stp;1p;2p;3p;4p;8p;7g01Z2j1YTg00DWj22Tg00^5j26Tg01`Vj3XTg01P\j2DTg010=j1=Tg00YIj1<Tg01STj1LTg01TMj2ITg00Ygj1:Tg00X;R0j28Tg01F@j20Tg01Zij15Tg01[oj14Tg01\oj27Tg01RQR1j1?Tg01XFR2j1>Tg00`cj1UTg00K@j1TTg00aCj2CTg00oAj1NTg00o_j4BTg00aaj1MTg00b?j1KTg00cMj29Tg00d0j3;Tg00dSj4@Tg00e>j1JTg0140j8HTg00e`j2GTg00?Hj2OTg00fBj2FTg00CBj3PTg00fnj3QTg00gMj4ETg01a=j4RTg01VGj1STg01Y>j1WTg012hj7VTf2R3f1R4f0R5'6'2p=1g01<:R6/25p=3P4g019NR7g019mR8P8g01:MR9P5g01:mFVp=Ag00OM%Y5g00?bR:P01234f3R;/64?134[R<1635?14512;3R=[f4R>/63?1;3\=AX345P4n2001000000120000000X7:X5:W6P<^7:^5:^6:P51D131D23g01=hR<#=R=#=R?#=#<R@%L3'IP1P2P3%<</25%:<R2#:#:#:#<,25'8P;P4P5O210>4R1#5RA#3%41R1/7@g01^LRB51A'8%31'8P0f5R1/03RA#5RC#3%4ARA/7@=1CB'8%3Af6RA/0;RC#?%>C'2P5f7RC/0>RD#5RE#3%4D/7@=1EB'8P0f8R0/01R1#5RE#3%41/7@=1EBf9RE/0A#4#3f:RA/0CRC#?%>C'2[P5%5C#3f;RC/00R0#5%40/7@;1Bf</0E#4#3g01>MRE#U%TEP:P:1C:>P3%N:CBP41C:;CB%M:%K:REP7P8P8P9P:19:=R=g018gR719:2R219:?R?5;:C@,AE%J8P:19:<R<=;:=P7A;:<2=;:?C@,AEGH1GE9P5P3g00UIREg00UiR9'O1F53=PE9dAQ:64CEb>b?b@X1:X2:X3:X4:A143;1643164;;1>[^1:^2:^3:^4:P5PBf>/0CRC#4RB/7@%5CPBP3O5b=f=/0ARA#?%>A'2eW:W9W8P4P5O2n2001000000120000000W0P4P5O2n2001000000121000000bAW<XB:CRO4b0%S4%W4'2eW;WCo"). Qed.

(* [comment removed for export] *)
Lemma zlen_app : forall {A} (l1 l2 : list A), zlen (l1 ++ l2) = zlen l1 + zlen l2.
Proof. intros. unfold zlen. rewrite length_app. lia. Qed.
Lemma zlen_cons : forall {A} (x : A) l, zlen (x :: l) = 1 + zlen l.
Proof. intros. unfold zlen. cbn [length]. lia. Qed.
Lemma zlen_nil : forall {A}, zlen (@nil A) = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanInv ()) [] "h01Ap;2p200R0p100Ijp4p710p8g00?Hj20Tg00?bg01<:'0X00o"). Qed.
Lemma zlen_nonneg : forall {A} (l : list A), 0 <= zlen l.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanInv ()) [] "h04__x1h11Ah27__arithh34__ffh48__varmaph55__with64cstrh71lp;1p;2p;4p;7p;8p;3p200R0g00IjR1p4p710p8P0g00J`R2p4p710p8g00K@j11TP2j23Tg00`>j18Tg00W[j12Tg00DWj20Tg00`cj1<Tg00aCj2;Tg00aaj17Tg00b?j15Tg00bjj26Tg00cMj24Tg00dSj49Tg012hj7:Tg00e>j1ETg0140j8DTg00e`j2CTg00?Hj2=Tg00fBj2>Tg00CBj3?Tg00fnj3@Tg00gMj4ATP1j2BTf0R1#1f1R2/31R3#8g01<:R4%23'0g00?bR3g01>MR5#<%151;32%73%53R5g019NR6g019mR7P7g01:MR8P5P6P7P7P8P31634g018gg01=h,43C9g01:mF:R6%E7P6GD1C58P1f2R8g00UIR5g00UiR6'=1>18=?56dA@342CAb3b4b5W010411042[^03P1f3/38#2P2O2b2b61B21,04eW7X10o"). Qed.

Lemma cntP_app : forall c l1 l2, cntP c (l1 ++ l2) = cntP c l1 + cntP c l2.
Proof. intros. unfold cntP. rewrite filter_app. apply zlen_app. Qed.
Lemma cntP_cons : forall c ch l, cntP c (ch :: l) = (if is_prim_of c ch then 1 else 0) + cntP c l.
Proof. intros. unfold cntP. cbn [List.filter]. destruct (is_prim_of c ch); [rewrite zlen_cons|]; lia. Qed.
Lemma cntP_nil : forall c, cntP c [] = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanInv ()) [] "h01cp;2g00?Hj20Tg00?bR0g01<:,00W0o"). Qed.
Lemma cntP_nonneg : forall c l, 0 <= cntP c l.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanInv ()) [] "h01ch11lp;1p;3p;2g00K@j15Tg01c9j14Tg01d5j30Tg01gZj21Tg01eij23Tg00DWj22Tg00?bg00L\R0#5f1R1#4f0R2500,10g01<:1312'2eW1W0o"). Qed.
Lemma secs_app : forall l1 l2, secs (l1 ++ l2) = secs l1 ++ secs l2.
Proof. intros. unfold secs. apply flat_map_app. Qed.
Lemma secs_cons : forall ch l, secs (ch :: l) = sec_of ch ++ secs l.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanInv ()) [] "h02chh11lp;1p;2p;3g00K@j10Tg00QBj25Tg01inj12Tg01i8j11Tg005^j34Tg00?Hj23Tg00L\R0%00g00?bR0/50R0#0f1#2f0#1540'3W1W0o"). Qed.
Lemma qchunks_app : forall b1 b2, qchunks (b1 ++ b2) = qchunks b1 ++ qchunks b2.
Proof. intros. unfold qchunks. apply flat_map_app. Qed.
Lemma qchunks_cons : forall b bs, qchunks (b :: bs) = b_chunks b ++ qchunks bs.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanInv ()) [] "h01bh12bsp;1p;3p;2g00K@j10Tg01k_j14Tg01jfj12Tg005^j31Tg00?Hj23Tg00MWR0%00g00L\R0#0f1#4f0#2510'3W1W0o"). Qed.
Lemma zsumc_app : forall l1 l2, zsumc (l1 ++ l2) = zsumc l1 + zsumc l2.
Proof. induction l1; intros; cbn; [lia|]. rewrite IHl1. lia. Qed.
Lemma bsum_app : forall l1 l2, bsum (l1 ++ l2) = bsum l1 + bsum l2.
Proof. induction l1; intros; cbn; [lia|]. rewrite IHl1. lia. Qed.
Lemma nbatch_app : forall c b1 b2, nbatch c (b1 ++ b2) = nbatch c b1 + nbatch c b2.
Proof. intros. unfold nbatch. destruct (c =? K_BATCH_CLASS); [apply zlen_app| lia]. Qed.

Lemma filter_perm : forall {A} (f : A -> bool) l l', Permutation l l' -> Permutation (List.filter f l) (List.filter f l').
Proof.
  intros A f l l' HP. induction HP; cbn.
  - constructor.
  - destruct (f x); [apply perm_skip|]; assumption.
  - destruct (f x), (f y); try apply perm_swap; try apply perm_skip; apply Permutation_refl.
  - eapply Permutation_trans; eassumption.
Qed.
Lemma cntP_perm : forall c l l', Permutation l l' -> cntP c l = cntP c l'.
Proof. intros. unfold cntP, zlen. rewrite (Permutation_length (filter_perm (is_prim_of c) l l' H)). reflexivity. Qed.
Lemma secs_perm : forall l l', Permutation l l' -> Permutation (secs l) (secs l').
Proof. intros. unfold secs. apply Permutation_flat_map. assumption. Qed.
Lemma zsumc_perm : forall l l', Permutation l l' -> zsumc l = zsumc l'.
Proof. intros l l' HP. induction HP; cbn; lia. Qed.

(* [comment removed for export] *)
Lemma live_chunks_insert : forall st id ch,
  (a_live st) !! id = None ->
  Permutation (live_chunks (set_live (<[id := ch]> (a_live st)) st)) (ch :: live_chunks st).
Proof.
  intros st id ch Hn. unfold live_chunks. cbn [a_live set_live].
  change (ch :: map snd (map_to_list (a_live st))) with (map snd ((id, ch) :: map_to_list (a_live st))).
  apply Permutation_map. apply map_to_list_insert. exact Hn.
Qed.
Lemma live_chunks_delete : forall st id ch,
  (a_live st) !! id = Some ch ->
  Permutation (live_chunks st) (ch :: live_chunks (set_live (delete id (a_live st)) st)).
Proof.
  intros st id ch Hs. unfold live_chunks. cbn [a_live set_live].
  change (ch :: map snd (map_to_list (delete id (a_live st)))) with (map snd ((id, ch) :: map_to_list (delete id (a_live st)))).
  apply Permutation_map. symmetry. apply map_to_list_delete. exact Hs.
Qed.

(* [comment removed for export] *)
Lemma sum_count_cons : forall P e l, sum_count P (e :: l) = iv_count P e + sum_count P l.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanInv ()) [] "h01Ph11eh21lp;1p;2g010=j10Tg02G2j18Tg02GPj12Tg00QBj21Tg00K@j17Tg02H3j26Tg02I2j23Tg00^5j24Tg00?Hj25Tg00?bR0g00UI[g01=h#0#0#0#0#0#0#8#2R1/11R1%71f2R1f1'6f0,31'4,50W2W1W0o"). Qed.
Lemma sum_count_perm : forall P l l', Permutation l l' -> sum_count P l = sum_count P l'.
Proof. intros P l l' HP. induction HP; rewrite ?sum_count_cons; lia. Qed.
Lemma iv_count_nonneg : forall P e, 0 <= iv_count P e.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanInv ()) [] "h01Ph11ep;1p;2p;3g010=j10Tg02G2j19Tg02GPj12Tg00QBj21Tg02K2j18Tg02Kjj17Tg00h?j13Tg02Lbj34Tg02H3j25Tg00DWj26Tg00?bg00UI[g01=h#0#0#0#0#0#0#9#2R0/10f1R0f0R1#8%71#334g01<:1501'6eW1W0o"). Qed.
Lemma iv_count_le_S : forall P e, iv_count P e <= S e.
Proof. intros. unfold iv_count. pose proof (zcount_le_len P (B e) (Z.to_nat (S e))). pose proof (S_range e). lia. Qed.
Lemma sum_count_le_live : forall P l, sum_count P l <= live_bytes l.
Proof.
  intros P l. rewrite live_bytes_sum_count. induction l; rewrite ?sum_count_cons; [cbn; lia|].
  pose proof (iv_count_le_S P a). unfold iv_count at 2. unfold iv_count in H. rewrite zcount_const_true.
  pose proof (S_range a). rewrite Z2Nat.id by lia. cbn [sum_count] in *. unfold iv_count in *. rewrite ?zcount_const_true in IHl. lia.
Qed.
Lemma sum_count_ext_on : forall P Q l,
  (forall e x, In e l -> B e <= x < B e + S e -> P x = Q x) -> sum_count P l = sum_count Q l.
Proof.
  intros P Q l H. induction l as [|e l IH]; [reflexivity|]. rewrite !sum_count_cons.
  rewrite IH by (intros e' x' He' Hx'; apply (H e' x'); [right|]; assumption).
  unfold iv_count. rewrite (zcount_ext P Q); [lia|]. intros x Hx. apply (H e); [left; reflexivity|].
  pose proof (S_range e). rewrite Z2Nat.id in Hx by lia. lia.
Qed.
Lemma sum_count_sub : forall P l1 l2, sum_count P l1 <= sum_count P (l1 ++ l2).
Proof. intros. rewrite sum_count_app. pose proof (sum_count_nonneg P l2). lia. Qed.

(* [comment removed for export] *)
Lemma wsep_sym : forall p q, wsep p q -> wsep q p.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanInv ()) [] "h04__x1h14__x2h24__x3h34__x4h41ph51qh67__arithh74__ffh88__varmaph95__witp;1p;2p;3p;4p;8p;7g010=j13Tg02G2j1QTg02GPj1ETg00QBj2ATg005Aj36Tg02Z>j20Tg02;Vj34Tg00^5j22Tg00DWj21Tg00jaj27Tg00`cj1@Tg00K@j1?Tg00aCj28Tg00oAj1PTg00o_j4>Tg00aaj1OTg00b?j1LTg00Ygj1KTg00cMj25Tg00d0j3<Tg00dSj49Tg00e>j1DTg0140j8FTg00e`j2CTg00?Hj2GTg00fBj2HTg00CBj3BTg00fnj3ITg00gMj4JTg02Zhj2=Tg012hj7MTg015]j7NTf1R0g019NR1g019mR2P2g01:MR3f0R4g01:mFMp=:f2R5P1P2P2P3P0P4FNp=;g01=hR6#3R7#3R8#3#3#3#3#QR9#ER:/A:R;A6::0,09R<A4::0,09'2A6::4,09R='1A4::4,09,2=/1<'7g00?bR<g01>MR=#@%?=P<P<f4R=,8<P5%P<C>P0f3R>,8<C>%O<%L<R?P1P2P2P3P<%K6,5<R115<85<<g018gR815<6R6C9,:?R@P<15<79<<6P8P1C9,:?R15;?%D2A;?1@GF1C?3P4P5g00UIR?g00UiR3'G1H45=B?3dg01<:=I<0CJb7b8b9X0<X1<X2<W3125>/141240/15'71205/1>12>=/10'7[^0<^1<^2<^3<P4A4::>,09A6::>,09A4::5,09A6::5,09P0O5b6UX5;W41=041=05[^5;^4;eo"). Qed.
Lemma seps_perm : forall l l', Permutation l l' -> seps l -> seps l'.
Proof.
  intros l l' HP. induction HP; intros Hs.
  - constructor.
  - inversion Hs; subst. constructor; [| auto]. eapply Permutation_Forall; eauto.
  - inversion Hs; subst. inversion H2; subst. apply Forall_cons_iff in H1 as [Hxy Hl].
    constructor. { constructor; [apply wsep_sym; exact Hxy| exact H3]. } constructor; assumption.
  - auto.
Qed.
Lemma seps_cons_inv : forall p l, seps (p :: l) -> Forall (wsep p) l /\ seps l.
Proof. intros p l H. inversion H; auto. Qed.
Lemma seps_app_inv_l : forall l1 l2, seps (l1 ++ l2) -> seps l2.
Proof. induction l1; intros l2 H; [exact H|]. cbn in H. apply seps_cons_inv in H as [_ H]. auto. Qed.
Lemma seps_In_wsep : forall l p q, seps l -> In p l -> In q l -> p = q \/ wsep p q.
Proof.
  induction l as [|e l IH]; intros p q H Hp Hq; [destruct Hp|].
  apply seps_cons_inv in H as [Hf Hl]. rewrite Forall_forall in Hf.
  destruct Hp as [<-|Hp], Hq as [<-|Hq].
  - left; reflexivity.
  - right. exact (Hf q Hq).
  - right. apply wsep_sym. exact (Hf p Hp).
  - apply IH; assumption.
Qed.

(* LPS 727298f3: munmap subtracts its range from [vm_maps]; on separated entries of
   positive size the range of one entry is that entry alone. *)
Lemma seps_maps_subtract_exact : forall ATOP l (a n : word),
  seps l -> Forall (entry_ok ATOP) l -> In (a, n) l ->
  maps_subtract l (bv_unsigned a) (bv_unsigned a + bv_unsigned n) = map_remove l a.
Proof.
  intros ATOP l a n Hs Hok Hin. rewrite Forall_forall in Hok.
  apply maps_subtract_exact.
  - exact (proj1 (Hok _ Hin)).
  - intros b s H. exact (proj1 (Hok _ H)).
  - intros b s H ->. destruct (seps_In_wsep _ _ _ Hs H Hin) as [E|D].
    + apply (f_equal snd) in E. exact E.
    + exfalso. pose proof (proj1 (Hok _ H)) as W. pose proof (proj1 (Hok _ Hin)) as W2.
      unfold wsep in D. cbn [fst snd] in D, W, W2. lia.
  - intros b s H Hne. destruct (seps_In_wsep _ _ _ Hs H Hin) as [E|D].
    + exfalso. apply (f_equal fst) in E. exact (Hne E).
    + unfold wsep in D. cbn [fst snd] in D. exact D.
Qed.
(* [comment removed for export] *)
Lemma region_free_wsep : forall l (a n : word),
  region_free l a n = true -> Forall (wsep (a, n)) l.
Proof.
  induction l as [|[b s] l IH]; intros a n H; [constructor|].
  cbn [region_free] in H. apply andb_true_iff in H as [H1 H2]. constructor; [|apply IH; exact H2].
  apply negb_true_iff in H1. unfold iv_overlap in H1. unfold wsep. cbn [fst snd].
  apply andb_false_iff in H1 as [H1|H1]; apply Z.ltb_ge in H1; lia.
Qed.

(* [comment removed for export] *)
Lemma overlap_sum_contained : forall l e lo hi,
  seps l -> In e l -> B e <= lo -> hi <= B e + S e -> lo <= hi ->
  overlap_sum l lo hi <= hi - lo.
Proof.
  intros l e lo hi Hs Hin H1 H2 Hlh. apply in_split in Hin as (l1 & l2 & ->).
  unfold overlap_sum. rewrite sum_count_app, sum_count_cons.
  assert (Z0 : forall l', Forall (wsep e) l' -> sum_count (in_rng lo hi) l' = 0).
  { intros l' Hf. induction l' as [|q l' IH]; [reflexivity|]. rewrite sum_count_cons. apply Forall_cons_iff in Hf as [Hq Hf].
    rewrite IH by exact Hf. fold (iv_count (in_rng lo hi) q). rewrite iv_count_in_rng_disjoint; [lia|].
    unfold wsep, B, S in *. lia. }
  pose proof (seps_perm _ _ (Permutation_sym (Permutation_middle l1 l2 e)) Hs) as Hs'.
  apply seps_cons_inv in Hs' as [Hf _]. apply Forall_app in Hf as [Hf1 Hf2].
  rewrite (Z0 l1 Hf1), (Z0 l2 Hf2). pose proof (iv_count_in_rng_le e lo hi Hlh). lia.
Qed.

(* [comment removed for export] *)
Lemma map_remove_perm : forall l (b s : word) l2,
  Permutation l ((b, s) :: l2) -> seps l -> 0 < bv_unsigned s -> Forall (fun e => 0 < bv_unsigned (snd e)) l2 ->
  Permutation (map_remove l b) l2.
Proof.
  intros l b s l2 HP Hs Hpos Hall.
  unfold map_remove. rewrite (filter_perm _ _ _ HP). cbn [List.filter fst]. rewrite bv_eqb_refl. cbn [negb].
  pose proof (seps_perm _ _ HP Hs) as Hs'. apply seps_cons_inv in Hs' as [Hf _].
  assert (E : List.filter (fun p : word * word => negb (bv_eqb (fst p) b)) l2 = l2).
  { clear HP Hs. induction l2 as [|[b' s'] l2 IH]; [reflexivity|]. apply Forall_cons_iff in Hf as [H1 Hf]. apply Forall_cons_iff in Hall as [H2 Hall].
    cbn [List.filter fst]. destruct (bv_eqb b' b) eqn:E.
    - exfalso. apply bv_eqb_eq in E. subst b'. unfold wsep in H1. cbn [fst snd] in H1, H2. lia.
    - cbn [negb]. rewrite IH; auto. }
  rewrite E. apply Permutation_refl.
Qed.

(* [comment removed for export] *)
Lemma map_contains_In : forall l e (a n : word),
  In e l -> bv_unsigned (fst e) <= bv_unsigned a -> bv_unsigned a + bv_unsigned n <= bv_unsigned (fst e) + bv_unsigned (snd e) ->
  map_contains l a n = true.
Proof.
  intros l e a n Hin H1 H2. unfold map_contains. apply existsb_exists. exists e. split; [exact Hin|].
  apply andb_true_iff. split; apply Z.leb_le; lia.
Qed.
Lemma map_has_In : forall l (a n : word), In (a, n) l -> map_has l a n = true.
Proof. intros. unfold map_has. apply existsb_exists. exists (a, n). split; [assumption|]. cbn. rewrite !bv_eqb_refl. reflexivity. Qed.

(* [comment removed for export] *)
Lemma iv_subtract_region_free : forall (a sz : word) lo hi (p n : word),
  bv_unsigned a + bv_unsigned sz <= 2^64 ->
  iv_overlap p n a sz = false ->
  region_free (iv_subtract a sz lo hi) p n = true.
Proof.
  intros a sz lo hi p n Hwf Hov. unfold iv_subtract. cbv zeta.
  pose proof (bv_unsigned_in_range 64 a) as Ra. pose proof (bv_unsigned_in_range 64 sz) as Rs.
  change (bv_modulus 64) with (2^64) in Ra, Rs.
  assert (Hov' : bv_unsigned p >= bv_unsigned a + bv_unsigned sz \/ bv_unsigned a >= bv_unsigned p + bv_unsigned n).
  { unfold iv_overlap in Hov. apply andb_false_iff in Hov as [H|H]; apply Z.ltb_ge in H; lia. }
  assert (L : forall b s : Z, 0 <= b < 2^64 -> 0 <= s < 2^64 -> bv_unsigned a <= b -> b + s <= bv_unsigned a + bv_unsigned sz ->
              iv_overlap p n (Z_to_bv 64 b) (Z_to_bv 64 s) = false).
  { intros b s0 Hb Hs H1 H2. unfold iv_overlap. rewrite (unsigned_lit b), (unsigned_lit s0) by lia.
    apply andb_false_iff. destruct Hov'; [left|right]; apply Z.ltb_ge; lia. }
  assert (L2 : forall s : Z, 0 <= s <= bv_unsigned sz -> iv_overlap p n a (Z_to_bv 64 s) = false).
  { intros s0 Hs. unfold iv_overlap. rewrite (unsigned_lit s0) by lia.
    apply andb_false_iff. destruct Hov'; [left|right]; apply Z.ltb_ge; lia. }
  pose proof (Z.min_spec (bv_unsigned sz) (lo - bv_unsigned a)) as Hmin.
  pose proof (Z.max_spec (bv_unsigned a) hi) as Hmax.
  destruct (Z.ltb_spec (bv_unsigned a) lo) as [H1|H1]; destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)) as [H2|H2];
    cbn [app region_free]; rewrite ?andb_true_r; try reflexivity.
  - rewrite L2 by (clear - Hmin H1 Rs; lia). rewrite L by (clear - Hmax H2 Hwf Ra Rs; lia). reflexivity.
  - rewrite L2 by (clear - Hmin H1 Rs; lia). reflexivity.
  - rewrite L by (clear - Hmax H2 Hwf Ra Rs; lia). reflexivity.
Qed.

Lemma region_free_maps_subtract : forall l lo hi (p n : word),
  ivs_wf l -> region_free l p n = true -> region_free (maps_subtract l lo hi) p n = true.
Proof.
  induction l as [|[a sz] l IH]; intros lo hi p n Hwf H; [reflexivity|].
  cbn [maps_subtract]. cbn [region_free] in H. apply andb_true_iff in H as [H1 H2]. apply negb_true_iff in H1.
  assert (E : forall l1 l2, region_free (l1 ++ l2) p n = region_free l1 p n && region_free l2 p n).
  { induction l1 as [|[b s0] l1 IH1]; intros; cbn; [reflexivity|]. rewrite IH1. apply andb_assoc. }
  rewrite E. apply andb_true_iff. split.
  - apply iv_subtract_region_free; [|exact H1]. specialize (Hwf (a, sz) (or_introl eq_refl)). unfold iv_wf, B, S in Hwf. exact Hwf.
  - apply IH; [|exact H2]. intros q Hq. apply Hwf. right. exact Hq.
Qed.

(* [comment removed for export] *)
Lemma region_free_of_bytes : forall na lo sz,
  0 <= lo -> 0 < sz -> lo + sz < 2^64 ->
  Forall (fun iv : word * word => 0 < bv_unsigned (snd iv)) na ->
  (forall iv x, In iv na -> lo <= x < lo + sz -> ~ (bv_unsigned (fst iv) <= x < bv_unsigned (fst iv) + bv_unsigned (snd iv))) ->
  region_free na (Z_to_bv 64 lo) (Z_to_bv 64 sz) = true.
Proof.
  induction na as [|[a s0] na IH]; intros lo sz Hlo Hsz Hhi Hpos Hb; [reflexivity|].
  apply Forall_cons_iff in Hpos as [Hp Hpos]. cbn [snd] in Hp.
  cbn [region_free]. rewrite (IH lo sz Hlo Hsz Hhi Hpos) by (intros iv x Hin; apply Hb; right; exact Hin). rewrite andb_true_r.
  apply negb_true_iff. unfold iv_overlap. rewrite !unsigned_lit by lia.
  destruct (Z.ltb_spec lo (bv_unsigned a + bv_unsigned s0)) as [H1|H1]; [|reflexivity].
  destruct (Z.ltb_spec (bv_unsigned a) (lo + sz)) as [H2|H2]; [|reflexivity]. exfalso.
  destruct (Z_le_gt_dec lo (bv_unsigned a)) as [L|G].
  - apply (Hb (a, s0) (bv_unsigned a) (or_introl eq_refl)); cbn [fst snd]; lia.
  - apply (Hb (a, s0) lo (or_introl eq_refl)); cbn [fst snd]; lia.
Qed.

Lemma noacc_clear_subtract : forall l lo hi, ivs_wf l -> noacc_clear l -> noacc_clear (maps_subtract l lo hi).
Proof. intros l lo hi Hwf [H1 H2]. split; apply region_free_maps_subtract; assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* LPS 727298f3: a range inside a mapping misses what the mapping misses *)
Lemma ami_region_free_within : forall R (a n a' n' : word), region_free R a n = true ->
  bv_unsigned a <= bv_unsigned a' -> bv_unsigned a' + bv_unsigned n' <= bv_unsigned a + bv_unsigned n ->
  region_free R a' n' = true.
Proof.
  induction R as [|[b s] R IH]; intros a n a' n' H H1 H2; [reflexivity|].
  cbn [region_free] in H |- *. apply andb_prop in H as [H0 H]. rewrite (IH a n a' n' H H1 H2), andb_true_r.
  unfold iv_overlap in *. apply negb_true_iff in H0. apply negb_true_iff.
  apply andb_false_iff in H0. apply andb_false_iff.
  destruct H0 as [H0|H0]; apply Z.ltb_ge in H0; [left|right]; apply Z.ltb_ge; lia.
Qed.

(* LPS 727298f3: a new mapping that misses the reserved ledger keeps the mappings clear of it *)
Lemma ami_maps_resv_cons : forall R maps (a n : word),
  (forall e, In e maps -> region_free R (fst e) (snd e) = true) ->
  region_free R a n = true ->
  forall e, In e ((a, n) :: maps) -> region_free R (fst e) (snd e) = true.
Proof. intros R maps a n Hm Hr e [<-|He]; [exact Hr| exact (Hm e He)]. Qed.

Section AMIT.
Variable RESV : list (Z * Z).
Variable ATOP : Z.
Local Notation AMI' := (AMI RESV ATOP).

Lemma AMI_with_fds : forall ch st f mo, AMI' ch st (with_fds f mo) <-> AMI' ch st mo.
Proof. intros. unfold AMI, Pm. cbn. tauto. Qed.

Lemma AMI_atop : forall ch st mo, AMI' ch st mo -> atop_ok ATOP /\ alloc_top (m_vmmaps mo) = ATOP.
Proof. intros ch st mo (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & MT & _). exact MT. Qed.

Lemma AMI_mono : forall ch st st' mo,
  AMI' ch st mo -> a_space_beg st' = a_space_beg st -> a_ptr_array st' = a_ptr_array st ->
  commit_bytes st <= commit_bytes st' -> AMI' ch st' mo.
Proof.
  intros ch st st' mo H Hsb Hpa Hcb. unfold AMI in *.
  destruct H as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & MT & MN & L0 & HP & HS & HB).
  repeat (split; [assumption|]). exists L0. split; [exact HP|]. split.
  - unfold START in *. rewrite Hsb, Hpa. exact HS.
  - lia.
Qed.

(* [comment removed for export] *)
Lemma AMI_ivs_wf : forall ch st mo, AMI' ch st mo -> model_ivs_wf mo.
Proof.
  intros ch st mo (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & [[T1 T2] T3] & _).
  unfold ACEIL, ATOP_MAX in T1, T2.
  split; [|split; [|split]].
  - intros q Hq. unfold iv_wf, B, S. destruct (proj1 (Forall_forall _ _) M6 q Hq) as (_ & _ & _ & Hhi). lia.
  - exact M7.
  - exact M8.
  - (* [comment removed for export] *) unfold AsanCeil.init_sp_ok. unfold alloc_top, stack_max_size in T3. unfold sp_window_lo. lia.
Qed.

Lemma nonlazy_sum_count : forall mo, m_vm_materialized mo = [] -> model_ivs_wf mo ->
  nonlazy_bytes mo = sum_count (Pm mo) (vm_maps (m_vmmaps mo)).
Proof.
  intros mo Hm Hwf. pose proof (vm_backing_used_sem mo Hwf) as E. rewrite vm_backing_used_split, Hm in E. cbn [length Z.of_nat] in E.
  unfold Pm. lia.
Qed.

Fixpoint zsum2 (l : list (Z * Z)) : Z := match l with [] => 0 | e :: l' => snd e + zsum2 l' end.

Lemma live_bytes_went : forall ch, Forall (fun e => 0 <= snd e < 2^64) ch -> live_bytes (map went ch) = zsum2 ch.
Proof.
  induction ch as [|[mb ms] ch IH]; intros Hf; [reflexivity|]. apply Forall_cons_iff in Hf as [H1 Hf]. cbn [map zsum2 snd fst] in *.
  change (live_bytes (went (mb, ms) :: map went ch)) with (bv_unsigned (snd (went (mb, ms))) + live_bytes (map went ch)).
  cbn [snd went fst]. rewrite unsigned_lit by lia. rewrite IH by exact Hf. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma AMI_nonlazy_bound : forall ch st mo,
  AMI' ch st mo -> Forall (fun e => 0 <= snd e < 2^64) ch ->
  nonlazy_bytes mo <= EAGER0 + commit_bytes st + zsum2 ch.
Proof.
  intros ch st mo H Hch. pose proof (AMI_ivs_wf _ _ _ H) as Hwf.
  destruct H as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & MT & MN & L0 & HP & HS & HB).
  rewrite (nonlazy_sum_count mo M1 Hwf). rewrite (sum_count_perm _ _ _ HP), sum_count_app.
  pose proof (sum_count_le_live (Pm mo) (map went ch)). rewrite live_bytes_went in H by exact Hch. lia.
Qed.

Lemma region_free_app : forall l1 l2 (a n : word), region_free (l1 ++ l2) a n = region_free l1 a n && region_free l2 a n.
Proof. induction l1 as [|[b s] l1 IH]; intros; cbn; [reflexivity|]. rewrite IH. apply andb_assoc. Qed.

(* [comment removed for export] *)
Lemma AMI_grant : forall ch st mo z nZ,
  AMI' ch st mo ->
  z mod 4096 = 0 -> 0 < z -> z + nZ <= ATOP -> nZ mod 4096 = 0 -> 0 < nZ ->
  region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (Z_to_bv 64 z) (Z_to_bv 64 nZ) = true ->
  AMI' ((z, nZ) :: ch) st (grant_model mo z nZ).
Proof.
  intros ch st mo z nZ H Hal Hz Hce Hnl Hn Hrf.
  destruct H as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & MT & MN & L0 & HP & HS & HB).
  pose proof MT as [[T1 T2] T3]. unfold ACEIL, ATOP_MAX in T1, T2.
  unfold AMI, grant_model. cbn -[Z.add Z.mul Z.pow Z_to_bv bv_unsigned sum_count Pm live_bytes zlen].
  repeat match goal with |- _ /\ _ => split end; try assumption.
  - (* LPS 727298f3: the new mapping misses the reserved ledger *)
    intros e He. rewrite region_free_app in Hrf. apply andb_true_iff in Hrf as [Hrf _].
    exact (ami_maps_resv_cons _ _ _ _ M3 Hrf e He).
  - constructor; [|exact M6]. unfold entry_ok. cbn [fst snd]. rewrite !unsigned_lit by lia. repeat split; lia.
  - constructor; [|exact M9]. rewrite region_free_app in Hrf. apply andb_true_iff in Hrf as [_ Hrf].
    apply (region_free_wsep (vm_maps (m_vmmaps mo)) (Z_to_bv 64 z) (Z_to_bv 64 nZ)). exact Hrf.
  - exact (proj1 MT).
  - exists L0. split; [|split; [exact HS| exact HB]].
    change ((Z_to_bv 64 z, Z_to_bv 64 nZ) :: vm_maps (m_vmmaps mo)) with (went (z, nZ) :: vm_maps (m_vmmaps mo)).
    cbn [map]. eapply Permutation_trans; [apply perm_skip; exact HP|]. apply Permutation_middle.
Qed.

Lemma covered_cons : forall e l x, covered (e :: l) x = in_iv e x || covered l x.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanInv ()) ["AMIT"] "h01eh11lh21xp;1p;2g010=j10Tg02G2j18Tg02GPj12Tg00QBj21Tg00K@j17Tg04@gj26Tg03Uhj23Tg04Acj24Tg00?Hj25Tg01=h#0#0#0#0#0#0#8#2R0/10R0%70g00?bg00UIf2f0R0'6f1/30'4'5W2W1W0o"). Qed.

(* [comment removed for export] *)
Lemma AMI_commit : forall ch st st' mo E a n,
  AMI' ch st mo ->
  In E (vm_maps (m_vmmaps mo)) -> B E <= a -> a + n <= B E + S E -> a mod 4096 = 0 -> n mod 4096 = 0 -> 0 < n ->
  a_space_beg st' = a_space_beg st -> a_ptr_array st' = a_ptr_array st -> commit_bytes st + n <= commit_bytes st' ->
  AMI' ch st' (fixed_model mo F_FIXED a n).
Proof.
  intros ch st st' mo E a n H HinE HE1 HE2 Hal Hnl Hn Hsb Hpa Hcb.
  pose proof (AMI_ivs_wf _ _ _ H) as (Wm & Wn & Wl & Wsp).
  destruct H as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & MT & MN & L0 & HP & HS & HB).
  pose proof MT as [[T1 T2] T3]. unfold ACEIL, ATOP_MAX in T1, T2.
  assert (HEok : bv_unsigned (fst E) + bv_unsigned (snd E) <= ATOP) by (destruct (proj1 (Forall_forall _ _) M6 E HinE) as (_ & _ & _ & ?); assumption).
  assert (Ha : 0 <= a /\ a + n < 2^64) by (unfold B, S in *; pose proof (bv_unsigned_in_range 64 (fst E)); lia).
  unfold fixed_model, with_mmap_replacement, with_mmap_backing. change (mmap_noreserve_b (Z_to_bv 64 F_FIXED)) with false. cbv iota.
  rewrite !unsigned_lit by lia.
  unfold AMI. model_proj. unfold mmap_fixed_rw_next. cbn [vm_reserved vm_maps vm_noaccess vm_limit vm_start_brk vm_brk vm_mmap_base vm_init_sp alloc_top].
  rewrite !unsigned_lit by lia. rewrite M1. cbn [List.filter].
  repeat match goal with |- _ /\ _ => split end; try assumption.
  all: try exact (proj1 MT).
  all: try (unfold alloc_top in *; cbn [vm_init_sp] in *; lia).
  - reflexivity.
  - apply maps_subtract_wf; [exact Wn| lia].
  - apply maps_subtract_wf; [exact Wl| lia].
  - apply noacc_clear_subtract; [exact Wn| exact MN].
  - exists L0. split; [exact HP|]. split. { unfold START in *. rewrite Hsb, Hpa. exact HS. }
    destruct (maps_subtract_sem _ a (a + n) Wn ltac:(lia)) as (_ & _ & Cn).
    destruct (maps_subtract_sem _ a (a + n) Wl ltac:(lia)) as (_ & _ & Cl).
    eapply Z.le_trans.
    { apply (sum_count_mono _ (fun x => Pm mo x || in_rng a (a + n) x)).
      intros x. unfold Pm. model_proj. cbn [vm_noaccess]. rewrite !covered_app, Cn, Cl.
      destruct (covered (vm_noaccess (m_vmmaps mo)) x), (covered (m_vm_lazy mo) x), (in_rng a (a + n) x); cbn; congruence. }
    eapply Z.le_trans; [apply sum_count_or_le|].
    fold (overlap_sum L0 a (a + n)).
    assert (HO : overlap_sum L0 a (a + n) <= n); [|lia].
    eapply Z.le_trans. { unfold overlap_sum. apply (sum_count_sub _ L0 (map went ch)). }
    fold (overlap_sum (L0 ++ map went ch) a (a + n)). unfold overlap_sum. rewrite <- (sum_count_perm _ _ _ HP).
    fold (overlap_sum (vm_maps (m_vmmaps mo)) a (a + n)).
    pose proof (overlap_sum_contained (vm_maps (m_vmmaps mo)) E a (a + n) M9 HinE HE1 HE2 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma AMI_recommit : forall ch st mo E a n,
  AMI' ch st mo ->
  In E (vm_maps (m_vmmaps mo)) -> B E <= a -> a + n <= B E + S E -> a mod 4096 = 0 -> n mod 4096 = 0 -> 0 < n ->
  AMI' ch st (fixed_model mo F_FIXNORES a n).
Proof.
  intros ch st mo E a n H HinE HE1 HE2 Hal Hnl Hn.
  pose proof (AMI_ivs_wf _ _ _ H) as (Wm & Wn & Wl & Wsp).
  destruct H as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & MT & MN & L0 & HP & HS & HB).
  pose proof MT as [[T1 T2] T3]. unfold ACEIL, ATOP_MAX in T1, T2.
  assert (HEok : bv_unsigned (fst E) + bv_unsigned (snd E) <= ATOP) by (destruct (proj1 (Forall_forall _ _) M6 E HinE) as (_ & _ & _ & ?); assumption).
  assert (Ha : 0 <= a /\ a + n < 2^64) by (unfold B, S in *; pose proof (bv_unsigned_in_range 64 (fst E)); lia).
  unfold fixed_model, with_mmap_replacement, with_mmap_backing. change (mmap_noreserve_b (Z_to_bv 64 F_FIXNORES)) with true. cbv iota.
  rewrite !unsigned_lit by lia.
  pose proof (lazy_interior_aligned (Z_to_bv 64 a) (Z_to_bv 64 n)) as HLI. rewrite !unsigned_lit in HLI by lia.
  specialize (HLI ltac:(unfold page_size; lia) ltac:(unfold page_size; lia) Hn ltac:(lia)).
  unfold AMI. model_proj. rewrite HLI. unfold mmap_fixed_rw_next. cbn [vm_reserved vm_maps vm_noaccess vm_limit vm_start_brk vm_brk vm_mmap_base vm_init_sp alloc_top app].
  rewrite !unsigned_lit by lia. rewrite M1. cbn [List.filter].
  repeat match goal with |- _ /\ _ => split end; try assumption.
  all: try exact (proj1 MT).
  all: try (unfold alloc_top in *; cbn [vm_init_sp] in *; lia).
  - reflexivity.
  - apply maps_subtract_wf; [exact Wn| lia].
  - apply ivs_wf_cons. { unfold iv_wf, B, S. cbn [fst snd]. rewrite !unsigned_lit by lia. lia. } apply maps_subtract_wf; [exact Wl| lia].
  - apply noacc_clear_subtract; [exact Wn| exact MN].
  - exists L0. split; [exact HP|]. split; [exact HS|].
    destruct (maps_subtract_sem _ a (a + n) Wn ltac:(lia)) as (_ & _ & Cn).
    destruct (maps_subtract_sem _ a (a + n) Wl ltac:(lia)) as (_ & _ & Cl).
    eapply Z.le_trans; [| exact HB]. apply sum_count_mono.
    intros x. unfold Pm. model_proj. rewrite HLI. cbn [vm_noaccess app]. rewrite !covered_app, covered_cons, Cn, Cl.
    unfold in_iv, B, S. cbn [fst snd]. rewrite !unsigned_lit by lia.
    destruct (covered (vm_noaccess (m_vmmaps mo)) x), (covered (m_vm_lazy mo) x), (in_rng a (a + n) x); cbn; congruence.
Qed.

Lemma seps_filter : forall f l, seps l -> seps (List.filter f l).
Proof.
  induction l as [|e l IH]; intros Hs; [constructor|]. apply seps_cons_inv in Hs as [Hf Hs]. cbn.
  destruct (f e); [|apply IH; exact Hs]. constructor; [|apply IH; exact Hs].
  apply (Forall_incl _ _ _ (incl_filter f l)) || (rewrite Forall_forall in *; intros q Hq; apply Hf; apply (incl_filter f l); exact Hq).
Qed.

(* [comment removed for export] *)
Lemma AMI_munmap : forall ch1 ch2 st st' mo mb ms,
  AMI' (ch1 ++ (mb, ms) :: ch2) st mo -> 0 < mb -> 0 < ms -> mb + ms <= ATOP ->
  a_space_beg st' = a_space_beg st -> a_ptr_array st' = a_ptr_array st -> commit_bytes st <= commit_bytes st' ->
  AMI' (ch1 ++ ch2) st' (munmap_model mo mb ms).
Proof.
  intros ch1 ch2 st st' mo mb ms H Hmb Hms Hce Hsb Hpa Hcb.
  pose proof (AMI_ivs_wf _ _ _ H) as (Wm & Wn & Wl & Wsp).
  destruct H as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & MT & MN & L0 & HP & HS & HB).
  pose proof MT as [[T1 T2] T3]. unfold ACEIL, ATOP_MAX in T1, T2.
  assert (HP2 : Permutation (vm_maps (m_vmmaps mo)) (went (mb, ms) :: (L0 ++ map went (ch1 ++ ch2)))).
  { eapply Permutation_trans; [exact HP|]. rewrite !map_app. cbn [map]. rewrite !app_assoc.
    apply Permutation_sym. apply Permutation_middle. }
  pose proof (seps_perm _ _ HP2 M9) as Hs2. apply seps_cons_inv in Hs2 as [Hfar _].
  assert (HR : Permutation (map_remove (vm_maps (m_vmmaps mo)) (Z_to_bv 64 mb)) (L0 ++ map went (ch1 ++ ch2))).
  { apply (map_remove_perm _ (Z_to_bv 64 mb) (Z_to_bv 64 ms)); [exact HP2| exact M9| rewrite unsigned_lit by lia; lia|].
    assert (HF : Forall (fun e : word * word => 0 < bv_unsigned (snd e)) (vm_maps (m_vmmaps mo))).
    { eapply Forall_impl; [|exact M6]. intros e (He & _). exact He. }
    pose proof (Permutation_Forall HP2 HF) as HF2. apply Forall_cons_iff in HF2 as [_ HF2]. exact HF2. }
  unfold munmap_model, with_mmap_destroyed. rewrite !unsigned_lit by lia.
  unfold AMI. model_proj. cbn [vm_reserved vm_maps vm_noaccess vm_limit vm_start_brk vm_brk vm_mmap_base vm_init_sp alloc_top].
  rewrite M1. cbn [List.filter].
  repeat match goal with |- _ /\ _ => split end; try assumption.
  all: try exact (proj1 MT).
  all: try (unfold alloc_top in *; cbn [vm_init_sp] in *; lia).
  - reflexivity.
  - (* LPS 727298f3: the mappings left are among the old ones *)
    unfold map_remove. intros e He. apply M3. apply (incl_filter _ _ _ He).
  - unfold map_remove. rewrite Forall_forall in *. intros e He. apply M6. apply (incl_filter _ _ _ He).
  - apply maps_subtract_wf; [exact Wn| lia].
  - apply maps_subtract_wf; [exact Wl| lia].
  - unfold map_remove. apply seps_filter. exact M9.
  - apply noacc_clear_subtract; [exact Wn| exact MN].
  - exists L0. split; [exact HR|]. split. { unfold START in *. rewrite Hsb, Hpa. exact HS. }
    destruct (maps_subtract_sem _ mb (mb + ms) Wn ltac:(lia)) as (_ & _ & Cn).
    destruct (maps_subtract_sem _ mb (mb + ms) Wl ltac:(lia)) as (_ & _ & Cl).
    rewrite (sum_count_ext_on _ (Pm mo)); [lia|].
    intros e x He Hx. unfold Pm. model_proj. cbn [vm_noaccess]. rewrite !covered_app, Cn, Cl.
    apply Forall_app in Hfar as [HfL _]. pose proof (proj1 (Forall_forall _ _) HfL e He) as Hw.
    unfold wsep, B, S in *. cbn [fst snd went] in Hw. rewrite !unsigned_lit in Hw by lia.
    replace (in_rng mb (mb + ms) x) with false.
    2:{ symmetry. unfold in_rng. apply andb_false_iff. destruct Hw; [right; apply Z.ltb_ge| left; apply Z.leb_gt]; lia. }
    destruct (covered (vm_noaccess (m_vmmaps mo)) x), (covered (m_vm_lazy mo) x); reflexivity.
Qed.
End AMIT.
(* [comment removed for export] *)
Arguments AMI_with_fds {RESV ATOP}.
Arguments AMI_atop {RESV ATOP}.
Arguments AMI_mono {RESV ATOP}.
Arguments AMI_ivs_wf {RESV ATOP}.
Arguments AMI_nonlazy_bound {RESV ATOP}.
Arguments AMI_grant {RESV ATOP}.
Arguments AMI_commit {RESV ATOP}.
Arguments AMI_recommit {RESV ATOP}.
Arguments AMI_munmap {RESV ATOP}.
