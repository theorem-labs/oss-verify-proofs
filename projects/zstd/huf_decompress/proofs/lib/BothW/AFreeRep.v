(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (60 recorded proofs replaced by written proofs (NoDup_app_l, NoDup_app_r, NoDup_mid and 57 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase ARep ARepQ ARepFrame ARepKit AHeapP AFreeModel ARepQP.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AFreeRep () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2InC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rC47Corelib4Init9Datatypes8list_indC47Corelib4Init9Datatypes3appI46Stdlib5Lists4List5NoDup00C46Stdlib5Lists4List8nil_consC46Stdlib5Lists4List8map_consC46Stdlib5Lists4List7existsbI47Corelib4Init9Datatypes4list00K47Corelib4Init9Datatypes4list01I47Corelib4Init5Logic2eq00C47Corelib4Init5Logic9False_indC47Corelib4Init5Logic3notK47Corelib4Init9Datatypes4list02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01c59OSSVerify5KrLib5BothW8AFreeRep;NoDup_app_lC1?~~~~~~~~~~~~~~~K46Stdlib5Lists4List5NoDup01I47Corelib4Init5Logic2or00C46Stdlib5Lists4List:in_app_iffK47Corelib4Init5Logic2or01K46Stdlib5Lists4List5NoDup02I47Corelib4Init5Logic3and00C47Corelib4Init5Logic8eq_transc59OSSVerify5KrLib5BothW8AFreeRep;NoDup_app_rC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<NoDup_removeK47Corelib4Init5Logic3and01C46Stdlib5Lists4List2hdc59OSSVerify5KrLib5BothW8AFreeRep9NoDup_midC1?~~~~~~~~~~~~~~~I46Stdlib7Sorting;Permutation;Permutation00C46Stdlib7Sorting;PermutationAPermutation_NoDupc59OSSVerify5KrLib5BothW8AFreeRepBPermutation_NoDup'C1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;Permutation>Permutation_inC46Stdlib5Lists4List4findI47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option01I47Corelib4Init9Datatypes4bool00c59OSSVerify5KrLib5BothW8AFreeRep8find_appC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02K47Corelib4Init9Datatypes4bool02I35stdpp9countable9Countable00C35stdpp4base;RelDecisionc59OSSVerify5KrLib5BothW8AFreeRep=find_app_noneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl4aptrC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapI47Corelib5Lists7ListDef6Forall00C45stdpp;list_basics4list;list_filterC35stdpp8fin_maps:map_deleteC35stdpp4gmap;gmap_lookupC35stdpp4gmapBgmap_partial_alterC35stdpp4gmap9gmap_foldC35stdpp8fin_maps:map_eq_iffC35stdpp4base6FilterC35stdpp4gmap;gmap_finmapC35stdpp4base6lookupC35stdpp4base6DeleteI46Stdlib5Lists4List6Exists00I35stdpp8fin_maps6FinMap00C35stdpp8fin_maps7MapFoldC35stdpp8fin_maps:map_insertC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base6InsertC35stdpp4base<PartialAlterC35stdpp4base5MergeI35stdpp4gmap4gmap00C35stdpp4base4fmapC35stdpp8fin_maps@lookup_delete_eqC35stdpp8fin_maps@lookup_delete_neC35stdpp4gmap:gmap_emptyC59OSSVerify5KrLib4Spec8AsanCtrl;a_space_begC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase<al_space_begC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;a_ptr_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase<al_ptr_arrayC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib4Spec8AsanCtrl7get_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5x_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=size_of_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl@c_allocated_userC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=c_mapped_userC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;c_num_freedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib4Spec8AsanCtrlCc_mapped_free_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7xc_freeC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib5BothW4ARep8xc_cacheC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7c_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl9max_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep:busy_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5ndistC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6x_busyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8xb_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5xb_stC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep4xb_nC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<rounded_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7rz_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5xb_b1C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z4landC59OSSVerify5KrLib5BothW4ARep6xb_ctxC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib4Spec8AsanCtrl6a_liveC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8AsanCtrl6achunk01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW4ARep6bstate01C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib4Spec8AsanCtrl6a_nextC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2ltI47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I59OSSVerify5KrLib5BothW4ARep5xbusy00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8AFreeRep4banyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7K_ALIGNC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib4Spec8AsanCtrl<K_SPACE_SIZEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_SPACE_EXTRAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_NUM_CLASSESC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6aclass00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep6xclass00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_OFFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl:K_USER_MAPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_MAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_MAPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7aclass0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep6bstate00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7AREQMAXC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6achunk00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableC59OSSVerify5KrLib4Spec8AsanCtrl=K_BATCH_CLASSC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6filterC46Stdlib5Lists4List7map_appC35stdpp4base6LookupC56Stdlib6ZArith6BinInt1Z3eqbK59OSSVerify5KrLib5BothW4ARep5aconc01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW4ARep5xbusy01C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:filter_appC59OSSVerify5KrLib5BothW4ARep7xb_slotC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6in_mapc59OSSVerify5KrLib5BothW8AFreeRepBbusy_slots_split_gC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_reflC46Stdlib5Lists4List9filter_InK47Corelib4Init9Datatypes4bool01c59OSSVerify5KrLib5BothW8AFreeRep9any_classC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbC46Stdlib4Bool4Bool=andb_true_iffC56Stdlib6ZArith6BinInt1Z6eqb_eqC46Stdlib4Bool4BoolBnot_true_iff_falsec59OSSVerify5KrLib5BothW8AFreeRep;key_fresh_gC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7busy_ofC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8AFreeRep;busy_of_X_gC1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes>Morphisms_Prop?or_iff_morphismC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismC47Corelib4Init5Logic6eq_symC47Corelib7Classes?RelationClasses>iff_TransitiveC47Corelib7Classes?RelationClasses?iff_equivalenceC47Corelib7Classes?RelationClasses=iff_ReflexiveC46Stdlib5Lists4List9in_or_appC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega=RingMicromega7Formula01K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K59OSSVerify5KrLib5BothW4ARep6bstate03C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205K59OSSVerify5KrLib5BothW4ARep6bstate02C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8AFreeRep6bfreedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8AFreeRep@busy_slots_splitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8AFreeRep5bquarC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8AFreeRep5xquarC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8AFreeRep:quar_classC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8AFreeRep9key_freshC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8AFreeRep9busy_of_XC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8AFreeRep4In_XC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C35stdpp4base6deleteC59OSSVerify5KrLib4Spec8AsanCtrl7a_cinitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl5a_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep3awfC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes2idC59OSSVerify5KrLib4Spec8AsanCtrl:max_cachedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divc59OSSVerify5KrLib5BothW8AFreeRep@busy_slots_xquarC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8AFreeRep8In_xquarC1?~~~~~~~~~~~~~~~C35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergec59OSSVerify5KrLib5BothW8AFreeRep:live_otherC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N6eq_decI47Corelib4Init6Specif7sumbool00C35stdpp6option;from_optionI59OSSVerify5KrLib4Spec8AsanCtrl6astate00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countablec59OSSVerify5KrLib5BothW8AFreeRep:freed_liveC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:removelastC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z6to_natC46Stdlib5Lists4List9nth_errorK47Corelib4Init9Datatypes3nat02C47Corelib4Init3Nat3subC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specK46Stdlib9micromega=RingMicromega5Psatz02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega;ZifyClasses;rew_iff_revC35stdpp7tactics<f_equal_helpC59OSSVerify5KrLib5BothW9ARepFrame@cache_split_lastC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses7rew_iffC59OSSVerify5KrLib5BothW9ARepFrameAlength_removelastC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega5Tauto8GFormula06I47Corelib4Init9Datatypes3nat00C56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqK46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes3nat01c59OSSVerify5KrLib5BothW8AFreeRep3K24C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_assocC59OSSVerify5KrLib5BothW7ARepKitBNoDup_app_disjointC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8AFreeRep=cache24_splitC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW4ARep6xclass01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame<busy_of_consC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8AFreeRep6bbatchC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep5aconc00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8AFreeRep6xbatchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame?busy_slots_consC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ARepKit?busy_of_Some_InC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8AFreeRep<k24_not_busyC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;PermutationDPermutation_app_headC59OSSVerify5KrLib4Spec8AsanCtrl=cls_set_countC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith4Znat3N2Z7inj_iffC56Stdlib6ZArith4Znat3N2Z9is_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC46Stdlib7Sorting;Permutation@Permutation_reflc59OSSVerify5KrLib5BothW8AFreeRepAbusy_slots_xbatchC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8AFreeRep9In_xbatchC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndK47Corelib4Init9Datatypes4prod01C46Stdlib5Lists4List<flat_map_appC59OSSVerify5KrLib5BothW5ARepQ9qprim_idsC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;PermutationDPermutation_flat_mapC46Stdlib5Lists4List8flat_mapC46Stdlib5Lists4List;in_flat_mapK59OSSVerify5KrLib4Spec8AsanCtrl6achunk02C1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;PermutationBPermutation_ForallC59OSSVerify5KrLib5BothW5ARepQ8qcoupledC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ5q_locC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_qlocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ6q_globC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7a_qglobC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ9qentry_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ6q_pendC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ8qentriesC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;Permutation?Permutation_symc59OSSVerify5KrLib5BothW8AFreeRep>qprim_ids_permC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;PermutationDPermutation_app_tailC47Corelib7Classes?RelationClasses8symmetryI59OSSVerify5KrLib5BothW5ARepQ7qbatchc00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6abatch00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ7qb_slotC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses=iff_SymmetricI59OSSVerify5KrLib5BothW5ABase7alayout00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW5ARepQ5qconc00C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C47Corelib4Init5Logic5proj1C46Stdlib5Lists4List;Forall_implK47Corelib5Lists7ListDef6Forall02C46Stdlib5Lists4List9NoDup_appC46Stdlib5Lists4List:in_map_iffC46Stdlib5Lists4List=Forall_forallC46Stdlib5Lists4List:Forall_appC47Corelib7Classes>Morphisms_Prop@and_iff_morphismC46Stdlib5Lists4List:length_appC46Stdlib7Sorting;PermutationBPermutation_middleC59OSSVerify5KrLib4Spec8AsanCtrl7b_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6b_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl8b_chunksC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8AsanCtrl6abatch01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ5qb_ksC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW5ARepQ7qbatchc01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW5ARepQ5qconc01C1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addK46Stdlib9micromega7EnvRing5PExpr03C46Stdlib5Lists4List7combineC46Stdlib5Lists4List9app_nil_rC59OSSVerify5KrLib5BothW6ARepQP<qentries_appC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01c59OSSVerify5KrLib5BothW8AFreeRep=qcoupled_add1C1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addc59OSSVerify5KrLib5BothW8AFreeRep8HQ_xquarC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8AFreeRep8HB_xquarC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8AFreeRep4FQ_XC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8AFreeRep8k_nonnegC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl8set_liveC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8AFreeRep9awf_xquarC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;PermutationDPermutation_app_commc59OSSVerify5KrLib5BothW8AFreeRep=qcoupled_permC1?~~~~~~~~~~~~~~~C35stdpp4base6insertC59OSSVerify5KrLib5BothW5ARepQ4qnumC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<a_qloc_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=a_qglob_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl:chunk_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:AFreeModel6st_enqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:AFreeModel8st_afterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:AFreeModel7enq_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:AFreeModel7enq_newC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:AFreeModel<enq_app_SomeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=batches_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ARepQPAbatches_bytes_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ARepQPBbatches_bytes_consC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl8set_qlocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:AFreeModel<enq_new_coreC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:AFreeModel9same_coreC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8ltb_specC56Stdlib6ZArith6BinInt1Z3ltbI47Corelib4Init9Datatypes8BoolSpec00C59OSSVerify5KrLib4Spec8AsanCtrl9set_qglobC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=Q_BATCH_BYTESC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7Q_CACHEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl5Q_MAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7Q_BATCHC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ARepQPAbatches_bytes_nilC1?~~~~~~~~~~~~~~~C35stdpp4base6filterC47Corelib4Init9Datatypes4negbC46Stdlib4Bool4Bool7Is_trueC35stdpp9decidable;Is_true_decC35stdpp4base6decideK59OSSVerify5KrLib5BothW5ABase6abkind01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW5ABase6ablock01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7ab_kindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase:abkind_eqbC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N3eqbC56Stdlib6NArith6BinNat1N8eqb_reflC59OSSVerify5KrLib5BothW5ABase9lb_removeC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW5ABase6ablock00C1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N8eqb_specK59OSSVerify5KrLib5BothW5ABase6abkind02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase6hb_idsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8AFreeRepClb_remove_cons_sameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8AFreeRepDlb_remove_cons_otherC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8AFreeRepClb_remove_cons_fakeC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW5ABase6abkind00C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7and_indC47Corelib7Classes9Morphisms:respectfulC47Corelib4Init5Logic6or_indC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismc59OSSVerify5KrLib5BothW8AFreeRep<In_lb_removeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP7ablocksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7xb_userC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7al_fakeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<NoDup_filterc59OSSVerify5KrLib5BothW8AFreeRep@hb_ids_lb_removeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8AFreeRep?NoDup_lb_removeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP7sec_wf1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP8SEC_UOFFC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8AFreeRep<ablocks_freeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep:aslot_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP8sec_sameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_nresC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_nsecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP=sec_chunks_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapPIsec_chunks_of_delete_primC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:AFreeModel5qfiltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP6is_secC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapPAfilter_is_sec_appC1?~~~~~~~~~~~~~~~C35stdpp8fin_maps;map_to_list".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Lemma NoDup_app_l : forall {A} (l1 l2 : list A), List.NoDup (l1 ++ l2) -> List.NoDup l2.
Proof. induction l1 as [|a l1 IH]; intros l2 ND; [exact ND|]. inversion ND; subst. apply IH. assumption. Qed.
Lemma NoDup_app_r : forall {A} (l1 l2 : list A), List.NoDup (l1 ++ l2) -> List.NoDup l1.
Proof.
  induction l1 as [|a l1 IH]; intros l2 ND; [constructor|]. inversion ND; subst. constructor.
  - intros Hin. apply H1. apply in_app_iff. left. exact Hin.
  - eapply IH. eassumption.
Qed.
Lemma NoDup_mid : forall {A} (l1 l2 : list A) x, List.NoDup (l1 ++ x :: l2) -> ~ In x (l1 ++ l2) /\ List.NoDup (l1 ++ l2).
Proof.
  intros A l1 l2 x ND. pose proof (List.NoDup_remove _ _ _ ND) as [ND' NI]. split; [exact NI| exact ND'].
Qed.
Lemma Permutation_NoDup' : forall {A} (l l' : list A), Permutation l l' -> List.NoDup l -> List.NoDup l'.
Proof. intros. eapply Permutation_NoDup; eassumption. Qed.

Lemma find_app : forall {A} (f : A -> bool) l1 l2,
  List.find f (l1 ++ l2) = match List.find f l1 with Some x => Some x | None => List.find f l2 end.
Proof. induction l1 as [|a l1 IH]; intros l2; cbn; [reflexivity|]. destruct (f a); [reflexivity| apply IH]. Qed.
Lemma find_app_none : forall {A} (f : A -> bool) l1 l2,
  (forall y, In y l1 -> f y = false) -> List.find f (l1 ++ l2) = List.find f l2.
Proof.
  induction l1 as [|a l1 IH]; intros l2 H; cbn; [reflexivity|].
  rewrite (H a (or_introl eq_refl)). apply IH. intros y Hy. apply H. right. exact Hy.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section BusyG.
Variables (L : alayout) (st : astate) (X : aconc) (s0 : bstate) (c k n b1 ctx : Z) (l1 l2 : list xbusy).
Definition bany : xbusy := mkXBusy c k n s0 b1 ctx.
Hypothesis XB : x_busy X = l1 ++ bany :: l2.
Hypothesis WF : awf L st X.

Lemma any_class : 1 <= c < K_NUM_CLASSES.
Proof.
  destruct WF as (_ & _ & _ & _ & _ & _ & _ & BUSY & _).
  destruct (BUSY bany ltac:(rewrite XB; apply in_app_iff; right; left; reflexivity)) as [CL _]. exact CL.
Qed.

Lemma busy_slots_split_g : forall c', busy_slots X c' =
  busy_slots (mkAConc (x_cls X) l1) c' ++ (if c =? c' then [k] else []) ++ busy_slots (mkAConc (x_cls X) l2) c'.
Proof.
  intros c'. unfold busy_slots. rewrite XB. cbn [x_busy]. rewrite List.filter_app, map_app. cbn [List.filter].
  unfold bany at 1. cbn [xb_class]. destruct (c =? c'); cbn [map xb_slot]; reflexivity.
Qed.

Lemma key_fresh_g : forall y, In y (l1 ++ l2) -> xb_class y = c -> xb_slot y = k -> False.
Proof.
  intros y Hy Cy Ky.
  destruct WF as (_ & _ & _ & _ & _ & PERC & _).
  destruct (PERC c any_class) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND & _).
  apply NoDup_app_l in ND. apply NoDup_app_l in ND.
  rewrite busy_slots_split_g, Z.eqb_refl in ND.
  destruct (NoDup_mid _ _ k ND) as [NI _]. apply NI. apply in_app_iff.
  apply in_app_iff in Hy. destruct Hy as [Hy|Hy]; [left|right];
    unfold busy_slots; cbn [x_busy]; rewrite <- Ky; apply in_map; apply List.filter_In; (split; [exact Hy| rewrite Cy; apply Z.eqb_refl]).
Qed.

Lemma busy_of_X_g : forall c' k', busy_of X c' k' = if (c =? c') && (k =? k') then Some bany else busy_of (mkAConc (x_cls X) (l1 ++ l2)) c' k'.
Proof.
  intros c' k'. unfold busy_of. rewrite XB. cbn [x_busy].
  destruct (andb (c =? c') (k =? k')) eqn:E.
  - apply andb_true_iff in E. destruct E as [E1 E2]. apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. subst c' k'.
    rewrite find_app_none.
    + cbn [List.find]. unfold bany at 1. cbn [xb_class xb_slot]. rewrite !Z.eqb_refl. reflexivity.
    + intros y Hy. apply not_true_iff_false. intros T. apply andb_true_iff in T. destruct T as [T1 T2].
      apply Z.eqb_eq in T1. apply Z.eqb_eq in T2. eapply key_fresh_g; [apply in_app_iff; left; exact Hy| exact T1| exact T2].
  - rewrite !find_app. destruct (List.find _ l1); [reflexivity|]. cbn -[Z.eqb]. rewrite E. reflexivity.
Qed.

Lemma busy_of_X_self_g : busy_of X c k = Some bany.
Proof. rewrite busy_of_X_g, !Z.eqb_refl. reflexivity. Qed.

Lemma In_X_g : forall y, In y (x_busy X) <-> In y (l1 ++ l2) \/ y = bany.
Proof.
  intros y. rewrite XB. rewrite !in_app_iff. cbn [In].
  split; [intros [H|[H|H]]| intros [[H|H]|H]]; auto.
Qed.

Lemma any_range : 1 <= c < K_NUM_CLASSES /\ 0 <= k < ndist st c.
Proof.
  split; [exact any_class|].
  destruct WF as (_ & _ & _ & _ & _ & PERC & _). destruct (PERC c any_class) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RANGE).
  apply RANGE. apply in_or_app. right. apply in_or_app. right.
  rewrite busy_slots_split_g, Z.eqb_refl. apply in_or_app. right. left. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma any_facts : s0 <> BBatch ->
  0 <= n <= AREQMAX /\ rounded_size n + rz_size n <= size_of_class c /\ 0 <= b1 < 256 /\ Z.land b1 3 = 1 /\ 0 <= ctx < 2^31.
Proof.
  intros NB. destruct WF as (_ & _ & _ & _ & _ & _ & _ & BUSY & _).
  destruct (BUSY bany ltac:(rewrite XB; apply in_app_iff; right; left; reflexivity)) as [_ M]. cbn in M.
  destruct s0 as [p| |]; [| | congruence]; cbn in M.
  - destruct M as (M1 & M2 & M3 & M4 & M5 & M6). repeat split; try assumption; lia.
  - destruct M as (M1 & M2 & M3 & M4 & M5). repeat split; try assumption; lia.
Qed.
End BusyG.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Quar.
Variables (L : alayout) (st : astate) (X : aconc) (p : aptr) (c k n b1 ctx : Z) (l1 l2 : list xbusy).
Definition bfreed : xbusy := mkXBusy c k n (BLive p) b1 ctx.
Definition bquar : xbusy := mkXBusy c k n BQuar b1 ctx.
Definition xquar : aconc := mkAConc (x_cls X) (l1 ++ bquar :: l2).
Hypothesis XB : x_busy X = l1 ++ bfreed :: l2.
Hypothesis WF : awf L st X.

Lemma quar_class : 1 <= c < K_NUM_CLASSES.
Proof.
  destruct WF as (_ & _ & _ & _ & _ & _ & _ & BUSY & _).
  destruct (BUSY bfreed ltac:(rewrite XB; apply in_app_iff; right; left; reflexivity)) as [CL _]. exact CL.
Qed.

Lemma busy_slots_split : forall c', busy_slots X c' =
  busy_slots (mkAConc (x_cls X) l1) c' ++ (if c =? c' then [k] else []) ++ busy_slots (mkAConc (x_cls X) l2) c'.
Proof.
  intros c'. unfold busy_slots. rewrite XB. cbn [x_busy]. rewrite List.filter_app, map_app. cbn [List.filter].
  unfold bfreed at 1. cbn [xb_class]. destruct (c =? c'); cbn [map xb_slot]; reflexivity.
Qed.

Lemma busy_slots_xquar : forall c', busy_slots xquar c' = busy_slots X c'.
Proof.
  intros c'. rewrite busy_slots_split. unfold busy_slots, xquar. cbn [x_busy]. rewrite List.filter_app, map_app. cbn [List.filter].
  unfold bquar at 1. cbn [xb_class]. destruct (c =? c'); cbn [map xb_slot]; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma key_fresh : forall y, In y (l1 ++ l2) -> xb_class y = c -> xb_slot y = k -> False.
Proof.
  intros y Hy Cy Ky.
  destruct WF as (_ & _ & _ & _ & _ & PERC & _).
  destruct (PERC c quar_class) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND & _).
  apply NoDup_app_l in ND. apply NoDup_app_l in ND.
  rewrite busy_slots_split, Z.eqb_refl in ND.
  destruct (NoDup_mid _ _ k ND) as [NI _]. apply NI. apply in_app_iff.
  apply in_app_iff in Hy. destruct Hy as [Hy|Hy]; [left|right];
    unfold busy_slots; cbn [x_busy]; rewrite <- Ky; apply in_map; apply List.filter_In; (split; [exact Hy| rewrite Cy; apply Z.eqb_refl]).
Qed.

Lemma busy_of_X : forall c' k', busy_of X c' k' = if (c =? c') && (k =? k') then Some bfreed else busy_of (mkAConc (x_cls X) (l1 ++ l2)) c' k'.
Proof.
  intros c' k'. unfold busy_of. rewrite XB. cbn [x_busy].
  destruct (andb (c =? c') (k =? k')) eqn:E.
  - apply andb_true_iff in E. destruct E as [E1 E2]. apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. subst c' k'.
    rewrite find_app_none.
    + cbn [List.find]. unfold bfreed at 1. cbn [xb_class xb_slot]. rewrite !Z.eqb_refl. reflexivity.
    + intros y Hy. apply not_true_iff_false. intros T. apply andb_true_iff in T. destruct T as [T1 T2].
      apply Z.eqb_eq in T1. apply Z.eqb_eq in T2. eapply key_fresh; [apply in_app_iff; left; exact Hy| exact T1| exact T2].
  - rewrite !find_app. destruct (List.find _ l1); [reflexivity|]. cbn -[Z.eqb]. rewrite E. reflexivity.
Qed.

Lemma busy_of_xquar : forall c' k', busy_of xquar c' k' = if (c =? c') && (k =? k') then Some bquar else busy_of X c' k'.
Proof.
  intros c' k'. rewrite busy_of_X. unfold busy_of, xquar. cbn [x_busy].
  destruct (andb (c =? c') (k =? k')) eqn:E.
  - apply andb_true_iff in E. destruct E as [E1 E2]. apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. subst c' k'.
    rewrite find_app_none.
    + cbn [List.find]. unfold bquar at 1. cbn [xb_class xb_slot]. rewrite !Z.eqb_refl. reflexivity.
    + intros y Hy. apply not_true_iff_false. intros T. apply andb_true_iff in T. destruct T as [T1 T2].
      apply Z.eqb_eq in T1. apply Z.eqb_eq in T2. eapply key_fresh; [apply in_app_iff; left; exact Hy| exact T1| exact T2].
  - rewrite !find_app. destruct (List.find _ l1); [reflexivity|]. cbn -[Z.eqb]. rewrite E. reflexivity.
Qed.

Lemma busy_of_X_self : busy_of X c k = Some bfreed.
Proof. rewrite busy_of_X, !Z.eqb_refl. reflexivity. Qed.

Lemma In_xquar : forall y, In y (x_busy xquar) <-> In y (l1 ++ l2) \/ y = bquar.
Proof.
  intros y. unfold xquar. cbn [x_busy]. rewrite !in_app_iff. cbn [In].
  split; [intros [H|[H|H]]| intros [[H|H]|H]]; auto.
Qed.
Lemma In_X : forall y, In y (x_busy X) <-> In y (l1 ++ l2) \/ y = bfreed.
Proof.
  intros y. rewrite XB. rewrite !in_app_iff. cbn [In].
  split; [intros [H|[H|H]]| intros [[H|H]|H]]; auto.
Qed.

Lemma freed_live : (a_live st) !! p = Some (CPrim c n) /\ 0 <= n <= AREQMAX /\ rounded_size n + rz_size n <= size_of_class c
  /\ 0 <= b1 < 256 /\ Z.land b1 3 = 1 /\ 0 <= ctx < 2^31.
Proof.
  destruct WF as (_ & _ & _ & _ & _ & _ & _ & BUSY & _).
  destruct (BUSY bfreed ltac:(rewrite XB; apply in_app_iff; right; left; reflexivity)) as [_ M]. cbn in M.
  destruct M as (M1 & M2 & M3 & M4 & M5 & M6). repeat split; try assumption; lia.
Qed.

(* [comment removed for export] *)
Lemma live_other : forall y p', In y (l1 ++ l2) -> xb_st y = BLive p' -> p' <> p.
Proof.
  intros y p' Hy Sy ->.
  destruct WF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & UNIQ).
  assert (E : y = bfreed).
  { apply UNIQ; [apply In_X; left; exact Hy| rewrite XB; apply in_app_iff; right; left; reflexivity| rewrite Sy; reflexivity| exists p; exact Sy]. }
  subst y. eapply key_fresh; [exact Hy| reflexivity| reflexivity].
Qed.

(* [comment removed for export] *)
Lemma awf_xquar : forall s,
  a_space_beg s = a_space_beg st -> a_ptr_array s = a_ptr_array st -> a_cinit s = a_cinit st -> a_cls s = a_cls st ->
  a_live s = delete p (a_live st) -> a_next s = a_next st ->
  awf L s xquar.
Proof.
  intros s E1 E2 E3 E4 E5 E6.
  pose proof freed_live as (LIVE0 & N0 & FIT0 & B10 & AT0 & CTX0).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  assert (N1x : 1 <= n <= AREQMAX).
  { destruct (BUSY bfreed ltac:(rewrite XB; apply in_app_iff; right; left; reflexivity)) as [_ M]. cbn in M. destruct M as (M1 & _). exact M1. }
  clear N0.
  assert (GC : forall c', get_cls s c' = get_cls st c') by (intros c'; unfold get_cls; rewrite E4; reflexivity).
  assert (MC : forall c', max_count s c' = max_count st c') by (intros c'; unfold max_count; rewrite E3; reflexivity).
  assert (ND' : forall c', ndist s c' = ndist st c') by (intros c'; unfold ndist; rewrite GC; reflexivity).
  unfold awf. rewrite E1, E2, E5, E6.
  split; [exact SBE|]. split; [exact PAE|]. split; [exact SAL|]. split; [exact SLO|]. split; [exact SHI|].
  split.
  { intros c' HC'. rewrite GC, MC, ND', busy_slots_xquar. cbn [x_cls xquar]. exact (PERC c' HC'). }
  split.
  { intros c' HC'. rewrite GC. exact (OUTC c' HC'). }
  split.
  { intros y Hy. apply In_xquar in Hy. destruct Hy as [Hy| ->].
    - destruct (BUSY y ltac:(apply In_X; left; exact Hy)) as [CL M]. split; [exact CL|].
      destruct (xb_st y) as [p'| |] eqn:SY; [| exact M| exact M].
      destruct M as (M1 & M2 & M3 & M3' & M4 & M5). repeat (split; [assumption|]).
      rewrite lookup_delete_ne; [exact M5|]. intros E. symmetry in E. exact (live_other y p' Hy SY E).
    - cbn. split; [exact quar_class|]. repeat (split; [assumption|]). exact CTX0. }
  split.
  { intros p' c' n' H. destruct (N.eq_dec p' p) as [->|NE]; [rewrite lookup_delete_eq in H; discriminate|].
    rewrite lookup_delete_ne in H by congruence. destruct (LIVE p' c' n' H) as (y & Hy & Sy & R).
    apply In_X in Hy. destruct Hy as [Hy| ->]; [| cbn in Sy; congruence].
    exists y. split; [apply In_xquar; left; exact Hy|]. split; [exact Sy| exact R]. }
  split.
  { intros p' ch H. destruct (N.eq_dec p' p) as [->|NE]; [rewrite lookup_delete_eq in H; discriminate|].
    rewrite lookup_delete_ne in H by congruence. exact (FRESH p' ch H). }
  intros y1 y2 H1 H2 EQ [p' S1]. apply In_xquar in H1. apply In_xquar in H2.
  destruct H1 as [H1| ->]; destruct H2 as [H2| ->]; try reflexivity.
  - apply UNIQ; [apply In_X; left; exact H1| apply In_X; left; exact H2| exact EQ| exists p'; exact S1].
  - exfalso. rewrite S1 in EQ. cbn in EQ. discriminate.
  - exfalso. cbn in S1. discriminate.
Qed.
End Quar.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Batch.
Variables (L : alayout) (st : astate) (X : aconc) (k24 cnt : Z).
Definition bbatch : xbusy := mkXBusy K_BATCH_CLASS k24 0 BBatch 0 0.
Definition xbatch : aconc :=
  mkAConc (fun c' => if c' =? K_BATCH_CLASS then mkXClass (xc_free (x_cls X K_BATCH_CLASS)) (removelast (xc_cache (x_cls X K_BATCH_CLASS))) else x_cls X c')
          (bbatch :: x_busy X).
Hypothesis WF : awf L st X.
Hypothesis CNT : c_count (get_cls st K_BATCH_CLASS) = cnt.
Hypothesis POS : 0 < cnt.
Hypothesis NK : nth_error (xc_cache (x_cls X K_BATCH_CLASS)) (Z.to_nat (cnt - 1)) = Some k24.

Lemma K24 : 1 <= K_BATCH_CLASS < K_NUM_CLASSES.
Proof. unfold K_BATCH_CLASS, K_NUM_CLASSES. lia. Qed.

Lemma cache24_split : xc_cache (x_cls X K_BATCH_CLASS) = removelast (xc_cache (x_cls X K_BATCH_CLASS)) ++ [k24]
  /\ Z.of_nat (length (removelast (xc_cache (x_cls X K_BATCH_CLASS)))) = cnt - 1.
Proof.
  destruct WF as (_ & _ & _ & _ & _ & PERC & _).
  destruct (PERC K_BATCH_CLASS K24) as (_ & _ & _ & _ & _ & _ & _ & _ & LENC & _).
  rewrite CNT in LENC.
  assert (C : xc_cache (x_cls X K_BATCH_CLASS) = removelast (xc_cache (x_cls X K_BATCH_CLASS)) ++ [k24]).
  { apply cache_split_last. rewrite <- NK. f_equal. lia. }
  split; [exact C|]. rewrite length_removelast; [lia|]. intros E. rewrite E in LENC. cbn in LENC. lia.
Qed.

Lemma k24_not_busy : ~ In k24 (busy_slots X K_BATCH_CLASS) /\ 0 <= k24 < ndist st K_BATCH_CLASS
  /\ ~ In k24 (xc_free (x_cls X K_BATCH_CLASS)) /\ ~ In k24 (removelast (xc_cache (x_cls X K_BATCH_CLASS))).
Proof.
  destruct WF as (_ & _ & _ & _ & _ & PERC & _).
  destruct (PERC K_BATCH_CLASS K24) as (_ & _ & _ & _ & _ & _ & _ & _ & LENC & _ & ND & RANGE).
  destruct cache24_split as [C _]. rewrite C in ND, RANGE.
  assert (IN : In k24 (xc_free (x_cls X K_BATCH_CLASS) ++ (removelast (xc_cache (x_cls X K_BATCH_CLASS)) ++ [k24]) ++ busy_slots X K_BATCH_CLASS)).
  { apply in_or_app. right. apply in_or_app. left. apply in_or_app. right. left. reflexivity. }
  split; [| split; [exact (RANGE k24 IN)| ]].
  - intros Hb. rewrite app_assoc in ND. eapply (NoDup_app_disjoint _ _ k24 ND); [| exact Hb].
    apply in_or_app. right. apply in_or_app. right. left. reflexivity.
  - rewrite <- !app_assoc in ND. cbn [app] in ND.
    replace (xc_free (x_cls X K_BATCH_CLASS) ++ removelast (xc_cache (x_cls X K_BATCH_CLASS)) ++ k24 :: busy_slots X K_BATCH_CLASS)
      with ((xc_free (x_cls X K_BATCH_CLASS) ++ removelast (xc_cache (x_cls X K_BATCH_CLASS))) ++ k24 :: busy_slots X K_BATCH_CLASS) in ND
      by (rewrite <- app_assoc; reflexivity).
    destruct (NoDup_mid _ _ k24 ND) as [NI _].
    split; intros H; apply NI; apply in_or_app; left; apply in_or_app; [left| right]; exact H.
Qed.

Lemma busy_of_xbatch : forall c' k', busy_of xbatch c' k' = if (K_BATCH_CLASS =? c') && (k24 =? k') then Some bbatch else busy_of X c' k'.
Proof. intros. unfold xbatch. rewrite busy_of_cons. cbn [xb_class xb_slot bbatch]. destruct X. reflexivity. Qed.
Lemma busy_slots_xbatch : forall c', busy_slots xbatch c' = (if K_BATCH_CLASS =? c' then [k24] else []) ++ busy_slots X c'.
Proof. intros. unfold xbatch. rewrite busy_slots_cons. cbn [xb_class xb_slot bbatch]. destruct X. reflexivity. Qed.
Lemma In_xbatch : forall y, In y (x_busy xbatch) <-> y = bbatch \/ In y (x_busy X).
Proof. intros y. unfold xbatch. cbn [x_busy In]. split; intros [H|H]; auto. Qed.
Lemma busy_of_X_k24 : busy_of X K_BATCH_CLASS k24 = None.
Proof.
  destruct k24_not_busy as [NB _]. destruct (busy_of X K_BATCH_CLASS k24) as [y|] eqn:E; [| reflexivity].
  exfalso. apply NB. eapply busy_of_Some_In. exact E.
Qed.

(* [comment removed for export] *)
Lemma awf_xbatch : forall s,
  a_space_beg s = a_space_beg st -> a_ptr_array s = a_ptr_array st -> a_cinit s = a_cinit st ->
  a_live s = a_live st -> a_next s = a_next st ->
  (forall c', c' <> K_BATCH_CLASS -> get_cls s c' = get_cls st c') ->
  get_cls s K_BATCH_CLASS = cls_set_count (cnt - 1) (get_cls st K_BATCH_CLASS) ->
  awf L s xbatch.
Proof.
  intros s E1 E2 E3 E5 E6 GC G24.
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  destruct cache24_split as [C LRL]. destruct k24_not_busy as (NB & KR & NF & NC).
  assert (MC : forall c', max_count s c' = max_count st c') by (intros c'; unfold max_count; rewrite E3; reflexivity).
  assert (ND24 : ndist s K_BATCH_CLASS = ndist st K_BATCH_CLASS) by (unfold ndist; rewrite G24; reflexivity).
  assert (NDo : forall c', c' <> K_BATCH_CLASS -> ndist s c' = ndist st c') by (intros c' NE; unfold ndist; rewrite (GC c' NE); reflexivity).
  unfold awf. rewrite E1, E2, E5, E6.
  split; [exact SBE|]. split; [exact PAE|]. split; [exact SAL|]. split; [exact SLO|]. split; [exact SHI|].
  split.
  { intros c' HC'. rewrite MC, busy_slots_xbatch. unfold xbatch. cbn [x_cls].
    destruct (Z.eqb_spec c' K_BATCH_CLASS) as [->|NE].
    - rewrite Z.eqb_refl, G24, ND24. cbn [xc_free xc_cache c_allocated_user c_mapped_user c_num_freed c_mapped_free_array c_count cls_set_count app].
      destruct (PERC K_BATCH_CLASS K24) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
      split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. split; [exact A6|]. split; [exact A7|].
      split; [exact LENF|]. split; [exact LRL|]. split; [rewrite CNT in CNTB; lia|].
      rewrite C in ND, RANGE. split.
      + eapply Permutation_NoDup'; [| exact ND]. rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_head.
        cbn [app]. apply Permutation_refl.
      + intros k0 Hk. apply RANGE. rewrite <- ?app_assoc. rewrite <- ?app_assoc in Hk. cbn [app] in *. exact Hk.
    - destruct (Z.eqb_spec K_BATCH_CLASS c') as [E|_]; [congruence|]. cbn [app]. rewrite (GC c' NE), (NDo c' NE). exact (PERC c' HC'). }
  split.
  { intros c' HC'. rewrite GC; [exact (OUTC c' HC')|]. intros ->. exact (HC' K24). }
  split.
  { intros y Hy. apply In_xbatch in Hy. destruct Hy as [-> | Hy].
    - cbn. split; [exact K24| reflexivity].
    - exact (BUSY y Hy). }
  split.
  { intros p' c' n' H. destruct (LIVE p' c' n' H) as (y & Hy & R). exists y. split; [apply In_xbatch; right; exact Hy| exact R]. }
  split; [exact FRESH|].
  intros y1 y2 H1 H2 EQ [p' S1]. apply In_xbatch in H1. apply In_xbatch in H2.
  destruct H1 as [-> |H1]; destruct H2 as [-> |H2]; try reflexivity.
  - exfalso. cbn in S1. discriminate.
  - exfalso. rewrite S1 in EQ. cbn in EQ. discriminate.
  - apply UNIQ; [exact H1| exact H2| exact EQ| exists p'; exact S1].
Qed.
End Batch.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma qprim_ids_app : forall es1 es2, qprim_ids (es1 ++ es2) = qprim_ids es1 ++ qprim_ids es2.
Proof. intros. unfold qprim_ids. apply flat_map_app. Qed.
Lemma qprim_ids_perm : forall es es', Permutation es es' -> Permutation (qprim_ids es) (qprim_ids es').
Proof. intros es es' P. unfold qprim_ids. apply Permutation_flat_map. exact P. Qed.
Lemma qprim_ids_In : forall es c k, In (c, k) (qprim_ids es) <-> exists n, In (CPrim c n, k) es.
Proof.
  intros es c k. unfold qprim_ids. rewrite in_flat_map. split.
  - intros ([ch k'] & Hin & Hck). cbn [fst snd] in Hck. destruct ch as [c' n| mb ms n]; cbn in Hck; [| destruct Hck].
    destruct Hck as [E|[]]. injection E as -> ->. exists n. exact Hin.
  - intros [n Hin]. exists (CPrim c n, k). split; [exact Hin|]. cbn. left. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma qcoupled_perm : forall L s s' X Q Q',
  qcoupled L s X Q ->
  length (q_loc Q') = length (a_qloc s') -> length (q_glob Q') = length (a_qglob s') ->
  Permutation (qentries (a_qloc s') (q_loc Q') ++ qentries (a_qglob s') (q_glob Q'))
              (qentries (a_qloc s) (q_loc Q) ++ qentries (a_qglob s) (q_glob Q)) ->
  Permutation (map qb_slot (q_loc Q' ++ q_glob Q')) (map qb_slot (q_loc Q ++ q_glob Q)) ->
  q_pend Q' = q_pend Q ->
  qcoupled L s' X Q'.
Proof.
  intros L s s' X Q Q' (LN1 & LN2 & OK & ND1 & ND2 & BS & PS & NN) L1 L2 PE PB PD.
  unfold qcoupled. cbv zeta. rewrite PD.
  split; [exact L1|]. split; [exact L2|]. split.
  { eapply Permutation_Forall; [apply Permutation_sym; exact PE| exact OK]. }
  split; [eapply Permutation_NoDup'; [apply Permutation_app_tail; apply qprim_ids_perm; apply Permutation_sym; exact PE| exact ND1]|].
  split; [eapply Permutation_NoDup'; [apply Permutation_sym; exact PB| exact ND2]|].
  split.
  { intros k0. rewrite <- (BS k0). split; intros H; (eapply Permutation_in; [| exact H]); [exact PB| apply Permutation_sym; exact PB]. }
  split.
  { intros c0 k0. rewrite <- (PS c0 k0). split; intros H; (eapply Permutation_in; [| exact H]);
      [apply Permutation_app_tail; apply qprim_ids_perm; exact PE| apply Permutation_app_tail; apply qprim_ids_perm; apply Permutation_sym; exact PE]. }
  eapply Permutation_Forall; [apply Permutation_sym; exact PB| exact NN].
Qed.

(* [comment removed for export] *)
Lemma qcoupled_add1 : forall L s s' X X' Q Q' c k n b1 ctx (newb : list xbusy),
  qcoupled L s X Q ->
  length (q_loc Q') = length (a_qloc s') -> length (q_glob Q') = length (a_qglob s') ->
  Permutation (qentries (a_qloc s') (q_loc Q') ++ qentries (a_qglob s') (q_glob Q'))
              ((CPrim c n, k) :: qentries (a_qloc s) (q_loc Q) ++ qentries (a_qglob s) (q_glob Q)) ->
  Permutation (map qb_slot (q_loc Q' ++ q_glob Q')) (map xb_slot newb ++ map qb_slot (q_loc Q ++ q_glob Q)) ->
  (forall y, In y (x_busy X') /\ xb_st y = BQuar <-> (In y (x_busy X) /\ xb_st y = BQuar) \/ y = mkXBusy c k n BQuar b1 ctx) ->
  (forall y, In y (x_busy X') /\ xb_st y = BBatch <-> (In y (x_busy X) /\ xb_st y = BBatch) \/ In y newb) ->
  Forall (fun y => xb_st y = BBatch /\ xb_class y = K_BATCH_CLASS /\ 0 <= xb_slot y) newb ->
  (forall y, In y (x_busy X) -> xb_st y = BQuar -> xb_class y = c -> xb_slot y = k -> False) ->
  (forall y, In y (x_busy X) -> xb_st y = BBatch -> xb_class y = K_BATCH_CLASS -> In (xb_slot y) (map xb_slot newb) -> False) ->
  List.NoDup (map xb_slot newb) -> 0 <= k ->
  q_pend Q' = q_pend Q ->
  qcoupled L s' X' Q'.
Proof.
  intros L s s' X X' Q Q' c k n b1 ctx newb (LN1 & LN2 & OK & ND1 & ND2 & BS & PS & NN) L1 L2 PE PB HQ HB NEWB FQ FB NDB K0 PD.
  unfold qcoupled. cbv zeta. rewrite PD.
  split; [exact L1|]. split; [exact L2|]. split.
  { eapply Permutation_Forall; [apply Permutation_sym; exact PE|]. constructor.
    - unfold qentry_ok. cbn [fst snd]. exists b1, ctx. apply (proj1 (proj2 (HQ _) (or_intror eq_refl))).
    - eapply Forall_impl; [| exact OK]. intros [ch k'] HOK. unfold qentry_ok in *. cbn [fst snd] in *.
      destruct ch as [c' n'| mb ms n']; [| exact I]. destruct HOK as (b1' & ctx' & Hin). exists b1', ctx'.
      apply (proj1 (proj2 (HQ _) (or_introl (conj Hin eq_refl)))). }
  split.
  { eapply Permutation_NoDup'; [apply Permutation_app_tail; apply qprim_ids_perm; apply Permutation_sym; exact PE|]. cbn [qprim_ids flat_map fst snd app].
    constructor; [| exact ND1]. intros Hin. apply (PS c k) in Hin. destruct Hin as (y & Hy & Sy & Cy & Ky). exact (FQ y Hy Sy Cy Ky). }
  split.
  { eapply Permutation_NoDup'; [apply Permutation_sym; exact PB|]. apply List.NoDup_app; [exact NDB| exact ND2|].
    intros k0 Hn Ho. apply (BS k0) in Ho. destruct Ho as (y & Hy & Sy & Cy & Ky). subst k0. exact (FB y Hy Sy Cy Hn). }
  split.
  { intros k0. split.
    - intros H. apply (Permutation_in _ PB) in H. apply in_app_iff in H. destruct H as [H|H].
      + apply in_map_iff in H. destruct H as (y & <- & Hy). pose proof (proj1 (Forall_forall _ _) NEWB y Hy) as (Sy & Cy & _).
        exists y. split; [apply (proj1 (proj2 (HB y) (or_intror Hy)))|]. auto.
      + apply (BS k0) in H. destruct H as (y & Hy & Sy & Cy & Ky). exists y. split; [apply (proj1 (proj2 (HB y) (or_introl (conj Hy Sy))))|]. auto.
    - intros (y & Hy & Sy & Cy & Ky). eapply Permutation_in; [apply Permutation_sym; exact PB|]. apply in_app_iff.
      destruct (proj1 (HB y) (conj Hy Sy)) as [[Hy0 _]|Hn].
      + right. apply (BS k0). exists y. auto.
      + left. subst k0. apply in_map. exact Hn. }
  split.
  { intros c0 k0. split.
    - intros H. apply (Permutation_in _ (Permutation_app_tail (q_pend Q) (qprim_ids_perm _ _ PE))) in H. cbn [qprim_ids flat_map fst snd app] in H. destruct H as [E|H].
      + injection E as <- <-. exists (mkXBusy c k n BQuar b1 ctx). split; [apply (proj1 (proj2 (HQ _) (or_intror eq_refl)))|]. cbn. auto.
      + apply (PS c0 k0) in H. destruct H as (y & Hy & Sy & Cy & Ky). exists y. split; [apply (proj1 (proj2 (HQ y) (or_introl (conj Hy Sy))))|]. auto.
    - intros (y & Hy & Sy & Cy & Ky). eapply Permutation_in; [apply Permutation_app_tail; apply qprim_ids_perm; apply Permutation_sym; exact PE|].
      cbn [qprim_ids flat_map fst snd app].
      destruct (proj1 (HQ y) (conj Hy Sy)) as [[Hy0 _]| ->].
      + right. apply (PS c0 k0). exists y. auto.
      + left. cbn in Cy, Ky. subst. reflexivity. }
  eapply Permutation_Forall; [apply Permutation_sym; exact PB|]. apply Forall_app. split; [| exact NN].
  apply Forall_forall. intros k0 H. apply in_map_iff in H. destruct H as (y & <- & Hy).
  pose proof (proj1 (Forall_forall _ _) NEWB y Hy) as (_ & _ & P). exact P.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section QUpdates.
Variables (L : alayout) (st : astate) (X : aconc) (Q : qconc) (p : aptr) (c k n b1 ctx : Z) (l1 l2 : list xbusy).
Let ch := CPrim c n.
Let X1 := xquar X c k n b1 ctx l1 l2.
Hypothesis XB : x_busy X = l1 ++ bfreed p c k n b1 ctx :: l2.
Hypothesis WF : awf L st X.
Hypothesis CP : qcoupled L st X Q.

Lemma HQ_xquar : forall y, In y (x_busy X1) /\ xb_st y = BQuar <-> (In y (x_busy X) /\ xb_st y = BQuar) \/ y = mkXBusy c k n BQuar b1 ctx.
Proof.
  intros y. subst X1. rewrite (In_xquar X c k n b1 ctx l1 l2 y), (In_X X p c k n b1 ctx l1 l2 XB y). unfold bquar, bfreed.
  split.
  - intros [[H| ->] S]; [left; auto| right; reflexivity].
  - intros [[[H| ->] S]| ->]; [split; [left; exact H| exact S]| cbn in S; discriminate| split; [right; reflexivity| reflexivity]].
Qed.
Lemma HB_xquar : forall y, In y (x_busy X1) /\ xb_st y = BBatch <-> (In y (x_busy X) /\ xb_st y = BBatch) \/ In y [].
Proof.
  intros y. subst X1. rewrite (In_xquar X c k n b1 ctx l1 l2 y), (In_X X p c k n b1 ctx l1 l2 XB y). unfold bquar, bfreed.
  split.
  - intros [[H| ->] S]; [left; auto| cbn in S; discriminate].
  - intros [[[H| ->] S]|[]]; [split; [left; exact H| exact S]| cbn in S; discriminate].
Qed.
Lemma FQ_X : forall y, In y (x_busy X) -> xb_st y = BQuar -> xb_class y = c -> xb_slot y = k -> False.
Proof.
  intros y Hy Sy Cy Ky. apply (In_X X p c k n b1 ctx l1 l2 XB) in Hy. destruct Hy as [Hy| ->]; [| cbn in Sy; discriminate].
  exact (key_fresh L st X p c k n b1 ctx l1 l2 XB WF y Hy Cy Ky).
Qed.
Lemma k_nonneg : 0 <= k.
Proof.
  destruct WF as (_ & _ & _ & _ & _ & PERC & _).
  destruct (PERC c (quar_class L st X p c k n b1 ctx l1 l2 XB WF)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RANGE).
  enough (In k (busy_slots X c)) by (specialize (RANGE k ltac:(apply in_or_app; right; apply in_or_app; right; assumption)); lia).
  rewrite (busy_slots_split X p c k n b1 ctx l1 l2 XB), Z.eqb_refl. apply in_or_app. right. left. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma qcoupled_app : forall s' l bl ql qz ia,
  a_qloc st = l ++ [bl] -> q_loc Q = ql ++ [qz] ->
  a_qloc s' = l ++ [mkABatch (b_count bl + 1) (b_size bl + n) (ch :: b_chunks bl)] -> a_qglob s' = a_qglob st ->
  qcoupled L s' X1 (mkQConc (ql ++ [mkQB (qb_slot qz) (k :: qb_ks qz)]) (q_glob Q) ia (q_pend Q)).
Proof.
  intros s' l bl ql qz ia QL QQ QL' QG'.
  pose proof CP as CP0. destruct CP0 as (LN1 & LN2 & _).
  assert (LNl : length ql = length l).
  { rewrite QL, QQ, !length_app in LN1. cbn in LN1. lia. }
  eapply (qcoupled_add1 L st s' X X1 Q _ c k n b1 ctx []); try exact CP.
  - cbn [q_loc]. rewrite QL', !length_app. cbn. lia.
  - cbn [q_glob]. rewrite QG'. exact LN2.
  - cbn [q_loc q_glob]. rewrite QL', QG', QL, QQ. rewrite !qentries_app by exact LNl. cbn [qentries combine b_chunks qb_ks app].
    rewrite <- !app_assoc. cbn [app]. apply Permutation_sym. rewrite ?app_nil_r.
    apply Permutation_middle.
  - cbn [q_loc q_glob map app]. rewrite QQ, !map_app. cbn [map qb_slot]. apply Permutation_refl.
  - exact HQ_xquar.
  - exact HB_xquar.
  - constructor.
  - exact FQ_X.
  - intros y _ _ _ [].
  - constructor.
  - exact k_nonneg.
  - reflexivity.
Qed.

(* [comment removed for export] *)
Lemma qcoupled_new : forall s' k24 cnt sz ia,
  c_count (get_cls st K_BATCH_CLASS) = cnt -> 0 < cnt ->
  nth_error (xc_cache (x_cls X K_BATCH_CLASS)) (Z.to_nat (cnt - 1)) = Some k24 ->
  a_qloc s' = a_qloc st ++ [mkABatch 1 sz [ch]] -> a_qglob s' = a_qglob st ->
  qcoupled L s' (xbatch X1 k24) (mkQConc (q_loc Q ++ [mkQB k24 [k]]) (q_glob Q) ia (q_pend Q)).
Proof.
  intros s' k24 cnt sz ia CNT POS NK QL' QG'.
  pose proof CP as CP0. destruct CP0 as (LN1 & LN2 & _ & _ & _ & BS & _).
  assert (WF1 : awf L (set_live (delete p (a_live st)) st) X1).
  { subst X1. apply (awf_xquar L st X p c k n b1 ctx l1 l2 XB WF); reflexivity. }
  pose proof (k24_not_busy L _ X1 k24 cnt WF1 CNT POS NK) as (NB & KR & _).
  eapply (qcoupled_add1 L st s' X (xbatch X1 k24) Q _ c k n b1 ctx [bbatch k24]); try exact CP.
  - cbn [q_loc]. rewrite QL', !length_app. cbn. lia.
  - cbn [q_glob]. rewrite QG'. exact LN2.
  - cbn [q_loc q_glob]. rewrite QL', QG'. rewrite !qentries_app by exact LN1. cbn [qentries combine b_chunks qb_ks app].
    apply Permutation_sym. rewrite <- ?app_assoc. cbn [app]. apply Permutation_middle.
  - cbn [q_loc q_glob map xb_slot bbatch]. rewrite <- app_assoc, !map_app. cbn [map qb_slot app]. apply Permutation_sym.
    apply Permutation_middle.
  - intros y. rewrite (In_xbatch X1 k24 y). rewrite <- (HQ_xquar y). unfold bbatch. split.
    + intros [[-> |H] S]; [cbn in S; discriminate| exact (conj H S)].
    + intros [H S]. split; [right; exact H| exact S].
  - intros y. rewrite (In_xbatch X1 k24 y). cbn [In]. split.
    + intros [[-> |H] S]; [right; left; reflexivity|]. left. destruct (proj1 (HB_xquar y) (conj H S)) as [HS|[]]. exact HS.
    + intros [[H S]|[<-|[]]].
      * split; [right| exact S]. exact (proj1 (proj2 (HB_xquar y) (or_introl (conj H S)))).
      * split; [left; reflexivity| reflexivity].
  - constructor; [| constructor]. cbn. split; [reflexivity|]. split; [reflexivity| lia].
  - exact FQ_X.
  - intros y Hy Sy Cy Hin. cbn in Hin. destruct Hin as [E|[]]. apply NB. subst X1. rewrite (busy_slots_xquar X p c k n b1 ctx l1 l2 XB).
    unfold busy_slots. rewrite E. apply in_map. apply List.filter_In. split; [exact Hy| rewrite Cy; apply Z.eqb_refl].
  - constructor; [intros []| constructor].
  - exact k_nonneg.
  - reflexivity.
Qed.

(* [comment removed for export] *)
Lemma qcoupled_drain : forall s s' X' Q' ia,
  qcoupled L s X' Q' ->
  a_qloc s' = [] -> a_qglob s' = a_qglob s ++ a_qloc s ->
  qcoupled L s' X' (mkQConc [] (q_glob Q' ++ q_loc Q') ia (q_pend Q')).
Proof.
  intros s s' X' Q' ia CP' QL' QG'. pose proof CP' as CP0. destruct CP0 as (LN1 & LN2 & _).
  eapply qcoupled_perm; [exact CP'| cbn; rewrite QL'; reflexivity| cbn; rewrite QG', !length_app; lia| | | reflexivity].
  - cbn [q_loc q_glob]. rewrite QL', QG'. cbn [qentries app]. rewrite qentries_app by exact LN2. apply Permutation_app_comm.
  - cbn [q_loc q_glob]. cbn [app]. rewrite !map_app. apply Permutation_app_comm.
Qed.
End QUpdates.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma qnum_free : forall st p ch,
  qnum st -> 0 <= chunk_size ch ->
  let st1 := set_live (delete p (a_live st)) st in
  let st2 := st_enq st1 ch in
  (Q_CACHE < a_qloc_bytes st2 -> a_qglob_bytes st2 + a_qloc_bytes st2 <= Q_MAX) ->
  qnum (st_after st2)
  /\ a_qloc_bytes st2 = batches_bytes (a_qloc st2) /\ a_qglob_bytes st2 = a_qglob_bytes st /\ a_qglob st2 = a_qglob st
  /\ Forall (fun b => Q_BATCH_BYTES <= b_size b) (a_qloc st2 ++ a_qglob st2).
Proof.
  intros st p ch (N1 & N2 & N3 & N4 & N5) NN st1 st2 NOREC.
  assert (S2 : a_qloc_bytes st2 = batches_bytes (a_qloc st2) /\ a_qglob_bytes st2 = a_qglob_bytes st /\ a_qglob st2 = a_qglob st
               /\ Forall (fun b => Q_BATCH_BYTES <= b_size b) (a_qloc st2 ++ a_qglob st2)).
  { subst st2. unfold st_enq. destruct (enq_app st1 ch) as [s|] eqn:E.
    - destruct (enq_app_Some st1 ch s E) as (l & bl & QL & NF & ->). cbn -[batches_bytes Z.add].
      subst st1. cbn -[batches_bytes Z.add] in QL |- *. rewrite QL in N1, N3.
      rewrite batches_bytes_app, batches_bytes_cons, batches_bytes_nil in N1 |- *. cbn [b_size].
      split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
      rewrite <- app_assoc in N3 |- *. apply Forall_app in N3. destruct N3 as [F1 F2]. inversion F2; subst.
      apply Forall_app. split; [exact F1|]. constructor; [cbn; lia| assumption].
    - pose proof (enq_new_core ch st1) as (_ & G1 & G2 & _ & L1 & L2 & _). rewrite G1, G2, L1, L2. subst st1. cbn -[batches_bytes Z.add].
      rewrite batches_bytes_app, batches_bytes_cons, batches_bytes_nil. cbn [b_size].
      split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
      rewrite <- app_assoc. apply Forall_app in N3. destruct N3 as [F1 F2].
      apply Forall_app. split; [exact F1|]. constructor; [cbn; unfold Q_BATCH_BYTES; lia| exact F2]. }
  split; [| exact S2]. destruct S2 as (B1 & B2 & B3 & B4).
  unfold st_after, qnum. destruct (Z.ltb_spec Q_CACHE (a_qloc_bytes st2)) as [LT|GE]; cbn -[batches_bytes Z.add].
  - specialize (NOREC LT). rewrite B2, B3 in *. rewrite ?batches_bytes_app, ?batches_bytes_nil, ?app_nil_r, ?Z.add_0_r.
    split; [reflexivity|]. split; [lia|]. split; [| unfold Q_CACHE; lia].
    apply Forall_app in B4. destruct B4 as [F1 F2]. apply Forall_app. split; [exact F2| exact F1].
  - rewrite B2, B3 in *. repeat split; try assumption; lia.
Qed.

Lemma lb_remove_cons_same : forall p A n LB, lb_remove p (HB p A n :: LB) = lb_remove p LB.
Proof. intros. unfold lb_remove. cbn. rewrite N.eqb_refl. cbn. reflexivity. Qed.
Lemma lb_remove_cons_other : forall p q A n LB, q <> p -> lb_remove p (HB q A n :: LB) = HB q A n :: lb_remove p LB.
Proof. intros. unfold lb_remove. cbn. destruct (N.eqb_spec q p); [congruence|]. cbn. reflexivity. Qed.
Lemma lb_remove_cons_fake : forall p cls A n LB, lb_remove p (mkABlock (ABFake cls) A n :: LB) = mkABlock (ABFake cls) A n :: lb_remove p LB.
Proof. intros. unfold lb_remove. cbn. reflexivity. Qed.

Lemma hb_ids_lb_remove : forall p LB, hb_ids (lb_remove p LB) = List.filter (fun q => negb (N.eqb q p)) (hb_ids LB).
Proof.
  intros p LB. induction LB as [|[[q|cls] A n] LB IH].
  - reflexivity.
  - destruct (N.eq_dec q p) as [->|NE].
    + rewrite lb_remove_cons_same. cbn [hb_ids flat_map ab_kind app List.filter]. rewrite N.eqb_refl. cbn [negb]. exact IH.
    + rewrite lb_remove_cons_other by exact NE. cbn [hb_ids flat_map ab_kind app List.filter].
      destruct (N.eqb_spec q p) as [E|_]; [congruence|]. cbn [negb]. unfold hb_ids in IH. rewrite IH. reflexivity.
  - rewrite lb_remove_cons_fake. cbn [hb_ids flat_map ab_kind app]. exact IH.
Qed.

Lemma In_lb_remove : forall p LB blk, In blk (lb_remove p LB) <-> In blk LB /\ ab_kind blk <> ABHeap p.
Proof.
  intros p LB blk. induction LB as [|[[q|cls] A n] LB IH].
  - cbn. tauto.
  - destruct (N.eq_dec q p) as [->|NE].
    + rewrite lb_remove_cons_same. rewrite IH. cbn [In]. split; [tauto|]. intros [[<-|H] NK]; [cbn in NK; congruence| tauto].
    + rewrite lb_remove_cons_other by exact NE. cbn [In]. rewrite IH. split; [| tauto].
      intros [<-|H]; [| tauto]. split; [left; reflexivity|]. cbn. congruence.
  - rewrite lb_remove_cons_fake. cbn [In]. rewrite IH. split; [| tauto].
    intros [<-|H]; [| tauto]. split; [left; reflexivity|]. cbn. congruence.
Qed.

Lemma NoDup_lb_remove : forall p LB, List.NoDup LB -> List.NoDup (lb_remove p LB).
Proof.
  intros p LB ND. induction LB as [|[[q|cls] A n] LB IH]; [constructor| |].
  - inversion ND; subst. destruct (N.eq_dec q p) as [->|NE].
    + rewrite lb_remove_cons_same. apply IH. assumption.
    + rewrite lb_remove_cons_other by exact NE. constructor; [| apply IH; assumption].
      intros Hin. apply In_lb_remove in Hin. tauto.
  - inversion ND; subst. rewrite lb_remove_cons_fake. constructor; [| apply IH; assumption].
    intros Hin. apply In_lb_remove in Hin. tauto.
Qed.

Section Blocks.
Variables (L : alayout) (st : astate) (X : aconc) (p : aptr) (c k n b1 ctx : Z) (l1 l2 : list xbusy).
Let X1 := xquar X c k n b1 ctx l1 l2.
Hypothesis XB : x_busy X = l1 ++ bfreed p c k n b1 ctx :: l2.
Hypothesis WF : awf L st X.

(* [comment removed for export] *)
Lemma ablocks_free : forall LB st' X', (forall y, In y (l1 ++ l2) -> In y (x_busy X')) ->
  a_live st' = delete p (a_live st) ->
  ablocks L st X LB -> ablocks L st' X' (lb_remove p LB).
Proof.
  intros LB st' X' INCL EL (BH & BF & NDI & NDL). split; [| split; [| split]].
  - intros p' A n' Hin. apply In_lb_remove in Hin. destruct Hin as [Hin NE]. cbn in NE.
    destruct (BH p' A n' Hin) as [(y & Hy & Sy & R)|(mb & ms & Lp & R)].
    + apply (In_X X p c k n b1 ctx l1 l2 XB) in Hy.
      destruct Hy as [Hy| ->]; [| cbn in Sy; exfalso; apply NE; congruence].
      left. exists y. split; [apply INCL; exact Hy|]. split; [exact Sy| exact R].
    + right. exists mb, ms. split; [| exact R]. rewrite EL, lookup_delete_ne; [exact Lp| congruence].
  - intros cls A n' Hin. apply In_lb_remove in Hin. destruct Hin as [Hin _]. exact (BF cls A n' Hin).
  - rewrite hb_ids_lb_remove. apply List.NoDup_filter. exact NDI.
  - apply NoDup_lb_remove. exact NDL.
Qed.

Lemma ablocks_xquar : forall LB st', a_live st' = delete p (a_live st) -> ablocks L st X LB -> ablocks L st' X1 (lb_remove p LB).
Proof. intros LB st' EL. apply ablocks_free; [| exact EL]. intros y Hy. subst X1. apply In_xquar. left. exact Hy. Qed.
Lemma ablocks_xbatch : forall LB st' k24, a_live st' = delete p (a_live st) -> ablocks L st X LB -> ablocks L st' (xbatch X1 k24) (lb_remove p LB).
Proof. intros LB st' k24 EL. apply ablocks_free; [| exact EL]. intros y Hy. apply In_xbatch. right. subst X1. apply In_xquar. left. exact Hy. Qed.

(* [comment removed for export] *)
Lemma freed_block : forall LB A n', ablocks L st X LB -> In (HB p A n') LB -> A = aslot_addr L c k + rz_size n /\ n' = n.
Proof.
  intros LB A n' (BH & _) Hin.
  pose proof WF as WF0. destruct WF0 as (_ & _ & _ & _ & _ & _ & _ & BUSY & _ & _ & UNIQ).
  destruct (BH p A n' Hin) as [(y & Hy & Sy & Uy & Ny)|(mb & ms & Lp & _)].
  2: { exfalso. assert (HB0 : In (bfreed p c k n b1 ctx) (x_busy X)) by (rewrite XB; apply in_or_app; right; left; reflexivity).
       destruct (BUSY _ HB0) as [_ M]. cbn in M. destruct M as (_ & _ & _ & _ & _ & M5). rewrite M5 in Lp. discriminate. }
  assert (E : y = bfreed p c k n b1 ctx).
  { apply UNIQ; [exact Hy| rewrite XB; apply in_or_app; right; left; reflexivity| rewrite Sy; reflexivity| exists p; exact Sy]. }
  subst y. cbn in Uy, Ny. unfold xb_user, xb_alloc in Uy. cbn in Uy. split; [symmetry; exact Uy| symmetry; exact Ny].
Qed.
End Blocks.

(* [comment removed for export] *)
Lemma sec_same_free : forall st p c n s,
  (a_live st) !! p = Some (CPrim c n) -> same_core (set_live (delete p (a_live st)) st) s ->
  Permutation (qfilt is_sec s) (qfilt is_sec st) ->
  sec_same st s.
Proof.
  intros st p c n s LIVE (E1 & E2 & E3 & E4 & E5 & E6 & E7 & _) PQ. unfold sec_same. cbn in *.
  rewrite E7, E6, E5, E1. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split.
  - intros p' mb ms n'. destruct (N.eq_dec p' p) as [->|NE].
    + rewrite lookup_delete_eq, LIVE. split; [discriminate| congruence].
    + rewrite lookup_delete_ne by congruence. tauto.
  - eapply sec_chunks_of_delete_prim; [exact LIVE| exact E1| exact PQ].
Qed.
Lemma sec_chunks_qperm : forall st s,
  a_live s = a_live st -> Permutation (qfilt is_sec s) (qfilt is_sec st) -> Permutation (sec_chunks_of s) (sec_chunks_of st).
Proof. intros st s EL PQ. unfold sec_chunks_of, achunks. rewrite EL, !filter_is_sec_app. apply Permutation_app_head. exact PQ. Qed.
Lemma sec_chunks_free : forall st p c n s,
  (a_live st) !! p = Some (CPrim c n) -> a_live s = delete p (a_live st) ->
  Permutation (qfilt is_sec s) (qfilt is_sec st) ->
  Permutation (sec_chunks_of s) (sec_chunks_of st).
Proof. intros st p c n s LIVE EL PQ. eapply sec_chunks_of_delete_prim; [exact LIVE| exact EL| exact PQ]. Qed.
End CANSEC1.
