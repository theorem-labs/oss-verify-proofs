(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (40 recorded proofs replaced by written proofs (newslots_length, newslots_In, newslots_NoDup and 37 more); refill_store takes zstd_frame_info's proof: the shadow footprint grows by the per-class lattice (GPSH) the run's mappings now give). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import MM_syscalls WStr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import SysStepF.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg AProto ABase AKit AKit2 ABytes AModelFacts ARep ARepKit ARepFrame ALayout AHeapP ARefill_iface RT_stubs
     F_apoison F_acache F_aalloc3 F_ammap F_aensure F_apopulate F_agetfrom F_arefill.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ARefillP () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List6nth_okC46Stdlib5Lists4List:length_mapC46Stdlib5Lists4List7map_mapC46Stdlib5Lists4List:firstn_nilC46Stdlib5Lists4List:firstn_mapC46Stdlib5Lists4List=repeat_lengthC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC47Corelib5Lists7ListDef3seqC47Corelib5Lists7ListDef3mapC47Corelib4Init9Datatypes6lengthI47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01C46Stdlib5Lists4List:length_seqC46Stdlib5Lists4List3revC46Stdlib5Lists4List:length_revc59OSSVerify5KrLib5BothW8ARefillP8newslotsC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01C47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes?RelationClasses8symmetryC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC46Stdlib5Lists4List:in_map_iffC46Stdlib5Lists4List2InC47Corelib4Init5Logic3iffC46Stdlib5Lists4List6in_revI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00I47Corelib4Init5Peano2le00C47Corelib4Init3Nat3addC47Corelib4Init5Peano2ltC46Stdlib5Lists4List6in_seqC56Stdlib6ZArith6BinInt1Z2ltC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K47Corelib7Numbers7BinNums8positive02K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr03K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z3maxC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega;ZifyClasses;rew_iff_revK46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06C47Corelib7Classes?RelationClasses>iff_TransitiveK47Corelib7Numbers7BinNums1Z01C56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqK46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201C47Corelib7Classes?RelationClasses=iff_SymmetricK47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C46Stdlib9micromega8ZifyInst7Inj_Z_ZC46Stdlib5Lists4List8map_consC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib5Lists4List;ForallPairsC46Stdlib5Lists4List9seq_NoDupC46Stdlib5Lists4ListKNoDup_map_NoDup_ForallPairsC46Stdlib5Lists4List9NoDup_revI46Stdlib5Lists4List5NoDup00I35stdpp9countable9Countable00C35stdpp4base;RelDecisionC59OSSVerify5KrLib4Spec8AsanCtrl4aptrC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2hdC46Stdlib5Lists4List7map_revC46Stdlib5Lists4List7existsbC59OSSVerify5KrLib5BothW7ARepKit>firstn_repeat'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ARepKit=skipn_repeat'C1?~~~~~~~~~~~~~~~I35stdpp4gmap4gmap00C35stdpp4base4fmapK47Corelib7Numbers7BinNums1Z02C59OSSVerify5KrLib5BothW9ARepFrameCsize_of_class_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=size_of_classC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloK47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C59OSSVerify5KrLib5BothW4ARep8acompactC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib5BothW;F_apopulate5fvalsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega7EnvRing3Pol02K46Stdlib9micromega=RingMicromega5Psatz03K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C35stdpp7tactics<f_equal_helpC46Stdlib5Lists4List7map_extK46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C59OSSVerify5KrLib4Spec8AsanCtrl=K_NUM_CLASSESC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00C46Stdlib5Lists4List4inclC46Stdlib5Lists4ListANoDup_incl_lengthC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9MorphismsBsubrelation_properC47Corelib7Classes9Morphisms5flip2C46Stdlib5Lists4List:in_app_iffC47Corelib4Init5Logic7f_equalC47Corelib4Init9Datatypes8list_indC47Corelib4Init9Datatypes3appC47Corelib4Init5Logic9False_indC47Corelib7Classes9Morphisms@subrelation_reflC47Corelib7Program6Basics4implC47Corelib7Classes9MorphismsFsubrelation_respectfulK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02K46Stdlib5Lists4List5NoDup02I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C47Corelib7Classes>Morphisms_Prop@not_iff_morphismC47Corelib7Classes9MorphismsIiff_flip_impl_subrelationc59OSSVerify5KrLib5BothW8ARefillP9nodup_appC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transI47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib5BothW4ARep7junk_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ARepKit:junk_splitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7fill_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Tac7sum_natC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3TacArw_cells_split_CBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Tac;mk_CB_cellsC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6repeatC47Corelib5Lists7ListDef5skipnC47Corelib5Lists7ListDef6firstnC47Corelib4Init3Nat3subC59OSSVerify5KrLib5BothW6ABytes<rw_cells_appC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat7add_0_rC56Stdlib6ZArith4Znat5Z2Nat2idC59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4BImg5bsegsC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC46Stdlib5Lists4List:repeat_appC59OSSVerify5KrLib5BothW9ARepFrame6cb_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr6u32arrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr4u32sC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common4WStr?u8arr_of_u32arrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3ArrArw_cells_of_u8arrC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3mulC59OSSVerify5KrLib3Lib3Arr;u32s_lengthC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulC46Stdlib5Lists4List:length_appC46Stdlib5Lists4List9nth_errorC46Stdlib5Lists4List=length_firstnC59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC47Corelib4Init3Nat3minC56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z8min_specK46Stdlib9micromega7EnvRing5PExpr07C46Stdlib5Lists4List<firstn_skipnC46Stdlib5Lists4List<length_skipnC59OSSVerify5KrLib3Lib3Arr8u32s_appC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List>nth_error_app1C46Stdlib9micromega;ZifyClasses6eq_iffC59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3mrdC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith4Znat5Nat2Z7inj_minC59OSSVerify5KrLib5BothW4ARep7busy_ofC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib5BothW9ARepFrameBbusy_of_Some_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6x_busyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8xb_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7xb_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep:busy_slotsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC46Stdlib5Lists4List6filterC46Stdlib5Lists4List9filter_InC56Stdlib6ZArith6BinInt1Z6eqb_eqI59OSSVerify5KrLib5BothW4ARep5xbusy00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep5aconc00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW4ARep6xclass01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5x_clsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_reflK59OSSVerify5KrLib5BothW4ARep5aconc01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ARefillP2xrC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep6xclass00C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7eqb_neqC47Corelib4Init5Logic6eq_symK47Corelib4Init9Datatypes4bool02I59OSSVerify5KrLib5BothW7ALayout:alayout_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout:ad_ctx_resC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase6al_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout6al_resC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout5adisjC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout8ad_t_resC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4al_tC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout8ao_spaceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase<al_space_begC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout6ao_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout4aobjC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout4ao_tC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4sclrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4iclrC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW5ABase7alayout00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<K_SPACE_SIZEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_SPACE_EXTRAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout=alayout_spaceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7aregionC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8afreearrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep<aregion_infoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep;acache_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed4shadC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed5shlenC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC59OSSVerify5KrLib5BothW9ARepFrame9shlen_divC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame8shad_divC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7K_ALIGNC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed6ASHOFFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7and_indK47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib3Lib5Frame3ivlC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib3Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula01c59OSSVerify5KrLib5BothW8ARefillP7rkfactsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7a_cinitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl9set_cinitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_liveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_qlocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<a_qloc_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7a_qglobC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=a_qglob_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_nsecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_nresC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;a_ptr_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;a_space_begC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl:init_cacheC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6astate00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableI59OSSVerify5KrLib4Spec8AsanCtrl6achunk00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6abatch00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7put_clsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6aclass00C1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC59OSSVerify5KrLib5BothW=ARefill_iface;refill_stmtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9F_arefill;refill_specC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep3awfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7get_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=c_mapped_userC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrlCc_mapped_free_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl:max_cachedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase<al_ptr_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl@c_allocated_userC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;c_num_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7xc_freeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8xc_cacheC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7c_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5xb_stC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep4xb_nC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<rounded_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7rz_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5xb_b1C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC59OSSVerify5KrLib5BothW4ARep6xb_ctxC1?~~~~~~~~~~~~~~~C35stdpp4gmap;gmap_lookupK59OSSVerify5KrLib4Spec8AsanCtrl6achunk01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW4ARep6bstate01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5ndistC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ARefillPAinit_cache_fieldsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ARefillP4rrecC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_mulC56Stdlib6ZArith6BinInt1Z?mul_add_distr_rC59OSSVerify5KrLib5BothW9ARepFrameBget_cls_put_cls_eqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ARefillP?newslots_lengthC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00C59OSSVerify5KrLib4Spec8AsanCtrl9max_countC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C46Stdlib6ZArith4Zdiv:Z_mod_multC46Stdlib7Sorting;PermutationHPermutation_app_swap_appc59OSSVerify5KrLib5BothW8ARefillP>newslots_NoDupC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ARefillP;newslots_InC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;PermutationAPermutation_NoDupC46Stdlib5Lists4List9app_assocC47Corelib7Classes9MorphismsDiff_impl_subrelationC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9MorphismsFreflexive_proper_proxyc59OSSVerify5KrLib5BothW8ARefillP=xr_busy_slotsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ARefillP9xr_cls_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9F_arefill@max_cached_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9F_arefill>init_cache_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrameBget_cls_put_cls_neC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ARefillP9xr_cls_neC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2ltC35stdpp4base6lookupC59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_OFFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl:K_USER_MAPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_MAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_MAPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7aclass0C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z8inj_succI59OSSVerify5KrLib5BothW4ARep6bstate00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7AREQMAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_BATCH_CLASSC1?~~~~~~~~~~~~~~~C47Corelib7Classes>Morphisms_Prop?or_iff_morphismC47Corelib7Classes?RelationClasses=iff_ReflexiveC47Corelib7Classes?RelationClasses=eq_TransitiveC59OSSVerify5KrLib5BothW6AHeapP4arngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep4AREPC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC59OSSVerify5KrLib5BothW9F_arefill:refill_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7arep_rtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep9ainstanceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7athreadC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep<aslot_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep=ashadow_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7ah_quarC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6ah_secC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8ah_depotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6arelroC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8arep_rt2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8arep_rt3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase6al_topC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase6al_botC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep<acache_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep=aregion_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep:afreearrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6aslotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep:aslot_busyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout9alayout_tC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout;alayout_ctxC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ARefillP@alayout_res_disjC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9F_arefill4ic_WC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9F_arefill?refill_tail_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA5fp_leC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AProto5fp_bwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9F_aensure8m3_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrlAcls_set_num_freedC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8AsanCtrl6aclass01C1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9Morphisms@reflexive_properC59OSSVerify5KrLib5BothW=ARefill_iface?put_cls_put_clsC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z4of_NC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegc59OSSVerify5KrLib5BothW8ARefillP;outside_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame6sub_fpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame<munch_weakenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;munch_transC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;wmono_transC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9F_arefillAic_W_disjoint_genC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ARefillP?map_cw_newslotsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7map_appc59OSSVerify5KrLib5BothW8ARefillP8RK_slotsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ARefillP6dj_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame:junk_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ARepKit:junk_mergeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF3rngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5azeroC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ARefillP8RK_shlowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame:fill_frameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ARefillP:fill_mergeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ARefillP5RK_riC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame;cells_frameC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat3N2Z7inj_iffC56Stdlib6ZArith4Znat3N2Z9is_nonnegC59OSSVerify5KrLib5BothW7ARepKit=junk_of_cellsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ARefillP=u32arr_firstnC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:F_agetfrom<u32arr_skipnC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9skipn_mapc59OSSVerify5KrLib5BothW8ARefillP>junk_of_u32arrC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ARefillP8RK_shmidC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl3rupC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ARefillP<junk_of_fillC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep:aslot_addrC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ARefillP@busy_of_In_slotsC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith:ZArith_dec;Z_lt_le_decC59OSSVerify5KrLib5BothW9ARepFrame8awf_fitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8xb_allocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame@aslot_busy_frameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ARefillP8junk_subC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ARefillP:xr_busy_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARepAslot_shadow_bytesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ARefillP8fill_subC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ARefillP@region_other_geoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ARefillP<RK_reg_otherC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ARefillP9RK_shhighC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrameCaregion_cells_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame@afreearray_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame7xb_fitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame>slot_in_regionC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame=aslots_updateC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame9shad_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrameCaslot_shadow_updateC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrameCashadow_avail_frameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ARefillP6RK_recC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9F_arefillDic_W_disjoint_chunksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame<u32arr_frameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ARefillP6RK_imgC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ARefillP7RK_tlowC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ARefillP8RK_tstatC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ARefillP8RK_thighC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ARefillP6RK_objC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ARefillP:awf_refillC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C59OSSVerify5KrLib5BothW9ARepFrame8rt_hullsC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C59OSSVerify5KrLib5BothW9ARepFrame=arep_rt_frameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ARefillP>put_cls_fieldsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame?ainstance_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9F_arefill<ic_W_outsideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP>quar_untouchedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP9quar_sameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP8hq_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7al_fakeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase8al_nodesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase8al_storeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout7al_dtlsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP=sec_untouchedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP=sec_chunks_ofC1?~~~~~~~~~~~~~~~I46Stdlib7Sorting;Permutation;Permutation00C47Corelib4Init5Logic6or_indC46Stdlib7Sorting;Permutation@Permutation_reflC59OSSVerify5KrLib5BothW6AHeapP@sec_chunks_of_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP8sec_sameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP8hs_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout8ao_nodesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout8ao_storeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout<ad_nodes_resC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout<ad_store_resC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout:ad_t_nodesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout:ad_t_storeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP8hd_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame<arelro_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame>arep_rt2_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame>arep_rt3_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP9arng_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP4RSECC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AProto9rng_mergeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF8rng_sub'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=cls_set_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr6u64arrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9F_arefill8arec_hdrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndK59OSSVerify5KrLib4Spec8AsanCtrl6achunk02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl8K_REGIONC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep<ASTATS_WORDSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7AIMG_HIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF9footprintC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase9AINSTANCEC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C59OSSVerify5KrLib5BothW5ABase3KLSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase9ARELRO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase9ARELRO_HIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame9rt3_hullsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ARefillPAstore_refill_stmtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl2AMC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC59OSSVerify5KrLib5BothW=ARefill_iface:refill_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6NodesA8at_nodeAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=ARefill_iface4apopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed6aembedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ARepKit:c8_of_junkC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4ListBNoDup_app_remove_rC56Stdlib6ZArith6BinInt1Z7div_posc59OSSVerify5KrLib5BothW8ARefillPBNoDup_bound_lengthC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List=Forall_forallK46Stdlib9micromega=RingMicromega5Psatz01C59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState6ret_pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=ARefill_iface<take_is_apopC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA6epostFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA5implFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=ARefill_ifaceAcache_refill_treeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9F_arefill5KKrefC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AProto6fstepSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase5ATP88C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4ATSDC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C59OSSVerify5KrLib5BothW5ABase3ATPC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List6Exists00c59OSSVerify5KrLib5BothW8ARefillPBarefill_from_storeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ARefillP<refill_storeC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition newslots (nd : Z) (n : nat) : list Z := rev (map (fun j => nd + Z.of_nat j) (seq 0 n)).

Lemma newslots_length : forall nd n, length (newslots nd n) = n.
Proof. intros. unfold newslots. rewrite length_rev, length_map, length_seq. reflexivity. Qed.

Lemma newslots_In : forall nd n k, In k (newslots nd n) <-> nd <= k < nd + Z.of_nat n.
Proof.
  intros nd n k. unfold newslots. rewrite <- in_rev, in_map_iff. split.
  - intros (j & <- & Hj). apply in_seq in Hj. lia.
  - intros Hk. exists (Z.to_nat (k - nd)). split; [lia|]. apply in_seq. lia.
Qed.

Lemma newslots_NoDup : forall nd n, List.NoDup (newslots nd n).
Proof.
  intros nd n. unfold newslots. apply NoDup_rev. apply NoDup_map_NoDup_ForallPairs; [| apply seq_NoDup].
  intros a b _ _ E. lia.
Qed.

Lemma map_cw_newslots : forall c nd n, 1 <= c < K_NUM_CLASSES ->
  map (fun k => Z_to_bv 64 (acompact c k)) (newslots nd n) = fvals (nd * size_of_class c) (size_of_class c) n.
Proof.
  intros c nd n Hc. pose proof (size_of_class_facts c Hc) as [S1 S3].
  unfold newslots, fvals. rewrite map_rev, map_map. f_equal. apply map_ext. intros j.
  f_equal. unfold acompact. rewrite Z.shiftr_div_pow2 by lia. change (2^4) with 16.
  generalize S1 S3; clear; intros. Z.div_mod_to_equations. nia.
Qed.

Lemma NoDup_bound_length : forall (l : list Z) n, List.NoDup l -> (forall k, In k l -> 0 <= k < n) -> 0 <= n -> Z.of_nat (length l) <= n.
Proof.
  intros l n ND B N.
  assert (INCL : incl (map Z.to_nat l) (seq 0 (Z.to_nat n))).
  { intros x Hx. apply in_map_iff in Hx. destruct Hx as (k & <- & Hk). apply in_seq. specialize (B k Hk). lia. }
  apply NoDup_incl_length in INCL.
  - rewrite length_map, length_seq in INCL. lia.
  - apply NoDup_map_NoDup_ForallPairs; [| exact ND]. intros a b Ha Hb E. pose proof (B a Ha). pose proof (B b Hb). lia.
Qed.

Lemma nodup_app : forall {A} (a b : list A), List.NoDup a -> List.NoDup b -> (forall x, In x a -> ~ In x b) -> List.NoDup (a ++ b).
Proof.
  intros A a b NA NB D. induction a as [|x a IH]; cbn; [exact NB|].
  inversion NA; subst. constructor.
  - rewrite in_app_iff. intros [Hx|Hx]; [exact (H1 Hx)|]. exact (D x (or_introl eq_refl) Hx).
  - apply IH; [exact H2|]. intros y Hy. apply D. right; exact Hy.
Qed.

Lemma junk_sub : forall m A n A' n', junk_at m A n -> A <= A' -> A' + n' <= A + n -> 0 <= n' -> junk_at m A' n'.
Proof.
  intros m A n A' n' J H1 H2 H3.
  destruct (junk_split m A (A' - A) (n - (A' - A)) ltac:(replace (A' - A + (n - (A' - A))) with n by lia; exact J) ltac:(lia) ltac:(lia)) as [_ J2].
  replace (A + (A' - A)) with A' in J2 by lia.
  destruct (junk_split m A' n' (n - (A' - A) - n') ltac:(replace (n' + (n - (A' - A) - n')) with (n - (A' - A)) by lia; exact J2) ltac:(lia) ltac:(lia)) as [J3 _].
  exact J3.
Qed.

Lemma fill_sub : forall m A n A' n' v, fill_at m A n v -> A <= A' -> A' + n' <= A + n -> 0 <= n' -> fill_at m A' n' v.
Proof.
  intros m A n A' n' v F H1 H2 H3. unfold fill_at in *.
  pose proof (rw_cells_split_CB bsegs m A [] (Z.to_nat n) (repeat (Z_to_bv 8 v) (Z.to_nat n)) [] [Z.to_nat (A' - A); Z.to_nat n'; Z.to_nat (n - (A' - A) - n')] F ltac:(cbn; lia)) as SP.
  cbn [app mk_CB_cells] in SP.
  rewrite !skipn_repeat' in SP. rewrite (firstn_repeat' _ (Z.to_nat n')) in SP by lia.
  apply (proj1 (rw_cells_app bsegs m A [_] [_; _])) in SP. destruct SP as [_ SP].
  apply (proj1 (rw_cells_app bsegs m _ [_] [_])) in SP. destruct SP as [SP _].
  cbn [cells_size csize Nat.add] in SP. rewrite Nat.add_0_r, Z2Nat.id in SP by lia.
  replace (A + (A' - A)) with A' in SP by lia. exact SP.
Qed.

Lemma fill_merge : forall m A a b v, fill_at m A a v -> fill_at m (A + a) b v -> 0 <= a -> 0 <= b -> fill_at m A (a + b) v.
Proof.
  intros m A a b v F1 F2 Ha Hb. unfold fill_at in *.
  pose proof (cb_app m A _ _ _ _ F1 ltac:(rewrite Z2Nat.id by lia; exact F2)) as CA.
  rewrite <- repeat_app in CA. replace (Z.to_nat a + Z.to_nat b)%nat with (Z.to_nat (a + b)) in CA by lia. exact CA.
Qed.

Lemma junk_of_u32arr : forall m A ws, u32arr bsegs m A ws -> junk_at m A (4 * Z.of_nat (length ws)).
Proof.
  intros m A ws AR. exists (u32s ws). apply rw_cells_of_u8arr' || idtac.
  pose proof (rw_cells_of_u8arr bsegs m A (u32s ws) (u8arr_of_u32arr bsegs m A ws AR)) as R.
  rewrite u32s_length in R. replace (Z.to_nat (4 * Z.of_nat (length ws))) with (4 * length ws)%nat by lia. exact R.
Qed.

Lemma junk_of_fill : forall m A n v, fill_at m A n v -> junk_at m A n.
Proof. intros m A n v F. eexists. exact F. Qed.

(* [comment removed for export] *)
Lemma u32arr_firstn : forall m A ws k, u32arr bsegs m A ws -> (k <= length ws)%nat -> u32arr bsegs m A (firstn k ws).
Proof.
  intros m A ws k [[B0 [B1 B]] [W0 [W1 W]]] K. rewrite u32s_length in B1. split.
  - split; [lia|]. split; [rewrite u32s_length, length_firstn; lia|].
    intros i Hi. rewrite u32s_length, length_firstn in Hi.
    rewrite <- (firstn_skipn k ws) in B. specialize (B i ltac:(rewrite u32s_length, length_app, length_firstn, length_skipn; lia)).
    rewrite u32s_app, nth_error_app1 in B by (rewrite u32s_length, length_firstn; lia). exact B.
  - split; [lia|]. split; [rewrite length_firstn; lia|]. intros i Hi. rewrite length_firstn in Hi. apply W. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition xr (X : aconc) (c : Z) (fr ca : list Z) : aconc :=
  mkAConc (fun c' => if c' =? c then mkXClass fr ca else x_cls X c') (x_busy X).

Lemma busy_of_In_slots : forall X c k b, busy_of X c k = Some b -> In k (busy_slots X c).
Proof.
  intros X c k b Hb. destruct (busy_of_Some_facts X c k b Hb) as (HIn & HC & HK).
  unfold busy_slots. apply in_map_iff. exists b. split; [exact HK|]. apply filter_In. split; [exact HIn|]. apply Z.eqb_eq. exact HC.
Qed.

Lemma xr_busy_of : forall X c fr ca c' k, busy_of (xr X c fr ca) c' k = busy_of X c' k.
Proof. intros. reflexivity. Qed.
Lemma xr_busy_slots : forall X c fr ca c', busy_slots (xr X c fr ca) c' = busy_slots X c'.
Proof. intros. reflexivity. Qed.
Lemma xr_cls_eq : forall X c fr ca, x_cls (xr X c fr ca) c = mkXClass fr ca.
Proof. intros. unfold xr. cbn. rewrite Z.eqb_refl. reflexivity. Qed.
Lemma xr_cls_ne : forall X c fr ca c', c' <> c -> x_cls (xr X c fr ca) c' = x_cls X c'.
Proof. intros X c fr ca c' NE. unfold xr. cbn. replace (c' =? c) with false by (symmetry; apply Z.eqb_neq; exact NE). reflexivity. Qed.


(* [comment removed for export] *)
Lemma alayout_res_disj : forall L, alayout_ok L ->
     (al_ctx L + 65536 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L)
  /\ (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L).
Proof.
  intros L H. pose proof (ad_ctx_res L H) as D1. pose proof (ad_t_res L H) as D2. pose proof (ao_space L H) as SB.
  pose proof (ao_ctx L H) as C. pose proof (ao_t L H) as T.
  unfold adisj, aobj, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472. lia.
Qed.

Lemma region_other_geo : forall L c c', alayout_ok L -> 1 <= c < 32 -> 1 <= c' < 32 -> c' <> c ->
  al_space_beg L <= aregion L c' /\ (aregion L c' + 4294967296 <= aregion L c \/ aregion L c + 4294967296 <= aregion L c') /\ aregion L c' + 4294967296 <= al_space_beg L + 137438953472
  /\ afreearr L c' = aregion L c' + 3758096384 /\ aregion_info L c' = al_space_beg L + 137438953472 + c' * 128 /\ acache_addr L c' = al_t L + 208 + c' * 80
  /\ aregion L c' mod 8 = 0 /\ (shad (aregion L c') + shlen 4294967296 <= shad (aregion L c) \/ shad (aregion L c + 4294967296) <= shad (aregion L c'))
  /\ 2201439137792 <= shad (aregion L c') /\ shad (aregion L c') + shlen 4294967296 <= 17594333495296
  /\ shad (afreearr L c') = shad (aregion L c') + shlen 3758096384.
Proof.
  intros L c c' ALO HC Hc' NE.
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in *. change (2^37) with 137438953472 in *.
  unfold afreearr, aregion_info, acache_addr, aregion, K_REGION, K_FREEARR_OFF, K_SPACE_SIZE, ARI_STRIDE.
  change (2^32) with 4294967296. change (2^37) with 137438953472.
  assert (Q : exists q, al_space_beg L = 65536 * q) by (exists (al_space_beg L / 65536); Z.div_mod_to_equations; lia).
  destruct Q as [q Hq]. rewrite Hq in *.
  rewrite !shad_div, !shlen_div. unfold ASHOFF.
  replace ((65536 * q + c' * 4294967296) / 8) with (8192 * q + c' * 536870912) by (Z.div_mod_to_equations; lia).
  replace ((65536 * q + c * 4294967296) / 8) with (8192 * q + c * 536870912) by (Z.div_mod_to_equations; lia).
  replace ((65536 * q + c * 4294967296 + 4294967296) / 8) with (8192 * q + c * 536870912 + 536870912) by (Z.div_mod_to_equations; lia).
  replace ((65536 * q + c' * 4294967296 + 3758096384) / 8) with (8192 * q + c' * 536870912 + 469762048) by (Z.div_mod_to_equations; lia).
  change (4294967296 / 8) with 536870912. change (3758096384 / 8) with 469762048.
  assert (CC : c' + 1 <= c \/ c + 1 <= c') by lia.
  repeat split; lia.
Qed.

Section RefillP.
Variable H : aholes.
Hypothesis HL : ahole_laws H.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition store_refill_stmt : Prop :=
  forall (L : alayout) (RNG RNG' : footprint) (sp : word) (m m' : amem) (st st2 : astate) (X : aconc) (c lo : Z) (chunks0 : list word),
  alayout_ok L -> arng L RNG st -> AREP H L st X m ->
  1 <= c < K_NUM_CLASSES -> c_count (get_cls st c) = 0 ->
  ATOP <= lo -> lo <= bv_unsigned sp - AREFILL_STACK ->
  u32arr bsegs m (acache_addr L c + 16) chunks0 -> length chunks0 = 16%nat ->
  refill_ret L RNG sp st c lo (map (fun k => Z_to_bv 64 (acompact c k)) (xc_free (x_cls X c))) chunks0 (fun j => c_count (get_cls st j)) m st2 RNG' m' ->
  let n := max_cached c / 2 in
  let st_r := put_cls c (cls_set_count n (cls_set_num_freed (c_num_freed (get_cls st2 c) - n) (get_cls st2 c))) st2 in
  exists X', AREP H L st_r X' m' /\ arng L RNG' st_r
    /\ a_cinit st_r = true /\ c_count (get_cls st_r c) = max_count st_r c / 2 /\ 0 < max_count st_r c / 2
    /\ x_busy X' = x_busy X /\ (forall c', c' <> c -> x_cls X' c' = x_cls X c')
    /\ a_live st_r = a_live st /\ a_next st_r = a_next st /\ a_qloc st_r = a_qloc st /\ a_qloc_bytes st_r = a_qloc_bytes st
    /\ a_qglob st_r = a_qglob st /\ a_qglob_bytes st_r = a_qglob_bytes st /\ a_nsec st_r = a_nsec st /\ a_nres st_r = a_nres st
    /\ (forall c', c' <> c -> get_cls st_r c' = get_cls st c')
    /\ munch (arefill_W L st c (bv_unsigned sp)) m m' /\ wmono bsegs m m'.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation Wr sp RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 t RI CA n :=
  ([(sp - 672, sp); (RB + mu, RB + mu'); (SHU0, SHU1); (FA + 4 * nf, FA + mfa'); (SHF0, SHF1);
    (t + 2792, t + 2800); (t + 2800, t + 3168); (RI, RI + 8); (RI + 16, RI + 56); (RI + 68, RI + 69); (RI + 72, RI + 80);
    (CA, CA + 4); (CA + 16, CA + 16 + 4 * n)]%Z) (only parsing).

Lemma outside_app : forall l1 l2 x, outside (l1 ++ l2) x <-> outside l1 x /\ outside l2 x.
Proof. intros l1 l2 x. induction l1 as [|[lo hi] l1 IH]; cbn; tauto. Qed.

Lemma dj_app : forall l1 l2 A k, disjoint_from l1 A k -> disjoint_from l2 A k -> disjoint_from (l1 ++ l2) A k.
Proof. intros l1 l2 A k D1 D2. induction l1 as [|[lo hi] l1 IH]; cbn in *; [exact D2|]. destruct D1 as [D1 D1']. split; [exact D1| apply IH; exact D1']. Qed.

Section Kinds.
Variables (sp lo t ctx SB c RB FA RI CA mu mu' au nf mfa mfa' n SHU0 SHU1 SHF0 SHF1 : Z).
Definition rkfacts : Prop :=
     (ATOP <= lo /\ lo <= sp - 672 /\ sp <= 2^64)
  /\ (sclr t 4096 /\ iclr t 4096 /\ t + 4096 <= ATOP /\ sclr ctx 65536 /\ 6352896 <= ctx /\ ctx + 65536 <= ATOP /\ (ctx + 4096 <= t \/ t + 4096 <= ctx))   (* [comment removed for export] *)
  /\ (1 <= c <= 31 /\ CA = t + 208 + c * 80 /\ 1 <= n <= 8)
  /\ (17594333495296 <= SB /\ SB + 137438957568 <= ATOP /\ RB = SB + c * 4294967296 /\ FA = RB + 3758096384 /\ RI = SB + 137438953472 + c * 128)
  /\ (t + 4096 <= SB \/ SB + 137438957568 <= t) /\ (ctx + 65536 <= SB \/ SB + 137438957568 <= ctx)
  /\ (0 <= au /\ au <= mu /\ mu <= mu' /\ mu' <= 3758096384 /\ 0 <= nf /\ 4 * nf <= mfa /\ mfa <= mfa' /\ mfa' <= 536870912)
  /\ (2201439137792 <= SHU0 /\ SHU0 <= SHU1 /\ SHU1 <= SHF0 /\ SHF0 <= SHF1 /\ SHF1 <= 17594333495296).
Hypothesis KF : rkfacts.

Ltac kind := pose proof KF as KF'; unfold rkfacts, AIMG_HI in *; unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in KF';
  destruct KF' as (F_lo & F_t & F_c & F_sb & F_tsb & F_csb & F_mu & F_sh);
  cbn [disjoint_from]; repeat (split; [lia|]); first [lia | exact I].

(* [comment removed for export] *)
Lemma RK_img : forall A k, 65536 <= A -> 0 <= k -> A + k <= 6352896 -> disjoint_from (Wr sp RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 t RI CA n) A k.
Proof.
ltac2:(KReplay.run1 (kr_t_ARefillP ()) ["CANSEC1"; "RefillP"; "Kinds"] "h04__p1h14__p2h24__x1h34__x2h44__x3h54__x4h64__x5h74__p3h82H3h94__p4h:4__p5h;4__p6h<7__arithh=4__ffh>6__sat4h?6__sat5h@8__varmaphA5__withB5__p10hC5__p11hD5__p12hE5__p13hF4__p7hG4__p8hH4__p9hI4__x6hJ4__x7hK4__x8hL5__p14hM5__p15hN5__p16hO4__x9hP2HahQ5__p17hR5__p18hS5__p19hT5__p20hU1AhV3F_chW5F_csbhX4F_lohY4F_muhZ4F_sbh[4F_shh\3F_th]5F_tsbh^3KF'h_1kp%0p%1p%2p&0p;1p;2p;3p;4p;5p;7p;6p;8p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Dp4p710p9p1003<p4p710R0p1003Yp4p710R1p8P0p10045p4p710R2p8p10103p4p710R3p1010QR4p4p710R5p8P3P4p4p7210R4p8p101T1p6051000R6p1011ap4p710R7p8P6P1p8P6P0p8P6p101Tnp4p710p8P6p101LHp4p7210p8P6P2p8P6p101Lep4p710p8P6p101MGp4p710p8P6p100oWp4p710p8p1010jp4p70R6P7p8P6P2p8P6p100knR7p4p710p8P6p1012Tp4p710p8p10130p4p710P1p8p10141p4p710P1p8p10151p4p710R6P3p8P6P5p8P6P4p8P6p1015Ep4p73110p8p1004Sp4p710P1p8P7p4p7210P2p8p1005Mp4p73110P2p8p1005ip4p710P2p8p1006Hp4p7210P1p8p1006gp4p710P2p8g00JMj13Tg015Wj1>Tg00X6j20Tg00KUj18Tg02S7k10?Tg00O^k202Tg01=5k20TTg007ij21Tg01;<j2OTg00B;R2j22Tg02h4k20DTg00Fek105Tg02hTj3QTg02R9k10>Tg02`Tk20=Tg00DTk203Tg02a<k30<Tg00SZj1@Tg00T9k20:Tg00GEk10STg00WXk10RTg00Hak10QTg00I?k10PTg00L]k10OTg00VJk30NTg00K2k208Tg00M?k20MTg00:8k20LTg00Mak20KTg009^j3~Tg00NMk30HTg00Nlk40GTg00Tbk10FTg00U@k20ETg00Uaj3qTg01FCj2uTg00Ijj2|Tg01C]j3rTg02UZk206Tg02VOk20BTg00S@j2dTg02iPk50@Tg00XRj4yTg02fbj4}Tg00^>j3XTg00\ij3kTg00]Rj2xTg00Gek20ITg00HCj4sTg00Ymj4lTg00ZXj7fTg00^^k60JTg00[<j7hTg00L:k309Tg00_Bj7vTg00[`j8wTg01Flk30;Tf0R1#3#3p=Ig00`WR7/01p=`%81#3p=\%31#3#3#3p=m%81#8p=g%31#3#3#3#3#3#3#>p=Vf2R6f1R4'1/01p=F%31#3#3#>p=b1064/21p=;%81#8#8#8p=H%31#3#3#3#3#3#3#3p=[f3R5/061041'dp=91d41,26p>001156/04/d1p=Jf6R3f5R0f4R81241,26,25'2'2'2p=Zg00<dR911417~6p=R1264/21p=_1241,26p=U%31#>p>0C1O41,16p=zP9P9P6P4C}=X51p>0AP9P9P0P8C}P9P9P6P4C}=X515X3p=i20:91p=AAk941p=MAk9419k96g00g6R:'xp=ag00gbR;?X41p>0120I91p=^P9P6P4P1Csp=CP9P9P8P5P6CsP4P1Csp=]1|91p==20891p=BP6g00ccR<g00dBR=P=g00dbR>P9P4g00c<R?P1Clg00eBR@Ffp=6P4P<P=P=P>P1J0Jp=7P9P4P?P1Clp=PP5P<P=P=P>P6P<P=P=P>P4P@FfP1Fhp=LB09941p=:P0P<P=P=P>P8P5P6P<P=P=P>P4P1FvGwp=NP0P<P=P=P>P8P<P=P=P>P5P6FhP4P1Gwp=<1064/d1p=EB0;941p=cAk9419k96p=YAk941/x:p=WAX;419X;69X;59X;8p=4P9P8P5P9P6P4P1CsCsp=pP9P4g00hNP1Clp=nP4P<P=P=P>P1P@Ffp={P8P<P=P=P>P5P6P<P=P=P>P4P1FhFhp=5P6P<P=P=P>P4P1Fhp=DP3P<P=P=P>P0P<P=P=P>P9P8P?P5ClP@FfP6P<P=P=P>P9P4P?P1ClP@FfFvp=KP8P<P=P=P>P5P<P=P=P>P9P6P?P4ClP@FfP1Fvp=GP3P<P=P=P>P0P8P5P<P=P=P>P6P4P1GwGwp=?A~941p>071x1:p=t1|91:0994p=T1241,26,25,28p=e1d64/21p=SP8P<P=P=P>P5P<P=P=P>P6P4FhP1Fhp=oP5P<P=P=P>P6P4P<P=P=P>P1P@FfFvp>04P3P0P8P5P6P4P1CyCyp=jg00ieR@#3R:#3R?#3S00#3RA#IRB#3RC#IRD#3#IRE#3RF#3#IRG#>RH/04%`4%\@#m#8#g#\#m#VRI9F56p,2KFS01g02j4P2p,2rcRJ$0?RKp,2loRLp,2spRM%8:RN#3RO#8RP#I#bRQ+02RR%>:RS%>BRB+0TRT,0MS025;L3;S03p,1tRU%>ERE'1RV%8@RW#8S04#8S05#8RX#g#H#HRY#3#8#gRZ#3#m#VR[%HF#H#H#H#[#VRFPUC9S0610EUS0710VH10IU40010VKS08p,3ctxR\/1HR]P[PFP\C910I\S0910]KS0:P\PEPU10V\CJFZS0;%>@R^p,1cR_'0%>XS0<,0_S0=p,2CAS0>%3WRX#\#bS0?,1U%bOR`,O_3Rp,1nS0@,0^S0AQ0@Q00#>S0B'0'2S0C'2S0D3_S0Ep,2SBRa%[GRG#\#m#VRb,1aRc/0KS0Fp,2RBRd%3G#mRG#3#IRe#>Rf,O_7RaS0Gp,2FAS0HQ04#3Rg#IRh#3#I#[#[#VS0I7RdS0Jp,2RIRi%Ie#bS0K,1a%>CS0L,O_3RS0M'2S0N3US0O5;FRCPVPaPcPUC9S0PP]PaPcP\C9S0Qp,2auS0R#`S0SQ0Rp,2muS0T'0S0UQ0Tp,3mu'Rc'0S0VQ0I,0cS0Wp,2nfS0X#`%>?R]Q0X'ORVp,3mfaRep,4mfa'Rj%>G,0j5;e3;S0Y'23US0Z3US0[%\D#I#8#g#H#H#\#g#\#m#VS0\p,4SHU0S0]Q0]p,4SHU1S0^Q0^p,4SHF0S0_Q0_p,4SHF1S0`Q0`/0F3;S0a3;3;S0b3;S0c'2RD'2S0d'2S0e'2S0f'2S0g'2S0h20D99RePRPMPeQ0T,1dRG11dcS0iPeQ0]Q0^PeQ0H/1VRVQ0H/1jS0jPeQ0_Q0`Pe%gPRP#3#8#bS0k,1URj%\P#bS0l,1URPPePP%3XS0m#3S0n#g#I#bS0o,1URXPePiQ0B,1iS0pPe%>ARA,1iRc%>h,1iS0qPeQ00#8Rh#3Rk$0CS0r,1iRl%8k#>,1iS0sPe%8?Rk#bS0t,1iRm11i`S0uPeQ0>Q0>/1]RnPeQ0>/1ARoQ0@9zo]Rp&05eH0AFiFiFiFiFiFiRe?Q30P1Q03Q0hP2Q0;Q0gf:Rqf9Rr5QeP1Q0;Q0gP2Q0EQ0ff>Rsf=Rt5QeP1Q0EQ0fP2PCQ0efBRufARv5QeP1Q0eP2Q0PQ0dfFS0vfERw5QeP1Q0PQ0dP2Q0QPDfJS0wfIRx5QeP1Q0QP2Q0[Q0cfNS0xfMS0y5QeP1Q0[Q0cfQR2fPS0z'1RyPRPMP2C9PyPGQ0iP2C9S0{PyQ0]Q0^P2C9S0|PyPVQ0jP2C9S0}PyQ0_Q0`P2C9S0~PyPjPPP2C9S10PyPPPXP2C9S11PyPiQ0pP2C9S12PyPcQ0qP2C9S13PyPlQ0sP2C9S14PyPmQ0uP2C9S15PyQ0>PnP2C9S16PyPoPpP2C9S17g01QQS18'2S19'2S1:'2S1;'2S1<'2S1='2S1>'2S1?'2S1@'2S1A'2S1B'2S1C'2&0>JRJ%8Z#H#[#[#VRZ%8Y#H#H#[#[#V,0KRY7;KRp20=SBRo2037S%`B2037T[[Ry%`SRnQ18B0<SB4UWPRBQ18%`T[^PnRnp-0RTg00=aRS#@Rm#@Rl#@Rc#@RX#AS1D%AcRc%AlS1E%AmS1F20:9SS1G'MS1H'MS1I3a&05;RS+01S1J&0S;R;%^8S1KP6&0R9RmP4%^0Rl?C5mD]&0Q9RP&0P9RjPj%=Z%B?R?56jf7RV,7jS1L&0O=RGPjPj%BNRR96j?PjPj%BWRW%=Q60N9Rz,PRf8RR,7jS1MCLPGPj2089@R{%B:':R:%=IS1N56jR|PGPjA6j:z17jrS1OENE<E<20Mj>RzP1P6g00jJR}g00jjR~+0L20K16=~}~dB0H974H0GR~b=b@bAX29X39X49X59X69X0TX1TW7A;Z502025Q=;0V9;801165S1P/0IRZ1158R}2020Q;Eq[[[^29^39^49^59^69^0T^1T^7TP1fURQ,0MQ02PYPLPKPMfTRMPQP5Q0yP2O;b<b>b?b8Q0{Q1CPJPpPoPyPBPn%@XRX#@RK#@RL#@RY#@S1C#AS0{%AYS02%ALS1Q&0F@-0E9R@%AKS1R5q91u9f%AXS1S'cQ1DQ1G'M3YS1T3Y'WRXPXPXPXPXPXPXPXPSD4D4P;Q1KP6%^3S1UPr%^RS1VDpS1WP4%^rS1XP0PmPrPmD]P5%^VS1Y?CrmDpPPPjPj1|97S1Z%BhRh56jPjPj1Ph?f;Rh,7jS1[CLPGPjPj%=FR7%BgRg56jS1\Pjf<RX,7jRKPj%8NS1]#BRN%=f5r9,:gS1^,nW,{j17jtS1_D5PGPjPj%=^S1`=6jNS1a17jsS1b5Djf?S1c,7jS1dPGPjP|PGPjPjf@S1e,7jS1fPjPj17jvS1gPj17juS1hPjfCS1i,7jS1jPjfDS1k,7jS1lPj17jwS1mPjQ0v,7jS1nPjPj%BORO%=ERL':%BkRkPj1:kLS1oPOFKS1pD5D5D5PjfGS1q,7jS1rPjfHS1s,7jS1tPjPjPjQ1oPgPj%=bS1u,:gS1vPkFKS1wPjPjPj%=HRY,:OPgPjQ1vPOFKS1v17jxS1xD5D5D5PGPjPjP:1:W?Q0w,7jS1yDGF?E<E<E<PzP~b=b@bAX29X39X49X59X69XI9XJ9XK9XO9X0TX1TX7TX9TX:TX;TXFTXGTXHTXBTXCTXDTXETXLTXMTXNT%`R10R5;Ur10FRS1zAzRVfS1{-075/2X7Uh10^RS1|Q1c7_s10}IS1}PuQ1iQ1kPwQ0vQ1qQ1sPrPEPR11RERf/0rCJS1~FZPxQ0wPfPh11hbRgPRC9S2011rHS21PhPgPrC9S22fKS23FZ1103S2411VRS25Q0y3E[[[[[^29^39^49^59^69^I9^J9^K9^O9^0T^1T^7T^9T^:T^;T^FT^GT^HT^BT^CT^DT^ET^LT^MT^NTP1Q0i/0QPDPCQ0EQ0:Q09206\HS0iQ0820BUES26206UES27Q03Q0DQ0=Q0NQ0FQ0ZQ0RPaP_P\PUQ0TPdPMPQP0PvPwP2Q01ONb<b>b?b8Q0|Q1BPJPpPoPyPBPnQ1I#t001SP;%^6S1I%^57C4PPPjPjQ0\#=S1B=6jW17j0PGPjP|PGPjA6j:WS0|17j3ENE<PzP~b=b@bAX29X39X49X0TX1TQ0\?;65AF46IS0TQ1P/08S1P/d3[[^29^39^49^0T^1TP1Q0^/0QQ0bQ0]PMPQP8P2O7b<b>b?b8Q0}Q1APJPpPoPyPBPn1u9]S1AQ0{'cQ02Q1Q9q9@Q1T3Y'WRgPgPgPgPgPgPgPgPSD4D4P;Q1WP4AClrmP5Q1YQ1X7CrDpPPPjPjQ1[PjPKPjQ1_PjQ1bPjQ1Z=6j?Q1dD5D5PGPjPjQ1\PjQ1fPjQ05#BRgQ1^'n,{jPjPjQ0I,Tg,nWQ1gCLD5PGPjPjQ1aQ1h5DjQ1jPGPjP|PGPjPjQ1lPjPjQ1mPjQ1nPjQ1rPjQ1tPjQ1xPjQ1yQ1pD5D5D5PjQ23,7jPjfLRg,7jPjQ1wPjQ1vQ0y,7jD5D5D5PGPjPjP:%=]S1v=r9?S1w,:WQ0x,7jDGF?E<E<E<PzP~b=b@bAX29X39X49X59X69XI9XJ9XK9XO9X0TX1TX7TX9TX:TX;TXFTXGTXHTXBTXCTXDTXETXLTXMTXNTXQTXRTXSTXTTPrPqPhPX%`5/2tDeQ1zQ1cQ1{-07rQ0I9R5rQ1eDeQ1|Q1i7_uQ1}Q0vQ1qQ1sPxQ0wQ23PgQ1~FZQ0yQ0xQ20Q22fOFZQ24AzV]R;E2[[[[[^29^39^49^59^69^I9^J9^K9^O9^0T^1T^7T^9T^:T^;T^FT^GT^HT^BT^CT^DT^ET^LT^MT^NT^QT^RT^ST^TTP1Q0j/0QPDPCQ0EQ0:Q09Q0iQ08Q26Q27Q03Q0DQ0=Q0MQ0FQ0YQ0WQ0VQ0UQ0SPdPaP_P\PUQ0XQ0HPMPQP0PvPwP2Q01ORb<b>b?b8Q0~Q1@PJPpPoPyPBPnQ1JP;ACm0lS1J?C0mP6PmP4PmP5PmP0Q1K?C0mS1KDpD]PPPjPjQ1BQ1]#8#BRd56jPjPjQ0n#BRg,PdPjPj1PgWQ1LCLCLPGPjP|PGPjQ0|Q1MENE<PzP~b=b@bAX29X39X49X59X69X0TX1TQ0\A;8609;587;5Q0TQ1P/dR[[^29^39^49^59^69^0T^1TP1Q0`/0QQ0aQ0^Q0]Q0_PMPQP8P2O9b<b>b?b8Q10Q1?PJPpPoPyPBPnQ1C#@S1C#@S1?#AQ1RQ1F'MRg'MS1R,WcRdPdPdPdPdPdPdPdQ0{Q1D/MgS1F'WS0{Q1C#AS1C/MgS10#tS0_Q02Q1F'MS1F#tS02Q1CQ1SQ1G3YS1C#tS1SQ0{Q1SQ02Q0_Q0_Q02Q1SQ0{Q1SQ02Q0_Q0{PdPdPdPdPdPdPdPdPSD4D4D4D4D4D4D4D4S0{P;Q1IP4PmP5ACl8mS1IDpS0_PPPjPjPjQ04#BRd/:YS04PNQ1u,:NS1u=6jdS02DGS1SPGPjPjPj1:WLS1GPNPjQ1uPWFKS0]PGPjA6j7NS0^Q1L5DjS0aPGPjPjQ1MPjQ1OPjPjQ1GPYPjQ1NPWFK5DjPj17jqS0`PjPjPjQ04%=[S04A6j7dS0TDGQ1N=6jdS1PQ1[PjPj1:dLS0\PWPjQ1GPdFK5DjS1G5DjD5D5S0nPGPjP|PGPjA6jY{S1BPGPjPjPKPjPjQ1_PjQ1bPjQ0`PjQ1dQ1fQ1G5DjD5D5PjQ1gPjQ1hPjQ0]PjQ1SQ1jD5D5D5S1GPGPjQ0k,TW96j:Q0l,TWS1]=6j{ENF?F?F?PzP~b=b@bAX29X39X49X59X69X0TX1TX7TX9TX:TX;TXFTXGTXHTXBTXCTXDTXETP5PHP8AF8b5CJS1@P5PEP0AF0b5CJS0~10F3S0H/2VS0XPr110ES0S/0H10I0600qPhP3PHP[Q0HCJAF3E0Q0S/03600X9;I3DeS0HAF80IS0U10H0S0VQ1ePvPuPsQ1iQ1kQ1cQ1~FZPwQ0v10fq11qbS0W/0RQ21/0qQ0W/0rQ1q3S3SDeS0WQ25Q0k,1rQ0l,1rS0lPVC9[[[[[[[^29^39^49^59^69^0T^1T^7T^9T^:T^;T^FT^GT^HT^BT^CT^DT^ETP1PDPCQ0EQ09Q0iQ26Q27Q03Q0:Q08Q07Q06Q0OPaP\PUPMPQPrPtPvPxP2fSS06Q01OIS0kb<b>b?b8Q11Q1>PJPpPoPyPBPnQ0{P;Q0_PPPjQ1SPGPjQ0]PGPjQ0aPGPjQ0nPGPjP|PGPjQ1BPGPjQ1GPGPjQ1]96j:Q0o,TW=6j{ENF?F?F?PzP~b=b@bAX29X39X49X59X69X0TX1TX7TX9TX:TX;TXFTXGTXHTXBTXCTXDTXETQ1@Q0~Q0XQ0HQ0UQ0VQ0WQ25Q0lQ0o=FrV3E[[[[[[[^29^39^49^59^69^0T^1T^7T^9T^:T^;T^FT^GT^HT^BT^CT^DT^ETQ0kb<b>b?b8Q12Q1=PJPpPoPyPBPnQ1DAq9@cQ0L,u9Q1E'cQ1H3Y'W001SS1DP;Q1JP6PmP4Q1K?C5mD]S1KPPPjPjPjQ0m#BS0m,P7PjQ1LPjQ1MQ1OQ0mQ0K'TQ0L#=9r9k':,nW,{j5DjD5CLS0mPGPjPjPjQ1`=6jkS1MQ0`Q1[DoS1LPGPjP|PGPjQ0|PKENF?PzP~b=b@bAX29X39X49X59X69X0TX1TX7TX9TX:TX;TQ0K,18Q0L,O55R6,2V9U039;F8S0L10^8?_rqS0KAE}0t\Z[[^29^39^49^59^69^0T^1T^7T^9T^:T^;TP1Q0p/0QQ0DQ0=Q0JQ0GQ0FPaP_PiPMPQPvPwP2O>b<b>b?b8Q13Q1<PJPpPoPyPBPnQ1DP;Q1KPPPjQ0mPGPjQ1LPGPjP|PGPj1TWAS1<96j:S13PKENF?PzP~b=b@bAX29X39X49X59X69X0TX1TX7TX9TX:TX;TQ0LQ0K110A=E}t\Z[[^29^39^49^59^69^0T^1T^7T^9T^:T^;TP1Q0q/0QQ0DQ0=Q0JQ0GQ0FPaP_PiPMPQPvPwP2O>b<b>b?b8Q14Q1;PJPpPoPyPBPnQ1DP;Q1KPPPjQ0mPGPjQ1LPGPjP|PGPjQ0r,TW96j:PKENF?PzP~b=b@bAX29X39X49X59X69X0TX1TX7TX9TX:TX;TQ0LQ0KQ0r,10=E}t\Z[[^29^39^49^59^69^0T^1T^7T^9T^:T^;TP1Q0s/0QQ0DQ0=Q0JQ0GQ0FPaP_PiPMPQPvPwP2O>b<b>b?b8Q15Q1:PJPpPoPyPBPnQ1DP;Q1KPPPjQ0mPGPjQ1LPGPjP|PGPjQ0t,TW96j:PKENF?PzP~b=b@bAX29X39X49X59X69X0TX1TX7TX9TX:TX;TQ0LQ0KQ0t,10=E}t\Z[[^29^39^49^59^69^0T^1T^7T^9T^:T^;TP1Q0u/0QQ0DQ0=Q0JQ0GQ0FPaP_PiPMPQPvPwP2O>b<b>b?b8Q16Q19PJPpPoPyPBPnQ1?#@Ri#@RZ#@R}#@S1?#AS191u9`S16%A}'cR}%AiS0F9q9@S0G/Mg3Y,WcRiPiPiPiPiPiPiPiPiPiPiPiQ0GQ1R5a}R:P:Q16%AZS0J'cQ0FQ1C3aS0=Q0GQ1F5a}RZQ0GQ105a}S0GPZQ0GPZQ0=PZP:P:P:P:PZQ0=PZQ0GPZQ0GPZQ0=P:P:PiPiPiPiPiPiPiPiPiPiPiPiPSD4D4D4D4D4D4D4D4D4D4D4D4P;AClVmP6PmP4Q1UPVPmP5Q1Y?C8mD]D]PPPjPjPjQ00#BRl/:YRiPNQ1u=6jlS00DGR:PGPjPjPjQ0\PNQ02DGRZPGPjPjQ0^Q1OPGPjPjQ1MQ0<#=S1O96jk5DjPjPjQ0?#=S1M,:d%=`S029r9k':,nWQ0`CLPGPjPjPjPjQ0\Q04Q0TDGPjPjQ1[PjPjQ0\PYQ1PDGPjPKPjPjPjPiQ04A6j7lS1PDGQ1N=6jlS0TQ1_PjPj1:lLRLPdPjQ0\PlFK5DjRd5DjD5DoPGPjP|PGPjQ1BPGPjPjQ1bPjPjQ1dPjQ1fPjPKPjQ1gPjQ1hPdD5D5PjQ1jPjQ1lPjPZPjP:Q1mD5D5DoPGPjQ0|PjQ1v,:W/P{H04E<F?E<E<E<F?PzP~b=b@bAX29X39X49X59X69XI9XJ9X0TX1TX7TX9TX:TX;TXFTXGTXHTXBTXCTXDTXETP8PHP3AF3b8CJP8PEPV11VbS1v/08CJQ1z/2rQ1|Q0<,0RQ0?,131OR`5R0/2h3_11VER:/0[10FVP:PHPIPVC9PsPRPHP[Q1zCJ10IRRZQ1cPfPVP:PRC9De5_t3SQ24/0IS2410H3S1|Q1iQ1kPwPvQ0vQ1qPu11hER:Pq11qERdPhC9FZQ1sPx10dt11tbRd/0qAFhHt10dhQ0w3S3SDe11RrS0|AFq]R7Eq[[[[[[[[^29^39^49^59^69^I9^J9^0T^1T^7T^9T^:T^;T^FT^GT^HT^BT^CT^DT^ETP1PDPCQ0EQ09Q0iQ26Q27Q03Q0:Q08Q07Q0CQ0OPaP_P\PUQ0>PMPQPrPtPvPwPxP2Q06Q01OLb<b>b?b8Q17Q18PJPpPoPyPBPnQ1?#@#AQ16Q19'cRdQ0J9q9@R@/Mg3Y,WcRcPcPcPcPcPcPcPcPcPcPcPcQ1R9ad@RgPgQ0JQ1AQ0F'cQ1C3Y,W}R}Q1F9ad@RiQ109ad@R@PiP@PiP}PiPgPgPgPgPiP}PiP@PiP@PiP}PgPgPcPcPcPcPcPcPcPcPcPcPcPcPSD4D4D4D4D4D4D4D4D4D4D4D4P;Q1IP6Q1Y?CRmP4Q1UPRPmP5Q1V?CRmD]D]PPPjPjPj1:kYR5PNPjQ1uPkFKR6PGPjPjPjPLPNQ00DGRNPGPjPjQ0^Q0`PGPjPjPjPjQ1`/POQ1O96jOCLPjPjQ1M,:lQ029r9O':,nWQ1[Q0B#=96j?5DjCLPGPjPjPjPjPLQ04Q1PDGPjPjPKPjPjPLPYQ0TDGPjQ1_PjPjPjP5Q04PjP7PkFKPjPjQ1N/PkQ1bPjPjQ1oPlPjPLPkFK5DjRkCLD5DoPGPjP|PGPjQ1BPGPjPjQ1dPjPjQ1fPjQ1gPjQ1_PjQ1hPjQ1jPkD5D5PjQ1lPjQ1mPjPNPjP6Q1nD5D5DoPGPjQ13PjQ1<Q1w':/P{H04E<F?E<E<E<F?PzP~b=b@bAX29X39X49X59X69XI9XJ9XK9X0TX1TX7TX9TX:TX;TXFTXGTXHTXBTXCTXDTXETP0PHPVQ1v/00CJQ0SAFRb07ER10FrRF/2q10^rQ0<,0rQ0?,1V1Or`5R0Q0B,037UX3_10f[Q1zAEfHZQ1cQ21?E[FQ1eQ1~'29;Ir3U5_s3SQ24Q1|Q1kPwQ0vPuQ1qQ1sQ1iPXPEPh10:XCJFZPxQ0w10:s11sbRb/0hAFXHs10bXQ233S3SDeQ0|11qARq1O]h=FqR3E[[[[[[[[^29^39^49^59^69^I9^J9^K9^0T^1T^7T^9T^:T^;T^FT^GT^HT^BT^CT^DT^ETP1PDPCQ0EQ09Q0iQ26Q27Q03Q0:Q08Q07Q0AQ0OPaP_P\PUQ0@Q0>PMPQPrPtPvPwPxP2Q06Q01OMb<b>b?b8PJPpPoPyPBPnPSP;PmPPPjP<P=P=P>I0@PzP~b=b@bAQ18P1b<b>b?b8CyFjFjFjFjFjFjQ0z9Qe2eW[WYP4P1O2n2001000010121000000X8DWWP4P1O2n2011000010121000000W8W]P4P1O2n2011000010121000000W8XZCP4P1O2n2111000010121000000W8WVP4P1O2n2011000010121000000W8W\P4P1O2n2111000010121000000W8WXP4P1O2n2011000010121000000AQe08eb^UUUX_9XU9o"). Qed.
(* [comment removed for export] *)
Lemma RK_obj : forall A k, (A + k <= 2147446784 \/ 17594333495296 <= A) -> A + k <= ATOP -> 0 <= k ->
  (A + k <= t \/ t + 4096 <= A) -> (A + k <= SB \/ SB + 137438957568 <= A) ->
  disjoint_from (Wr sp RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 t RI CA n) A k.
Proof. intros. kind. Qed.
(* [comment removed for export] *)
Lemma RK_tlow : forall A k, t <= A -> A + k <= t + 288 -> 0 <= k -> disjoint_from (Wr sp RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 t RI CA n) A k.
Proof. intros. kind. Qed.
Lemma RK_thigh : forall A k, t + 3168 <= A -> A + k <= t + 4096 -> 0 <= k -> disjoint_from (Wr sp RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 t RI CA n) A k.
Proof. intros. kind. Qed.
Lemma RK_tstat : forall A k, t + 2768 <= A -> A + k <= t + 2792 -> 0 <= k -> disjoint_from (Wr sp RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 t RI CA n) A k.
Proof. intros. kind. Qed.
(* [comment removed for export] *)
Lemma RK_rec : forall A k, t + 288 <= A -> A + k <= t + 2768 -> 0 <= k -> (A + k <= CA \/ CA + 4 <= A) -> (A + k <= CA + 16 \/ CA + 16 + 4 * n <= A) ->
  disjoint_from (Wr sp RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 t RI CA n) A k.
Proof. intros. kind. Qed.
(* [comment removed for export] *)
Lemma RK_reg_other : forall A k, SB <= A -> 0 <= k -> (A + k <= RB \/ RB + 4294967296 <= A) -> A + k <= SB + 137438953472 ->
  disjoint_from (Wr sp RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 t RI CA n) A k.
Proof. intros. kind. Qed.
(* [comment removed for export] *)
Lemma RK_slots : forall A k, RB <= A -> A + k <= RB + mu -> 0 <= k -> disjoint_from (Wr sp RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 t RI CA n) A k.
Proof. intros. kind. Qed.
(* [comment removed for export] *)
Lemma RK_gap : forall A k, RB + mu' <= A -> A + k <= FA + 4 * nf -> 0 <= k -> disjoint_from (Wr sp RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 t RI CA n) A k.
Proof. intros. kind. Qed.
(* [comment removed for export] *)
Lemma RK_ri : forall A k, SB + 137438953472 <= A -> A + k <= SB + 137438957568 -> 0 <= k ->
  (A + k <= RI \/ RI + 8 <= A) -> (A + k <= RI + 16 \/ RI + 56 <= A) -> (A + k <= RI + 68 \/ RI + 69 <= A) -> (A + k <= RI + 72 \/ RI + 80 <= A) ->
  disjoint_from (Wr sp RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 t RI CA n) A k.
Proof. intros. kind. Qed.
(* [comment removed for export] *)
Lemma RK_shlow : forall A k, 2201439137792 <= A -> A + k <= SHU0 -> 0 <= k -> disjoint_from (Wr sp RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 t RI CA n) A k.
Proof. intros. kind. Qed.
Lemma RK_shmid : forall A k, SHU1 <= A -> A + k <= SHF0 -> 0 <= k -> disjoint_from (Wr sp RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 t RI CA n) A k.
Proof. intros. kind. Qed.
Lemma RK_shhigh : forall A k, SHF1 <= A -> A + k <= 17594333495296 -> 0 <= k -> disjoint_from (Wr sp RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 t RI CA n) A k.
Proof. intros. kind. Qed.
(* [comment removed for export] *)
Lemma RK_stkhi : forall A k, sp <= A -> 0 <= k -> disjoint_from (Wr sp RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 t RI CA n) A k.
Proof. intros. kind. Qed.
End Kinds.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rrec (mu' au2 nfr mfa' n : Z) : aclass := mkAClass mu' au2 nfr mfa' n.

Lemma init_cache_fields : forall st,
  a_live (init_cache st) = a_live st /\ a_next (init_cache st) = a_next st /\ a_qloc (init_cache st) = a_qloc st
  /\ a_qloc_bytes (init_cache st) = a_qloc_bytes st /\ a_qglob (init_cache st) = a_qglob st /\ a_qglob_bytes (init_cache st) = a_qglob_bytes st
  /\ a_nsec (init_cache st) = a_nsec st /\ a_nres (init_cache st) = a_nres st /\ a_ptr_array (init_cache st) = a_ptr_array st
  /\ a_space_beg (init_cache st) = a_space_beg st /\ a_cinit (init_cache st) = true.
Proof. intros st. unfold init_cache. destruct (a_cinit st) eqn:E; cbn; repeat split; try reflexivity. exact E. Qed.

Lemma put_cls_fields : forall c r st,
  a_live (put_cls c r st) = a_live st /\ a_next (put_cls c r st) = a_next st /\ a_qloc (put_cls c r st) = a_qloc st
  /\ a_qloc_bytes (put_cls c r st) = a_qloc_bytes st /\ a_qglob (put_cls c r st) = a_qglob st /\ a_qglob_bytes (put_cls c r st) = a_qglob_bytes st
  /\ a_nsec (put_cls c r st) = a_nsec st /\ a_nres (put_cls c r st) = a_nres st /\ a_ptr_array (put_cls c r st) = a_ptr_array st
  /\ a_space_beg (put_cls c r st) = a_space_beg st /\ a_cinit (put_cls c r st) = a_cinit st.
Proof. intros. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
Lemma awf_refill : forall L st X c mu' ncnt mfa' n,
  let r := get_cls st c in let S := size_of_class c in
  let mu := c_mapped_user r in let au := c_allocated_user r in let nf := c_num_freed r in let mfa := c_mapped_free_array r in
  let nd := ndist st c in let nf2 := nf + ncnt in let au2 := au + ncnt * S in
  let FL2 := xc_free (x_cls X c) ++ newslots nd (Z.to_nat ncnt) in
  let st_r := put_cls c (rrec mu' au2 (nf2 - n) mfa' n) (init_cache st) in
  let X' := xr X c (firstn (Z.to_nat (nf2 - n)) FL2) (skipn (Z.to_nat (nf2 - n)) FL2) in
  awf L st X -> 1 <= c < K_NUM_CLASSES -> c_count r = 0 ->
  mu <= mu' <= K_FREEARR_OFF -> mu' mod K_USER_MAP = 0 -> 0 <= ncnt -> au2 <= mu' ->
  4 * nf2 <= mfa' <= K_FREEARR_MAX -> mfa <= mfa' -> mfa' mod K_FREEARR_MAP = 0 ->
  1 <= n <= nf2 -> 2 * n = max_cached c ->
  awf L st_r X'.
Proof.
  intros L st X c mu' ncnt mfa' n. cbv zeta.
  intros WF HC CNT0 MUB MUM NC0 NCS NEWB NEWM NEWMOD N N2.
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  destruct (PERC c HC) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
  pose proof (size_of_class_facts c HC) as [SZ16 SZM].
  pose proof (init_cache_fields st) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11).
  set (st1 := init_cache st) in *.
  set (S := size_of_class c) in *. set (nd := ndist st c) in *.
  set (FL2 := xc_free (x_cls X c) ++ newslots nd (Z.to_nat ncnt)) in *.
  assert (XC0 : xc_cache (x_cls X c) = []).
  { destruct (xc_cache (x_cls X c)) as [|y l] eqn:E; [reflexivity|]. exfalso. rewrite ?E in LENC. cbn [length] in LENC. clear -LENC CNT0. lia. }
  assert (NDE : nd * S <= c_allocated_user (get_cls st c) < nd * S + S /\ 0 <= nd).
  { subst nd S. unfold ndist. generalize A1 SZ16; clear; intros. Z.div_mod_to_equations. nia. }
  destruct NDE as [NDE ND0].
  assert (AUE : c_allocated_user (get_cls st c) = nd * S) by (subst nd S; unfold ndist; generalize A3 A1 SZ16 NDE; clear; intros; Z.div_mod_to_equations; nia).
  assert (ND2 : ndist (put_cls c (rrec mu' (c_allocated_user (get_cls st c) + ncnt * S) (c_num_freed (get_cls st c) + ncnt - n) mfa' n) st1) c = nd + ncnt).
  { unfold ndist. rewrite get_cls_put_cls_eq. cbn [c_allocated_user rrec]. fold S. rewrite AUE.
    generalize SZ16 ND0 NC0; clear; intros. rewrite <- Z.mul_add_distr_r, Z.div_mul by lia. reflexivity. }
  assert (LFL2 : Z.of_nat (length FL2) = c_num_freed (get_cls st c) + ncnt) by (subst FL2; rewrite length_app, newslots_length; clear -LENF NC0; lia).
  unfold awf.
  cbn [a_space_beg a_ptr_array a_live a_next put_cls set_cls].
  rewrite E10, E9.
  split; [exact SBE|]. split; [exact PAE|]. split; [exact SAL|]. split; [exact SLO|]. split; [exact SHI|].
  split.
  { (* [comment removed for export] *)
    intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE].
    - rewrite get_cls_put_cls_eq, xr_cls_eq. cbn [c_mapped_user c_allocated_user c_num_freed c_mapped_free_array c_count rrec xc_free xc_cache]. fold S.
      rewrite ND2. unfold max_count. cbn [a_cinit put_cls set_cls]. rewrite E11.
      rewrite xr_busy_slots.
      split; [clear -A1 NC0 NCS SZ16; nia|]. split; [exact (proj2 MUB)|]. split.
      { rewrite AUE. rewrite <- Z.mul_add_distr_r. apply Z_mod_mult. }
      split; [exact MUM|]. split; [clear -N NC0 A5; lia|]. split; [clear -NEWB N; lia|]. split; [exact NEWMOD|].
      split; [rewrite length_firstn; clear -LFL2 N NC0 A5; lia|].
      split; [rewrite length_skipn; clear -LFL2 N NC0 A5; lia|].
      split; [clear -N N2; lia|].
      rewrite app_assoc, firstn_skipn.
      split.
      + (* [comment removed for export] *)
        subst FL2. rewrite XC0 in ND. cbn [app] in ND. rewrite <- app_assoc.
        eapply Permutation.Permutation_NoDup; [apply Permutation.Permutation_app_swap_app|].
        apply nodup_app; [apply newslots_NoDup | exact ND |].
        intros x Hx Hx'. apply newslots_In in Hx. rewrite Z2Nat.id in Hx by exact NC0.
        specialize (RANGE x ltac:(rewrite XC0; cbn [app]; exact Hx')). unfold ndist in RANGE. fold S nd in RANGE. clear -Hx RANGE. lia.
      + intros k0 Hk. subst FL2. rewrite <- app_assoc, in_app_iff, in_app_iff in Hk.
        destruct Hk as [Hk|[Hk|Hk]].
        * specialize (RANGE k0 ltac:(apply in_app_iff; left; exact Hk)). unfold ndist in RANGE. fold S nd in RANGE. clear -RANGE NC0; lia.
        * apply newslots_In in Hk. rewrite Z2Nat.id in Hk by exact NC0. clear -Hk ND0; lia.
        * specialize (RANGE k0 ltac:(rewrite XC0; cbn [app]; apply in_app_iff; right; exact Hk)). unfold ndist in RANGE. fold S nd in RANGE. clear -RANGE NC0; lia.
    - rewrite (get_cls_put_cls_ne c c') by exact NE. rewrite (xr_cls_ne X c _ _ c' NE), xr_busy_slots.
      subst st1. rewrite init_cache_cls. unfold ndist. rewrite (get_cls_put_cls_ne c c') by exact NE. rewrite init_cache_cls.
      unfold max_count. cbn [a_cinit put_cls set_cls]. rewrite E11.
      destruct (PERC c' Hc') as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & BLENF & BLENC & BCNTB & BND & BRANGE).
      pose proof (max_cached_range c' ltac:(unfold K_NUM_CLASSES in Hc'; clear -Hc'; lia)) as [MCR' _].
      unfold max_count in BCNTB. unfold ndist in BRANGE.
      repeat lazymatch goal with |- _ /\ _ => split end; try assumption; try (clear -B1 B6 BCNTB MCR'; lia).
      destruct (a_cinit st); clear -BCNTB MCR'; lia. }
  split.
  { intros c' Hc'. rewrite (get_cls_put_cls_ne c c') by (intros ->; exact (Hc' HC)). subst st1. rewrite init_cache_cls. apply OUTC. exact Hc'. }
  cbn [x_busy xr]. rewrite E1, E2.
  split; [exact BUSY|]. split; [exact LIVE|]. split; [exact FRESH|]. exact UNIQ.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma refill_store : store_refill_stmt.
Proof.
  unfold store_refill_stmt.
  intros L RNG RNG' sp m m' st st2 X c lo chunks0 ALO ARNG AR HC CNT0 CEIL LO CH LCH RR.
  (* [comment removed for export] *)
  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  destruct THR as (T0c & T40 & CACHES & CSTATS & [sj [STATS LSJ]] & UNW).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  destruct (PERC c HC) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
  destruct (CLS c HC) as (RCELLS & FARR & SLOTS & SSH). destruct (AVL c HC) as [AZU AZF].
  destruct RCELLS as (MTX16 & REG & RJ4 & EXH & RJ56). destruct FARR as (FL & FJ & FSJ).
  destruct SLOTS as [SL UND]. destruct SSH as [SSL SUND].
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  pose proof TL1 as TL1u; unfold sclr, KLS in TL1u. pose proof TL4 as TL4u; unfold iclr, AIMG_LO, AIMG_HI in TL4u.   (* [comment removed for export] *)
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof CL1 as CL1u; unfold sclr, KLS in CL1u.   (* [comment removed for export] *)
  pose proof (alayout_res_disj L ALO) as [SCX TSP].
  pose proof (size_of_class_facts c HC) as [SZ16 SZM].

pose proof (max_cached_range c ltac:(unfold K_NUM_CLASSES in HC; clear -HC; lia)) as [MCR MCE].
  assert (XC0 : xc_cache (x_cls X c) = []).
  { destruct (xc_cache (x_cls X c)) as [|y l] eqn:E; [reflexivity|]. exfalso. rewrite ?E in LENC. cbn [length] in LENC. clear -LENC CNT0. lia. }
  (* [comment removed for export] *)
  destruct RR as (m1 & MU1 & WM1 & TR & RECS').
  unfold refill_tail_ret in TR. rewrite !init_cache_cls in TR. cbv zeta in TR.
  destruct TR as (FPLE & mu' & mfa' & ncnt & sj' & stm' & stn' & UD & MUB & MUM' & NCE & NC0 & NCS & FD & NEWB & NEWM & NEWMOD & NLE & AR2 & JR
                  & GC2 & ST2E & MUT & WMT & MIT & STT & MTX' & REG' & EXH' & STN' & STATS' & LSJ' & STM' & REC' & CH' & AZU' & AZF' & MC').
  unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in *.
  change (2^37) with 137438953472 in *.
  (* [comment removed for export] *)
  set (S := size_of_class c) in *. set (n := max_cached c / 2) in *.
  set (mu := c_mapped_user (get_cls st c)) in *. set (au := c_allocated_user (get_cls st c)) in *.
  set (nf := c_num_freed (get_cls st c)) in *. set (mfa := c_mapped_free_array (get_cls st c)) in *.
  set (nd := ndist st c) in *.
  set (FL2 := xc_free (x_cls X c) ++ newslots nd (Z.to_nat ncnt)).
  set (fr := firstn (Z.to_nat (nf + ncnt - n)) FL2). set (ca := skipn (Z.to_nat (nf + ncnt - n)) FL2).
  set (X' := xr X c fr ca).
  assert (N : 1 <= n <= 8 /\ 2 * n = max_cached c) by (subst n; clear -MCR MCE; (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ])). destruct N as [N N2].
  assert (NDE : nd * S <= au < nd * S + S /\ 0 <= nd /\ au = nd * S).
  { subst nd S au. unfold ndist. generalize A1 A3 SZ16; clear; intros. Z.div_mod_to_equations. nia. }
  destruct NDE as (NDE & ND0 & AUE).
  assert (GEO : aregion_info L c = al_space_beg L + 137438953472 + c * 128 /\ aregion L c = al_space_beg L + c * 4294967296
                /\ afreearr L c = al_space_beg L + c * 4294967296 + 3758096384 /\ acache_addr L c = al_t L + 208 + c * 80).
  { unfold aregion_info, afreearr, aregion, acache_addr, K_REGION, K_FREEARR_OFF, K_SPACE_SIZE, ARI_STRIDE. change (2^32) with 4294967296. change (2^37) with 137438953472. repeat split; reflexivity. }
  destruct GEO as (RIE & RBE & FAE & CAE).
  (* [comment removed for export] *)
  assert (STR : put_cls c (cls_set_count n (cls_set_num_freed (c_num_freed (get_cls st2 c) - n) (get_cls st2 c))) st2
                = put_cls c (rrec mu' (au + ncnt * S) (nf + ncnt - n) mfa' n) (init_cache st)).
  { rewrite GC2. cbn [c_num_freed cls_set_num_freed cls_set_count c_mapped_user c_allocated_user c_mapped_free_array c_count]. unfold rrec.
    destruct ST2E as [E|E]; rewrite E at 1; [reflexivity| apply put_cls_put_cls]. }
  set (st_r := put_cls c (rrec mu' (au + ncnt * S) (nf + ncnt - n) mfa' n) (init_cache st)) in *. rewrite STR.
  pose proof (init_cache_fields st) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11).
  assert (GR : get_cls st_r c = rrec mu' (au + ncnt * S) (nf + ncnt - n) mfa' n) by (subst st_r; apply get_cls_put_cls_eq).
  assert (GO : forall c', c' <> c -> get_cls st_r c' = get_cls st c') by (intros c' NE; subst st_r; rewrite (get_cls_put_cls_ne c c') by exact NE; apply init_cache_cls).
  assert (CIR : a_cinit st_r = true) by (subst st_r; cbn; exact E11).
  assert (ND2 : ndist st_r c = nd + ncnt).
  { unfold ndist. rewrite GR. cbn [c_allocated_user rrec]. fold S. rewrite AUE. generalize SZ16 ND0 NC0; clear; intros. rewrite <- Z.mul_add_distr_r, Z.div_mul by lia. reflexivity. }
  (* [comment removed for export] *)
  set (RB := aregion L c) in *. set (FA := afreearr L c) in *. set (RI := aregion_info L c) in *. set (CA := acache_addr L c) in *.
  set (SHU0 := shad (RB + mu)) in *. set (SHU1 := SHU0 + shlen (mu' - mu)) in *.
  set (SHF0 := shad (FA + mfa)) in *. set (SHF1 := SHF0 + shlen (mfa' - mfa)) in *.
  assert (SHE : SHU1 = shad (RB + mu') /\ SHF1 = shad (FA + mfa') /\ shad RB + shlen mu = SHU0 /\ shad FA + shlen mfa = SHF0
                /\ 2201439137792 <= shad RB /\ shad RB <= SHU0 /\ SHU0 <= SHU1 /\ SHU1 + shlen (3758096384 - mu') = shad FA /\ shad FA <= SHF0 /\ SHF0 <= SHF1
                /\ SHF1 + shlen (536870912 - mfa') = shad (RB + 4294967296) /\ shad (RB + 4294967296) <= 17594333495296
                /\ SHU1 <= shad FA /\ SHF1 <= shad (RB + 4294967296)
                /\ shad RB = shad (al_space_beg L) + c * 536870912 /\ shad (RB + 4294967296) = shad (al_space_beg L) + (c + 1) * 536870912
                /\ shad (al_space_beg L) + 32 * 536870912 <= 17594333495296).
  { subst SHU1 SHU0 SHF1 SHF0. rewrite RBE, FAE. rewrite !shad_div, !shlen_div. unfold ASHOFF.
    clear -SP1 SP2 SP3 HC MUB A1 A2 A4 MUM' A5 A6 A7 NEWB NEWM NEWMOD. (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]). }
  destruct SHE as (SHE1 & SHE2 & SHE3 & SHE4 & SH1 & SH2 & SH3 & SH4 & SH5 & SH6 & SH7 & SH8 & SH12 & SH13 & SH9 & SH10 & SH11).
  assert (KF : rkfacts (bv_unsigned sp) lo (al_t L) (al_ctx L) (al_space_beg L) c RB FA RI CA mu mu' au nf mfa mfa' n SHU0 SHU1 SHF0 SHF1).
  { unfold rkfacts. pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
    clear -CEIL LO SPR TL1 TL2 TL4 CL1 CL2 CL3 CL5 HC CAE N SP1 SP2 RBE FAE RIE TSP SCX A1 MUB A5 A6 NEWB NEWM SH1 SH2 SH3 SH5 SH6 SH8 SH12 SH13.
    unfold AIMG_HI in CL3. unfold iclr, AIMG_LO, AIMG_HI in TL4 |- *. repeat split; first [assumption | lia]. }   (* [comment removed for export] *)
  assert (MUALL : munch (Wr (bv_unsigned sp) RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 (al_t L) RI CA n ++ ic_W L 1 31) m m').
  { eapply munch_trans; [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MUT]].
    - unfold sub_fp. intros x Hx. apply outside_app in Hx. destruct Hx as [H13 HW]. cbn [outside] in H13 |- *. split; [exact (proj1 H13) | exact HW].
    - unfold sub_fp. intros x Hx. apply outside_app in Hx. destruct Hx as [H13 _]. subst CA. exact H13. }
  pose proof (wmono_trans _ _ _ _ WM1 WMT) as WMALL.
  (* [comment removed for export] *)
  assert (ICW_far : forall A k, (A + k <= al_t L \/ al_t L + 4096 <= A) -> disjoint_from (ic_W L 1 31) A k).
  { intros A k HA. apply ic_W_disjoint_gen; [unfold acache_addr; clear -HA; lia | clear; cbn; lia | clear; lia]. }
  assert (ICW_t : forall A k, (A + k <= al_t L + 292 \/ al_t L + 2768 <= A) -> disjoint_from (ic_W L 1 31) A k).
  { intros A k HA. apply ic_W_disjoint_gen; [unfold acache_addr; clear -HA; lia | clear; cbn; lia | clear; lia]. }
  (* [comment removed for export] *)
  assert (FLE : map (fun k => Z_to_bv 64 (acompact c k)) FL2 = map (fun k => Z_to_bv 64 (acompact c k)) (xc_free (x_cls X c)) ++ fvals au S (Z.to_nat ncnt)).
  { subst FL2. rewrite map_app. f_equal. rewrite AUE. apply map_cw_newslots. unfold K_NUM_CLASSES; exact HC. }
  rewrite <- FLE in AR2, CH'.
  assert (LFL2 : length FL2 = Z.to_nat (nf + ncnt)) by (subst FL2; rewrite length_app, newslots_length; clear -LENF NC0 A5; lia).
  assert (MOD8 : mu mod 8 = 0 /\ mu' mod 8 = 0 /\ mfa mod 8 = 0 /\ mfa' mod 8 = 0 /\ au mod 8 = 0 /\ S mod 8 = 0 /\ RB mod 8 = 0 /\ FA mod 8 = 0).
  { rewrite RBE, FAE, AUE. clear -A4 MUM' A7 NEWMOD SZM SP3 ND0. Z.div_mod_to_equations. nia. }
  destruct MOD8 as (M8a & M8b & M8c & M8d & M8e & M8f & M8g & M8h).
  (* [comment removed for export] *)
  assert (BIGJ : junk_at m' (RB + au) (mu' - au)).
  { assert (J1 : junk_at m' (RB + au) (mu - au)).
    { eapply junk_frame; [exact UND | exact MUALL | exact WMALL |]. intros _.
      apply dj_app; [eapply (RK_slots _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -A1; lia | apply ICW_far; clear -A1 A2 TSP RBE HC; lia]. }
    destruct UD as [Emu|(_ & _ & Emu & ZN & _)].
    - rewrite Emu. exact J1.
    - replace (mu' - au) with ((mu - au) + (mu' - mu)) by (clear; lia). apply junk_merge; [exact J1 | | clear -A1; lia | clear -MUB; lia].
      replace (RB + au + (mu - au)) with (RB + mu) by (clear; lia). eexists. exact ZN. }
  assert (BIGF : fill_at m' (shad (RB + au)) (shlen (mu' - au)) 0xfa).
  { assert (F1 : fill_at m' (shad (RB + au)) (shlen (mu - au)) 0xfa).
    { eapply fill_frame; [exact SUND | exact MUALL | exact WMALL |]. intros _.
      assert (B : shad (RB + au) + shlen (mu - au) <= SHU0 /\ 2201439137792 <= shad (RB + au) /\ 0 <= shlen (mu - au)).
      { subst SHU0. rewrite !shad_div, !shlen_div in *. unfold ASHOFF in *. clear -A1 SH1 M8g M8e M8a. (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]). }
      apply dj_app; [eapply (RK_shlow _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -B; lia | apply ICW_far; clear -B TL1u SH2 SH3 SH12 SH5 SH6 SH13 SH8; lia]. }
    destruct UD as [Emu|(_ & _ & Emu & _ & FI & _)].
    - rewrite Emu. exact F1.
    - replace (shlen (mu' - au)) with (shlen (mu - au) + shlen (mu' - mu)) by (rewrite !shlen_div; clear -M8a M8b M8e A1 MUB; (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ])).
      apply fill_merge; [exact F1 | | rewrite shlen_div; clear -A1 M8a M8e; (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]) | rewrite shlen_div; clear -MUB; (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ])].
      replace (shad (RB + au) + shlen (mu - au)) with (shad (RB + mu)) by (rewrite !shad_div, shlen_div; clear -A1 M8a M8e M8g; (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ])).
      exact FI. }
  (* [comment removed for export] *)
  assert (RCc : aregion_cells L st_r m' c).
  { unfold aregion_cells. cbv zeta. fold RI. rewrite GR. cbn [c_num_freed c_mapped_free_array c_allocated_user c_mapped_user rrec]. fold S.
    pose proof MTX16 as M2. rw_split M2 1%nat M2a M2b. clear M2a.
    eapply cells_frame in M2b; [| exact MUALL | exact WMALL | cbn [cells_size csize Nat.add];
      apply dj_app; [eapply (RK_ri _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RIE; clear -HC SP1; lia | apply ICW_far; rewrite RIE; clear -HC SP1 TSP; lia]].
    split. { rw_join MTX' M2b M16. exact M16. }
    split; [exact REG'|].
    split. { eapply junk_frame; [exact RJ4 | exact MUALL | exact WMALL |]. intros _.
             apply dj_app; [eapply (RK_ri _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RIE; clear -HC SP1; lia | apply ICW_far; rewrite RIE; clear -HC SP1 TSP; lia]. }
    split; [exact EXH'|].
    destruct (junk_split m (RI + 72) 8 48 RJ56 ltac:(clear; lia) ltac:(clear; lia)) as [_ J48].
    replace 56 with (8 + 48) by reflexivity. apply junk_merge; [| | clear; lia | clear; lia].
    - pose proof (junk_of_cells m' _ _ STN') as J8. cbn in J8. exact J8.
    - eapply junk_frame; [exact J48 | exact MUALL | exact WMALL |]. intros _.
      apply dj_app; [eapply (RK_ri _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RIE; clear -HC SP1; lia | apply ICW_far; rewrite RIE; clear -HC SP1 TSP; lia]. }
  (* [comment removed for export] *)
  assert (FAc : afreearray L st_r X' m' c).
  { unfold afreearray. cbv zeta. fold FA. rewrite GR. cbn [c_num_freed c_mapped_free_array rrec]. subst X'. rewrite xr_cls_eq. cbn [xc_free].
    split; [| split].
    - subst fr. rewrite <- firstn_map. apply u32arr_firstn; [exact AR2 | rewrite length_map, LFL2; clear -N NLE NC0 A5; lia].
    - replace (mfa' - 4 * (nf + ncnt - n)) with (4 * Z.of_nat (length (skipn (Z.to_nat (nf + ncnt - n)) FL2)) + (mfa' - 4 * (nf + ncnt)))
        by (rewrite length_skipn, LFL2; clear -N NLE NC0 A5; lia).
      apply junk_merge; [| | clear; lia | clear -NEWB; lia].
      + pose proof (u32arr_skipn m' FA _ (Z.to_nat (nf + ncnt - n)) AR2 ltac:(rewrite length_map, LFL2; clear -N NLE NC0 A5; lia)) as SK.
        replace (FA + 4 * Z.of_nat (Z.to_nat (nf + ncnt - n))) with (FA + 4 * (nf + ncnt - n)) in SK by (clear -N NLE NC0 A5; lia).
        rewrite skipn_map in SK. apply junk_of_u32arr in SK. rewrite length_map in SK. exact SK.
      + rewrite length_skipn, LFL2. replace (FA + 4 * (nf + ncnt - n) + 4 * Z.of_nat (Z.to_nat (nf + ncnt) - Z.to_nat (nf + ncnt - n))) with (FA + 4 * (nf + ncnt)) by (clear -N NLE NC0 A5; lia).
        exact JR.
    - (* [comment removed for export] *)
      assert (FS1 : junk_at m' (shad FA) (shlen mfa)).
      { eapply junk_frame; [exact FSJ | exact MUALL | exact WMALL |]. intros _.
        apply dj_app; [eapply (RK_shmid _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite <- ?SHE4; clear -SH12 SHE4 A5 A6 M8c; rewrite ?shlen_div in *; (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ])
                      | apply ICW_far; clear -SHE4 SH5 SH6 SH13 SH8 SH1 SH2 SH3 SH12 TL1u; rewrite ?shlen_div in *; (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ])]. }
      destruct FD as [Emfa|(_ & Emfa & FI & _)].
      + rewrite Emfa. exact FS1.
      + replace (shlen mfa') with (shlen mfa + shlen (mfa' - mfa)) by (rewrite !shlen_div; clear -M8c M8d NEWM A5 A6; (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ])).
        apply junk_merge; [exact FS1 | rewrite SHE4; eapply junk_of_fill; exact FI | rewrite shlen_div; clear -A5 A6; (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]) | rewrite shlen_div; clear -NEWM; (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ])]. }
  (* [comment removed for export] *)
  assert (SLOTK : forall k, 0 <= k -> aslot_addr L c k = RB + k * S /\ (k < nd -> k * S + S <= au) /\ (nd <= k < nd + ncnt -> au <= k * S /\ k * S + S <= au + ncnt * S)
                            /\ shad (aslot_addr L c k) = shad RB + shlen (k * S) /\ shad (aslot_addr L c k) + shlen S = shad RB + shlen (k * S + S)).
  { intros k Hk. assert (E : aslot_addr L c k = RB + k * S) by reflexivity. rewrite E.
    assert (KS8 : (k * S) mod 8 = 0) by (clear -M8f Hk; Z.div_mod_to_equations; nia).
    split; [reflexivity|]. split; [rewrite AUE; clear -Hk SZ16; intros; nia|]. split; [rewrite AUE; clear -Hk SZ16; intros; nia|].
    rewrite !shad_div, !shlen_div. clear -KS8 M8g M8f Hk SZ16. Z.div_mod_to_equations. nia. }
  assert (NEWFREE : forall k, nd <= k -> busy_of X c k = None).
  { intros k Hk. destruct (busy_of X c k) as [b|] eqn:Bk; [exfalso| reflexivity].
    apply busy_of_In_slots in Bk. specialize (RANGE k ltac:(apply in_app_iff; right; apply in_app_iff; right; exact Bk)).
    unfold ndist in RANGE. fold S au nd in RANGE. clear -RANGE Hk. lia. }
  assert (SLc : aslots L st_r X' m' c).
  { unfold aslots. cbv zeta. rewrite ND2, GR. cbn [c_allocated_user c_mapped_user rrec]. fold S RB. subst X'. split.
    - intros k Hk. rewrite xr_busy_of. destruct (SLOTK k ltac:(clear -Hk; lia)) as (AE & KLO & KHI & _ & _).
      destruct (Z_lt_le_dec k nd) as [KL|KG].
      + specialize (SL k ltac:(clear -Hk KL; lia)). specialize (KLO KL).
        destruct (busy_of X c k) as [b|] eqn:Bk.
        * destruct (busy_of_Some_facts X c k b Bk) as (BIn & BC & BK).
          eapply (aslot_busy_frame L _ m m' MUALL WMALL); [exact SL | exact (awf_fits L st X b WF BIn) |].
          unfold xb_alloc. rewrite BC, BK, AE. fold S.
          apply dj_app; [eapply (RK_slots _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -KLO Hk A1 SZ16; nia | apply ICW_far; clear -KLO Hk A1 A2 SZ16 TSP RBE HC; nia].
        * eapply junk_frame; [exact SL | exact MUALL | exact WMALL |]. intros _. rewrite AE.
          apply dj_app; [eapply (RK_slots _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -KLO Hk A1 SZ16; nia | apply ICW_far; clear -KLO Hk A1 A2 SZ16 TSP RBE HC; nia].
      + rewrite (NEWFREE k KG). specialize (KHI ltac:(clear -KG Hk; lia)). rewrite AE.
        eapply junk_sub; [exact BIGJ | clear -KHI | clear -KHI NCS | clear -SZ16]; lia.
    - eapply junk_sub; [exact BIGJ | clear -NC0 SZ16; nia | clear; lia | clear -NCS; lia]. }
  (* [comment removed for export] *)
  assert (SSc : aslot_shadow L st_r X' m' c).
  { unfold aslot_shadow. cbv zeta. rewrite ND2, GR. cbn [c_allocated_user c_mapped_user rrec]. fold S RB. subst X'. split.
    - intros k Hk. rewrite xr_busy_of. destruct (SLOTK k ltac:(clear -Hk; lia)) as (AE & KLO & KHI & SHA & SHB).
      destruct (Z_lt_le_dec k nd) as [KL|KG].
      + specialize (SSL k ltac:(clear -Hk KL; lia)). specialize (KLO KL).
        eapply cells_frame; [exact SSL | exact MUALL | exact WMALL |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by (rewrite shlen_div; clear -SZ16; (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ])).
        assert (B : shad RB + shlen (k * S + S) <= SHU0 /\ 2201439137792 <= shad RB + shlen (k * S)).
        { rewrite <- SHE3. rewrite !shlen_div. clear -KLO A1 SH1 Hk SZ16. Z.div_mod_to_equations. nia. }
        rewrite SHA.
        apply dj_app; [eapply (RK_shlow _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); [clear -B; lia | rewrite <- SHA, SHB; clear -B; lia | rewrite shlen_div; clear -SZ16; (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ])]
                      | apply ICW_far; rewrite <- SHA, SHB; clear -B SHA SHB TL1u TL4u SH2 SH3 SH12 SH5 SH6 SH13 SH8; lia].
      + rewrite (NEWFREE k KG). specialize (KHI ltac:(clear -KG Hk; lia)). cbn [slot_shadow_bytes]. rewrite SHA.
        eapply fill_sub; [exact BIGF | | | rewrite shlen_div; clear -SZ16; (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ])].
        * rewrite shad_div, (shad_div RB), shlen_div. clear -KHI M8g M8e A1. Z.div_mod_to_equations. nia.
        * rewrite (shad_div (RB + au)), (shad_div RB), !shlen_div. clear -KHI NCS M8g M8e M8f A1 SZ16 Hk. Z.div_mod_to_equations. nia.
    - eapply fill_sub; [exact BIGF | | | rewrite shlen_div; clear -NCS; (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ])].
      + rewrite !shad_div. clear -NC0 SZ16 M8g M8e; Z.div_mod_to_equations; nia.
      + rewrite !shad_div, !shlen_div. clear -NC0 NCS SZ16 M8g M8e M8f A1; Z.div_mod_to_equations; nia. }
  (* [comment removed for export] *)
  assert (AVc : ashadow_avail L st_r m' c).
  { unfold ashadow_avail. cbv zeta. rewrite GR. cbn [c_mapped_user c_mapped_free_array rrec]. fold RB FA. split; [exact AZU' | exact AZF']. }
  assert (ACc : acache_cells L st_r X' m' c).
  { unfold acache_cells. cbv zeta. fold CA. rewrite GR. cbn [c_count rrec]. subst X'. rewrite xr_cls_eq. cbn [xc_cache].
    unfold max_count. rewrite CIR. exists (skipn (Z.to_nat n) chunks0).
    split; [exact REC'|]. split.
    - subst ca. rewrite <- skipn_map. exact CH'.
    - subst ca. rewrite !length_skipn, LFL2, LCH. clear -N NLE NC0 A5; lia. }
  (* [comment removed for export] *)
  assert (CLS' : forall c', 1 <= c' < 32 -> c' <> c ->
            aregion_cells L st_r m' c' /\ afreearray L st_r X' m' c' /\ aslots L st_r X' m' c' /\ aslot_shadow L st_r X' m' c' /\ ashadow_avail L st_r m' c' /\ acache_cells L st_r X' m' c').
  { intros c' Hc' NE. destruct (CLS c' Hc') as (RC2 & FA2 & SL2 & SS2). pose proof (AVL c' Hc') as AV2. destruct (CACHES c' Hc') as [tl (RH & RCH & RLEN)].
    destruct (PERC c' Hc') as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & BLENF & BLENC & BCNTB & BND & BRANGE).
    pose proof (size_of_class_facts c' Hc') as [SZ' SZM'].
    pose proof (GO c' NE) as G'.
    pose proof (region_other_geo L c c' ALO HC Hc' NE) as REGD. change (aregion L c) with RB in REGD.
    destruct REGD as (RD1 & RD2 & RD3 & RD4 & RD5 & RD6 & RD7 & RD8 & RD9 & RD10 & RD11).
    (* [comment removed for export] *)
    assert (DJR : forall A k, aregion L c' <= A -> A + k <= aregion L c' + 4294967296 -> 0 <= k ->
                   disjoint_from (Wr (bv_unsigned sp) RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 (al_t L) RI CA n ++ ic_W L 1 31) A k).
    { intros A k HA HB Hk. apply dj_app; [eapply (RK_reg_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -HA HB Hk RD1 RD2 RD3; lia
                                        | apply ICW_far; clear -HA HB Hk RD1 RD3 TSP; lia]. }
    assert (DJS : forall A k, shad (aregion L c') <= A -> A + k <= shad (aregion L c') + shlen 4294967296 -> 0 <= k ->
                   disjoint_from (Wr (bv_unsigned sp) RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 (al_t L) RI CA n ++ ic_W L 1 31) A k).
    { intros A k HA HB Hk. apply dj_app; [| apply ICW_far; clear -HA HB Hk RD9 RD10 TL1u; lia].
      destruct RD8 as [LOW|HIGH].
      - eapply (RK_shlow _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -HA HB Hk LOW RD9 SH2; lia.
      - eapply (RK_shhigh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -HA HB Hk HIGH RD10 SH13; lia. }
    assert (DJI : disjoint_from (Wr (bv_unsigned sp) RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 (al_t L) RI CA n ++ ic_W L 1 31) (aregion_info L c') 128).
    { apply dj_app; [eapply (RK_ri _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RD5, ?RIE; clear -Hc' NE HC; lia | apply ICW_far; rewrite ?RD5; clear -Hc' SP1 TSP; lia]. }
    split; [| split; [| split; [| split; [| split]]]].
    - eapply (aregion_cells_frame L _ m m' MUALL WMALL st); [exact RC2 | rewrite G'; reflexivity | rewrite G'; reflexivity | rewrite G'; reflexivity | rewrite G'; reflexivity | exact DJI].
    - eapply (afreearray_frame L _ m m' MUALL WMALL st st_r X); [exact FA2 | rewrite G'; reflexivity | rewrite G'; reflexivity | subst X'; rewrite (xr_cls_ne X c _ _ c' NE); reflexivity
        | exact BLENF | exact B5 | | clear -B6; lia |].
      + apply DJR; rewrite ?RD4; clear -B5 B6 B2; lia.
      + apply DJS; rewrite ?RD11, ?shlen_div; try (clear -B2 B5 B6; (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ])).
    - eapply (aslots_update L _ m m' MUALL WMALL st st_r X _ c' (-1)); [exact SL2 | unfold ndist; rewrite G'; reflexivity | rewrite G'; reflexivity | rewrite G'; reflexivity | | |].
      + intros k Hk _. subst X'. rewrite xr_busy_of. split; [reflexivity|]. split.
        * destruct (slot_in_region L st c' k ltac:(clear -SZ'; lia) ltac:(clear -B1; lia) Hk) as (Q1 & Q2 & Q3).
          apply DJR; [exact Q1 | clear -Q2 B1 B2; lia | clear -SZ'; lia].
        * intros b Hb. destruct (busy_of_Some_facts X c' k b Hb) as (BIn & BC & BK). split; [exact BC|]. split; [exact BK|]. exact (awf_fits L st X b WF BIn).
      + intros POS. apply DJR; clear -B1 B2 POS; lia.
      + intros HK. exfalso. clear -HK. lia.
    - eapply (aslot_shadow_update L _ m m' MUALL WMALL st st_r X _ c' (-1)); [exact SS2 | unfold ndist; rewrite G'; reflexivity | rewrite G'; reflexivity | rewrite G'; reflexivity | | | | rewrite shlen_div; clear -SZ'; (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ])].
      + intros k Hk _. subst X'. rewrite xr_busy_of. split; [reflexivity|].
        destruct (slot_in_region L st c' k ltac:(clear -SZ'; lia) ltac:(clear -B1; lia) Hk) as (Q1 & Q2 & Q3).
        apply DJS.
        * apply shad_mono. exact Q1.
        * rewrite !shad_div, !shlen_div in *. clear -Q1 Q2 B1 B2 RD7. (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]).
        * rewrite shlen_div. clear -SZ'; (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]).
      + intros POS. apply DJS.
        * apply shad_mono. clear -B1; lia.
        * rewrite !shad_div, !shlen_div in *. clear -B1 B2 RD7. (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]).
        * clear -POS; lia.
      + intros HK. exfalso. clear -HK. lia.
    - eapply (ashadow_avail_frame L _ m m' MUALL WMALL st); [exact AV2 | rewrite G'; reflexivity | rewrite G'; reflexivity | |]; unfold K_FREEARR_OFF, K_FREEARR_MAX.
      + intros POS. apply DJS.
        * apply shad_mono. clear -B1; lia.
        * rewrite !shad_div, !shlen_div in *. clear -B1 B2 RD7. (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]).
        * clear -POS; lia.
      + intros POS. apply DJS.
        * apply shad_mono. rewrite RD4. clear -B5 B6; lia.
        * rewrite RD4. rewrite !shad_div, !shlen_div in *. clear -B5 B6 RD7. (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]).
        * clear -POS; lia.
    - unfold acache_cells. cbv zeta. rewrite G'. unfold max_count. rewrite CIR. subst X'. rewrite (xr_cls_ne X c _ _ c' NE). exists tl.
      split; [exact (RECS' c' ltac:(clear -Hc'; lia) NE)|]. split; [| exact RLEN].
      eapply u32arr_frame; [exact RCH | exact MUALL | exact WMALL |]. rewrite length_app, length_map.
      replace (Z.of_nat (length (xc_cache (x_cls X c')) + length tl)) with 16 by (clear -RLEN; lia).
      apply dj_app; [eapply (RK_rec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RD6, ?CAE; clear -Hc' NE HC N; lia | change (4 * 16) with 64; apply ic_W_disjoint_chunks]. }
  (* [comment removed for export] *)
  assert (BB : forall b, In b (x_busy X) ->
      al_space_beg L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_space_beg L + 137438953472
      /\ (xb_alloc L b + size_of_class (xb_class b) <= RB + mu \/ RB + 4294967296 <= xb_alloc L b)).
  { intros b Hb. destruct (BUSY b Hb) as [CLB _].
    destruct (PERC (xb_class b) CLB) as (Q1 & Q2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & QR).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
    pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as (P5 & P4 & P0).
    unfold xb_alloc.
    destruct (Z.eq_dec (xb_class b) c) as [EC|NC].
    - rewrite EC in P5, P4, Q1, Q2 |- *.
      change (aregion L c) with RB in P5, P4. change (c_allocated_user (get_cls st c)) with au in P4, Q1. change (c_mapped_user (get_cls st c)) with mu in Q1, Q2.
      split; [clear -P5 RBE HC; lia|]. split; [clear -P4 A1 A2 RBE HC; lia|]. left. clear -P4 A1; lia.
    - pose proof (region_other_geo L c (xb_class b) ALO HC CLB NC) as (R1 & R2 & R3 & _). change (aregion L c) with RB in R2.
      split; [clear -P5 R1; lia|]. split; [clear -P4 Q1 Q2 R3; lia|].
      destruct R2 as [D|D]; [left; clear -D P4 Q1 Q2 A1; lia | right; clear -D P5; lia]. }
  (* [comment removed for export] *)
  assert (DJimg : forall A k, 65536 <= A -> 0 <= k -> A + k <= 6352896 ->
            disjoint_from (Wr (bv_unsigned sp) RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 (al_t L) RI CA n ++ ic_W L 1 31) A k).
  { intros A k H1 H2 H3. apply dj_app; [eapply (RK_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); assumption | apply ICW_far; clear -H1 H3 TL4u; lia]. }
  assert (DJt : forall A k, al_t L <= A -> 0 <= k ->
            (A + k <= al_t L + 288 \/ (al_t L + 2768 <= A /\ A + k <= al_t L + 2792) \/ (al_t L + 3168 <= A /\ A + k <= al_t L + 4096)) ->
            disjoint_from (Wr (bv_unsigned sp) RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 (al_t L) RI CA n ++ ic_W L 1 31) A k).
  { intros A k H1 H2 H3. apply dj_app; [| apply ICW_t; clear -H3; lia].
    destruct H3 as [H3|[H3|H3]];
      [ eapply (RK_tlow _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF)
      | eapply (RK_tstat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF)
      | eapply (RK_thigh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF)]; clear -H1 H2 H3; lia. }
  assert (DJctx : forall A k, al_ctx L <= A -> A + k <= al_ctx L + 4096 -> 0 <= k ->
            disjoint_from (Wr (bv_unsigned sp) RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 (al_t L) RI CA n ++ ic_W L 1 31) A k).
  { intros A k H1 H2 H3. apply dj_app; [| apply ICW_far; clear -H1 H2 H3 CL5; lia].
    pose proof CL1 as CL1'; unfold sclr, KLS in CL1'.
    eapply (RK_obj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); atop_facts; clear -H1 H2 H3 CL1' CL2 CL5 SCX; lia. }
  (* [comment removed for export] *)
  assert (WF' : awf L st_r X').
  { subst st_r X' fr ca FL2. apply awf_refill; first [exact WF | exact HC | exact CNT0 | exact MUB | exact MUM' | exact NC0 | exact NCS | exact NEWB | exact NEWM | exact NEWMOD | exact N2 | clear -N NLE; lia]. }
  assert (RT' : arep_rt L m').
  { eapply arep_rt_frame; [exact MUALL | exact WMALL | exact RT |]. unfold rt_hulls, ATP88, ATSD.
    repeat (apply Forall_cons; [cbn [fst snd]; first [apply DJimg; clear; lia | apply DJctx; clear; lia] |]). apply Forall_nil. }
  assert (EF : a_live st_r = a_live st /\ a_next st_r = a_next st /\ a_qloc st_r = a_qloc st /\ a_qloc_bytes st_r = a_qloc_bytes st
               /\ a_qglob st_r = a_qglob st /\ a_qglob_bytes st_r = a_qglob_bytes st /\ a_nsec st_r = a_nsec st /\ a_nres st_r = a_nres st
               /\ a_ptr_array st_r = a_ptr_array st /\ a_space_beg st_r = a_space_beg st).
  { subst st_r. destruct (put_cls_fields c (rrec mu' (au + ncnt * S) (nf + ncnt - n) mfa' n) (init_cache st)) as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & _).
    rewrite P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, E1, E2, E3, E4, E5, E6, E7, E8, E9, E10. repeat split; reflexivity. }
  destruct EF as (EF1 & EF2 & EF3 & EF4 & EF5 & EF6 & EF7 & EF8 & EF9 & EF10).
  assert (INST' : ainstance L st_r m').
  { eapply ainstance_frame; [exact MUALL | exact WMALL | exact INST | exact EF8 | exact EF7 | | |]; apply DJimg; clear; unfold AINSTANCE; lia. }
  assert (THR' : athread L st_r X' m').
  { unfold athread. split; [| split; [| split; [| split; [| split]]]].
    - eapply cells_frame; [exact T0c | exact MUALL | exact WMALL |]. cbn [cells_size csize Nat.add]. apply DJt; clear; lia.
    - eapply cells_frame; [exact T40 | exact MUALL | exact WMALL |]. cbn [cells_size csize Nat.add]. apply DJt; clear; lia.
    - intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE]; [exact ACc | exact (proj2 (proj2 (proj2 (proj2 (proj2 (CLS' c' Hc' NE))))))].
    - apply (junk_merge m' (al_t L + 2768) 24 8); [| | clear; lia | clear; lia].
      + destruct (junk_split m (al_t L + 2768) 24 8 CSTATS ltac:(clear; lia) ltac:(clear; lia)) as [J24 _].
        eapply junk_frame; [exact J24 | exact MUALL | exact WMALL | intros _; apply DJt; clear; lia].
      + replace (al_t L + 2768 + 24) with (al_t L + 2792) by (clear; lia). pose proof (junk_of_cells m' _ _ STM') as J. cbn in J. exact J.
    - exists sj'. split; [exact STATS' | exact LSJ'].
    - eapply cells_frame; [exact UNW | exact MUALL | exact WMALL |]. cbn [cells_size csize Nat.add]. apply DJt; clear; lia. }
  (* [comment removed for export] *)
  assert (SHX : shlen 4294967296 = 536870912 /\ shad (RB + 4294967296) = shad RB + 536870912 /\ SHF1 <= shad RB + 536870912).
  { split; [rewrite shlen_div; reflexivity|]. clear -SH9 SH10 SH13. split; lia. }
  destruct SHX as (SX1 & SX2 & SX3).
  pose proof (ao_space L ALO) as RSP.
  set (WH := [(bv_unsigned sp - 672, bv_unsigned sp); (al_t L + 208, al_t L + 3168); (RI, RI + 128); (RB + mu, RB + 4294967296); (SHU0, shad RB + 536870912)]).
  assert (MUH : munch WH m m').
  { eapply munch_weaken; [| exact MUALL]. unfold sub_fp. intros x Hx. subst WH. cbn [outside] in Hx. destruct Hx as (O1 & O2 & O3 & O4 & O5 & _).
    apply outside_app. split.
    - cbn [outside]. clear -O1 O2 O3 O4 O5 SX3 SH2 SH3 SH12 SH5 SH6 MUB NEWB A5 A1 CAE RBE FAE HC N.
      repeat split; try exact I; lia.
    - apply ic_W_outside; [unfold acache_addr; clear -O2; lia | clear; cbn; lia | clear; lia]. }
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
  assert (QU : quar_untouched L X WH).
  { unfold quar_untouched. subst WH. unfold AINSTANCE in *.
    repeat (apply Forall_cons; [cbn [fst snd];
      split; [clear -CEIL LO TL1u TL4u TL2 TSP SP1 SP2 RIE RBE HC MUB A1 SH1 SH2 SH9 SH11; lia|];
      split; [clear -CEIL LO TL1u TL4u TL2 TSP SP1 SP2 RIE RBE HC MUB A1 SH1 SH2 SH9 SH11; lia|];
      split; [clear -CEIL LO TL1u TL4u TL2 TSP SP1 SP2 RIE RBE HC MUB A1 SH1 SH2 SH9 SH11; lia|];
      split; [clear -CEIL LO TL1u TL4u TL2 TSP SP1 SP2 RIE RBE HC MUB A1 SH1 SH2 SH9 SH11; lia|];
      intros b Hb; destruct (BB b Hb) as (Bb1 & Bb2 & Bb3); destruct (xb_st b); [exact I| |];
      clear -Bb1 Bb2 Bb3 CEIL LO TL1u TL4u TL2 TSP SP1 SP2 RIE RBE HC MUB A1 SH1 SH2 SH9 SH11; lia |]).
    apply Forall_nil. }
  assert (QSM : quar_same st st_r X X').
  { unfold quar_same. rewrite EF3, EF4, EF5, EF6, EF10. repeat (split; [reflexivity|]). subst X'. unfold xr. cbn [x_busy].
    split; intros b Hb; destruct (xb_st b); first [exact I | exact Hb]. }
  assert (HQ' : ah_quar H L st_r X' m').
  { eapply (hq_frame _ HL L st st_r X X' m m'); [exact HQ | exact MUH | exact WMALL | exact QU | exact QSM]. }
  assert (SU : sec_untouched L WH).
  { unfold sec_untouched, aknown. subst WH. unfold AINSTANCE, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
    (* [comment removed for export] *)
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 4 right; left; clear -Ha CEIL LO; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 5 right; left; clear -Ha TL1u TL4u TL2; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 7 right; left; clear -Ha RSP RIE HC; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 7 right; left; clear -Ha RSP RBE HC MUB A1; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; right; left; clear -Ha HC SH1 SH2 SH9 SH10 SH11; lia |].
    apply Forall_nil. }
  assert (SSM : sec_same st st_r).
  { unfold sec_same. rewrite EF7, EF8, EF9, EF1. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [intros; tauto|].
    rewrite (sec_chunks_of_eq st st_r EF1 EF3 EF5). apply Permutation_refl. }
  assert (HS' : ah_sec H L st_r X' m').
  { eapply (hs_frame _ HL L st st_r X X' m m'); [exact HS | exact MUH | exact WMALL | exact SU | exact SSM]. }
  assert (HD' : ah_depot H L m').
  { eapply (hd_frame _ HL L m m'); [exact HD | exact MUH | exact WMALL |]. subst WH.
    pose proof (ao_nodes L ALO) as (_ & ON1 & ON3 & ONs & _). pose proof (ao_store L ALO) as (_ & OS1 & OS3 & OSs & _). unfold sclr, KLS in ONs, OSs.
    pose proof (ad_nodes_res L ALO) as DNR. pose proof (ad_store_res L ALO) as DSR. pose proof (ad_t_nodes L ALO) as DTN. pose proof (ad_t_store L ALO) as DTS.
    unfold adisj in *.
    (* [comment removed for export] *)
    repeat (apply Forall_cons; [cbn [fst snd]; intros a Ha; split; [| split];
      [ clear -Ha CEIL LO TL4u TL2 SP1 SP2 RSP RIE RBE HC MUB A1 SH1 SH2 SH9 SH11; lia
      | clear -Ha CEIL LO TL2 SP1 SP2 RSP RIE RBE HC MUB A1 SH1 SH2 SH9 SH11 ON1 ON3 ONs DNR DTN; lia
      | clear -Ha CEIL LO TL2 SP1 SP2 RSP RIE RBE HC MUB A1 SH1 SH2 SH9 SH11 OS1 OS3 OSs DSR DTS; lia ] |]). apply Forall_nil. }
  assert (AR' : AREP H L st_r X' m').
  { split; [exact WF'|]. split; [exact RT'|]. split; [exact INST'|]. split; [exact THR'|]. split.
    { intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE].
      - split; [exact RCc|]. split; [exact FAc|]. split; [exact SLc| exact SSc].
      - destruct (CLS' c' Hc' NE) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6). split; [exact Y1|]. split; [exact Y2|]. split; [exact Y3| exact Y4]. }
    split; [exact HQ'|]. split; [exact HS'|]. split; [exact HD'|].
    split; [eapply arelro_frame; [exact MUALL | exact HRO | apply DJimg; clear; unfold ARELRO_LO, ARELRO_HI; lia]|].
    split; [eapply arep_rt2_frame; [exact MUALL | exact WMALL | exact RT2 | | |]; apply DJimg; clear; lia|].
    split; [| eapply arep_rt3_frame; [exact MUALL | exact WMALL | exact RT3 |]; unfold rt3_hulls;
              repeat (apply Forall_cons; [cbn [fst snd]; apply DJimg; clear; lia |]); apply Forall_nil].
    intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE]; [exact AVc | exact (proj1 (proj2 (proj2 (proj2 (proj2 (CLS' c' Hc' NE))))))]. }
  (* [comment removed for export] *)
  assert (ARNG' : arng L RNG' st_r).
  { pose proof (arng_mono L RNG RNG' st FPLE ARNG) as AM.
    destruct AM as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & GC & GPA & GSC & GPSH).
    unfold arng. split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|]. split; [exact G5|].
    split; [exact G6|]. split; [exact G7|]. split; [exact G8|]. split; [exact G9|].
    split; [| split; [rewrite EF8; exact GPA| split; [rewrite (sec_chunks_of_eq st st_r EF1 EF3 EF5); exact GSC| exact GPSH]]].
    intros c' Hc'. cbv zeta. destruct (Z.eq_dec c' c) as [->|NE].
    - rewrite GR. cbn [c_mapped_user c_mapped_free_array rrec].
      destruct (GC c HC) as (R1 & R2 & R3 & R4).
      change (aregion L c) with RB in R1, R2 |- *. change (afreearr L c) with FA in R3, R4 |- *.
      change (c_mapped_user (get_cls st c)) with mu in R1, R2. change (c_mapped_free_array (get_cls st c)) with mfa in R3, R4.
      split; [| split; [| split]].
      + destruct UD as [Emu|(_ & _ & _ & _ & _ & RU & RSU & BW)]; [rewrite Emu; exact R1|].
        replace mu' with (mu + (mu' - mu)) by (clear; lia). apply rng_merge; [exact BW | clear -A1; lia | clear -MUB; lia | exact R1 | exact RU].
      + destruct UD as [Emu|(_ & _ & _ & _ & _ & RU & RSU & BW)]; [rewrite Emu; exact R2|].
        (* [comment removed for export] *)
        destruct (GPSH c HC) as [_ LAT]. specialize (LAT (mu' / 262144) ltac:(clear -MUB A1; (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]))).
        change (aregion L c) with RB in LAT.
        assert (HLU : shad RB - 4096 + (shlen mu + 4096) = SHU0 /\ SHU0 + shlen (mu' - mu) = shad RB + 32768 * (mu' / 262144)
                     /\ shlen mu' + 8192 = (shlen mu + 4096) + (shlen (mu' - mu) + 4096) /\ 0 <= shlen mu + 4096 /\ 0 <= shlen (mu' - mu)).
        { rewrite <- SHE3. rewrite !shlen_div. clear -MUB A1 A4 MUM' M8a M8b. (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]). }
        destruct HLU as (HLU1 & HLU2 & HLU3 & HLU4 & HLU5). rewrite HLU3.
        apply rng_merge; [exact BW| exact HLU4| clear -HLU5; lia| eapply rng_sub'; [exact R2| clear -HLU4; lia]|].
        rewrite HLU1. apply rng_merge; [exact BW| exact HLU5| clear; lia| exact RSU|]. rewrite HLU2. exact LAT.
      + destruct FD as [Emfa|(_ & _ & _ & RF & RSF & BW)]; [rewrite Emfa; exact R3|].
        replace mfa' with (mfa + (mfa' - mfa)) by (clear; lia). apply rng_merge; [exact BW | clear -A5 A6; lia | clear -NEWM; lia | exact R3 | exact RF].
      + destruct FD as [Emfa|(_ & _ & _ & RF & RSF & BW)]; [rewrite Emfa; exact R4|].
        replace (shlen mfa') with (shlen mfa + shlen (mfa' - mfa)) by (rewrite !shlen_div; clear -M8c M8d; (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ])).
        apply rng_merge; [exact BW | rewrite shlen_div; clear -A5 A6; (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]) | rewrite shlen_div; clear -NEWM; (first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]) | exact R4 |].
        rewrite SHE4. exact RSF.
    - rewrite (GO c' NE). exact (GC c' Hc'). }
  (* [comment removed for export] *)
  exists X'.
  split; [exact AR'|]. split; [exact ARNG'|]. split; [exact CIR|].
  split; [rewrite GR; unfold max_count; rewrite CIR; cbn [c_count rrec]; subst n; reflexivity|].
  split; [unfold max_count; rewrite CIR; subst n; clear -N; lia|].
  split; [subst X'; reflexivity|].
  split; [intros c' NE; subst X'; apply xr_cls_ne; exact NE|].
  split; [exact EF1|]. split; [exact EF2|]. split; [exact EF3|]. split; [exact EF4|]. split; [exact EF5|]. split; [exact EF6|]. split; [exact EF7|]. split; [exact EF8|].
  split; [exact GO|].
  split; [| exact WMALL].
  eapply munch_weaken; [| exact MUH]. unfold sub_fp. intros x Hx. subst WH. unfold K_REGION in Hx. change (2^32) with 4294967296 in Hx.
  rewrite SX1 in Hx. cbn [outside] in Hx |- *. clear -Hx. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithStore.
Hypothesis STORE : store_refill_stmt.

Theorem arefill_from_store : refill_stmt H.
Proof.
  unfold refill_stmt.
  intros R k Q L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st X c lo
         ALO ARNG AR MI ST CEIL LO TP Ha0 Ha1 Ha2 Ha3 HC CNT0 RSTK KONT.
  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  destruct THR as (T0c & T40 & CACHES & CSTATS & [sj [STATS LSJ]] & UNW).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  destruct (PERC c HC) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
  destruct (CLS c HC) as (RCELLS & FARR & SLOTS & SSH). destruct (AVL c HC) as [AZU AZF].
  destruct RCELLS as (MTX16 & REG & RJ4 & EXH & RJ56). destruct FARR as (FL & FJ & FSJ).
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  pose proof TL1 as TL1u; unfold sclr, KLS in TL1u. pose proof TL4 as TL4u; unfold iclr, AIMG_LO, AIMG_HI in TL4u.   (* [comment removed for export] *)
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof CL1 as CL1u; unfold sclr, KLS in CL1u.   (* [comment removed for export] *)
  pose proof (alayout_res_disj L ALO) as [SCX TSP].
  pose proof ARNG as ARNG0. destruct ARNG0 as (RIMG & RT4 & RCTX & RNO & RSTO & RRI & RFK & RSFK & RDTLS & RCLS & RPA & RSECS & RPSH).
  destruct (RCLS c HC) as (RREG & RSREG & RFA & RSFA).
  pose proof RT as RT0.
  destruct RT0 as (GPG & GOT & GOT80 & RIC & LS1 & REAL & IMAX4 & FLG5 & FLG & HPP & SHB & CANP & TI & TK & INI2 & LAY & MCS & OOM3
                    & PGC & HK2 & CF8 & CF34 & CSMT & T88 & TSD & LS2 & CT8 & CT).
  destruct RT2 as (DPM & MLIM & RWCS).
  destruct INST as (I32 & I48 & I64 & I72 & I112 & I680 & I984 & I40 & I56).
  (* [comment removed for export] *)
  assert (MC : m3_cells L m).
  { unfold m3_cells, poison_cells, rmap_cells, AINSTANCE in *. repeat lazymatch goal with |- _ /\ _ => split end; assumption. }
  pose proof MTX16 as MTX. rw_split MTX 1%nat MTX MTXb. clear MTXb.
  destruct (junk_split m (aregion_info L c + 72) 8 48 RJ56 ltac:(lia) ltac:(lia)) as [STN8 _]. destruct (c8_of_junk m _ STN8) as [stn STN].
  destruct (junk_split m (al_t L + 2768) 24 8 CSTATS ltac:(lia) ltac:(lia)) as [_ STM8].
  replace (al_t L + 2768 + 24) with (al_t L + 2792) in STM8 by lia. destruct (c8_of_junk m _ STM8) as [stm STM].
  destruct FJ as [fj FJ'].
  destruct (CACHES c HC) as [tail (RECc & CH & LCH)]. cbv zeta in CH.
  assert (XC0 : xc_cache (x_cls X c) = []).
  { destruct (xc_cache (x_cls X c)) as [|y l] eqn:E; [reflexivity|]. exfalso. rewrite ?E in LENC. cbn [length] in LENC. clear -LENC CNT0. lia. }
  rewrite XC0 in CH, LCH. cbn [map app length] in CH, LCH.
  assert (NFA : c_num_freed (get_cls st c) <= c_allocated_user (get_cls st c) / size_of_class c).
  { rewrite <- LENF. apply NoDup_bound_length.
    - apply NoDup_app_remove_r in ND. exact ND.
    - intros k0 Hk. apply RANGE. apply in_app_iff. left. exact Hk.
    - unfold ndist in RANGE. apply Z.div_pos; [lia|]. pose proof (size_of_class_facts c HC); lia. }
  pose proof (size_of_class_facts c HC) as [SZ16 SZM].
  assert (FL31 : Forall (fun w : word => bv_unsigned w < 2^31) (map (fun k => Z_to_bv 64 (acompact c k)) (xc_free (x_cls X c)))).
  { apply Forall_forall. intros w Hw. apply in_map_iff in Hw. destruct Hw as (k0 & <- & Hk).
    pose proof (RANGE k0 ltac:(apply in_app_iff; left; exact Hk)) as KR. unfold ndist in KR.
    assert (B : 0 <= acompact c k0 < 2^28).
    { unfold acompact. unfold K_FREEARR_OFF in A2. generalize KR A1 A2 SZ16 SZM; clear; intros. Z.div_mod_to_equations. nia. }
    rewrite unsigned_lit; lia. }
  eapply refill_spec with (lo := lo) (L := L) (st := st) (cnt := fun j => c_count (get_cls st j)) (sj := sj) (stm := stm) (stn := stn) (fj := fj)
                          (fl := map (fun k => Z_to_bv 64 (acompact c k)) (xc_free (x_cls X c))) (chunks0 := tail);
  try lazymatch goal with
       | |- implS _ _ _ _ _ => idtac
       | |- stk _ _ _ _ => exact ST
       | |- ATOP <= _ => exact CEIL
       | |- _ <= bv_unsigned _ - _ => clear -LO; lia
       | |- mem_inv _ _ => exact MI
       | |- m3_cells _ _ => exact MC
       | |- rw_cells _ _ (aregion_info _ _) _ => exact MTX
       | |- rw_cells _ _ (aregion_info _ _ + 16) _ => exact REG
       | |- rw_cells _ _ (aregion_info _ _ + 68) _ => exact EXH
       | |- rw_cells _ _ (aregion_info _ _ + 72) _ => exact STN
       | |- rw_cells _ _ (afreearr _ _ + _) _ => exact FJ'
       | |- rw_cells _ _ (al_t _ + 2792) _ => exact STM
       | |- u64arr _ _ _ _ => exact STATS
       | |- u32arr _ _ (afreearr _ _) _ => exact FL
       | |- u32arr _ _ _ _ => exact CH
       | |- Forall _ _ => exact FL31
       | |- length (map _ _) = _ => rewrite length_map; clear -LENF; lia
       | |- length _ = _ => first [exact LSJ | exact LCH]
       | |- azero _ (shad (aregion _ _ + _)) _ => exact AZU
       | |- azero _ (shad (afreearr _ _ + _)) _ => exact AZF
       | |- a_space_beg _ = _ => exact SBE
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (bv_unsigned _ - _) => exact RSTK
       | |- rng _ (aregion_info _ _) _ => eapply rng_sub'; [exact RRI|]; unfold aregion_info, ARI_STRIDE, K_SPACE_EXTRA; clear -HC; unfold K_NUM_CLASSES in HC; lia
       | |- rng _ (afreearr _ _) _ => exact RFA
       | |- rng _ (al_ctx _) _ => eapply rng_sub'; [exact RCTX|]; clear; lia
       | |- rng _ (al_t _) _ => exact RT4
       | |- @eq word _ _ => first [exact TP | exact Ha0 | exact Ha1 | exact Ha2 | exact Ha3]
       | |- _ \/ _ => first [exact CL5 | exact TSP | clear -SCX; unfold K_SPACE_SIZE, K_SPACE_EXTRA in *; lia]
       | |- forall j, _ -> arec_hdr _ _ _ _ _ _ => intros j Hj; destruct (CACHES j ltac:(unfold K_NUM_CLASSES; clear -Hj; lia)) as [tl (RH & _ & _)]; exact RH
       | |- forall st2, _ => idtac
       end.
  all: lazymatch goal with
       | |- forall _, _ => idtac
       | _ => first [assumption | clear -A1 A2 A3 A4 A5 A6 A7 NFA HC SP1 SP2 SP3 TL1u TL4u TL2 TL3 CL1 CL1u CL2 CNT0; unfold K_NUM_CLASSES in *; lia]
       end.
  (* [comment removed for export] *)
  intros st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' RR.
  destruct (STORE L RNG RNG' sp m m' st st2 X c lo tail ALO ARNG AR HC CNT0 CEIL LO CH LCH RR)
    as (X' & AR' & ARNG' & CIN & CCNT & NPOS & XB & XC & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & GC & MU & WM).
  destruct RR as (m1 & _ & _ & TR & _).
  destruct TR as (FPLE & mu' & mfa' & ncnt & sj' & stm' & stn' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MIT & STT & _).
  unfold KKref. rewrite (take_is_apop c (max_cached c / 2) st2).
  eapply KONT. unfold ARefill_iface.refill_ret. split; [exact FPLE|]. do 15 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MIT|]. split; [exact STT|]. split; [exact AR'|]. split; [exact ARNG'|].
  split; [exact CIN|]. split; [exact CCNT|]. split; [exact NPOS|]. split; [exact XB|]. split; [exact XC|].
  split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|]. split; [exact L5|]. split; [exact L6|]. split; [exact L7|]. split; [exact L8|].
  exact GC.
Qed.
End WithStore.

(* [comment removed for export] *)
Theorem arefillP : refill_stmt H.
Proof. exact (arefill_from_store refill_store). Qed.
End RefillP.
End CANSEC1.
