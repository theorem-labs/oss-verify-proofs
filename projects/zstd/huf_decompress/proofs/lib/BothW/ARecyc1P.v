(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (19 recorded proofs replaced by written proofs (RK_tlow, RK_thigh, RK_tstat and 16 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import MM_syscalls WStr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import SysStepF.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg AProto ABase AKit AKit2 AKitQ AKitR ABytes AQConst AModelFacts ARep ARepKit ARepFrame ALayout AHeapP
     ARepQ ARepQP ARepQR AFreeRep AFreeGeo AFreeRead ARecRep ARepQD ARefillP RT_stubs
     F_apoison F_acache F_aalloc3 F_ammap F_aensure F_apopulate F_agetfrom F_arefill F_amaybe F_areturn F_acdrain F_acdealloc F_arecyc1.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ARecyc1P () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C46Stdlib5Lists4List2hdC46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rI35stdpp9countable9Countable00C35stdpp4base;RelDecisionC59OSSVerify5KrLib4Spec8AsanCtrl4aptrC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC46Stdlib5Lists4List8map_consC46Stdlib5Lists4List7existsbI35stdpp4gmap4gmap00C35stdpp4base4fmapC59OSSVerify5KrLib3Lib3Arr@upd_firstn_skipnC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:firstn_nilC46Stdlib5Lists4List:firstn_mapC46Stdlib5Lists4List=repeat_lengthC59OSSVerify5KrLib5BothW5ABase4sclrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01I47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3mulI47Corelib4Init5Logic2ex00K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr05C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init5Logic2ex01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic2or00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib5BothW5ABase4iclrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4ablkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula03I59OSSVerify5KrLib3Lib8RunConst9runConstT00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3powI47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib3Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegc59OSSVerify5KrLib5BothW8ARecyc1P8iclr_intC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ARecyc1P8sclr_intC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega5Tauto8GFormula01K47Corelib4Init5Logic3and01K47Corelib4Init9Datatypes4prod01K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega3Op201c59OSSVerify5KrLib5BothW8ARecyc1P5reckfC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00C59OSSVerify5KrLib3Lib3Arr3updC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indC47Corelib4Init9Datatypes6lengthI47Corelib4Init5Peano2le00C56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib5Arith8PeanoNat3Nat7sub_0_rC56Stdlib6ZArith6BinInt1Z6of_natC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init3Nat3subC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelI47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith4Znat5Nat2Z6inj_lec59OSSVerify5KrLib5BothW8ARecyc1P=upd_app_rightC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega=RingMicromega3Op205c59OSSVerify5KrLib5BothW8ARecyc1P<upd_app_leftC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib5BothW6ARepQR<aquar_constsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7AQConst9aq_tcacheC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_qlocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ARepQR6qr_locC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<a_qloc_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ7aqcacheC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC59OSSVerify5KrLib5BothW6ARepQR6qr_tmpC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib5BothW4ARep3awfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ARecRep4xrecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ARepQR<qcoupled_recC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ARepQD5qnumRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ARepQR8qnum_tmpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7a_qglobC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ARepQR7qr_globC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=a_qglob_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ARepQR5qr_iaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ6aintalC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ARepQR8qr_pendbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ARepQR8qr_qpendC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW6ARepQR6qrconc01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ARepQDFqcoupled_rec_drop_primC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ARepQD4AQdrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ARepQR;aquar_mutexC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib5BothW5ARepQ8abatchesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ARepQR7qr_pendC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8AsanCtrl6achunk01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW8AFreeRep4banyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6x_busyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ARepQD7qr_dropC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7AQConst9AQ_GCACHEC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6abatch00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW5ARepQ7qbatchc00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6achunk00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW4ARep6bstate02C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep5xbusy00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW6ARepQR6qrconc00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW5ABase7alayout00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6astate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep5aconc00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW7ALayout:alayout_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6aslotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5ndistC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7busy_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep:aslot_busyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep:aslot_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=size_of_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7junk_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7aregionC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7get_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl@c_allocated_userC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=c_mapped_userC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep<aslot_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7rz_sizeC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvK59OSSVerify5KrLib3Lib5Cells4cell03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed4shadC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed5shlenC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC59OSSVerify5KrLib5BothW4ARep8granulesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARepAslot_shadow_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7fill_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW8AFreeRep9any_rangeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC47Corelib4Init5Logic3notC59OSSVerify5KrLib5BothW8AFreeRep9any_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<rounded_sizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landK47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib5BothW8AFreeRep@busy_of_X_self_gC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic5proj1C59OSSVerify5KrLib5BothW8AFreeGeo@chunk_shadow_geoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW8AFreeGeo=rz_size_factsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib5BothW9ARepFrame<shlen_nonnegC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith6BinInt1Z8max_specC47Corelib5Lists7ListDef6repeatK59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AFreeRead=cb_split3_genC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Z2Nat2idK59OSSVerify5KrLib3Lib5Cells4cell04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8xb_allocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl3rupC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses6mkapp2I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4BImg5bsegsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7AREQMAXC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC59OSSVerify5KrLib5BothW4ARep6AMAGICC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_NUM_CLASSESC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep6bstate00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW4ARep6bstate03C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01C47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9MorphismsBsubrelation_properC47Corelib7Classes9Morphisms5flip2C46Stdlib5Lists4List2InC46Stdlib5Lists4List:in_app_iffC59OSSVerify5KrLib5BothW6ARepQR:qr_entriesC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List5NoDup00C59OSSVerify5KrLib5BothW6ARepQR9qr_bslotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5xb_stC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8xb_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7xb_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ9qentry_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ8qentriesC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List=Forall_forallC47Corelib4Init5Logic3iffC47Corelib7Program6Basics4implC47Corelib7Classes9Morphisms@subrelation_reflC47Corelib7Classes9MorphismsFsubrelation_respectfulC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C46Stdlib5Lists4List8in_splitC59OSSVerify5KrLib5BothW5ARepQ9qprim_idsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW4ARep5xbusy01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_BATCH_CLASSC1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsIiff_flip_impl_subrelationC47Corelib7Classes>Morphisms_Prop?or_iff_morphismC47Corelib7Classes?RelationClasses=iff_ReflexiveC59OSSVerify5KrLib4Spec8AsanCtrl;a_space_begC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase<al_space_begC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;a_ptr_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase<al_ptr_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5x_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;c_num_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrlCc_mapped_free_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7xc_freeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8xc_cacheC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7c_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep4xb_nC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5xb_b1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6xb_ctxC1?~~~~~~~~~~~~~~~C35stdpp4gmap;gmap_lookupC59OSSVerify5KrLib4Spec8AsanCtrl6a_liveC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW4ARep6bstate01C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC46Stdlib5Lists4ListBNoDup_app_remove_rC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC59OSSVerify5KrLib5BothW9ARepFrameCsize_of_class_factsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_posC59OSSVerify5KrLib5BothW8ARefillPBNoDup_bound_lengthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;F_apopulateAsize_of_class_posC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ARecRep@max_cached_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl:max_cachedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02K46Stdlib9micromega=RingMicromega5Psatz03K46Stdlib9micromega5Tauto8GFormula07C59OSSVerify5KrLib5BothW4ARep:busy_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl9max_countC1?~~~~~~~~~~~~~~~C35stdpp4base6lookupC59OSSVerify5KrLib4Spec8AsanCtrl6a_nextC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2ltC59OSSVerify5KrLib4Spec8AsanCtrl7K_ALIGNC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_OFFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl:K_USER_MAPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_MAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_MAPC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6aclass00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7aclass0C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C59OSSVerify5KrLib4Spec8AsanCtrl<K_SPACE_SIZEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_SPACE_EXTRAC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep6xclass00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableC46Stdlib5Lists4List<firstn_skipnC45stdpp9bitvector;definitions;bv_unsignedC47Corelib5Lists7ListDef6firstnC47Corelib5Lists7ListDef5skipnC46Stdlib5Lists4List:in_map_iffK46Stdlib9micromega=RingMicromega5Psatz01K46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib5BothW4ARep8acompactC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_nil_rC46Stdlib5Lists4List8firstn_0C46Stdlib5Lists4List:length_mapC46Stdlib5Lists4List:firstn_appC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxI46Stdlib5Lists4List6Exists00C47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes?RelationClasses=eq_TransitiveC47Corelib7Classes9MorphismsFtrans_co_impl_morphismC46Stdlib5Lists4List=length_firstnC46Stdlib5Lists4List:repeat_appC59OSSVerify5KrLib5BothW6AHeapP4arngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep;acache_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9F_arecyc1:recyc1_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7arep_rtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep9ainstanceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7athreadC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ARecyc1P3AHrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep=ashadow_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_nsecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_nresC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7ah_quarC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6ah_secC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8ah_depotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6arelroC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8arep_rt2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8arep_rt3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4al_tC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase6al_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase6al_topC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase6al_botC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep<acache_cellsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ARecyc1P5rec_WC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep=aregion_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep:afreearrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep<aregion_infoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8afreearrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout=alayout_spaceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout9alayout_tC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout;alayout_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7a_cinitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW8ARefillP@alayout_res_disjC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;F_acdealloc<cdealloc_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA5fp_leC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8AsanCtrl6aclass01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;F_acdealloc4cd_WC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC59OSSVerify5KrLib4Spec8AsanCtrl:init_cacheC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9F_aensure8m3_cellsC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9F_arefill8arec_hdrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW8ARefillPAinit_cache_fieldsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrameBget_cls_put_cls_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9F_arefill>init_cache_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7put_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrameBget_cls_put_cls_neC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW8ARefillP>put_cls_fieldsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW8AFreeGeo8slot_geoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW8AFreeGeoBrounded_size_factsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z9div_exactC47Corelib4Init5Logic5proj2C57Corelib7BinNums6PosDef3Pos3mulC46Stdlib6ZArith4Zdiv:Z_mod_multC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z4of_NC47Corelib4Init5Logic8iff_reflC59OSSVerify5KrLib5BothW9F_arefill4ic_WC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW8ARefillP;outside_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame6sub_fpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame<munch_weakenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;munch_transC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;wmono_transC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9F_arefillAic_W_disjoint_genC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ARecyc1P;read_qchunkC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_mulC59OSSVerify5KrLib5BothW7ARecRep6rfree'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ARecRep7rcache'C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW4ARep6xclass01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ARecRep4rcutC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_assocC46Stdlib5Lists4List7map_appC47Corelib4Init3Nat3minC56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z8min_specC46Stdlib5Lists4List<length_skipnC46Stdlib5Lists4List:length_appC56Stdlib5Arith8PeanoNat3Nat8sub_diagC59OSSVerify5KrLib5BothW7ARecRep=xrec_cls_selfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ABytes<rw_cells_appC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ARecyc1P5RK_riC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW8ARefillP6dj_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame;cells_frameC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat3N2Z7inj_iffC56Stdlib6ZArith4Znat3N2Z9is_nonnegC59OSSVerify5KrLib5BothW9ARepFrame:junk_frameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ARecyc1P6RK_gapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame<u32arr_frameC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9skipn_appC46Stdlib5Lists4List9skipn_mapC46Stdlib5Lists4List7skipn_0C46Stdlib5Lists4List;firstn_all2C59OSSVerify5KrLib5BothW:F_agetfrom:u32arr_appC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ARecyc1P5RK_shC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame9shlen_divC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ARepKit<fill_is_junkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ARepKit:junk_mergeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame7xb_fitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame>slot_in_regionC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame>slots_disjointC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ARecyc1P:RK_space_cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrameBbusy_of_Some_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame8awf_fitsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC59OSSVerify5KrLib5BothW7ARecRepBbusy_of_xrec_otherC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ARepKit=junk_of_cellsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;lt_ge_casesC59OSSVerify5KrLib5BothW7ARecRepAbusy_of_xrec_selfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame=aslots_updateC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame<slot_alignedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame8shad_divC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5azeroC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat7add_0_rC59OSSVerify5KrLib5BothW9ARepFrame6cb_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrameCaslot_shadow_updateC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame;azero_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW8ARefillP@region_other_geoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ARecyc1P<RK_reg_otherC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrameCaregion_cells_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ARecRep>xrec_cls_otherC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame@afreearray_frameC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic:not_eq_symC59OSSVerify5KrLib5BothW9ARepFrame9shad_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrameCashadow_avail_frameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ARecyc1P6RK_recC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9F_arefillDic_W_disjoint_chunksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ARecRep8xrec_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ARecRep7In_xrecC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6filterC46Stdlib5Lists4List9filter_InC56Stdlib6ZArith6BinInt1Z8eqb_reflC56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00C59OSSVerify5KrLib5BothW8AFreeRep;key_fresh_gC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ARecyc1P6RK_imgC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ARecyc1P7RK_tlowC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ARecyc1P8RK_tstatC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ARecyc1P8RK_thighC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ARecyc1P6RK_objC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ARecRep4rnf'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ARecRep5rcnt'C1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC59OSSVerify5KrLib5BothW7ARecRep8awf_xrecC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C59OSSVerify5KrLib5BothW9ARepFrame8rt_hullsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame=arep_rt_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame?ainstance_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ARepKit:junk_splitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout8ao_spaceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout6al_resC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9F_arefill<ic_W_outsideC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ARecyc1P>AQdr_drop_primC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP>quar_untouchedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP9quar_sameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ARepQD:AQdr_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7al_fakeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase8al_nodesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase8al_storeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout7al_dtlsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP=sec_untouchedC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8AsanCtrl6achunk02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP=sec_chunks_ofC1?~~~~~~~~~~~~~~~I46Stdlib7Sorting;Permutation;Permutation00C46Stdlib7Sorting;Permutation@Permutation_reflC59OSSVerify5KrLib5BothW6AHeapP@sec_chunks_of_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP8sec_sameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP8hs_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout8ao_nodesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout4aobjC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout8ao_storeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout<ad_nodes_resC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout5adisjC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout<ad_store_resC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout:ad_t_nodesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout:ad_t_storeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP8hd_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame<arelro_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame>arep_rt2_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame>arep_rt3_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep4AREPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP9arng_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF3rngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP4RSECC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AProto5fp_bwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AProto9rng_mergeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ARecRep9xrec_liveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr6u32arrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr6u64arrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C46Stdlib;setoid_ring6Ncring>ring_mult_compC46Stdlib9micromega;ZifyClasses3injC59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep<ASTATS_WORDSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7AIMG_HIC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02C56Stdlib6ZArith6BinInt1Z3oppC46Stdlib;setoid_ring>Ncring_initial4ZopsC46Stdlib;setoid_ring>Ncring_initial2ZrC59OSSVerify5KrLib4Spec9AsanEmbed6ASHOFFC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZC56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith4Znat5Nat2Z7inj_minC59OSSVerify5KrLib4LibA5ExecF9footprintC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3ivlC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C59OSSVerify5KrLib5BothW5ABase9AINSTANCEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase3KLSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase9ARELRO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase9ARELRO_HIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame9rt3_hullsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ARecyc1P?store_rec1_stmtC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses<transitivityC59OSSVerify5KrLib4Spec8AsanCtrl2AMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed6aembedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9F_arecyc1;recyc1_specC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=cache_deallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA5implFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA6epostFC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC59OSSVerify5KrLib5BothW5ARepQ4qhdrC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ARecyc1P;arecyc1_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6NodesA8at_nodeAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ARecyc1P>pend_head_busyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ARepKit:c8_of_junkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ARecyc1P=cache_vals_ltC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ARecyc1P8nf_boundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW8AFreeGeo8slot_rngC1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClassesCPreOrder_TransitiveC56Stdlib6ZArith6BinInt1ZDmul_le_mono_nonneg_rC56Stdlib6ZArith6BinInt1Z:mul_div_leC56Stdlib6ZArith6BinInt1Z8mul_commC59OSSVerify5KrLib5BothW9ARepFrame?rounded_size_geC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF8rng_sub'C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW8ARecyc1P:rec1_storeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState6ret_pcC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AProto6fstepSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase5ATP88C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4ATSDC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C59OSSVerify5KrLib5BothW5ABase3ATPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9F_arecyc1<recyc1_entryC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;le_preorder".
(* [comment removed for export] *)
(* [comment removed for export] *)
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI :=
  ([(sp - 688, sp); (AB, AB + 8); (HB, HB + 4); (SHUB, SHUB + gr); (t + 2784, t + 2792); (t + 2800, t + 3168);
    (CA, CA + 4); (CA + 16, CA + 80); (FA + 4 * nf, FA + mfa'); (SHF0, SHF1); (RI, RI + 8); (RI + 16, RI + 32); (RI + 72, RI + 128)]%Z) (only parsing).

(* [comment removed for export] *)
Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_ARecyc1P ()) [] "h04__x1h14__x2h21Hh37__arithh44__ffh58__varmaph65__with71kh82G1h92G2h:1ah;1np;2p;1p;4p;3p;7p;8p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Dp4p710p9P0p1003<p4p710R0p8p1003Sp4p710R1p10040p4p710R2p8P1p1004Lp4p710R3p8p1004jp4p710R4p1005HR5p4p710R6p8P4P5p4p7210R5p8p1005ap4p70R7P0p8P7P2p8P7P1p8P7P3p8P7p1006Xp4p710p8P7p10075R1p4p710p8P7p1007Rp4p710p8p1007np4p710R7P4p8P7P6p8P7P5p8P7p1008Bp4p73110p8p1008Tp4p710P2p8P1p4p7210P3p8p1009Qp4p710R1P2p8P1P3p8p100:0p4p7210P2p8p100:Op4p710P3p8g00;1j2WTg00;fj20Tg00<Bj22Tg00<_j11Tg00=Dj1;Tg00=bj16Tg00>Gj23Tg00>bj29Tg00??j2VTg00?Yj1UTg00@9j1TTg00@Yj2PTg00A7j1OTg00AUj4NTg00B3j1LTg00BQj1KTg00C<j2:Tg00C_j2ATg00DBj1ITg00Ddj3>Tg00EGj3=Tg00Ejj2HTg00FLj2JTg00Ffj2GTg00GRj3FTg00Glj3MTg00HKj4ETg00I=j4CTg00IWj4QTg00JBj7DTg00Jfj7RTg00KJj8STf0R3#1#1#1#1p=?%13#1#1#1#1#1#1#1p=5%13#1p=B%63#6p=@%63#6#6#6p=7f2R2g00KnR1g00LMR7P7g00LmR5g00MMR6f1R4g00MkP3CQg00NRFDp=4P2P1P7P7P5P4P3FRp=8f3R0P1P7P7P5P2P4P3GSp=<1W43g00O2R1/021202g00OPR8#1R9#?#5R:#1#B#5#5#5#5#5#5#;R;'0g00P5f4R</20%@8#7#7#7#1#6#@#?#5#;R='0%7:#7#7#7#1#B#?#5#;R:/0<1013R>%;8R?,03'3R@f6RAf5RB'2193;,2=RC'019:3RD/0A'3'3X76,V6P212B</0=P6f7RE/2A/0C10DE'3,3@X76R@P1g00PORD#URC%TDRDP61P62P4%O6CNRF%L6RG%K6RH1:61RI1A68R854H%I7R7PH1A699>68R91:6=RJ54HP7A4HII1:6?RK94HIRL58H1:6;RM9=6I9>6J94H91:6:RN==6I=4H858H58HC<C<1HH5R5P3P2g00Q;RIg00Q[RO'J1G32=FIOdAM614CEROb4b5b6X06X161242/0=1011101?RI'31220RP191;,2='019:1/02'3'3[\>^06^16P3PAPEP<P4O4b3CCW2P3O110:BP6P@P?PCPDPFPGPHA4H9MP7PHA4HN8P7A4HKK98HLA=6KM9>6J94H9A=6NK=4H858H58HC<C<P5POb4b5b6X06X161234/0;10:410??,3I19?;,2=,0P19:?/02'3'3[[^06^16P3PAPEP0P4O4b3CCW2P3O1n200100001021100011000W9W8W2X;6X:6o"). Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6352896 * k <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_ARecyc1P ()) [] "h04__x1h14__x2h22H0h31kh41Hh57__arithh64__ffh78__varmaph85__with92G2h:1ah;1np;2p;1p;4p;3p;7p;8p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Dp4p710p9P0p1003<p4p710R0p8p1003Sp4p710R1p10040p4p710R2p8P1p1004Lp4p710R3p8p1004jp4p710R4p1005HR5p4p710R6p8P4P5p4p7210R5p8p1005ap4p70R7P0p8P7P2p8P7P1p8P7P3p8P7p1006Xp4p710p8P7p10075R1p4p710p8P7p1007Rp4p710p8p1007np4p710R7P4p8P7P6p8P7P5p8P7p1008Bp4p73110p8p1008Tp4p710P2p8P1p4p7210P3p8p1009Qp4p710R1P2p8P1P3p8p100:0p4p7210P2p8p100:Op4p710P3p8g00R;j2YTg00<_j11Tg00=Dj1<Tg00;fj20Tg00=bj1:Tg00P5R3j2DTg00<Bj23Tg00>bj27Tg00??j2ETg00?Yj1VTg00@9j1UTg00@Yj2TTg00A7j1RTg00AUj4QTg00B3j1PTg00BQj1NTg00C_j2BTg00Ddj3@Tg00C<j28Tg00DBj1KTg00EGj3>Tg00Ejj2JTg00FLj2ITg00Ffj2HTg00GRj3MTg00Glj3GTg00HKj4OTg00I=j4CTg00>GR2j2?Tg00IWj4FTg00JBj7STg00Jfj7XTg00KJj8WTf0R1#1#1p=L%11#1#1#1#1#1#1#1p=5%11#1#1#1p=Af2R7f1R5'3/01p=;1075/?1p=61?51,?7p==P7g00KnR6g00LMR4P4g00LmR0g00MMR8P5g00MkP1CFg00NRFSp=2P7P6P4P4P0P5P1FXp=4f3R9P6P4P4P0P7P5P1GWp=91Y51g00OPR6#1R:#1#L#5R;#AR<#5#5#5#5#5#5#<R=9;75P2%<;R;/09R2%<<R<9;97%:6#1#A#:#:#:#:#A#5#<R>/09'Dg00O2R?%<6R@,01761RAf5RB,0;RCf4RD,3B171=,3<RE17>1RF/0B363=X38,E8P5f6RG?;B<10>G'DP3f7R3?;G<10>3f9RG,0;f8RB,3G10FG76E5=AX38,E8P1A;B3<P8f:RH,0;13HG10FH76E5=AX38RAP?g00PORE#VRF%UEREP81T87P5%R8CQRI%P8RJ%N8RK1B86R61B8:5@8R:188<RL52K%K4R4PK188;=2K6RMP4188?RN=2KN188@RO92KNRP54K188=RQ9>8N9@8L92K:188>RR=>8N=2K654K94KM54KC9C91JK0R0P1P7g00Q;RNg00Q[RS'I1H17=MNSdAG8?5CORSb6b7b8X08X181315RN/0<10;510?@RT96??10;7R;137917?=,3<17>?/07363=[[^08^18P1PGPHP5PDO4b5CCW2P1O110>BP8PAP@PFPEPIPJPKA2K:QP4PKA2KR6P4PKPMP4A2KOO94KPA>8OQ9@8L92K:A>8RO=2K654K94KM54KC9C9C9P0PSb6b7b8X08X1810N=10>510@@,?T139D17@=,3<17>@/09367=2\;[[^08^18P1PGPHP3P5PDO5b5CCW2P1O1n200100000021100011000W2X4CP5P1O2n2001000000121000000W9W4X;8X:8o"). Qed.
Local Lemma ablk_int {rc : runConstT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6352896 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof.
ltac2:(KReplay.run1 (kr_t_ARecyc1P ()) [] "h01Hh14__p1h24__x1h34__x2h44__x3h51kh62rch72H1h87__arithh94__ffh:8__varmaph;5__with<2H0h=2hih>2lop;3p;1p;2p;4p;6p;7p;8p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Dp4p710p9P0p1003<p4p710R0p8p1003Sp4p710R1p10040p4p710R2p8P1p1004Lp4p710R3p8p1004jp4p710R4p1005HR5p4p710R6p8P4P5p4p7210R5p8p1005ap4p70R7P0p8P7P2p8P7P1p8P7P3p8P7p1006Xp4p710p8P7p10075R1p4p710p8P7p1007Rp4p710p8p1007np4p710R7P4p8P7P6p8P7P5p8P7p1008Bp4p73110p8p1008Tp4p710P2p8P1p4p7210P3p8p1009Qp4p710R1P2p8P1P3p8p100:0p4p7210P2p8p100:Op4p710P3p8g00S0j3bTg00Sej1aTg00=bj15Tg00<_j11Tg00=Dj19Tg00Tcj18Tg00;fj20Tg00>GR3j2>Tg00>bj2=Tg00<Bj2ETg00??j2JTg00UYj1DTg00V8j2CTg00Vaj3ITg00WJj2VTg00?Yj1UTg00X6j3TTg00@9j1STg00@Yj2GTg00AUj4RTg00B3j1QTg00BQj1PTg00C_j2BTg00XVj6OTg00DBj1NTg00C<j2FTg00EGj3ATg00Ddj3HTg00Ejj2MTg00FLj2`Tg00Ffj2_Tg00GRj3^Tg00Glj3[Tg00HKj4ZTg00I=j4KTg00IWj4YTg00JBj7\Tg00Jfj7WTg00KJj8]Tf0R2#5#5#5#5p=7%52#5p=X%12#1p=@%12#1#1#1p=:%12#1#1#1#1#1#1#1p=3f2R1f1R7'0/>2p=21>72,>1p=?g00MMR5/F2p=;P1g00KnR6g00LMR4P4g00LmR0P5P7g00MkP2CYg00NRF\p=4P1P6P4P4P0P7P2FWp=6f3R8P6P4P4P0P1P7P2G]p=<1072,>1p=Lg00Y:R9Ab172%a8g00OPR:#5R;#5#7#7#7R<#1#5#XR=#5#7#1#@#:#3#3#9R>%88R?%5<#7#7#1#@#:#3#3#9R<,0?32g00P5%5:#1#:#7#:#3#9R?/08R@%:=#3#9R=,01RA'>%1:RB#:#3RC#7#7#7#7#1#@#:#3#9RDf4RE#8,01728g00O2RF%9:RG,02722RHf5RI,0?RJ1=D2RK%1C#@#3#3#3#3#3#3#9RC,=2,E=RLf6RM#8,0ERN52E72I3?X55,J5P7108=92?EP3PJ10E=f7RJ,0?ROf8#8,0M92ML92KJ5?HX55,J5RMP210J=P5f:RP,0?f9RQf;#8RR,0Q72L92KP5?HX55RHPFp-0RKg00PORLg00Z7RS#D#DRT#D,C51C5T1C5S5I55I5g00ZV'V%UL3TRS%SLRLP51G51P71G58CRRT%Q5RU%P5RV%;>1B5;R;54VPVP6P4P4P0PIEOR656V%N4R4PV1B5BRB%;=RW54VP4PV%;?1B5:R:54VRXP41F5FRY=4VY%;GRZ94VYR[56V%;DR\=A5Y=4V:%;CR]9A5Y9H5W94VBA4VB;RY56V56V96VX56VC<C<C<1MV0R0P2P1g00Q;R^g00Q[R_'`1_21=^^_dA[5F7CZR_b9b:b;X25X35X45W1A2>1810?110FGR?92FF1=DF1=FC,E=10EIRF52E7287?@[\A[^25^35^45^1KP210R<PRPQPPPJP7P1O7b8CKW7X0OP7P2O2n2001000010121000000W0P2O1%8I,0892DEP310DIPNPMP210DJ%8Q,0JP5PHPGPSPLPTPUPV%;<94V;96V6P4PVPYP4PVA4V\:P4A4VZZ96V[AA5\Z=4V:AA5Z]9H5W94VB=6VY56V96VX56VC<C<C<P0P_b9b:b;X25X35X45X1KAL81<101810D1AL?GG1=DG1=GC,E==2EF7287?@[[[^25^35^45^1KP210>RPRPQPPPJP7P1O7b8CKW7W0P7P2O2n2001000010121000000W0P2O1n200100001021100011000b<W0X=5X>5X69P2O1X69P2O1W6o"). Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (sclr_int a n H G1 G2) as (k & A & B & C); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>      (* [comment removed for export] *)
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.

Section CANSEC1. Context {rc : runConstT}.
Section Kinds.
Variables (sp lo t ctx SB c RB FA RI CA mu au nf mfa mfa' AB S rz gr SHLO SHUB SHHI SHF0 SHF1 : Z).
Let HB := AB + rz - 16.
Definition reckf : Prop :=
     (ATOP <= lo /\ lo <= sp - 688 /\ sp <= 2^64)
  /\ (sclr t 4096 /\ iclr t 4096 /\ t + 4096 <= ATOP /\ sclr ctx 65536 /\ 6352896 <= ctx /\ ctx + 65536 <= ATOP /\ (ctx + 4096 <= t \/ t + 4096 <= ctx))
  /\ (1 <= c <= 31 /\ CA = t + 208 + c * 80)
  /\ (17594333495296 <= SB /\ SB + 137438957568 <= ATOP /\ RB = SB + c * 4294967296 /\ FA = RB + 3758096384 /\ RI = SB + 137438953472 + c * 128)
  /\ (t + 4096 <= SB \/ SB + 137438957568 <= t) /\ (ctx + 65536 <= SB \/ SB + 137438957568 <= ctx)
  /\ (0 <= au /\ au <= mu /\ mu <= 3758096384 /\ 0 <= nf /\ 4 * nf <= mfa /\ mfa <= mfa' /\ mfa' <= 536870912)
  /\ (RB <= AB /\ AB + S <= RB + au /\ 16 <= rz /\ rz <= S)
  /\ (2201439137792 <= SHLO /\ SHLO <= SHUB /\ 0 <= gr /\ SHUB + gr <= SHHI /\ SHHI <= SHF0 /\ SHF0 <= SHF1 /\ SHF1 <= 17594333495296).
Hypothesis KF : reckf.

Ltac kind := pose proof KF as KF'; unfold reckf, AIMG_HI in *; subst HB;
  destruct KF' as (F_lo & (Ft1 & Ft2 & Ft3 & Fc1 & Fc2 & Fc3 & Ftc) & F_c & F_sb & F_tsb & F_csb & F_mu & F_ab & F_sh);
  band_int Ft2; band_int Ft1; band_int Fc1; clear Ft1 Ft2 Fc1;   (* [comment removed for export] *)
  cbn [disjoint_from]; repeat (split; [lia|]); first [lia | exact I].

Lemma RK_img : forall A k, 65536 <= A -> 0 <= k -> A + k <= 6352896 -> disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof.
ltac2:(KReplay.run1 (kr_t_ARecyc1P ()) ["CANSEC1"; "Kinds"] "p'0h02H2h14__x1h24__p1h34__x2h44__x3h54__x4h64__p2h74__x5h84__p3h97__arithh:6__sat4h;6__sat5h<4__ffh=8__varmaph>5__with?4__x6h@4__p4hA4__p5hB4__p6hC4__x7hD4__x8hE4__p7hF5__p10hG5__p11hH5__p12hI5__p13hJ5__p14hK5__p15hL5__p16hM4__p8hN4__p9hO5__p17hP4__x9hQ1khR2G0hS1ehT1GhU2HahV5__p18hW5__p19hX1AhY4F_abhZ3F_ch[5F_csbh\4F_loh]4F_muh^4F_sbh_4F_shh`5F_tsbha3Fc1hb3Fc2hc3Fc3hd3Ft1he3Ft2hf3Ft3hg3Ftchh5KAFc1hi5KAFt1hj5KAFt2hk5KBFc1hl5KBFt1hm5KBFt2hn5KCFc1ho5KCFt1hp5KCFt2hq5KDFt2hr3KF'hs4kFc1ht4kFt1hu4kFt2i001xp%0p%1p%2p&0p;1p;2p;3p;4p;5p;6p;7p;8p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Dp4p710p9P0p1003<p4p710R0p8p1003Sp4p710R1p10040p4p710R2p8P1p1004Lp4p710R3p8p1004jp4p710R4p1005HR5p4p710R6p8P4P5p4p7210R5p8p1005ap4p70R7P0p8P7P2p8P7P1p8P7P3p8P7p1006Xp4p710p8P7p10075R1p4p710p8P7p1007Rp4p710p8p1007np4p710R7P4p8P7P6p8P7P5p8P7p1008Bp4p73110p8p1008Tp4p710P2p8P1p4p7210P3p8p1009Qp4p710R1P2p8P1P3p8p100:0p4p7210P2p8p100:Op4p710P3p8g00<_j12Tg00=Dj1CTg00;fj20Tg00=bj1:Tg00Tck10DTg00[Bj2pTg00[_k20XTg00;1k20@Tg00R;k20STg00<Bj21Tg00>GR3j23Tg00>bj25Tg00\<k20GTg00?Yk108Tg00\\j38Tg00Sek10CTg00]Xk20BTg00^@k204Tg00^\k30[Tg00UYj1FTg00V8k20ATg00@9k10WTg00A7k10VTg00B3k10UTg00BQk10TTg00DBk10RTg00C_k20?Tg00Ejk20QTg00FLk20PTg00Ffk20OTg00GRk30>Tg00Glk30LTg00HKk40KTg00_@k40JTg00??S00j2~Tg00C<j2|Tg00`<k50<Tg00a8k30;Tg00a[k10ITg00b9k20HTg00bZj3yTg00cCj2lTg00P5j2sTg00clj2rTg00dXk50ETg00e<j4xTg00eWj4uTg00X6j3NTg00Vaj3vTg00WJk205Tg00@Yk20MTg00AUj4mTg00XVk60NTg00IWj4fTg00JBj7aTg00Ddk302Tg00Jfj7[Tg00KJj8oTg00f7j7wTg00f[k30ZTg00EGk30YTf0R2#2#2p>03%22#2#2p>01g00O2R1/02p=G%:2#2p=`%22#2#2#2p=Q%:2#:p=Y%22#2#2#2#2#2#2#Cp=Of2R7f1R5'1/02p=E%22#2#2#Cp=^1075/32p=Af3R6/071052'sp=;g00MMR4115280>7p=T1375/32p=d%:2#:#:#:p=I%22#2#2#2#2#2#2#2p=K10671052'3p=Sf4R01352,37,36'3p=J1075/32,36p=WP4P4P5P2Cup>09f6R8P4P4f5R9P0CuP4P4P7P5Cu=N623Np=hP4P4P7P5Cu=N62p>0:AN7529N06p>0620A42p=MAv452p=LAv452g00ZVR:+05p=]g00POR;?N52p=\20M42p=PP4P7P5P2Cmp=@P4P4P0P6P7CmP5P2Cmp=BP5g00KnR<g00LMR=P=g00LmR>P2J0Np=620?42p=?1|42p=>P7P<P=P=P>P4P5g00MkR?P2Cfg00NRR@Fap=4B02452p=9P7P<P=P=P>P5P2F[p=nP8P<P=P=P>P9P0P6P<P=P=P>P7P5P2GoGop=<P9P<P=P=P>P0P<P=P=P>P6P7F[P5P2Gop==1352,37p=D1052,37p>001152,07p=k1552,17p=}P6P<P=P=P>P7P5P2Gop>0=P0P<P=P=P>P6P7P<P=P=P>P5P2F[F[p=7P0P<P=P=P>P6P<P=P=P>P7P5F[P2F[p={Av4529v47p=_2052:p=zP0P<P=P=P>P6P<P=P=P>P4P7P?P5CfP@FaP2F[p=XP9P<P=P=P>P0P6P7P<P=P=P>P5P2FwGop=U1075/s2p=HB0Z452p=bAN;529N;79N;69N;0p=cP4P0P6P4P7P5P2CmCmp=tB0Y452p=ZP4P5g00gDP2Cfp=gP5P<P=P=P>P2P@Fap=jP0P<P=P=P>P6P<P=P=P>P4P7P?P5CfP@FaP2Fwp=RP4B02475P?P2Cfp=iP9P<P=P=P>P0P<P=P=P>P6P@FaP7P<P=P=P>P4P5P?P2CfP@FaFwp=qP7P<P=P=P>P5P2Fwp>0F1|42:0245p=VP6P<P=P=P>P7P<P=P=P>P5P@FaP2F[p>07P8P9P0P6P7P5P2CxCxp=eg00OPR@#2R?#2R:#2RA#2RB#2RC#2RD#2RE$03RF$01RG#2RH$01RI#CRJ/05%G5RK%`@#Q#:#Y#`#Q#ORL9E67p,2KFS01g00gkP3p,2rcRM$0DRNp,2loS02Q02p,2spRO%:?RP#2RQ#YRR#2#^RS'pS03%C?RT%CDRD+0XRU,0OS043A3AS05p,1tRV%CGRG+0@S0620SVGS0711VGRW/0NS08p,3ctxRX00@JS0910LXS0:11XJRY/0NS0;11XGPVPWPXC;S0<'3S0='3S0>'3S0?'3S0@'3S0A'3S0B%C@RZp,1cR['0%:@R\#:R]#YR^#CS0C,0[S0Dp,2CAR_%2\R`#:S0E#2S0F#^S0G,1V%^QRa,5[3TS0H3dS0I%IH#I#I#I#K#ORHp,2SBRb'0S0J%KIRI#`#Q#ORc,1bRd/0NS0Kp,2RBRe%2I#QRI$01Rf#CRg,5[7TbS0Lp,2FAS0M%2]S0N#2S0O#Q#K#K#OS0P7TeS0Qp,2RIRh%2f#QRf#CS0R,1b%CERE,5[3TS0S'3S0T'3S0U'3S0V'3S0WPWPbPdPVC;S0XPYPbPdPXC;S0Yp,2auRd#GS0Zp,2muRi,0dS0[Q0P,0iS0\p,2nfS0]#G%C:RiQ0]'5Rjp,3mfaRkPkp,4mfa'RkPk%CICS3AS0^DJS0_p,2ABRIp,1SRl11ed5EIS0`%CBRBp,2rzS0aQ0a/0lS0bCWS0c5AeS0d%`F$03#:#Y#I#I#`#Y#`#Q#OS0ep,4SHLOS0fQ0fp,4SHUBS0gp,2grS0h#GQ0gQ0h'1S0ip,4SHHIS0jQ0jp,4SHF0S0kQ0kp,4SHF1S0lQ0lPHCSS0m3ACWS0n3A3AS0o'3S0p'3S0q'3S0r'3S0s'3S0t'3RF'3S0u20G44RlQ03009OS0vPl%CARd,1IS0w-09IS0xPlQ0a,1I/pBS0yQ0y/1iS0zPlQ0gQ0iPl%:RRR#2Rm#2#^S0{,1VS0|%:m#^S0},1VS0~Pl%`R#^S10,1VS11%2`S12#2S13#Y$03#^S14,1VS15PlP_11_iS16Pl11_BS1711_aS18PlQ0M/1jS19Q0M/1kS1:PlQ0kQ0lPlPh11hdS1;Pl11hBS1<%CC,1hS1=Pl%::S1>#^S1?,1hS1@11hES1A&08lFhFhFhFhFhS1BH0:I06RC?889P2Q05Q0uP3Q0BPFf:Rdf9Rk58CP2Q0BP3Q06Q0Af>S1Cf=Rj58C\FP2Q06Q0AP3Q07Q0@fBS1DfAS1E58C\FP2Q07Q0@P3Q08Q0?fFS1FfES1G58C\FP2Q08Q0?P3Q09Q0>fJS1HfIS1I58C\FP2Q09Q0>P3Q0:Q0=fNS1JfMS1K58C\FP2Q0:Q0=P3Q0;Q0<fRS1LfQ58C\FP2Q0;Q0<P3Q0IQ0tfVfU58CP2Q0IQ0tP3Q0WQ0sfZS1MfY58CP2Q0WQ0sP3Q0XQ0rf^f]58CP2Q0XQ0rP3Q0YQ0qfbfaS1N58CP2Q0YQ0qP3Q0_Q0pfffeS1O58CP2Q0_Q0pP3Q0dQ0ofjfiS1P58CP2Q0dQ0o&0CMRM%Y^#I#IR^#2#:#YS1Q#:#I#K#K#OR`/0NRR%:^#I#I#K#K#OR^,0NS1R'3Rm20BTDRn2041T%GD2041U[[Ro%GTRpg00hdS1SB0[TD5UWURDQ1S%GU[^UpRpp-0RUg00Z7RT#FRq#FS1T#FS1U#FS1V#MS1W%Mq20A4TRT'LS1X']&08;Rq'\&0W;R;%P0Rr&0V4Rs7@0P7PsP5%P6S1Y?@0sDB&0U4Rt&0T4RuPu16u8S1Z%??R?%>^54uS1[&0R=RvPuPuf7Rw,6uS1\%?ARA%>cS1]'9=4u?S1^f8Rx,6uS1_5nuPvPu%?PS1`%>JRy'9=4u?PvPu20?4@Rz%>GR{'9R|=4u?Pv%Qf#K#K#ORf#>S1a94u|F<E=E=20Qu>R|P2P7g00Q;R}g00Q[R~+0P20O27>0>}~dB0L415H0KR~b<b=b>X14X34X44X54X2UX6UW8S1b105^S1c,30AE0c7=D8wAE0J6116GS1d/00110GS1e/0f[[[[^14^34^44^54^2U^6U^8US1fP2Q0UQ0JPRPbPXPNPVP6Q1GQ1JQ1MO;b9b:b;10WfR^eb0P^PVPGf[P2H0J%G2@002ZS1M10GVS1gPW152fS1h,1J15L2PVCS3DS1iXQ4R},~4Q00P4P}fpS1jfo58CP2Q1iP3B00K5ZS1kQ1g155fS1l9kWJ15L5/0V3Dftfs58CP2%G6S1m@006ZS1nQ1g150fS1o9kWJ15L0/0V3DP3Q1gPW159fS1p,1J15L9S1qPVCSfxfw58CP2Q1gPWA}JxfS1r15LxPVCSP315kf9kWJ15Lk/0Vf|f{58CP2f;R}/5f9kWJf<S1s,5L/0VPMPmPnPoPDPpPqP;%P5S1tPtPuA4u{zPv1|41S1u=4uzS1vH0=P|P~b<b=b>X1410G2PK[^14P2PVPkO2b9b:b;%GVR1eb0P1PMPmPnPoPDPpQ1bQ1fP2Q0UQ0JPRPbPXPNPVP6fXQ1NfmO;b9b:b;P^eb0P^PVPGfrP5P2I0<Q1MPWQ1Q#2#Q#OR^Q1h'1S1h15H2S1Q/0VCWS1NXQ4R1,~4Q00P4P1p+01Dp+01CS1f58CP2Q1NP3Q1kPWQ1l,1^S1l15H5S1bPVCSp+01Hp+01G58CP2Q1nPWQ1o,1^S1o15H0S1wPVCSP3Q1p,1^S1p,0W15H9S1x/0Vp+01Lp+01K58CP2A}^wfR^,0W15HxRW/0VPMPmPnPoPDPpPqP;Q1tPtPuPu16u6PuPu16u0Pu16u9S1tPuQ1ZPuQ1\Pu%>LR1=4uzQ1_D7D716ukS1yD{PvQ1vE=P|P~b<b=b>X14X2UX6UX8UX@UXAUXBUXEUP7P6P0P9AAL28DJ=D5wPK[^14^2U^6U^8U^@U^AU^BU^EUP2PFQ0=Q09Q08Q07Q06Q05PXQ01O9b9b:b;%GXRKeb0PKPMPmPnPoPDPpQ1U#MS1UQ1X']/\qP;Q1Y?@6sP7PsP5PsDBPtPuPuQ1tQ1[PvPuPuQ1ZQ1^Q1\5nuPvPu19zyRK=4u?PvQ1a94uKH0=E=E=P|P~b<b=b>X14X34X44X2UX6UX8UQ1c,36AE6c7=D98AE7J6AE6Jf[[[^14^34^44^2U^6U^8UP2Q0UQ0JPRPbPNPXP6fgQ1jO9b9b:b;10YfRReb0PRPXPJfuRRP5P2I0<Q1MPYQ1hQ1Q/0XCWS1QXQ4RK,~4Q00P4PKp+01Sp+01R58CP2Q1QP3Q1kPYQ1lQ1bPXCSp+01Wp+01V58CP2Q1nPYQ1oQ1wPXCSP3Q1p,0YQ1x/0Xp+01[p+01ZS1x58CP210Y^10WXp+01^RWp+01]S1p'1R^Q03POPWC;P^PIQ0wPWC;S03P^Q0yQ0zPWC;S0yP^Q0gQ0iPWC;S1wP^Q0|Q0~PWC;S0~P^Q11Q15PWC;S15P^P_Q16PWC;S16P^Q17Q18PWC;S18P^Q19Q1:PWC;S19P^Q0kQ0lPWC;S17P^PhQ1;PWC;S11P^Q1<Q1=PWC;S1<P^Q1@Q1APWC;S1@Q1S'3S0|'3S1o'3S1b'3S1l'3S1k'3S00'3S1h'3S1M'3S1j'3S0J'3R^'3PMPmPnPoPDPpQ1WQ1UQ1T#MS1TQ1X3_S0U'LS1c#z/\qP;PrP7PsP5%P9RY?@6sDBPtPuPu%>`%?:R:54uQ1\PvPuPuQ1`94u:PuPuQ1`%?\R\%>S60;4R3Q1_DXPvPu19z?R?=4u1RKPvPuA4u?3Q1yEUE=E=P|P~b<b=b>X14X34X44X54X74X2UX6UX8UAA`691p6S=A9w9A091176S1`/0LS1^1160R`1p9S;Hd[[[^14^34^44^54^74^2U^6U^8UP2p+01bRS,0OQ04Q1RQ02PNPOp+01aROPSP6Q1xPWO;b9b:b;b0Q03P^PMPmPnPoPDPpQ1V#FR^#FRN#FR3#FS1V#MS03%M3S1x&0I@-0H4S02%MNS1R5y41l4g%M^S04'bQ1W/LT3_S1[3_R^#zRNPNPNPNPNPNPNPNPqDcDcP;%PxS1t9@YxP7PsP5%P8S1v?@xsS1zP6%PwS1{P0PsDtDBPtPuPuQ12#?RN=4u\16udS1|PvPuPu%>HS1}%:P#?RP54uS1~Pu16u}S20PuQ1>#?R@%>gS1>'Z,9P,gN,juQ1s,6uS21D7PvPuPu%>ZS22=4u@S2316ujS245nuQ1C,6uS25PvPuPKPvPuPuf?S26,6uS27PuPuf@S28,6uS29PuQ1E,6uS2:PuQ1D,6uS2;PufCS2<,6uS2=PufDS2>,6uS2?PuQ1G,6uS2@PuPu19A{S2A%?]R]19]{S2B=4uADRD7D7D7PuQ1F,6uS2CPufGS2D,6uS2EPuPuPuQ2BPPQ1],9PR3=4u]DRPuPuPuAiAyPPuP3PAEqfHS2F,6uS2GD7D7D7PvA4u?\S2HQ1I,6uS2I60FuF<E=E=E=P|P~b<b=b>X14X34X44X54X74X?4XC4XD4X2UX6UX8UX@UXAUXBUXEUXMUXNUXFUXGUXHUXIUXJUXKUXLUAAw7x158g9Txw=Dd}9AHw10ZwQ1C7dj10`LS2JQ1EQ1DQ2<Q2>Q1GQ1FQ2D11xGS2KPw11wGR3PxC;3DDJQ2FQ1IP3Pd11dcR3PwC;11xJPdP3PxC;Q1H3DDJ1198S2LfLS2M7Hw[[[[[^14^34^44^54^74^?4^C4^D4^2U^6U^8U^@U^AU^BU^EU^MU^NU^FU^GU^HU^IU^JU^KU^LUP2Q0w/0SQ0qQ0WQ0IQ0;Q0:Q09Q08Q07Q06Q05Q0HQ0DQ0TQ0KQ0cPePbP[PXPVPIPOPSQ1OPRfyS0cPWQ01OMb9b:b;b0Q0yQ0JPMPmPnPoPDPpQ1V#FS1V#MR3/]^R^P^P^P^P^P^P^P^PqDcDcP;Q1t9@Y0P7Q1{?@ksS0JP5Q1v%Pk7@kS0y?@6sDBPtPuPuQ0E#?R^=4u\PuQ20Pu%>BS0w=4u:Q21D7PvPuPuQ1}=4uNPuQ24Pu%?QRQQ1>'Z,9N,g^,juQ25D7PvPuPuPuPuQ22PQQ27DXQ29PvPuPKPvPuPuQ2:PuPuQ2;PuQ2=PuQ2?PuQ2@PuQ2CPuQ2EPuPu19@{S2NPAQ2A=4u@DRD7D7D7PuQ2GPuQ2IPuPuPuQ2APNQ1],9NS2A=4uADRPuPuPuAi@yNPuQ2AP@EqQ1H,6uS2AD7D7D7PvPuPuP?19\:Q0w60;4fKS2O,6uS2PDRF<E=E=E=P|P~b<b=b>X14X34X44X54X74X?4XC4XD4XP4X2UX6UX8UX@UXAUXBUXEUXMUXNUXFUXGUXHUXIUXJUXKUXLUXOUPkPBP6PdCW9Ax710HxRNQ1s15wg9TkxS2Q/3j3D10ZxRgQ26Q283dQ2JQ2<Q2>Q1GQ1FQ2DQ2FQ1I11kGPxQ2KPkC;S2>3DDJQ1HQ2OQ2KP}11}cRcPxC;S2K11kJP}PcPkC;S2<Q2M3DDJQ2L11wxRc/pBQ1J3H[[[[[^14^34^44^54^74^?4^C4^D4^P4^2U^6U^8U^@U^AU^BU^EU^MU^NU^FU^GU^HU^IU^JU^KU^LU^OUP2Q0z/0SQ0qQ0WQ0IQ0;Q0:Q09Q08Q07Q06Q05Q0HQ0DQ0TQ0KQ0bQ0`PePbP[PXPVQ0aPIPOPSQ1OPRQ0cPWQ01OOb9b:b;b0Q1wQ1jPMPmPnPoPDPpQ0U#z/\qP;PsP0PrP0PsDBP7PsP5Q1YDBPtPuPuQ0e#>Q13#?S1354uS1YPuPuQ13P\Q1ZDXPvPuPKPvPuQ2HQ1\EUE=P|P~b<b=b>X14X34X44X54X2UX6UQ0e/06S0eP6P7P0CWAE57LS1ZQ1`/00S1`/sw[[^14^34^44^54^2U^6UP2Q0i/0SQ0nQ0fQ0gPOPSfdS0nPWO8b9b:b;b0Q0~Q1MPMPmPnPoPDPpQ1RQ1T/LTS1M'L1l4L/bTS0~Q04Q1U'LS0i,L3'],rT'r/\qS0UP;PsP8PsP8Q1vDtP7A@Y8sP5A@s6rDBS1jPtPuQ0O#?RI,Z1S0O=4u\S1wPvPu19\{Q1a,ZI,9yS1a54uS1OPvPuQ1}=4uQS0aQ1_5nuS0`PvPuA4u1]S0bPvPuPKPvPuA4uyzRIPvPuPuP?Q0{,V\Q0},V\=4uzDRF<F<F<P|P~b<b=b>X14X34X44X54X74X?4X2UQ1q/07S1qQ1d158f7kJS1dAAH8xS0T10L8S0z1109S28/0LS2R10J9Rf118wRGQ0{,1xQ0}=Ex83H[[[[[[^14^34^44^54^74^?4^2UP2Q0Vf_S0}PbPXPVPOPSQ1LfSS0{PRQ1fPWp+01`S2SO=S2Tb9b:b;b0Q15Q1hPMPmPnPoPDPpQ0UP;Q1jPtPuQ1wPvPuQ1OPvPuQ0`PvPuQ0bPvPuPKPvPuPIPvPuPuP?Q10,V\Q14,V\=4uzDRF<F<F<P|P~b<b=b>X14X34X44X54X74X?4X2UQ1qQ1dQ0TQ0zQ2RQ10,1xQ14=Ex85HG\f[[[[[^14^34^44^54^74^?4^2UQ2Tb9b:b;b0Q16Q00PMPmPnPoPDPp1l4aRfQ1R'bQ04Q1M'L5_3Q0~Q1V#F#F#F#M1bf3Q02Q1x5y4S1xQ0i'L3_'],rT'r/\qS0~P;PYPxPsPxQ1tDtP7Q1{?@xsP5Q1z?@6rDBS1zPtPuQ0O=4u]S0OPvPuQ2BQ1a54uS1aPvPuQ0aQ1|5nuS0aPvPuPuPuQ23Q0C#>94u@Q0G,V]%>aR],Z@'9,g\,juD{S2BPvPuA4u1AS0iPvPuPKPvPuPIPvPuQ2H%>iS1V,9\=4uzEUF<F<F<P|P~b<b=b>X14X34X44X54X74X?4XC4XD4X2U15Lw/06R1Q1eQ1r'0RA13NdRTQ0C,0xQ0G,1815xa5T95dgRf10LxRGQ2L/0LRL10J8RJAEkiw9Hck[[[[[[[^14^34^44^54^74^?4^C4^D4^2UP2Q0VQ0}PbP[PXPVP_POPSQ1LQ0{PRQ0cQ1fPWQ2SO@R_b9b:b;b0Q18Q1kPMPmPnPoPDPpQ0~P;Q1zPtPuQ0OPvPuQ1aPvPuQ0aPvPuQ2BPvPuQ0iPvPuPKPvPuPIPvPuQ0w,9\94u?RI19\]=4uzEUF<F<F<P|P~b<b=b>X14X34X44X54X74X?4XC4XD4X2U11kBAEkaw5Hc\J\L\G\f\T\A\1^14^34^44^54^74^?4^C4^D4^2UP_b9b:b;b0Q19Q1lPMPmPnPoPDPp1l4i/b3Q03Q1xQ1[3_']R3P3P3P3P3P3P3P3PqDcDcP;PrP7Q0yP5PYPkQ1tP6Q0JDBDBPtPuPuQ20PuQ21PuQ24PuPuQ1uP:Q25DXD7PvPuPuQ1}=4u^PuQ27PuQ0N#?R3Q1>,ZP,9^'g,juPuPuQ0P,V3,g\Q29H07D7PvPuPuPuPuQ22PPQ2:DXQ2;PvPuPKPvPuPuQ2=PuPuQ2?PuQ2@PuQ2CPuQ2EPuQ2GPuQ2IPuPuAiQ{@PuQ2NPQEqD7D7D7PuQ2APuQ2PPuPuPuQ2NP^Q1],9^R{=4u@DRPuPuPuAiQy^PuP{PQEqQ2M,6uD7D7D7PvPuPuP?Q1V/Z:,9\Q1K,6uDRF<E=E=E=P|P~b<b=b>X14X34X44X54X74X?4XC4XD4XP4X2UX6UX8UX@UXAUXBUXEUXMUXNUXFUXGUXHUXIUXJUXKUXLUXOUXVUXWUPkPdP}Q1mQ1sDJPNQ1CQ2QQ0P9T6kQ26DJQ1EQ1D5dgQ2JQ1GQ1FQ2DQ2FQ1IQ1HQ2OQ2>3DDJQ2MQ1KQ2KQ2<Q1J3DDJQ2LA}wixfP3H[[[[[^14^34^44^54^74^?4^C4^D4^P4^2U^6U^8U^@U^AU^BU^EU^MU^NU^FU^GU^HU^IU^JU^KU^LU^OU^VU^WUP2Q1:/0SQ0qQ0WQ0IQ0;Q0:Q09Q08Q07Q06Q05Q0HQ0DQ0SQ0KQ0^Q0\Q0[Q0ZPePbP[PXPVQ0]Q0MPOPSQ1PPRQ0cPWQ01OQb9b:b;b0Q17Q1bPMPmPnPoPDPpQ1RQ04Q1c'L']/\qP;PsPwPrPwPsDBP7PsPwQ1vPwPsDBP5A@swYPwPsP6PsPwQ1{PwPsDBDBDBPtPuPuQ1YPuPuQ13Q12#:#?RVPuPuQ1uQ0F#?RXPuPuQ0E#:#?Re9iVXPuPuPeP\Q1yDXH07DXDXPvPuPKPvPuQ2HQ1|EUE=P|P~b<b=b>X14X34X44X54X74X?4XC4X2UX6UQ0eP6P0%G9Q28P8AA87wCWCWQ1ZQ1`/sd[[^14^34^44^54^74^?4^C4^2U^6UP2Q0l/0SQ0mQ0jQ0hQ0gQ0fQ0kPOPSQ0nPWO;b9b:b;b0Q11Q1oPMPmPnPoPDPpQ1WQ02Q1U5y41l4EQ1T'bQ1X3_']/\qReP;%P7P5A@r9sP6A@Y9sDtRYPtPuPuQ1~PuQ1\PuQ1_PuQ1yQ0R,VP%>E,Z@'9,g\,juD7D7R@PvPuPuPuQ23Q1|Q20D{RPPvPuPKPvPuQ2HQ21EUF<P|P~b<b=b>X14X34X44X54X74X2UX6UX8UX@UXAUXBUQ0R,10156E5T7,3w9D989AH0RH10Z0?dkdRkQ1^AH`9j[[[^14^34^44^54^74^2U^6U^8U^@U^AU^BUP2Q1;/0SQ0HQ0DQ0QQ0LQ0KPbP[PhPOPSPRQ0cPWO>b9b:b;b0Q1<Q0|PMPmPnPoPDPpPeP;PYPtPuP@PvPuPPPvPuPKPvPuPIQ21EUF<P|P~b<b=b>X14X34X44X54X74X2UX6UX8UX@UXAUXBUQ1^119B=H`j[\k\H^14^34^44^54^74^2U^6U^8U^@U^AU^BUP2Q1=/0SQ0HQ0DQ0QQ0LQ0KPbP[PhPOPSPRQ0cPWO>b9b:b;b0Q1@Q1SPMPmPnPoPDPpPeP;PYPtPuP@PvPuPPPvPuPKPvPuQ1?,V\94u?Q21EUF<P|P~b<b=b>X14X34X44X54X74X2UX6UX8UX@UXAUXBUQ1^Q1?,19=H`j[\k\H^14^34^44^54^74^2U^6U^8U^@U^AU^BUP2Q1A/0SQ0HQ0DQ0QQ0LQ0KPbP[PhPOPSPRQ0cPWO>b9b:b;b0PMPmPnPoPDPpPqP;PsPtPuP<P=P=P>I0EP|P~b<b=b>Q1SP2b9b:b;b0CxFeFeFeFeFeFeQ1p98CWeWnWkP5P2O2n2001000010121000000W0WhP5P2O2n2011000010121000000W0Xs4P5P2O2n2011000010121100000bSbRbTWoWlP5P2O2n2001000010121000000W0WiP5P2O2n2011000010121000000W0Xt4P5P2O2n2011000010121100000bSbRbTWqWpP5P2O2n2001000010121000000W0WmP5P2O2n2001000010121000000W0WjP5P2O2n2001000010121000000W0Xu4P5P2O2n2011000010121100000bSbRW_WYP5P2O2n2001000010121000000W0W]P5P2O2n2001000010121000000W0W[P5P2O2n2011000010121000000W0W`P5P2O2n2011000010121000000W0W^P5P2O2n2111000010121000000W0WZP5P2O2n2011000010121000000X0FWgWcP5P2O2n2001000010121000000W0WbP5P2O2n2001000010121000000W0WaP5P2O2n2001000010121000000W0WfP5P2O2n2001000010121000000W0WeP5P2O2n2001000010121000000W0WdP5P2O2n2001000010121000000W0P5P2O2n2111000010121000000W0W\P5P2O2n2011000010121000000PlQ0vPlQ0xPlp,2HBRl11liQ1BH0:I06?890ebrUUUXQ4XX4o"). Qed.
Lemma RK_obj : forall A k, ((6352896 <= A /\ A + k <= 2147446784) \/ 17594333495296 <= A) -> A + k <= ATOP -> 0 <= k ->      (* [comment removed for export] *)
  (A + k <= t \/ t + 4096 <= A) -> (A + k <= SB \/ SB + 137438957568 <= A) ->
  disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof.
ltac2:(KReplay.run1 (kr_t_ARecyc1P ()) ["CANSEC1"; "Kinds"] "p'0h02H4h14__x1h24__x2h34__x3h44__p1h54__p2h64__p3h74__p4h84__p5h94__p6h:4__p7h;4__x4h<5__p10h=5__p11h>4__p8h?4__p9h@4__x5hA4__x6hB4__x7hC7__arithhD6__sat5hE6__sat6hF4__ffhG5__p12hH8__varmaphI5__withJ5__p13hK5__p14hL4__x8hM5__x10hN4__x9hO5__x11hP5__p15hQ5__x12hR1khS2G0hT1ehU1GhV2HahW5__p16hX5__p17hY5__p18hZ1Ah[4F_abh\3F_ch]5F_csbh^4F_loh_4F_muh`4F_sbha4F_shhb5F_tsbhc3Fc1hd3Fc2he3Fc3hf3Ft1hg3Ft2hh3Ft3hi3Ftchj5KAFc1hk5KAFt1hl5KAFt2hm5KBFc1hn5KBFt1ho5KBFt2hp5KCFc1hq5KCFt1hr5KCFt2hs5KDFt2ht3KF'hu4kFc1hv4kFt1hw4kFt2i001xp%0p%1p%2p&0p;1p;2p;3p;4p;5p;6p;7p;8p-1R0p10000p4p710p9P0p1000Sp4p710p9P0p1001?R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001]p4p710p9P0p1002Dp4p710p9P0p1003<p4p710R0p8p1003Sp4p710R1p10040p4p710R2p8P1p1004Lp4p710R3p8p1004jp4p710R4p1005HR5p4p710R6p8P4P5p4p7210R5p8p1005ap4p70R7P0p8P7P2p8P7P1p8P7P3p8P7p1006Xp4p710p8P7p10075R1p4p710p8P7p1007Rp4p710p8p1007np4p710R7P4p8P7P6p8P7P5p8P7p1008Bp4p73110p8p1008Tp4p710P2p8P1p4p7210P3p8p1009Qp4p710R1P2p8P1P3p8p100:0p4p7210P2p8p100:Op4p710P3p8g00=bj1;Tg00<_j14Tg00Tck10fTg00=Dj1ETg00<Bj21Tg00;fj20Tg00[Bj2uTg00[_k20YTg00;1k20ETg00R;k20VTg00>GR3j23Tg00>bj2:Tg00\<k20MTg00?Yk10<Tg00\\j3=Tg00Sek10dTg00]Xk20bTg00^@k20ITg00^\k30_Tg00UYj1ATg00V8k20HTg00@9k10^Tg00A7k10]Tg00B3k10\Tg00BQk10[Tg00DBk10ZTg00C_k20FTg00Ejk20XTg00FLk20WTg00Ffk20UTg00GRk30CTg00Glk30TTg00HKk40STg00_@k40RTg00??S00k208Tg00C<k205Tg00`<k50BTg00a8k30ATg00cCj2yTg00a[k10OTg00b9k20NTg00bZk300Tg00dXk50JTg00e<k407Tg00P5j2jTg00eWj4{Tg00X6j3STg00Vaj3pTg00WJk20:Tg00@Yk20eTg00AUj4wTg00XVk60cTg00IWj4VTg00JBj7LTg00Ddk309Tg00Jfj7QTg00KJj8vTg00f7j7nTg00f[k30`Tg00EGk30aTf0R2#;#4p=g%42#4#4#4p=]%;2#;p=h%42#4#4#4#4#4#4#Ep=_%;2#;#;#;p=Of2R1f1R7'1/02p=H1017/32p=F%42#4p>02%42#4#4p>01%42#4#4#4#4#4#4#4p=T1072,j1p=ag00O2R5/02p=Gf3R6/11/07/j2p=^%42#4#4#Ep=f%42#Ep>0Qg00MMR4117280C1p=[1317/32p>0310611072'jp=81072,31p=X1372,31p=N10611072'3p=\f4R01017/32,36'3p=tP4P4P7P2C{p>0>f6R8P4P4f5R9P0C{P4P4P1P7C{=S623Sp=rP4P4P1P7C{=S62p>0DAS1729S06p>0;20H42p=CAp472p=oAp472g00ZVR:+0:p=Pg00POR;?S72p>0G20e42p=MP4P1P7P2Cwp=@P4P4P0P6P1CwP7P2Cwp=IP7g00KnR<g00LMR=P=g00LmR>P2J0cp=<20F42p=?20542p=BP1P<P=P=P>P4P7g00MkR?P2CVg00NRR@FLp=6B09472p=9P1P<P=P=P>P7P2FQp=eP8P<P=P=P>P9P0P6P<P=P=P>P1P7P2GvGvp=7P9P<P=P=P>P0P<P=P=P>P6P1FQP7P2Gvp=>1172,01p=s1:72,11p>06P6P<P=P=P>P1P7P2Gvp>04P0P<P=P=P>P6P1P<P=P=P>P7P2FQFQp=5P0P<P=P=P>P6P<P=P=P>P1P7FQP2FQp=z1372,31,36,30p=ZAp4729p41p=KAp4729p4100::p=RAS;729S;19S;69S;0p=2P0P<P=P=P>P6P<P=P=P>P4P1P?P7CVP@FLP2FQp=JP8P<P=P=P>P9P<P=P=P>P4P0P?P6CVP@FLP1P<P=P=P>P4P7P?P2CVP@FLFnp=DP4B09417P?P2CVp=YP6P<P=P=P>P1P<P=P=P>P7P@FLP2Fnp>0PP0P<P=P=P>P6P<P=P=P>P4P1P?P7CVP@FLP2Fnp>0@1372,31,36,30,39,38p=W1j17/32p=`B0`472p=dP4P0P6P4P1P7P2CwCwp>0?P4P7P?P2CVp=bP8P<P=P=P>P9P<P=P=P>P0P@FLP6P<P=P=P>P1P<P=P=P>P7P@FLP2FQFQp=~B0a472p=lP4P7g00gDP2CVp=mP7P<P=P=P>P2P@FLp=xP6P<P=P=P>P1P7P<P=P=P>P2P@FLFnp=q1017/j2p>0=10061117/02'jp=UP9P<P=P=P>P0P<P=P=P>P6P@FLP1P<P=P=P>P4P7P?P2CVP@FLFnp=}P6P<P=P=P>P1P7P<P=P=P>P2P@FLFQp=|20542:0947p=cP9P<P=P=P>P0P6P1P<P=P=P>P7P2FnGvp=kP6P<P=P=P>P1P<P=P=P>P7P@FLP2FQp>0L20:2:p>0KP8P9P0P6P1P7P2H07H07p=ig00OPR:#g#]#;#h#g#]#_R@%;:R?#;RA#;S01#;RB#h#O#ORC#4#;#hRD#4#]#_RE9H727F7%4:RF#4RG#4S02#4S03#4RH#4RI#4RJ$02RK$01RL#4RM#O#O#O#O#T#_RN;a7p,2rcRO$0fRP9H17%G1P0P6p,1tRQ%ELRL,1QRR/00C^P9P0p,2SBRS&01MRM#TRT#g#]#_RU,1SRV/09C^p,2KFS04g00gkP3p,2loS05Q05p,2spRW%;FRX#4RY#;S06#;RZ#4#fR['uS07%EFR\%EIRI+0YR],0WS083F5FPR^20EQLR_20VQLR`10RPRap,3ctxRb%EMRM+0ERc10@bRd11bMRe/0PRfPbPLPQ10RbC^S09'3S0:'3S0;'3S0<'3S0='3S0>'3S0?%E:Rgp,1cRh'0%EBS0@,0hp,2CAS0A%4?RB#;S0B#4S0C#fS0D,1Q%4YS0E#4$0QS0F,:h3[S0G403Ri10NSS0H10VPS0Ip,2RBS0J%4T#]RT$01Rj#ES0K,:h7[SS0Lp,2FAS0MQ0J%4AS0N#4#]#T#T#_S0O3[S0Pp,2RIRk%4j#]Rj#ES0Q,1S%EJS0R,:h3[S0S'3S0T'3S0U'3S0V'3RJPRPSPVPQC8S0WPePSPVPbC8S0Xp,2auS0Y#GS0ZQ0Yp,2muS0['0S0\Q0[Q0O'0S0]p,2nfS0^#G%EGRVQ0^':Rlp,3mfaRm'0S0_p,4mfa'S0`,0mS0aQ0`%ETS0b3X3NS0c'33NS0dQ0Jp,2ABRTp,1SS0e,1TQ0JQ0Y'1Q03#ERmp,2rzS0fQ0fQ0eC\3F3FS0g%gK$02#;#h#O#O#g#h#g#]#_S0hp,4SHLOS0iQ0ip,4SHUBS0jp,2grS0k#GS0lQ0jQ0k'1S0mp,4SHHIS0n'0Q0np,4SHF0S0oQ0op,4SHF1S0p'0S0qQ0p;XNDt3F3FS0r'3S0s'3RK'3S0t'3S0u'3S0v'3Rn'3S0w20M44RoQ0700>WS0xPoQ02#ES0y,1TS0z-0>TS0{PoQ0f,1T/umS0|Q0|/1VS0}PoQ0jQ0mPo%;ZRZ#4Rp#4#fS0~,1QS10%;p#fS11,1QS12Po%gZ#fS13,1QS14%4BS15#4S16#h$02#fS17,1QS18PoQ0AQ0A/1VS19PoQ0A/1mS1:Q0AQ0F'1S1;PoQ0M/1lS1<Q0MQ0`'1S1=PoQ0oQ0pPoPkQ0y,1kS1>Po11kmS1?%EHS1@,1kS1APo%;GS1B#fS1C,1kS1DQ0R,1kS1E&0<oFrFrFrFrFrS1FH0DI0;RHf8Rlf7RZ3=P2Q0wP3Q0?Pnf<Rpf;Rq5=HP2Q0?P3P_Q0>f@S1Gf?Rr5=H\nP2Q0>P3P`Q0=fDS1HfCS1I5=H\nP2Q0=P3PaQ0<fHS1JfGS1K5=H\nP2Q0<P3PcQ0;fLS1LfKS1M5=H\nP2Q0;P3PdQ0:fPS1NfOS1O5=H\nP2Q0:P3PfQ09fTS1PfSS1Q5=H\nP2Q09P3PiQ0vfXS1RfW5=HP2Q0vP3PJQ0uf\f[S1S5=HP2Q0uP3Q0WQ0tf`f_5=HP2Q0WQ0tP3Q0XPKfdS1Tfc5=HP2Q0XP3Q0dQ0sfhfgS1U5=HP2Q0dQ0sP3Q0gQ0rflfk5=HP2Q0gQ0r&0dORO%;D#O#T#T#_/0PS1V%;C#O#O#T#T#_RC7XPRD20b\IRs20I5\%GI20I5][[Rt%G\Rug00hdS1WB0_\I7UWVRIQ1W%G][^VuRup-0R]g00Z7R\#ARv#AS1X#AS1Y#AS1Z#CS1[%CvS1\20H4\S1]'oS1^'P&0<;R\+0G&0^;R;%M0S1_&0]4Rv7@0P1PvP7%M6S1`?@0vDI&0\4Rw&0[4RxPx1<x8S1a%?FRF%BC56xS1b&0Z=RyPxPx1<xZS1cQ02#?S1d%BUS1e'9=6xFS1f1<xlS1g5exPyPx%?XS1h%BMS1i'9=6xFPyPx20F4:Rz%BLR{'9R|=6xFPy%]j#T#T#_Rj#BS1j96x|F7E>E>20Xx>R|P2P1g00Q;R}g00Q[R~+0W20U21>0C}~dB0T457H0SR~bFbHbIX14X24X34X;4X4]X5]W6S1k107CS1l,30AH0U1=N8Z110MS1m/06AH6L0110LS1n/0j[[[[^14^24^34^;4^4]^5]^6]S1oP2Q0UQ0HQ1VPSPbPPPQP6fES1pfNS1qfZO;bCbDbE10RjS1reb0Q1rPQPLQ1SP2H0R%G2?X2gRC10LQS1SPR1:2jS1s,1M1:@2/0QDtS1tXR4R}-084Q00P4P}frS1ufqS1v5=HP2Q1tP3%G7S1w?X7gS1xQ1S1:7jS1y9sRM1:@7/0Q3NfvfuS1z5=HP2%G6S1{?X6gS1|Q1S1:0jS1}9sRM1:@0/0Q3NP3Q1SPR1:9jS1~,1M1:@9PQC\fzfyS205=HP2Q1SPRB06Mlj1:@lPQC\P3f9R}/:j9sRM1:@}/0Qf~f}S215=HP21:qj9sRM1:@p/0QPOPDPsPtPIPuP\P;%M7S22PwPxA6x{zPy20545S23=6xzS24H04P|P~bFbHbIX1410L2Q1w[^14P2PQP}O2bCbDbE%GQR5eb0P5POPDPsPtPIPuQ1kQ1oP2Q0UQ0HQ1VPSPbPPPQP6Q1RfafmS1RO;bCbDbEQ1reb0Q1rPQPLQ1uP7P2I0BQ1s,1ES1s,0R1:N2S1u/0Q5NCS1rXR4R5-084Q00P4P5p+01Fp+01E5=HP2Q1rP3Q1xPRQ1y,1ES1y1:N7S1oPQC\p+01Jp+01I5=HP2Q1|PRQ1},1ES1}1:N0S1kPQC\P3Q1~,1ES1~,0R1:N9S25/0Qp+01Np+01M5=HP2B06EZjS26,0R1:NlRR/0QPOPDPsPtPIPuP\P;Q22PwPxPx1<x6PxPx1<x0Px1<x9S22PxQ1aPxQ1cPx%B@=6xzQ1gD5D51<x}S1gDzPyQ24E>P|P~bFbHbIX14X4]X5]X6]X7]X8]X9]X:]P1P6P0P9AF@28DZ=N7ZQ1w[^14^4]^5]^6]^7]^8]^9]^:]P2PnQ0:PcPaP`P_P^PbQ04O9bCbDbE%GbR5eb0P5POPDPsPtPIPuQ1Y#CS1YQ1^'P00G\P;Q1`?@6vP1PvP7PvDIPwPxPxQ22Q1bPyPxPxQ1aQ1fQ1c5exPyPxQ1i,9zR5=6xFPyQ1j96x5H04E>E>P|P~bFbHbIX14X24X34X4]X5]X6]Q1l,36AH6U1=N98AH1M6AH6Mj[[[^14^24^34^4]^5]^6]P2Q0UQ0HQ1VPSPPPbP6Q1UfpO9bCbDbE10ejRjeb0PjPbPMQ1zP7P2I0BQ1s,0eQ1u/0b5NCS1uXR4RC-084Q00P4PCp+01Up+01T5=HP2Q1uP3Q1xPeQ1yQ1oPbC\p+01Yp+01X5=HP2Q1|PeQ1}Q1kPbC\P3Q1~,0eQ25/0bp+01]p+01\5=HP2Q26,0e10Rbp+01`RRp+01_S26'1ReQ07PWPRC8PePTQ0zPRC8S0zPeQ0|Q0}PRC8S0}PeQ0jQ0mPRC8S0mPeQ10Q12PRC8S12PeQ14Q18PRC8S18PeQ0AQ19PRC8S19PeQ1:Q1;PRC8S1;PeQ1<Q1=PRC8S1=PeQ0oQ0pPRC8S1<PePkQ1>PRC8S1>PeQ1?Q1APRC8S1APeQ1DQ1EPRC8S1EQ1W'3S1D'3S1?'3S1:'3S14'3S10'3S0|'3S07'3S25'3S1~'3S1k'3S1}'3POPDPsPtPIPuQ1Z#ARe#AR3#CS1Z%CeS1oQ1[Q1]3K'PRePePePePePePeQ1YQ1X#CQ1\3RP\D2D2P;Q1_P1%MlS1X?@8vP7%M9S1[%MZS1y7@6DIPwPxPx%?GRGQ1h56xPxPxQ1h%??R?%B[60A4S1xf:Re,<xS00DJPyPx19zFRC=6xGPyPxPx1<xqS1sPxPx1<xpS1UPxf=Rj,<xS1VPxf>R5,<xS0HPx1<xrS0UPxQ1G,<xS1lPxfAS1j,<xS1fPxPx%?ARA/9{S1c%?BRBPx19B{S1aPAFDD5D5D5PxfBS1b,<xS22PxQ1I,<xS1^PxPxPxQ1a%?YRYPxQ1e,9YS1aPBFDPxPxPxQ1i=YAYQ1a=6xAS1wH0PQ1H,<xS24D5D5D5PyPxPxPCQ1xQ1p,<xS1xI0@F7E>P|P~bFbHbIX14X24X34X;4X@4XA4XB4XL4X4]X5]X6]X7]X8]X9]X:]X>]X?]X<]X=]XG]1u1[=F0l9F601171S27/00PqPpPjP5PrQ1GQ1j11lLS28PZ11ZLS29PlC8S2:FWQ1bQ1IQ29/0}11}US2;/0ZS2<AHlM}Q2;/0lQ1H3`3`DZP6P01u9[fFS2=C^[[[^14^24^34^;4^@4^A4^B4^L4^4]^5]^6]^7]^8]^9]^:]^>]^?]^<]^=]^G]P2p+01dR[,0WPKPJPiPfPdPcPaP`P_P^Q08PSPbPQQ05PPPWp+01cS05P[p+01Zp+01aQ04OGbCbDbEb0Q0zQ1}POPDPsPtPIPu%A3S1}#A#AS0z#AS08#AS2>#AS2?#AS2@#AS2A#AS2B#AR3#ARW#ARP#AS2C#CRB%CPS2D%CWS2E%C3R3Q2B#CS2BQ1YQ2>#CS2>Q0K,y4S2FQ0z#CS0z'dRWQ1ZQ1]'oS2G3KS2H3K3KS2I3RRPQ2DQ2EQ2BQ2>Q1}#CS1}Q1]'oS2J7KWS2K'o7K3S2L5RBRWQ2C#A#CS2C&0O:-0N4S2MQ2>6004S2NQ2FQ08#CS08'dQ1}Q1\'oS1}3KS2F'PR:PPPPP:PWPPPWPWP:P:P:P:PWPWPWPWP:P:P:P:PWPWPPPWP:PPPPP:PWPPP\D2D2D2D2D2D2D2D2P;%MeS2O?@9vS2PPp%MqS2QPlPvI0?P1PvP7%M8S2RPp%MpS2S?@pvP6Q1y%M}S2T7@0DIDIPwPxPxQ15#?RP=6x?PxPxQ0E#?RWQ01#?R:,9P5Y?PxPx%BmS01Q06#?S06'bQ06=6xWF~PyPxPxQ0HPxPxP:Q03#?S03PxPxQ03Q0O#BS0EQ0UDJDJPyPxPxPxQ1dQ1i'9S2U%;X#?RXPxQ1e,9XS2VQ1dFDS2WPyPxPxPxQ1cPXPxQ2VPAFDS2XPyPxPx%BNR:=6xXS2YPxQ1lPxQ1B#?RWQ0K#BS1B'l,9X,mP,xxQ1fD5PyPxPxPxPx%BgS2ZPWQ0@#BS2[96xWDJS2\Q22PyPxPxPxQ1d/9{S2]PAPxQ1cQ1dFDS2^PyPxPxPxPCPXPxQ2VPzFDS2VPyPxPxPxPCPAPxQ1cPzFDS2_PyPxQ23=6xFS2`PyPxPxQ1^PxPxQ24PxQ1xPxQ2=,<xS2aPxQ1K,<xS2bPxQ1J,<xS2cfIS2d,<xS2eQ2^5exD5D5PxfJS2f,<xS2gPxQ1M,<xS2hPxQ2XPxQ2WQ1L,<xS2iD5D5DzPyPxA6xC?S2jPxQ0y#B=Y?zCqS2kE>F7F7E>E>F7E>E>P|P~bFbHbIX14X24X34X;4X@4XA4XB4XL4XN4XM4XO4XQ4X4]X5]X6]X7]X8]X9]X:]X>]X?]X<]X=]XG]XJ]XK]XP]10Z1S2l11ZlS2m9H1ePmPq10qeDtPj10}eS2nPeQ0OP5Dt118MS2oAHlU8S2p80=l118LS2qP}Q2;P8C8Q1bQ0K,:}9[qeQ1I3N9FNe10geQ0@,0eQ1p40311eLS2;P}11}LS2rPeC8Q2mPjPjPUPZDU11l}S2sPq11qLS2tPlC8%GeS2uQ1MQ1LfMS2vQ1qQ1OQ1NfQS2w115LS2xPj11jLS2yP5C8FWfRS2zQ1QQ2yQ1G'0Q1G/1URF/0jQ1G9H5M10F5Q1P3`3`DZ11qpS2{PjPjQ0yPqDU[[[[[[[[[[[^14^24^34^;4^@4^A4^B4^L4^N4^M4^O4^Q4^4]^5]^6]^7]^8]^9]^:]^>]^?]^<]^=]^G]^J]^K]^P]P2PKPJPiPfPdPcPaP`P_P^Q0GQ0TQ0IQ0cQ0ZQ0fQ0eQ0[Q0YQ0JPSPhPbPQPTQ05P[feS2|fiS2}Q1RQ1vQ1zQ20Q21p+01^S2~Q26PRQ04OVbCbDbEb0Q0}Q1kPOPDPsPtPIPuQ2I,PBS2IQ2L,PBRBQ2CQ2DQ2F3RRFQ2IQ2IPFPBQ2IPBPBPFPFPFPFPBPBPBPBPFPFPFPFPBPBQ2IPBPFQ2IQ2IPFPBQ2IP\D2D2D2D2D2D2D2D2P;Q2PQ1X7@0P1Q1y?@pvP7Q2Q?@8vPpQ2S?@}vP6PvDIDIPwPxPxQ0B#?RB=6x?PxPxQ06Q03,9B5Y?PxPxQ01/bGQ0696xGF~PyPxPxQ0HPxPxQ03Q02#;#?RFPxPxPFQ0EQ0UDJDJPyPxPxPxQ1i=YWPPxQ1e,9PRFPWE}S02PyPxPxPxQ2]PPPxPFQ1dFDS03PyPxPxA6x:PS06PxQ1lPxQ1B,lY,9P,mB,xxQ1fD5PyPxPxPxPxQ2ZPYQ2[96xYDJQ22PyPxPxPx19W{S2SQ1dPxQ2]PWFDS2PPyPxPxPxPCPPPxPFPzFDPyPxPxPxPCQ1dPxQ2]PzFDS2]PyPxQ2`PyPxPxQ1^PxPxQ24PxQ1xPxQ2aPxQ2bPxQ2cQ2eQ2P5exD5D5PxQ2gPxQ2hPxQ03PxQ02Q2iD5D5DzPyPxPxPC19?GS2IQ0160A4RFPx%BVS2C,9FPzFDE>F7F7E>E>F7E>E>P|P~bFbHbIX14X24X34X;4X@4XA4XB4XL4XN4XM4XO4XQ4X4]X5]X6]X7]X8]X9]X:]X>]X?]X<]X=]XG]XJ]XK]XP]111qQ2sPmP6P6PqC\3F9Fl1Pj10eqPqQ0OP5DtPZPMP}Q2<C^S2<Q29PePePUPZDUS2910NqS2DQ1bQ0K,:e9[pqS0KQ1I'33N10gqQ0@,0qQ1p403S2LQ2tPeQ2;PqC8S2;Q2mP5115US1kPZC8Q2sPp11pLS0}PlC8Q2uQ1MQ1LQ2vQ1qQ1OQ1NQ2wPrPLP5Q2x/0rC^FWQ2zQ1QQ2xQ1j'0Q1j/1URF/05Q1j9HrM10FrQ1P3`3`DZS1PQ2{11j5/umRFPFPVPqDU[[[[[[[[[[[^14^24^34^;4^@4^A4^B4^L4^N4^M4^O4^Q4^4]^5]^6]^7]^8]^9]^:]^>]^?]^<]^=]^G]^J]^K]^P]P2PKPJPiPfPdPcPaP`P_P^Q0GQ0TQ0IQ0cQ0ZQ0eQ0[Q0YQ0JPSPhPbPQQ0fPTQ05P[Q2|Q2}Q1RQ1vQ1zQ20Q21Q2~Q26PRQ04OVbCbDbEb0Q0mQ1~POPDPsPtPIPuQ2EQ1oQ1\'oS1~7R3RTQ2BQ2A#CS2AQ2@#CS2@Q2?#CRFQ1oQ1]3KS1o3K'PRPPPPTPTPPPPPTPTPPPPPTPTPPPPPTPTPPPPPTPTPPPPPTPTPPPPPTPTPPPPPTP\D2D2D2D2D2D2D2D2P;PvP9Q1XP0Q1yDIP1PvPqQ2OPqPvDIP7Q2T9@v8PqPvP6PvPqQ2QPqPvDIDIDIS2QPwPxPxQ0h#BQ16#?S1656xS1]PxPxQ16P?PxQ1VPxQ2IQ15#;#?S1556xPxPxQ15Q0C#?RTPxPxPTQ0B#;#?RPA6xP:DJDJD5DJPyPxQ02PyPxQ03PyPxQ06Q0H5exS06PyPxQ2PPyPxQ2]PyPxQ2`PyPxPxPxQ0UPx%BE,bCC|Px1b:zCqS0BPyPxPxQ1lPxPxQ1fPxQ22PxQ1^PxQ24PxQ1xPxQ2aQ2PD5D5D5PxQ2bPxQ2cPxQ03PxQ02Q2eD5D5D5S0CPyPxQ2jPxQ2I/bzCqF7F7F7F7E>P|P~bFbHbIX14X24X34X;4X@4XA4XB4XL4XN4XM4XO4X4]X5]X6]X7]X8]X9]X:]X>]X?]X<]X=]XG]XJ]Q0h/0ZS0hQ2lPqAH16lQ2n?XeN9Fl}DZQ2oPZ11ZUS2oP8C8S2nQ2qQ2p80=lS2qAFN}rS2pQ2rPlQ28P}C8S281198S2lP}Q2rP9C8S2I%GZS2?Q1HQ2m;XE?aNZS0mQ2=Q1KQ1JQ2dQ2fQ1MQ1LQ2yPpQ0}PjC8FWQ2vQ1qQ0}/05Q1k/0pS1qAHjM5Q1k/0jQ1O3`3`DZS1O11}eRE/0qRrQ2{;a}[[[[[[[[[^14^24^34^;4^@4^A4^B4^L4^N4^M4^O4^4]^5]^6]^7]^8]^9]^:]^>]^?]^<]^=]^G]^J]P2PKPJPiPfPdPcPaP`P_P^10@[S2{Q0VQ0lQ0pQ0oQ0nQ0iPSPbPQQ0kQ0jQ05P[Q1TQ1RQ1vQ1zQ21Q26PRp+01bS0lQ04OQbCbDbEb0Q12Q25POPDPsPtPIPuP\P;%M1Q1`7@7S1`PwPxPxQ2jPxAY?{zCqS25PyPxQ0~,c?96xCQ11,c?=6xzEkP|P~bFbHbIX14X24X34P2P7P1AH1L2C^RLQ27Q0~,16P6Q11P7DU[^14^24^34P2PQQ05P[Q26O4R@bCbDbEb0Q18Q07POPDPsPtPIPuP\P;Q1`PwPxQ25PyPxQ13,c?96xCQ17,c?=6xzEkP|P~bFbHbIX14X24X34Q27Q13,16P6Q17P7DU\L^14^24^34P@bCbDbEb0Q19Q0|POPDPsPtPIPuQ0F,y4R@Q08'dQ0zQ2G3RRLQ2>,d@Q2MQ0z6004Q1ZQ1\3K'PR@P@PLPLP@P@PLPLP@P@PLPLP@P@PLPLP@P@PLPLP@P@PLPLP@P@PLPLP@P@PLP\D2D2D2D2D2D2D2D2S1ZP;Q1[?@ZvS1[P1Q1y?@ZvP7Q2R?@ZvS1\Q1_7@6DIS0|PwPxPxPxQ2UPYPxQ1aQ1dFDS1dPyPxPxPxQ1cPYQ1wI0@S1wPyPxPxPxP:PYQ1gDJS1cPyPxPxQ2\PxQ0D,cAQ0F#BS2U,lW'9,m?C|S19PyPxQ2^PyPxPxPxPCPYPxQ1aPzFDS1aPyPxQ2_PyPxQ2`PyPxPxQ00PxPxQ1sPxQ1UPxQ1VPxQ0HPxQ0UPxQ1lQ2^D5D5D5PxQ1fPxQ22PxQ1wPxQ1dQ1^D5D5D5S17PyPxQ2jQ2C,9?=6xzEkF7F7F7F7P|P~bFbHbIX14X24X34X;4X@4XA4XB4X4]X5]X6]X7]X8]X9]X:]X>]X?]X<]X=]Q1mP8P8PUP0DURAQ1nPZQ2oP0C8RL10NlS2o/3}S1nPgPlPlQ0@C\S0@Q0D,18Q0F,:l5[9'3S0DQ2:Q2lPqPqPUP9DURU118ZS2lP}Q2rP8C8Rg%GlR@Q1GQ1jQ1bQ1IQ1HQ1pQ2=Q0}PqQ2tPpC8S1jFWQ1KQ1JQ2tP5Q1kPqC8S2tPpPMP5Q1qC^S1qQ2dFWRM11qV=ar}[[[[[[[[[^14^24^34^;4^@4^A4^B4^4]^5]^6]^7]^8]^9]^:]^>]^?]^<]^=]P2PKPJPiPfPdPcPaP`P_P^Q0VPSPhPbPQQ0AQ05P[Q1RQ1vQ1zQ20Q21Q2~Q26PRQ04OKS0AbCbDbEb0Q1;Q10POPDPsPtPIPuQ1ZP;Q0|PwPxQ1dPyPxQ1wPyPxQ1cPyPxQ19PyPxQ2^PyPxQ1aPyPxQ2_PyPxQ2`PyPxQ17PyPxQ01,9?96xCS01Q2U,9?=6xzEkF7F7F7F7P|P~bFbHbIX14X24X34X;4X@4XA4XB4X4]X5]X6]X7]X8]X9]X:]X>]X?]X<]X=]Q1nQ0DQ2:AsEqmS2UQ0F,1q;a}\M\@\g\U[[[\L\A^14^24^34^;4^@4^A4^B4^4]^5]^6]^7]^8]^9]^:]^>]^?]^<]^=]Q0AbCbDbEb0Q1=Q14POPDPsPtPIPuQ1YQ2H7KF,P3RMQ2K9R3FRm1y4VQ2E'dQ2M>004FQ2F3RRFPMPMPFPmPMPmPmPFPFPFPFPmPmPmPmPFPFPFPFPmPmPMPmPFPMPMPFPmPMP\D2D2D2D2D2D2D2D2P;Q1_P1Q1yQ2O7@eP7Q2RP9Q2TP6Q1X?@evDIDIPwPxPxQ1UPxQ1VPxQ0HPxPxQ23PGPxQ0UPxQ1lQ1hQ0b#B56xD5DJD5PyPxPxPxQ1i=YYBPxQ1e,9BRMPYE}S1ePyPxPxPxQ2SPBPxPMPWFDRmPyPxPxA6x:BPxQ1fPxQ0N#?RFQ1B,lX,9B'm,xxPxPxQ0E,9F,m?Q22H0LD5PyPxPxPxPxQ2ZPXQ2[96xXDJQ1^PyPxPxPxAYY{WPxQ2SPYE}RYPyPxPxPxPCPBPxPMPzFDPyPxPxPxPCPWPxQ2SPzFDPyPxQ2`PyPxPxQ24PxPxQ1xPxQ2aPxQ2bPxQ2cPxQ2eQ2g=exYD5D5PxQ2hPxQ2iPxPmPxQ1eQ2v,<xD5D5DzPyPxPxPCQ2C/lG,9?PxQ1h,9?PzFDE>F7F7E>E>F7E>P|P~bFbHbIX14X24X34X;4X@4XA4XB4XL4XN4XM4X4]X5]X6]X7]X8]X9]X:]X>]X?]X<]X=]XG]XJ]XK]XP]XW]XX]XY]PePqPpQ1{PjP5Q0b,00FWQ2<Q29Q2DQ1bQ0KQ0O9[9pQ1IDZQ2LQ2;Q2lP5Q1kP8C8Q2mPpQ0}PZC8%G}R9Q1PPePqB06pVjAHp5eC^[[[[[[[[[[^14^24^34^;4^@4^A4^B4^L4^N4^M4^4]^5]^6]^7]^8]^9]^:]^>]^?]^<]^=]^G]^J]^K]^P]^W]^X]^Y]P2PKPJPiPfPdPcPaP`P_P^Q0GQ0SQ0IQ0aQ0_Q0]Q0\Q0ZQ0JPSPhPbPQQ0`Q0^Q0MQ05P[Q2}Q1RQ1vQ1zQ20Q21Q2~Q26PRQ04OVbCbDbEb0Q1<Q1:POPDPsPtPIPuQ2EQ2BQ2AQ2@Q1~3K5K3'PR3Q1o$0KR5P5P3P3P5P5P3P3P5P5P3P3P5P5P3P3P5P5P3P3P5P5P3P3P5P5P3P3P5P5P3P\D2D2D2D2D2D2D2D2P;Q2QPwPxPxQ1]PxPxQ16Q15PxPxQ23PTPxPxQ15?YTPPxPx1bP?PxQ1VPx1bG:C|F~DJDJPyPxQ02PyPxQ03PyPxQ06PyPxQ2PPyPxQ2]PyPxQ2`PyPxQ0BPyPxQ0CPyPxQ2jPx1bGzCqF7F7F7F7E>P|P~bFbHbIX14X24X34X;4X@4XA4XB4XL4XN4XM4XO4X4]X5]X6]X7]X8]X9]X:]X>]X?]X<]X=]XG]XJ]Q0h10ZlP9Q2s/0eAXq6N9Fe1DZQ2nQ2qQ2pQ28Q2IQ2?Q0mQ1OAarp}[[[[[[[[[^14^24^34^;4^@4^A4^B4^L4^N4^M4^O4^4]^5]^6]^7]^8]^9]^:]^>]^?]^<]^=]^G]^J]P2PKPJPiPfPdPcPaP`P_P^Q2{Q0VQ0qQ0nQ0kQ0jQ0iPSPbPQQ0pQ0oQ05P[Q1TQ1RQ1vQ1zQ21Q26PRQ0lQ04OQbCbDbEb0Q1>Q1?POPDPsPtPIPuQ1YQ2>Q0R,y4RpQ0z'dRNQ2G3K'PR9Q2>Q2J7RNRNQ2NQ08,dpQ1}3RRpP9P9PpPNP9PNPNPpPpPpPpPNPNPNPNPpPpPpPpPNPNP9PNPpP9P9PpPNP9P\D2D2D2D2D2D2D2D2R9P;Q1[P1PvP7Q1\P6Q1yP0PvI0?DIR6PwPxQ2WPyPxQ2XPyPxPxQ2YPxQ1gPxQ00PxQ1sQ0Q,cXQ0R#BRX,lW'9,m?,xxD5D5RWPyPxQ2\Q1U5exR1PyPxQ2^PyPxQ2VPyPxQ2_PyPxQ2`PyPxPxQ1VPxPxQ0HPxQ0UPxQ1lPxQ1fPxQ22PxQ1^Q2^D5D5D5PxQ24PxQ1xPxQ2XPxQ2WQ2aD5D5D5RNPyQ2kH04F7F7F7F7P|P~bFbHbIX14X24X34X;4X@4XA4XB4X4]X5]X6]X7]X8]X9]X:]X>]X?]X<]X=]XG]XJ]XK]Q2oP}PePqQ0Q,1lQ0R,:Z5[0DZR0Q0@/3jRjQ2:Q1IQ1HQ1pQ2=Q1KQ1JQ2dQ1jFWQ2fQ1MQ2tQ1qQ1LFWRlQ0y,1q=ar}[\@\g\U[[[\L\A^14^24^34^;4^@4^A4^B4^4]^5]^6]^7]^8]^9]^:]^>]^?]^<]^=]^G]^J]^K]P2PKPJPiPfPdPcPaP`P_P^Q0GQ0PQ0LQ0IPSPhPbPQPkQ05P[Q1RQ1vQ1zQ20Q21Q2~Q26PRQ04ONR[bCbDbEb0Q1AQ1DPOPDPsPtPIPuP9P;P6PwPxQ2WPyPxQ2XPyPxPWPyPxP1PyPxQ2^PyPxQ2VPyPxQ2_PyPxQ2`PyPxPNPyPxQ01Q1@,c?=6xzEkF7F7F7F7P|P~bFbHbIX14X24X34X;4X@4XA4XB4X4]X5]X6]X7]X8]X9]X:]X>]X?]X<]X=]XG]XJ]XK]Q2:Q2UQ1@,1q;a}\l\@\g\U[\j\0\L\A^14^24^34^;4^@4^A4^B4^4]^5]^6]^7]^8]^9]^:]^>]^?]^<]^=]^G]^J]^K]P[bCbDbEb0Q1EQ1WPOPDPsPtPIPuP9P;P6PwPxQ2WPyPxQ2XPyPxPWPyPxP1PyPxQ2^PyPxQ2VPyPxQ2_PyPxQ2`PyPxPNPyPxQ1C,c?96xC19?X=6xzEkF7F7F7F7P|P~bFbHbIX14X24X34X;4X@4XA4XB4X4]X5]X6]X7]X8]X9]X:]X>]X?]X<]X=]XG]XJ]XK]Q2:PEQ1C,1qPqQ0RP}DU\l\@\g\U[\j\0\L\A^14^24^34^;4^@4^A4^B4^4]^5]^6]^7]^8]^9]^:]^>]^?]^<]^=]^G]^J]^K]P[bCbDbEb0POPDPsPtPIPuP\P;PvPwPxP<P=P=P>I0JP|P~bFbHbIQ1WP2bCbDbEb0H07FiFiFiFiFiFiQ269=HReWpWmP7P2O2n2001000010121000000W0WjP7P2O2n2011000010121000000W0Xu4P7P2O2n2011000010121100000bTbSbUWqWnP7P2O2n2001000010121000000W0WkP7P2O2n2011000010121000000W0Xv4P7P2O2n2011000010121100000bTbSbUWsWrP7P2O2n2001000010121000000W0WoP7P2O2n2001000010121000000W0WlP7P2O2n2001000010121000000W0Xw4P7P2O2n2011000010121100000bTbSWaW[P7P2O2n2001000010121000000W0W_P7P2O2n2001000010121000000X0KW]P7P2O2n2011000010121000000W0WbP7P2O2n2011000010121000000W0X`JP7P2O2n2111000010121000000W0X\iP7P2O2n2011000010121000000X0nWiXefP7P2O2n2001000010121000000W0XddP7P2O2n2001000010121000000W0XccP7P2O2n2001000010121000000W0XhaP7P2O2n2001000010121000000W0Xg`P7P2O2n2001000010121000000W0Xf_P7P2O2n2001000010121000000W0P7P2O2n2111000010121000000W0X^^P7P2O2n2011000010121000000PoQ0xPoQ0{Pop,2HBRo11oVQ1FH0DI0;?=Z8ebtUUUUUXR4XZ4o"). Qed.
Lemma RK_tlow : forall A k, t <= A -> A + k <= t + 288 -> 0 <= k -> disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind. Qed.
Lemma RK_thigh : forall A k, t + 3168 <= A -> A + k <= t + 4096 -> 0 <= k -> disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind. Qed.
Lemma RK_tstat : forall A k, t + 2768 <= A -> A + k <= t + 2800 -> 0 <= k -> (A + k <= t + 2784 \/ t + 2792 <= A) ->
  disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind. Qed.
Lemma RK_rec : forall A k, t + 288 <= A -> A + k <= t + 2768 -> 0 <= k -> (A + k <= CA \/ CA + 4 <= A) -> (A + k <= CA + 16 \/ CA + 80 <= A) ->
  disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind. Qed.
Lemma RK_reg_other : forall A k, SB <= A -> 0 <= k -> (A + k <= RB \/ RB + 4294967296 <= A) -> A + k <= SB + 137438953472 ->
  disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind. Qed.
(* [comment removed for export] *)
Lemma RK_space_c : forall A k, RB <= A -> A + k <= RB + mu -> 0 <= k ->
  (A + k <= AB \/ AB + 8 <= A) -> (A + k <= HB \/ HB + 4 <= A) ->
  disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind. Qed.
Lemma RK_gap : forall A k, RB + mu <= A -> A + k <= FA + 4 * nf -> 0 <= k -> disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind. Qed.
Lemma RK_ri : forall A k, SB + 137438953472 <= A -> A + k <= SB + 137438957568 -> 0 <= k ->
  (A + k <= RI \/ RI + 8 <= A) -> (A + k <= RI + 16 \/ RI + 32 <= A) -> (A + k <= RI + 72 \/ RI + 128 <= A) ->
  disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind. Qed.
Lemma RK_sh : forall A k, 2201439137792 <= A -> A + k <= 17594333495296 -> 0 <= k ->
  (A + k <= SHUB \/ SHUB + gr <= A) -> (A + k <= SHF0 \/ SHF1 <= A) ->
  disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind. Qed.
Lemma RK_stkhi : forall A k, sp <= A -> 0 <= k -> disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind. Qed.
End Kinds.

Lemma upd_app_right : forall {X} (l1 l2 : list X) i x, (length l1 <= i)%nat -> upd (l1 ++ l2) i x = l1 ++ upd l2 (i - length l1) x.
Proof.
  induction l1 as [|y l1 IH]; intros l2 i x Hi; cbn in *; [rewrite Nat.sub_0_r; reflexivity|].
  destruct i as [|i]; [lia|]. cbn. rewrite IH by lia. reflexivity.
Qed.
Lemma upd_app_left : forall {X} (l1 l2 : list X) i x, (i < length l1)%nat -> upd (l1 ++ l2) i x = upd l1 i x ++ l2.
Proof.
  induction l1 as [|y l1 IH]; intros l2 i x Hi; cbn in *; [lia|].
  destruct i as [|i]; [reflexivity|]. cbn. rewrite IH by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma AQdr_drop_prim : forall R L st X m c k n b1 ctx l1 l2 drained pend',
  AQdr R 0 0 L st X m -> qr_pend R = (CPrim c n, k) :: pend' ->
  x_busy X = l1 ++ bany BQuar c k n b1 ctx :: l2 -> awf L st X ->
  AQdr (qr_drop R pend') 0 0 L st (xrec st X c k l1 l2 drained) m.
Proof.
  intros R L st X m c k n b1 ctx l1 l2 drained pend' (QC & MX & TC & GL & TB & IA & CP & NUM & NT) EP XB WF.
  unfold AQdr, qr_drop. cbn [qr_loc qr_glob qr_tmp qr_ia].
  split; [exact QC|]. split; [exact MX|]. split; [exact TC|]. split; [exact GL|]. split; [exact TB|]. split; [exact IA|].
  split; [| exact (conj NUM NT)].
  exact (qcoupled_rec_drop_prim L st st X R c k n b1 ctx l1 l2 drained pend' CP EP XB WF eq_refl eq_refl).
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section P.
Variables (ASECc : list achunk -> alayout -> astate -> aconc -> amem -> Prop)
          (AD : alayout -> amem -> Prop) (AF : alayout -> list ablock -> amem -> Prop).
Definition AHr (R : qrconc) (cs : list achunk) : aholes := mkAHoles (AQdr R 0 0) (ASECc cs) AD AF.
Hypothesis HL : forall R cs, ahole_laws (AHr R cs).

(* [comment removed for export] *)
Definition rec_W (L : alayout) (sp : Z) (c k n nf mfa mfa' : Z) : list (Z * Z) :=
  let AB := aslot_addr L c k in let rz := rz_size n in let HB := AB + rz - 16 in let UB := AB + rz in
  ([(sp - 688, sp); (AB, AB + 8); (HB, HB + 4); (shad UB, shad UB + granules n); (al_t L + 2800, al_t L + 3168)]%Z)
  ++ cd_W L sp c nf mfa mfa'.

(* [comment removed for export] *)
Definition arecyc1_ret (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (X : aconc) (R : qrconc) (pend' : list (achunk * Z)) (cs : list achunk) (c k n lo : Z) (m : amem)
    (stX : astate) (X' : aconc) (RNG' : footprint) (ms' : machine_state) : Prop :=
  fp_le RNG RNG' /\ exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (mfa' : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch (rec_W L (bv_unsigned sp) c k n (c_num_freed (get_cls st c)) (c_mapped_free_array (get_cls st c)) mfa') m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ c_mapped_free_array (get_cls st c) <= mfa' <= K_FREEARR_MAX
    /\ AREP (AHr (qr_drop R pend') cs) L stX X' m' /\ arng L RNG' stX
    /\ a_cinit stX = true /\ a_live stX = a_live st /\ a_next stX = a_next st
    /\ a_qloc stX = a_qloc st /\ a_qloc_bytes stX = a_qloc_bytes st /\ a_qglob stX = a_qglob st /\ a_qglob_bytes stX = a_qglob_bytes st
    /\ a_nsec stX = a_nsec st /\ a_nres stX = a_nres st /\ a_ptr_array stX = a_ptr_array st /\ a_space_beg stX = a_space_beg st
    /\ (forall c', c' <> c -> get_cls stX c' = get_cls st c')
    /\ c_mapped_user (get_cls stX c) = c_mapped_user (get_cls st c) /\ c_allocated_user (get_cls stX c) = c_allocated_user (get_cls st c)
    /\ (forall b, In b (x_busy X') -> In b (x_busy X))
    /\ (forall b p, In b (x_busy X) -> xb_st b = BLive p -> In b (x_busy X')).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition store_rec1_stmt : Prop :=
  forall (L : alayout) (RNG RNG' : footprint) (sp : word) (m m' : amem) (st stX : astate) (X : aconc) (R : qrconc)
         (pend' : list (achunk * Z)) (cs : list achunk) (c k n b1 ctx lo : Z) (l1 l2 : list xbusy) (tail : list word),
  alayout_ok L -> arng L RNG st -> AREP (AHr R cs) L st X m ->
  qr_pend R = (CPrim c n, k) :: pend' -> x_busy X = l1 ++ bany BQuar c k n b1 ctx :: l2 ->
  ATOP <= lo -> lo <= bv_unsigned sp - RECYC1_STACK ->
  u32arr bsegs m (acache_addr L c + 16) (map (fun k => Z_to_bv 64 (acompact c k)) (xc_cache (x_cls X c)) ++ tail) ->
  (length (xc_cache (x_cls X c)) + length tail = 16)%nat ->
  recyc1_ret L RNG sp st c k n b1 ctx lo (map (fun k => Z_to_bv 64 (acompact c k)) (xc_cache (x_cls X c)) ++ tail) m stX RNG' m' ->
  exists X' mfa',
       munch (rec_W L (bv_unsigned sp) c k n (c_num_freed (get_cls st c)) (c_mapped_free_array (get_cls st c)) mfa') m m'
    /\ wmono bsegs m m'
    /\ c_mapped_free_array (get_cls st c) <= mfa' <= K_FREEARR_MAX
    /\ AREP (AHr (qr_drop R pend') cs) L stX X' m' /\ arng L RNG' stX
    /\ a_cinit stX = true /\ a_live stX = a_live st /\ a_next stX = a_next st
    /\ a_qloc stX = a_qloc st /\ a_qloc_bytes stX = a_qloc_bytes st /\ a_qglob stX = a_qglob st /\ a_qglob_bytes stX = a_qglob_bytes st
    /\ a_nsec stX = a_nsec st /\ a_nres stX = a_nres st /\ a_ptr_array stX = a_ptr_array st /\ a_space_beg stX = a_space_beg st
    /\ (forall c', c' <> c -> get_cls stX c' = get_cls st c')
    /\ c_mapped_user (get_cls stX c) = c_mapped_user (get_cls st c) /\ c_allocated_user (get_cls stX c) = c_allocated_user (get_cls st c)
    /\ (forall b, In b (x_busy X') -> In b (x_busy X))
    /\ (forall b p, In b (x_busy X) -> xb_st b = BLive p -> In b (x_busy X')).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma read_qchunk : forall L st X m c k n b1 ctx l1 l2,
  alayout_ok L -> awf L st X -> x_busy X = l1 ++ bany BQuar c k n b1 ctx :: l2 ->
  aslots L st X m c -> aslot_shadow L st X m c ->
  let S := size_of_class c in let AB := aslot_addr L c k in let rz := rz_size n in let UB := AB + rz in
     rw_cells bsegs m (UB - 16) [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 ctx)]
  /\ junk_at m UB (S - rz)
  /\ (16 < rz -> rw_cells bsegs m AB [C8 (Z_to_bv 64 AMAGIC); C8 (Z_to_bv 64 (UB - 16))] /\ junk_at m (AB + 16) (rz - 32))
  /\ rw_cells bsegs m (shad AB) [CB (Z.to_nat (shlen rz)) (repeat (Z_to_bv 8 0xfa) (Z.to_nat (shlen rz)))]
  /\ rw_cells bsegs m (shad UB) [CB (Z.to_nat (granules n)) (repeat (Z_to_bv 8 0xfd) (Z.to_nat (granules n)))]
  /\ rw_cells bsegs m (shad UB + granules n) [CB (Z.to_nat (shlen S - shlen rz - granules n)) (repeat (Z_to_bv 8 0xfa) (Z.to_nat (shlen S - shlen rz - granules n)))].
Proof.
  intros L st X m c k n b1 ctx l1 l2 ALO WF XB [SL _] [SH _]. cbv zeta.
  destruct (any_range L st X BQuar c k n b1 ctx l1 l2 XB WF) as [HC KR].
  pose proof (any_facts L st X BQuar c k n b1 ctx l1 l2 XB WF ltac:(discriminate)) as (N0 & FIT0 & B10 & AT0 & CTX0).
  specialize (SL k KR). specialize (SH k KR). rewrite (busy_of_X_self_g L st X BQuar c k n b1 ctx l1 l2 XB WF) in SL, SH.
  unfold aslot_busy in SL. cbn [xb_st xb_class xb_n xb_b1 xb_ctx bany bstate_byte xb_alloc xb_slot] in SL.
  destruct SL as (LH & [stb [E HDR]] & UJ). injection E as <-.
  replace (aslot_addr L c k + rz_size n - 16) with (aslot_addr L c k + rz_size n + -16) by lia.
  split; [exact HDR|]. split; [exact UJ|]. split; [exact LH|].
  pose proof (chunk_shadow_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as (SE & G2 & GE & G0 & GF & _).
  cbn [slot_shadow_bytes xb_n xb_st bany] in SH.
  pose proof (rz_size_facts n (proj1 N0)) as [RZ1 _].
  pose proof (shlen_nonneg (rz_size n) ltac:(lia)) as SRZ. pose proof (shlen_nonneg (n + 7) ltac:(lia)) as SG7.
  replace (Z.to_nat (shlen (size_of_class c))) with
    (Z.to_nat (shlen (rz_size n)) + Z.to_nat (granules n) + Z.to_nat (shlen (size_of_class c) - shlen (rz_size n) - granules n))%nat in SH
    by (generalize SRZ SG7 GF; clear; unfold granules; intros; lia).
  destruct (cb_split3_gen m _ _ _ _ _ _ _ ltac:(apply repeat_length) ltac:(apply repeat_length) ltac:(apply repeat_length) SH) as (SHA & SHU & SHR).
  rewrite Z2Nat.id in SHU by lia. rewrite Z2Nat.id in SHR by lia. rewrite Z2Nat.id in SHR by (generalize SG7; clear; unfold granules; intros; lia).
  rewrite <- SE in SHU, SHR.
  split; [exact SHA|]. split; [exact SHU| exact SHR].
Qed.

(* [comment removed for export] *)
Lemma pend_head_busy : forall L st X R m c n k pend',
  AQdr R 0 0 L st X m -> qr_pend R = (CPrim c n, k) :: pend' ->
  exists b1 ctx l1 l2, x_busy X = l1 ++ bany BQuar c k n b1 ctx :: l2.
Proof.
  intros L st X R m c n k pend' (_ & _ & _ & _ & _ & _ & CP & _) EP.
  destruct CP as (_ & _ & OK & _). unfold qr_entries in OK. rewrite EP in OK.
  assert (HOK : qentry_ok X (CPrim c n, k)).
  { eapply (proj1 (Forall_forall _ _) OK). rewrite !in_app_iff. right. right. right. left. reflexivity. }
  unfold qentry_ok in HOK. cbn [fst snd] in HOK. destruct HOK as (b1 & ctx & Hin).
  destruct (in_split _ _ Hin) as (l1 & l2 & E). exists b1, ctx, l1, l2. exact E.
Qed.

(* [comment removed for export] *)
Lemma nf_bound : forall L st X c, awf L st X -> 1 <= c < K_NUM_CLASSES ->
  c_num_freed (get_cls st c) <= c_allocated_user (get_cls st c) / size_of_class c
  /\ 4 * (c_num_freed (get_cls st c) + max_cached c / 2) <= K_FREEARR_MAX.
Proof.
  intros L st X c WF HC. pose proof WF as (_ & _ & _ & _ & _ & PERC & _).
  destruct (PERC c HC) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
  assert (NFA : c_num_freed (get_cls st c) <= c_allocated_user (get_cls st c) / size_of_class c).
  { rewrite <- LENF. apply NoDup_bound_length.
    - apply NoDup_app_remove_r in ND. exact ND.
    - intros k0 Hk. apply RANGE. apply in_app_iff. left. exact Hk.
    - unfold ndist in RANGE. apply Z.div_pos; [lia|]. pose proof (size_of_class_facts c HC); lia. }
  split; [exact NFA|].
  pose proof (size_of_class_pos c HC) as [SZ _]. pose proof (ARecRep.max_cached_range c) as (_ & MC & _).
  unfold K_FREEARR_MAX, K_FREEARR_OFF in *. generalize NFA A1 A2 SZ MC. clear. intros. Z.div_mod_to_equations. nia.
Qed.

(* [comment removed for export] *)
Lemma cache_vals_lt : forall L st X c tail, awf L st X -> 1 <= c < K_NUM_CLASSES ->
  (length (xc_cache (x_cls X c)) + length tail = 16)%nat ->
  Forall (fun w : word => bv_unsigned w < 2^31)
         (firstn (Z.to_nat (c_count (get_cls st c))) (map (fun k => Z_to_bv 64 (acompact c k)) (xc_cache (x_cls X c)) ++ tail)).
Proof.
  intros L st X c tail WF HC LEN. pose proof WF as (_ & _ & _ & _ & _ & PERC & _).
  destruct (PERC c HC) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
  pose proof (size_of_class_facts c HC) as [SZ16 SZM].
  rewrite firstn_app, length_map. replace (Z.to_nat (c_count (get_cls st c)) - length (xc_cache (x_cls X c)))%nat with 0%nat by lia.
  rewrite firstn_O, app_nil_r. apply Forall_forall. intros w Hw.
  assert (Hw' : In w (map (fun k => Z_to_bv 64 (acompact c k)) (xc_cache (x_cls X c)))).
  { rewrite <- (firstn_skipn (Z.to_nat (c_count (get_cls st c))) (map _ _)). apply in_app_iff. left. exact Hw. }
  apply in_map_iff in Hw'. destruct Hw' as (k0 & <- & Hk).
  pose proof (RANGE k0 ltac:(apply in_app_iff; right; apply in_app_iff; left; exact Hk)) as KR. unfold ndist in KR.
  assert (B : 0 <= acompact c k0 < 2^28).
  { unfold acompact. unfold K_FREEARR_OFF in A2. generalize KR A1 A2 SZ16 SZM; clear; intros. Z.div_mod_to_equations. nia. }
  rewrite unsigned_lit; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rec1_store : store_rec1_stmt.
Proof.
  unfold store_rec1_stmt.
  intros L RNG RNG' sp m m' st stX X R pend' cs c k n b1 ctx lo l1 l2 tail ALO ARNG AR EP XB CEIL LO CH LCH RR.
  (* [comment removed for export] *)
  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  cbn [ah_quar ah_sec ah_depot AHr] in HQ, HS, HD.
  destruct THR as (T0c & T40 & CACHES & CSTATS & [sj [STATS LSJ]] & UNW).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  destruct (any_range L st X BQuar c k n b1 ctx l1 l2 XB WF) as [HC KR].
  pose proof (any_facts L st X BQuar c k n b1 ctx l1 l2 XB WF ltac:(discriminate)) as (N0 & FIT0 & B10 & AT0 & CTX0).
  destruct (PERC c HC) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
  destruct (CLS c HC) as (RCELLS & FARR & SLOTS & SSH). destruct (AVL c HC) as [AZU AZF].
  destruct RCELLS as (MTX16 & REG & RJ4 & EXH & RJ56). destruct FARR as (FL & FJ & FSJ).
  pose proof SLOTS as SLOTS0. pose proof SSH as SSH0. destruct SLOTS as [SL UND]. destruct SSH as [SSL SUND].
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof TL1 as TL1u. pose proof TL4 as TL4u. pose proof CL1 as CL1u. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in TL1u, TL4u, CL1u.   (* [comment removed for export] *)
  pose proof (alayout_res_disj L ALO) as [SCX TSP].
  pose proof (size_of_class_facts c HC) as [SZ16 SZM].
  pose proof (ARecRep.max_cached_range c) as (MCR & MCH & MCE).
  (* [comment removed for export] *)
  destruct RR as (m1 & MU1 & WM1 & CDR & MAG' & HDR' & SHU'). cbv zeta in MU1.
  destruct CDR as (FPLE & drained & mfa' & sj' & sta' & DR & GCX & STE & MFD & NEWB & NEWM & NEWMOD & MU2 & WM2 & MI' & ST' & RECS' & RECc' & CH' & MTX' & REG' & J72' & STATS' & LSJ' & STA' & DRA & FJ' & AZF' & MC').
  unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in *.
  change (2^37) with 137438953472 in *.
  (* [comment removed for export] *)
  set (S := size_of_class c) in *. set (half := max_cached c / 2) in *.
  set (mu := c_mapped_user (get_cls st c)) in *. set (au := c_allocated_user (get_cls st c)) in *.
  set (nf := c_num_freed (get_cls st c)) in *. set (mfa := c_mapped_free_array (get_cls st c)) in *. set (cnt := c_count (get_cls st c)) in *.
  set (nd := ndist st c) in *.
  set (nf' := if drained then nf + half else nf) in *. set (cnt' := if drained then cnt - half + 1 else cnt + 1) in *.
  set (X' := xrec st X c k l1 l2 drained).
  set (AB := aslot_addr L c k) in *. set (rz := rz_size n) in *.
  assert (GEO : aregion_info L c = al_space_beg L + 137438953472 + c * 128 /\ aregion L c = al_space_beg L + c * 4294967296
                /\ afreearr L c = al_space_beg L + c * 4294967296 + 3758096384 /\ acache_addr L c = al_t L + 208 + c * 80).
  { unfold aregion_info, afreearr, aregion, acache_addr, K_REGION, K_FREEARR_OFF, K_SPACE_SIZE, ARI_STRIDE. change (2^32) with 4294967296. change (2^37) with 137438953472. repeat split; reflexivity. }
  destruct GEO as (RIE & RBE & FAE & CAE).
  set (RB := aregion L c) in *. set (FA := afreearr L c) in *. set (RI := aregion_info L c) in *. set (CA := acache_addr L c) in *.
  (* [comment removed for export] *)
  assert (MCle : forall c', max_count st c' <= max_cached c') by (intros c'; unfold max_count; pose proof (ARecRep.max_cached_range c'); destruct (a_cinit st); lia).
  assert (DRC : if drained then cnt = max_cached c else cnt < max_cached c).
  { rewrite DR. pose proof (MCle c) as M. unfold max_count in CNTB, M. fold cnt in CNTB.
    destruct (a_cinit st); cbn [andb]; [destruct (Z.eqb_spec cnt (max_cached c)); [exact e| lia] | lia]. }
  assert (HALF : 1 <= half <= 8 /\ max_cached c = 2 * half) by (subst half; clear -MCR MCH MCE; lia). destruct HALF as [HALF MC2].
  assert (CNT16 : 0 <= cnt <= 16 /\ cnt' - 1 <= cnt /\ 1 <= cnt' <= 16 /\ Z.of_nat (length (xc_cache (x_cls X c))) = cnt /\ nf <= nf' <= nf + 8).
  { subst cnt' nf'. fold cnt in CNTB, LENC. pose proof (MCle c). destruct drained; clear -CNTB LENC DRC HALF MC2 MCR H; lia. }
  destruct CNT16 as (CNT16 & CNTle & CNT1 & LENCc & NFle).
  (* [comment removed for export] *)
  set (st_r := put_cls c (mkAClass mu au nf' mfa' cnt') (init_cache st)) in *.
  assert (STR : stX = st_r) by (rewrite STE, GCX; reflexivity). subst stX.
  pose proof (init_cache_fields st) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11).
  assert (GR : get_cls st_r c = mkAClass mu au nf' mfa' cnt') by (subst st_r; apply get_cls_put_cls_eq).
  assert (GO : forall c', c' <> c -> get_cls st_r c' = get_cls st c') by (intros c' NE; subst st_r; rewrite (get_cls_put_cls_ne c c') by exact NE; apply init_cache_cls).
  assert (CIR : a_cinit st_r = true) by (subst st_r; cbn; exact E11).
  assert (NDR : ndist st_r c = nd) by (unfold ndist; rewrite GR; reflexivity).
  assert (EF : a_live st_r = a_live st /\ a_next st_r = a_next st /\ a_qloc st_r = a_qloc st /\ a_qloc_bytes st_r = a_qloc_bytes st
               /\ a_qglob st_r = a_qglob st /\ a_qglob_bytes st_r = a_qglob_bytes st /\ a_nsec st_r = a_nsec st /\ a_nres st_r = a_nres st
               /\ a_ptr_array st_r = a_ptr_array st /\ a_space_beg st_r = a_space_beg st).
  { subst st_r. destruct (put_cls_fields c (mkAClass mu au nf' mfa' cnt') (init_cache st)) as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & _).
    rewrite P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, E1, E2, E3, E4, E5, E6, E7, E8, E9, E10. repeat split; reflexivity. }
  destruct EF as (EF1 & EF2 & EF3 & EF4 & EF5 & EF6 & EF7 & EF8 & EF9 & EF10).
  (* [comment removed for export] *)
  pose proof (slot_geo L st X c k ALO WF HC KR) as (_ & _ & AL16 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & R8 & M8).
  fold S AB RB mu au in AL16, G1, G2, G3, G4, G5, G6, G7, G8, R8, M8.
  pose proof (rz_size_facts n (proj1 N0)) as [RZ1 RZ2]. fold rz in RZ1, RZ2.
  pose proof (rounded_size_facts n (proj1 N0)) as (RS1 & RS2 & RS3 & RS4 & RS5).
  assert (FITr : rz + n <= S /\ rz <= S) by (subst S rz; clear -FIT0 RS1 RZ1 N0; lia). destruct FITr as [FITr RZS].
  pose proof (chunk_shadow_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as (SE & SG2 & GE & SG0 & SGF & SHLO1 & SHHI1 & SHR1 & SHR2).
  fold S AB rz RB mu in SE, SG2, GE, SG0, SGF, SHLO1, SHHI1, SHR1, SHR2.
  (* [comment removed for export] *)
  assert (AU8 : au mod 8 = 0).
  { pose proof (proj2 (Z.div_exact au S ltac:(clear -SZ16; lia)) A3) as EA. pose proof (proj2 (Z.div_exact S 16 ltac:(clear; lia)) SZM) as ES.
    rewrite ES in EA at 1. rewrite EA. replace (16 * (S / 16) * (au / S)) with ((2 * (S / 16) * (au / S)) * 8) by (clear; lia). apply Z_mod_mult. }
  set (SHUB := shad (AB + rz)) in *. set (SHF0 := shad (FA + mfa)) in *. set (SHF1 := SHF0 + shlen (mfa' - mfa)) in *.
  assert (SHE : SHF1 = shad (FA + mfa') /\ shad FA + shlen mfa = SHF0 /\ shad AB + shlen S <= shad (RB + au) /\ shad (RB + au) <= shad FA /\ shad FA <= SHF0 /\ SHF0 <= SHF1
                /\ SHF1 + shlen (536870912 - mfa') = shad (RB + 4294967296) /\ shad (RB + 4294967296) <= 17594333495296
                /\ shad RB = shad (al_space_beg L) + c * 536870912 /\ shad (RB + 4294967296) = shad (al_space_beg L) + (c + 1) * 536870912
                /\ shad (al_space_beg L) + 32 * 536870912 <= 17594333495296 /\ 2201439137792 <= shad RB /\ shad RB <= shad AB
                /\ shad (RB + au) + shlen (mu - au) = shad (RB + mu) /\ shad (RB + mu) <= shad FA
                /\ shad (RB + mu) + shlen (3758096384 - mu) = shad FA /\ SHUB = shad AB + shlen rz).
  { subst SHUB SHF1 SHF0. clearbody S mu au nf mfa nd RB FA RI CA AB rz half cnt nf' cnt'.
    generalize R8 AL16 SZM M8 A7 NEWMOD AU8 G1 G2 A1 A2 A5 A6 NEWB NEWM HC SP1 SP2 SP3 SE RBE FAE SZ16. clear. intros.
    rewrite !shad_div, !shlen_div in *. unfold ASHOFF in *. Z.div_mod_to_equations. lia. }
  destruct SHE as (SHE1 & SHE4 & SH1 & SH2 & SH3 & SH4 & SH5 & SH6 & SH9 & SH10 & SH11 & SH12 & SH13 & SH14 & SH15 & SH16 & SHE0).
  assert (KF : reckf (bv_unsigned sp) lo (al_t L) (al_ctx L) (al_space_beg L) c RB FA RI CA mu au nf mfa mfa' AB S rz (granules n) (shad AB) SHUB (shad AB + shlen S) SHF0 SHF1).
  { unfold reckf. pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
    clear -CEIL LO SPR TL1 TL1u TL4u TL2 TL4 CL1 CL1u CL2 CL3 CL5 HC CAE SP1 SP2 RBE FAE RIE TSP SCX A1 A2 A5 A6 NEWB NEWM G1 G2 RZ1 RZS SHLO1 SE SG2 SG0 GE SGF SH1 SH2 SH3 SH4 SH5 SH6 SH10 SH11.
    pose proof (shlen_nonneg (536870912 - mfa') ltac:(clear -NEWB; lia)). unfold granules in *.
    unfold iclr, AIMG_LO, AIMG_HI in *; repeat match goal with H : _ /\ _ |- _ => destruct H end; repeat split; first [assumption | lia].   (* [comment removed for export] *) }
  assert (MUALL : munch (Wk (bv_unsigned sp) AB (AB + rz - 16) SHUB (granules n) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) m m').
  { eapply munch_trans; [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MU2]].
    - unfold sub_fp. intros x Hx. apply outside_app in Hx. destruct Hx as [H13 _]. subst AB rz SHUB. cbn [outside] in H13 |- *.
      pose proof (bv_unsigned_in_range 64 sp). clear -H13 H. lia.
    - unfold sub_fp, cd_W. cbv zeta. fold nf mfa CA FA RI. intros x Hx. apply outside_app in Hx. destruct Hx as [H13 HW].
      apply outside_app. split; [cbn [outside] in H13 |- *; clear -H13; lia|]. apply outside_app. split; [exact HW|].
      subst SHF0 SHF1. cbn [outside] in H13 |- *. clear -H13. lia. }
  pose proof (wmono_trans _ _ _ _ WM1 WM2) as WMALL.
  assert (ICW_far : forall A k, (A + k <= al_t L \/ al_t L + 4096 <= A) -> disjoint_from (ic_W L 1 31) A k).
  { intros A k0 HA. apply ic_W_disjoint_gen; [unfold acache_addr; clear -HA; lia | clear; cbn; lia | clear; lia]. }
  assert (ICW_t : forall A k, (A + k <= al_t L + 292 \/ al_t L + 2768 <= A) -> disjoint_from (ic_W L 1 31) A k).
  { intros A k0 HA. apply ic_W_disjoint_gen; [unfold acache_addr; clear -HA; lia | clear; cbn; lia | clear; lia]. }
  (* [comment removed for export] *)
  destruct (read_qchunk L st X m c k n b1 ctx l1 l2 ALO WF XB SLOTS0 SSH0) as (_ & UJ & LH & SHA & _ & SHR).
  fold S AB rz in UJ, LH, SHA, SHR. rewrite <- ?SHE0 in SHR.
  assert (HBE : AB + rz + -16 = AB + rz - 16) by (clear; lia).
  (* [comment removed for export] *)
  assert (CPT : (AB - RB) / 16 = acompact c k).
  { subst AB RB. unfold aslot_addr, acompact. fold S. pose proof (proj2 (Z.div_exact S 16 ltac:(clear; lia)) SZM) as ES.
    set (q := S / 16) in ES. replace (aregion L c + k * S - aregion L c) with (k * q * 16) by (rewrite ES; clear; nia). rewrite Z.div_mul by (clear; lia). reflexivity. }
  rewrite CPT in CH'.
  (* [comment removed for export] *)
  assert (RCUT : drained = true -> rcut st c = Z.to_nat (cnt - half) /\ (Z.to_nat (cnt - half) < length (xc_cache (x_cls X c)))%nat /\ Z.to_nat (cnt' - 1) = Z.to_nat (cnt - half)).
  { intros D. unfold rcut, rcnt, rhalf. fold cnt half. subst cnt'. rewrite D in DRC |- *. split; [reflexivity|]. clear -LENCc DRC HALF MC2. split; lia. }
  (* [comment removed for export] *)
  assert (ACc : acache_cells L st_r X' m' c).
  { unfold acache_cells. cbv zeta. fold CA. rewrite GR. cbn [c_count]. unfold max_count. rewrite CIR. subst X'. rewrite (xrec_cls_self st X c k l1 l2 drained). cbn [xc_cache].
    unfold rcache'. pose proof RCUT as RC. destruct drained.
    - destruct (RC eq_refl) as (RC1 & RC2 & RC3). rewrite RC1. rewrite RC3 in CH'.
      exists (skipn (Datatypes.S (Z.to_nat (cnt - half))) (map (fun k0 => Z_to_bv 64 (acompact c k0)) (xc_cache (x_cls X c))) ++ tail).
      split; [exact RECc'|]. split.
      + rewrite upd_app_left in CH' by (rewrite length_map; exact RC2). rewrite upd_firstn_skipn in CH' by (rewrite length_map; exact RC2).
        rewrite map_app, <- List.firstn_map. cbn [map]. rewrite <- !app_assoc in CH' |- *. cbn [app] in CH' |- *. exact CH'.
      + rewrite !length_app, length_skipn, length_map, length_firstn. cbn [length]. clear -RC2 LCH. lia.
    - assert (TL : exists t0 tail', tail = t0 :: tail').
      { destruct tail as [|t0 tail']; [exfalso| exists t0, tail'; reflexivity]. cbn [length] in LCH. clear -LCH LENCc DRC MCR. lia. }
      destruct TL as (tw & tail' & ->). exists tail'.
      split; [exact RECc'|]. split.
      + subst cnt'. replace (Z.to_nat (cnt + 1 - 1)) with (length (map (fun k0 => Z_to_bv 64 (acompact c k0)) (xc_cache (x_cls X c)))) in CH' by (rewrite length_map; clear -LENCc; lia).
        rewrite upd_app_right, Nat.sub_diag in CH' by (clear; lia). cbn [upd] in CH'. rewrite map_app. cbn [map]. rewrite <- app_assoc. cbn [app]. exact CH'.
      + rewrite length_app. cbn [length] in LCH |- *. clear -LCH. lia. }
  (* [comment removed for export] *)
  assert (RCc : aregion_cells L st_r m' c).
  { unfold aregion_cells. cbv zeta. fold RI. rewrite GR. cbn [c_num_freed c_mapped_free_array c_allocated_user c_mapped_user].
    pose proof MTX16 as M2. rw_split M2 1%nat M2a M2b. clear M2a.
    eapply cells_frame in M2b; [| exact MUALL | exact WMALL | cbn [cells_size csize Nat.add];
      apply dj_app; [eapply (RK_ri _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RIE; clear -HC SP1; lia | apply ICW_far; rewrite RIE; clear -HC SP1 TSP; lia]].
    split. { rw_join MTX' M2b M16. exact M16. }
    split; [exact REG'|].
    split. { eapply junk_frame; [exact RJ4 | exact MUALL | exact WMALL |]. intros _.
             apply dj_app; [eapply (RK_ri _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RIE; clear -HC SP1; lia | apply ICW_far; rewrite RIE; clear -HC SP1 TSP; lia]. }
    split; [| exact J72'].
    eapply cells_frame; [exact EXH | exact MUALL | exact WMALL |]. cbn [cells_size csize Nat.add].
    apply dj_app; [eapply (RK_ri _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RIE; clear -HC SP1; lia | apply ICW_far; rewrite RIE; clear -HC SP1 TSP; lia]. }
  assert (FAB : 2201439137792 <= shad FA /\ SHF1 <= 17594333495296 /\ SHUB + granules n <= shad FA /\ 0 <= shlen mfa /\ 0 <= shlen S
                /\ 0 <= shlen (mu - au) /\ 0 <= shlen (3758096384 - mu)).
  { pose proof (shlen_nonneg mfa ltac:(clear -A5 A6; lia)). pose proof (shlen_nonneg S ltac:(clear -SZ16; lia)). pose proof (shlen_nonneg (536870912 - mfa') ltac:(clear -NEWB; lia)).
    pose proof (shlen_nonneg (mu - au) ltac:(clear -A1; lia)). pose proof (shlen_nonneg (3758096384 - mu) ltac:(clear -A2; lia)).
    clear -H H0 H1 H2 H3 SH12 SH13 SH1 SH2 SH3 SH4 SH5 SH6 SGF SHE0 SG0 GE. lia. }
  destruct FAB as (FB1 & FB2 & FB3 & FB4 & FB5 & FB6 & FB7).
  assert (SHB : shad RB <= SHUB /\ SHF1 <= shad (RB + 4294967296) /\ 0 <= granules n) by (clear -SH13 SHE0 SG2 SH5 FB2 GE SG0 NEWB; pose proof (shlen_nonneg (536870912 - mfa') ltac:(lia)); lia).
  destruct SHB as (SB1 & SB2 & SB3).
  (* [comment removed for export] *)
  assert (FAc : afreearray L st_r X' m' c).
  { unfold afreearray. cbv zeta. fold FA. rewrite GR. cbn [c_num_freed c_mapped_free_array]. subst X'. rewrite (xrec_cls_self st X c k l1 l2 drained). cbn [xc_free].
    assert (FL' : u32arr bsegs m' FA (map (fun k0 : Z => Z_to_bv 64 (acompact c k0)) (xc_free (x_cls X c)))).
    { eapply u32arr_frame; [exact FL | exact MUALL | exact WMALL |]. rewrite length_map, LENF. fold nf.
      apply dj_app; [eapply (RK_gap _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?FAE, ?RBE; clear -A1 A2 A5; lia | apply ICW_far; rewrite FAE; clear -A5 A6 HC TSP; lia]. }
    split; [| split; [exact FJ'|]].
    - unfold rfree'. pose proof RCUT as RC. destruct drained; [| exact FL'].
      destruct (RC eq_refl) as (RC1 & RC2 & RC3). rewrite RC1, map_app. apply u32arr_app; [exact FL'|].
      rewrite length_map, LENF. fold nf. specialize (DRA eq_refl).
      rewrite skipn_app, List.skipn_map, length_map in DRA. replace (Z.to_nat (cnt - half) - length (xc_cache (x_cls X c)))%nat with 0%nat in DRA by (clear -RC2; lia).
      rewrite skipn_O, firstn_app, length_map, length_skipn in DRA.
      replace (Z.to_nat half - (length (xc_cache (x_cls X c)) - Z.to_nat (cnt - half)))%nat with 0%nat in DRA by (clear -RC2 LENCc HALF MC2 DRC; lia).
      rewrite firstn_O, app_nil_r, firstn_all2 in DRA by (rewrite length_map, length_skipn; clear -RC2 LENCc HALF MC2 DRC; lia). exact DRA.
    - assert (FS1 : junk_at m' (shad FA) (shlen mfa)).
      { eapply junk_frame; [exact FSJ | exact MUALL | exact WMALL |]. intros _.
        apply dj_app; [eapply (RK_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -FB1 FB2 FB3 FB4 SHE4 SH3 SH4; lia
                      | apply ICW_far; clear -FB2 SHE4 SH3 SH4 TL1 TL1u TL4u FB1 FB4 FB5 FB6 FB7 SG2 SG0 GE SGF SH10 SH11 SH12 SH13 SH1 SH2 SH3; lia]. }
      destruct MFD as [Emfa|(_ & _ & Emfa & FI & _)].
      + rewrite Emfa. exact FS1.
      + replace (shlen mfa') with (shlen mfa + shlen (mfa' - mfa)) by (rewrite !shlen_div; clear -A7 NEWMOD NEWM A5 A6; Z.div_mod_to_equations; lia).
        apply junk_merge; [exact FS1 | rewrite SHE4; eapply fill_is_junk; exact FI | rewrite shlen_div; clear -A5 A6; Z.div_mod_to_equations; lia | rewrite shlen_div; clear -NEWM; Z.div_mod_to_equations; lia]. }
  (* [comment removed for export] *)
  assert (HBK : 16 < rz -> 32 <= rz) by (intros H16; clear -RZ2 H16; Z.div_mod_to_equations; lia).
  assert (SLc : aslots L st_r X' m' c).
  { eapply (aslots_update L _ m m' MUALL WMALL st st_r X X' c k); [exact SLOTS0 | exact NDR | rewrite GR; reflexivity | rewrite GR; reflexivity | | |].
    - intros k' Hk' NE'. subst X'. rewrite (busy_of_xrec_other L st X BQuar c k n b1 ctx l1 l2 drained XB WF) by (right; congruence). split; [reflexivity|]. split.
      + destruct (slot_in_region L st c k' ltac:(clear -SZ16; fold S; lia) ltac:(clear -A1; fold au; lia) Hk') as (Q1 & Q2 & Q3). fold RB S au in Q1, Q2, Q3.
        pose proof (slots_disjoint L c k' k ltac:(clear -Hk'; lia) (proj1 KR) NE' ltac:(clear -SZ16; fold S; lia)) as DJ. fold S AB in DJ.
        apply dj_app; [eapply (RK_space_c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -Q1 Q2 A1 SZ16 DJ RZ1 RZS; lia | apply ICW_far; clear -Q1 Q2 A1 A2 RBE HC TSP; lia].
      + intros b Hb. destruct (busy_of_Some_facts X c k' b Hb) as (BIn & BC & BK). split; [exact BC|]. split; [exact BK|]. exact (awf_fits L st X b WF BIn).
    - intros POS. apply dj_app; [eapply (RK_space_c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -POS A1 G2 SZ16 RZ1 RZS; lia | apply ICW_far; clear -A1 A2 RBE HC TSP; lia].
    - intros _. subst X'. rewrite (busy_of_xrec_self L st X BQuar c k n b1 ctx l1 l2 drained XB WF). fold S AB.
      (* [comment removed for export] *)
      assert (UJ' : junk_at m' (AB + rz) (S - rz)).
      { eapply junk_frame; [exact UJ | exact MUALL | exact WMALL |]. intros POS.
        apply dj_app; [eapply (RK_space_c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -POS G1 G2 A1 RZ1 RZS; lia | apply ICW_far; clear -G1 G2 A1 A2 RZ1 RZS RBE HC TSP; lia]. }
      pose proof (junk_of_cells m' _ _ HDR') as JH. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in JH. fold AB rz in JH. rewrite ?HBE in JH.
      change (Z.of_nat 16) with 16 in JH.
      destruct (Z.lt_ge_cases 16 rz) as [RZG|RZE].
      + specialize (HBK RZG). destruct (LH RZG) as [_ LJ]. pose proof (junk_of_cells m' _ _ (MAG' RZG)) as JM. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in JM. change (Z.of_nat 16) with 16 in JM.
        assert (LJ' : junk_at m' (AB + 16) (rz - 32)).
        { eapply junk_frame; [exact LJ | exact MUALL | exact WMALL |]. intros POS.
          apply dj_app; [eapply (RK_space_c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -POS G1 G2 A1 RZ1 RZS; lia | apply ICW_far; clear -G1 G2 A1 A2 RZ1 RZS RBE HC TSP; lia]. }
        replace S with (16 + ((rz - 32) + (16 + (S - rz)))) by (clear; lia).
        apply junk_merge; [exact JM | | clear; lia | clear -HBK RZS; lia].
        apply junk_merge; [exact LJ' | | clear -HBK; lia | clear -RZS; lia].
        replace (AB + 16 + (rz - 32)) with (AB + rz - 16) by (clear; lia).
        apply junk_merge; [exact JH | | clear; lia | clear -RZS; lia].
        replace (AB + rz - 16 + 16) with (AB + rz) by (clear; lia). exact UJ'.
      + assert (RZ16 : rz = 16) by (clear -RZE RZ1; lia). rewrite RZ16 in JH, UJ'.
        replace (AB + 16 - 16) with AB in JH by (clear; lia).
        replace S with (16 + (S - 16)) by (clear; lia). apply junk_merge; [exact JH | exact UJ' | clear; lia | clear -RZS RZ16; lia]. }
  (* [comment removed for export] *)
  assert (SSc : aslot_shadow L st_r X' m' c).
  { eapply (aslot_shadow_update L _ m m' MUALL WMALL st st_r X X' c k); [exact SSH0 | exact NDR | rewrite GR; reflexivity | rewrite GR; reflexivity | | | | exact FB5].
    - intros k' Hk' NE'. fold S. subst X'. rewrite (busy_of_xrec_other L st X BQuar c k n b1 ctx l1 l2 drained XB WF) by (right; congruence). split; [reflexivity|].
      destruct (slot_in_region L st c k' ltac:(clear -SZ16; fold S; lia) ltac:(clear -A1; fold au; lia) Hk') as (Q1 & Q2 & Q3). fold RB S au in Q1, Q2, Q3.
      pose proof (slots_disjoint L c k' k ltac:(clear -Hk'; lia) (proj1 KR) NE' ltac:(clear -SZ16; fold S; lia)) as DJ. fold S AB in DJ.
      pose proof (slot_aligned L c k' SAL HC) as AL'. fold S in AL'.
      assert (B : 2201439137792 <= shad (aslot_addr L c k') /\ shad (aslot_addr L c k') + shlen S <= shad (RB + au)
                  /\ (shad (aslot_addr L c k') + shlen S <= shad AB \/ shad AB + shlen S <= shad (aslot_addr L c k'))).
      { rewrite !shad_div, !shlen_div in *. unfold ASHOFF in *. clear -Q1 Q2 DJ AL' AL16 SZM SH12 R8 AU8. Z.div_mod_to_equations. lia. }
      apply dj_app; [eapply (RK_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -B FB2 FB5 SH2 SH3 SH4 SGF SHE0 SG2; lia | apply ICW_far; clear -B FB2 SH2 SH3 SH4 TL1 TL1u TL4u FB1 FB4 FB5 FB6 FB7 SG2 SG0 GE SGF SH10 SH11 SH12 SH13 SH1 SH2 SH3; lia].
    - intros POS. fold RB mu au in POS |- *. apply dj_app; [eapply (RK_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -POS FB1 FB2 FB3 FB4 FB5 FB6 FB7 SH1 SH2 SH3 SH4 SH10 SH11 SH12 SH13 SH14 SH15 SGF SHE0 SG2 SG0 GE; lia
                                | apply ICW_far; clear -POS FB2 SH1 SH2 SH3 SH4 SH12 SH13 SH14 SH15 TL1 TL1u TL4u FB1 FB4 FB5 FB6 FB7 SG2 SG0 GE SGF SH10 SH11 SH12 SH13 SH1 SH2 SH3; lia].
    - intros _. subst X'. rewrite (busy_of_xrec_self L st X BQuar c k n b1 ctx l1 l2 drained XB WF). cbn [slot_shadow_bytes]. fold S AB.
      assert (SHA' : rw_cells bsegs m' (shad AB) [CB (Z.to_nat (shlen rz)) (repeat (Z_to_bv 8 250) (Z.to_nat (shlen rz)))]).
      { eapply cells_frame; [exact SHA | exact MUALL | exact WMALL |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by (clear -SG2; lia).
        apply dj_app; [eapply (RK_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -SG2 SH12 SH13 FB2 SH1 SH2 SH3 SH4 SGF SHE0 FB5 GE SG0; lia
                      | apply ICW_far; clear -SG2 SHE0 SGF FB5 SH1 SH2 SH3 SH4 FB2 TL1 TL1u TL4u FB1 FB4 FB5 FB6 FB7 SG2 SG0 GE SGF SH10 SH11 SH12 SH13 SH1 SH2 SH3 GE SG0; lia]. }
      assert (SHR' : rw_cells bsegs m' (SHUB + granules n) [CB (Z.to_nat (shlen S - shlen rz - granules n)) (repeat (Z_to_bv 8 250) (Z.to_nat (shlen S - shlen rz - granules n)))]).
      { eapply cells_frame; [exact SHR | exact MUALL | exact WMALL |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by (clear -SGF GE SG0; lia).
        apply dj_app; [eapply (RK_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -SG2 SH12 SH13 FB2 SH1 SH2 SH3 SH4 SGF SHE0 GE SG0; lia
                      | apply ICW_far; clear -SG2 SHE0 SGF GE SG0 SH1 SH2 SH3 SH4 FB2 TL1 TL1u TL4u FB1 FB4 FB5 FB6 FB7 SG2 SG0 GE SGF SH10 SH11 SH12 SH13 SH1 SH2 SH3 SH12 SH13; lia]. }
      assert (C2pre : rw_cells bsegs m' (shad AB + Z.of_nat (Z.to_nat (shlen rz))) [CB (Z.to_nat (granules n)) (repeat (Z_to_bv 8 250) (Z.to_nat (granules n)))]).
      { rewrite Z2Nat.id by (clear -SG2; lia). rewrite <- SHE0. exact SHU'. }
      pose proof (cb_app m' _ _ _ _ _ SHA' C2pre) as C2.
      assert (C3pre : rw_cells bsegs m' (shad AB + Z.of_nat (Z.to_nat (shlen rz) + Z.to_nat (granules n))) [CB (Z.to_nat (shlen S - shlen rz - granules n)) (repeat (Z_to_bv 8 250) (Z.to_nat (shlen S - shlen rz - granules n)))]).
      { replace (shad AB + Z.of_nat (Z.to_nat (shlen rz) + Z.to_nat (granules n))) with (SHUB + granules n) by (rewrite SHE0; clear -SG2 GE SG0; lia). exact SHR'. }
      pose proof (cb_app m' _ _ _ _ _ C2 C3pre) as C3.
      rewrite <- !repeat_app in C3.
      replace (Z.to_nat (shlen rz) + Z.to_nat (granules n) + Z.to_nat (shlen S - shlen rz - granules n))%nat with (Z.to_nat (shlen S)) in C3 by (clear -SG2 GE SG0 SGF; lia).
      exact C3. }
  (* [comment removed for export] *)
  assert (AVc : ashadow_avail L st_r m' c).
  { unfold ashadow_avail. cbv zeta. rewrite GR. cbn [c_mapped_user c_mapped_free_array]. fold RB FA. split; [| exact AZF'].
    eapply azero_frame; [exact AZU | exact MUALL | exact WMALL |]. unfold K_FREEARR_OFF. intros POS.
    apply dj_app; [eapply (RK_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -POS FB2 FB5 FB6 FB7 SH1 SH2 SH3 SH4 SH12 SH13 SH14 SH15 SH16 SGF SHE0 SG2; lia
                  | apply ICW_far; clear -POS FB2 FB5 FB6 FB7 SH1 SH2 SH3 SH4 SH12 SH13 SH14 SH15 SH16 TL1 TL1u TL4u FB1 FB4 FB5 FB6 FB7 SG2 SG0 GE SGF SH10 SH11 SH12 SH13 SH1 SH2 SH3; lia]. }
  (* [comment removed for export] *)
  assert (CLS' : forall c', 1 <= c' < 32 -> c' <> c ->
            aregion_cells L st_r m' c' /\ afreearray L st_r X' m' c' /\ aslots L st_r X' m' c' /\ aslot_shadow L st_r X' m' c' /\ ashadow_avail L st_r m' c' /\ acache_cells L st_r X' m' c').
  { intros c' Hc' NE. destruct (CLS c' Hc') as (RC2 & FA2 & SL2 & SS2). pose proof (AVL c' Hc') as AV2. destruct (CACHES c' Hc') as [tl (RH & RCH & RLEN)].
    destruct (PERC c' Hc') as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & BLENF & BLENC & BCNTB & BND & BRANGE).
    pose proof (size_of_class_facts c' Hc') as [SZ' SZM'].
    pose proof (GO c' NE) as G'.
    pose proof (region_other_geo L c c' ALO HC Hc' NE) as REGD. fold RB in REGD.
    destruct REGD as (RD1 & RD2 & RD3 & RD4 & RD5 & RD6 & RD7 & RD8 & RD9 & RD10 & RD11).
    assert (DJR : forall A k, aregion L c' <= A -> A + k <= aregion L c' + 4294967296 -> 0 <= k ->
                   disjoint_from (Wk (bv_unsigned sp) AB (AB + rz - 16) SHUB (granules n) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) A k).
    { intros A k0 HA HB Hk. apply dj_app; [eapply (RK_reg_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -HA HB Hk RD1 RD2 RD3; lia
                                         | apply ICW_far; clear -HA HB Hk RD1 RD3 TSP; lia]. }
    assert (DJS : forall A k, shad (aregion L c') <= A -> A + k <= shad (aregion L c') + shlen 4294967296 -> 0 <= k ->
                   disjoint_from (Wk (bv_unsigned sp) AB (AB + rz - 16) SHUB (granules n) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) A k).
    { intros A k0 HA HB Hk. apply dj_app; [| apply ICW_far; clear -HA HB Hk RD9 RD10 TL1u; lia].
      destruct RD8 as [LOW|HIGH].
      - eapply (RK_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -HA HB Hk LOW RD9 RD10 SB1 SB2 SB3 SH3 SH4 SH2 SH1 SH13 FB5 SHE0 SG2; lia.
      - eapply (RK_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -HA HB Hk HIGH RD9 RD10 SB1 SB2 SB3 SH3 SH4 SH2 SH1 SH13 FB5 SHE0 SG2 SGF FB3; lia. }
    assert (DJI : disjoint_from (Wk (bv_unsigned sp) AB (AB + rz - 16) SHUB (granules n) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) (aregion_info L c') 128).
    { apply dj_app; [eapply (RK_ri _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RD5, ?RIE; clear -Hc' NE HC; lia | apply ICW_far; rewrite ?RD5; clear -Hc' SP1 TSP; lia]. }
    split; [| split; [| split; [| split; [| split]]]].
    - eapply (aregion_cells_frame L _ m m' MUALL WMALL st); [exact RC2 | rewrite G'; reflexivity | rewrite G'; reflexivity | rewrite G'; reflexivity | rewrite G'; reflexivity | exact DJI].
    - eapply (afreearray_frame L _ m m' MUALL WMALL st st_r X); [exact FA2 | rewrite G'; reflexivity | rewrite G'; reflexivity | subst X'; rewrite (xrec_cls_other st X c k l1 l2 drained c' NE); reflexivity
        | exact BLENF | exact B5 | | clear -B6; lia |].
      + apply DJR; rewrite ?RD4; clear -B5 B6 B2; lia.
      + apply DJS; rewrite ?RD11, ?shlen_div; try (clear -B2 B5 B6; Z.div_mod_to_equations; lia).
    - eapply (aslots_update L _ m m' MUALL WMALL st st_r X _ c' (-1)); [exact SL2 | unfold ndist; rewrite G'; reflexivity | rewrite G'; reflexivity | rewrite G'; reflexivity | | |].
      + intros k0 Hk _. subst X'. rewrite (busy_of_xrec_other L st X BQuar c k n b1 ctx l1 l2 drained XB WF) by (left; exact (not_eq_sym NE)). split; [reflexivity|]. split.
        * destruct (slot_in_region L st c' k0 ltac:(clear -SZ'; lia) ltac:(clear -B1; lia) Hk) as (Q1 & Q2 & Q3).
          apply DJR; [exact Q1 | clear -Q2 B1 B2; lia | clear -SZ'; lia].
        * intros b Hb. destruct (busy_of_Some_facts X c' k0 b Hb) as (BIn & BC & BK). split; [exact BC|]. split; [exact BK|]. exact (awf_fits L st X b WF BIn).
      + intros POS. apply DJR; clear -B1 B2 POS; lia.
      + intros HK. exfalso. clear -HK. lia.
    - eapply (aslot_shadow_update L _ m m' MUALL WMALL st st_r X _ c' (-1)); [exact SS2 | unfold ndist; rewrite G'; reflexivity | rewrite G'; reflexivity | rewrite G'; reflexivity | | | | rewrite shlen_div; clear -SZ'; Z.div_mod_to_equations; lia].
      + intros k0 Hk _. subst X'. rewrite (busy_of_xrec_other L st X BQuar c k n b1 ctx l1 l2 drained XB WF) by (left; exact (not_eq_sym NE)). split; [reflexivity|].
        destruct (slot_in_region L st c' k0 ltac:(clear -SZ'; lia) ltac:(clear -B1; lia) Hk) as (Q1 & Q2 & Q3).
        apply DJS.
        * apply shad_mono. exact Q1.
        * rewrite !shad_div, !shlen_div in *. clear -Q1 Q2 B1 B2 RD7. Z.div_mod_to_equations. lia.
        * rewrite shlen_div. clear -SZ'; Z.div_mod_to_equations; lia.
      + intros POS. apply DJS.
        * apply shad_mono. clear -B1; lia.
        * rewrite !shad_div, !shlen_div in *. clear -B1 B2 RD7. Z.div_mod_to_equations. lia.
        * clear -POS; lia.
      + intros HK. exfalso. clear -HK. lia.
    - eapply (ashadow_avail_frame L _ m m' MUALL WMALL st); [exact AV2 | rewrite G'; reflexivity | rewrite G'; reflexivity | |]; unfold K_FREEARR_OFF, K_FREEARR_MAX.
      + intros POS. apply DJS.
        * apply shad_mono. clear -B1; lia.
        * rewrite !shad_div, !shlen_div in *. clear -B1 B2 RD7. Z.div_mod_to_equations. lia.
        * clear -POS; lia.
      + intros POS. apply DJS.
        * apply shad_mono. rewrite RD4. clear -B5 B6; lia.
        * rewrite RD4. rewrite !shad_div, !shlen_div in *. clear -B5 B6 RD7. Z.div_mod_to_equations. lia.
        * clear -POS; lia.
    - unfold acache_cells. cbv zeta. rewrite G'. unfold max_count. rewrite CIR. subst X'. rewrite (xrec_cls_other st X c k l1 l2 drained c' NE). exists tl.
      split; [exact (RECS' c' ltac:(clear -Hc'; lia) NE)|]. split; [| exact RLEN].
      eapply u32arr_frame; [exact RCH | exact MUALL | exact WMALL |]. rewrite length_app, length_map.
      replace (Z.of_nat (length (xc_cache (x_cls X c')) + length tl)) with 16 by (clear -RLEN; lia).
      apply dj_app; [eapply (RK_rec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RD6, ?CAE; clear -Hc' NE HC; lia | change (4 * 16) with 64; apply ic_W_disjoint_chunks]. }
  (* [comment removed for export] *)
  assert (BB : forall b, In b (x_busy X') ->
      al_space_beg L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_space_beg L + 137438953472
      /\ ((xb_alloc L b + size_of_class (xb_class b) <= RB + mu /\ (xb_alloc L b + size_of_class (xb_class b) <= AB \/ AB + S <= xb_alloc L b))
          \/ xb_alloc L b + size_of_class (xb_class b) <= RB \/ RB + 4294967296 <= xb_alloc L b)).
  { intros b Hb. subst X'. pose proof (xrec_sub st X BQuar c k n b1 ctx l1 l2 drained XB b Hb) as HbX. apply In_xrec in Hb.
    destruct (BUSY b HbX) as [CLB _].
    destruct (PERC (xb_class b) CLB) as (Q1 & Q2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & QR).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact HbX| apply Z.eqb_refl]. }
    pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as (P5 & P4 & P0).
    unfold xb_alloc.
    destruct (Z.eq_dec (xb_class b) c) as [EC|NC].
    - assert (NK : xb_slot b <> k) by (intros EK; exact (key_fresh_g L st X BQuar c k n b1 ctx l1 l2 XB WF b Hb EC EK)).
      pose proof (slots_disjoint L c (xb_slot b) k (proj1 KB) (proj1 KR) NK ltac:(clear -SZ16; fold S; lia)) as DJ. fold S AB in DJ.
      rewrite EC in P5, P4, Q1, Q2 |- *. fold RB au mu S in P5, P4, Q1, Q2.
      split; [clear -P5 RBE HC; lia|]. split; [clear -P4 A1 A2 RBE HC; lia|]. left. split; [clear -P4 A1; lia| exact DJ].
    - pose proof (region_other_geo L c (xb_class b) ALO HC CLB NC) as (R1 & R2 & R3 & _). fold RB in R2.
      split; [clear -P5 R1; lia|]. split; [clear -P4 Q1 Q2 R3; lia|].
      right. destruct R2 as [D|D]; [left; clear -D P4 Q1 Q2; lia | right; clear -D P5; lia]. }
  (* [comment removed for export] *)
  assert (DJimg : forall A k, 65536 <= A -> 0 <= k -> A + k <= 6352896 ->      (* [comment removed for export] *)
            disjoint_from (Wk (bv_unsigned sp) AB (AB + rz - 16) SHUB (granules n) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) A k).
  { intros A k0 H1 H2 H3. apply dj_app; [eapply (RK_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); assumption | apply ICW_far; clear -H1 H3 TL4u; lia]. }
  assert (DJt : forall A k, al_t L <= A -> 0 <= k ->
            (A + k <= al_t L + 288 \/ (al_t L + 2768 <= A /\ A + k <= al_t L + 2784) \/ (al_t L + 2792 <= A /\ A + k <= al_t L + 2800) \/ (al_t L + 3168 <= A /\ A + k <= al_t L + 4096)) ->
            disjoint_from (Wk (bv_unsigned sp) AB (AB + rz - 16) SHUB (granules n) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) A k).
  { intros A k0 H1 H2 H3. apply dj_app; [| apply ICW_t; clear -H3; lia].
    destruct H3 as [H3|[H3|[H3|H3]]];
      [ eapply (RK_tlow _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF)
      | eapply (RK_tstat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF)
      | eapply (RK_tstat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF)
      | eapply (RK_thigh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF)]; clear -H1 H2 H3; lia. }
  assert (DJctx : forall A k, al_ctx L <= A -> A + k <= al_ctx L + 4096 -> 0 <= k ->
            disjoint_from (Wk (bv_unsigned sp) AB (AB + rz - 16) SHUB (granules n) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) A k).
  { intros A k0 H1 H2 H3. apply dj_app; [| apply ICW_far; clear -H1 H2 H3 CL5; lia].
    eapply (RK_obj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); atop_facts; clear -H1 H2 H3 CL1u CL2 CL3 CL5 SCX; unfold AIMG_HI in *; lia. }   (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (WF' : awf L st_r X').
  { subst X'. eapply (awf_xrec L st X BQuar c k n b1 ctx l1 l2 drained XB WF ltac:(intros p; discriminate) DRC st_r mfa');
      [exact EF10 | exact EF9 | exact CIR | exact EF1 | exact EF2 | exact GO | | clear -NEWB; unfold K_FREEARR_MAX; subst nf'; unfold rnf', rhalf; fold nf half; destruct drained; lia | exact NEWMOD].
    rewrite GR. unfold rnf', rcnt', rcnt, rhalf. fold nf half cnt. subst nf' cnt'. destruct drained; f_equal; lia. }
  assert (RT' : arep_rt L m').
  { eapply arep_rt_frame; [exact MUALL | exact WMALL | exact RT |]. unfold rt_hulls, ATP88, ATSD.
    repeat (apply Forall_cons; [cbn [fst snd]; first [apply DJimg; clear; lia | apply DJctx; clear; lia] |]). apply Forall_nil. }
  assert (INST' : ainstance L st_r m').
  { eapply ainstance_frame; [exact MUALL | exact WMALL | exact INST | exact EF8 | exact EF7 | | |]; apply DJimg; clear; unfold AINSTANCE; lia. }
  assert (THR' : athread L st_r X' m').
  { unfold athread. split; [| split; [| split; [| split; [| split]]]].
    - eapply cells_frame; [exact T0c | exact MUALL | exact WMALL |]. cbn [cells_size csize Nat.add]. apply DJt; clear; lia.
    - eapply cells_frame; [exact T40 | exact MUALL | exact WMALL |]. cbn [cells_size csize Nat.add]. apply DJt; clear; lia.
    - intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE]; [exact ACc | exact (proj2 (proj2 (proj2 (proj2 (proj2 (CLS' c' Hc' NE))))))].
    - apply (junk_merge m' (al_t L + 2768) 16 16); [| | clear; lia | clear; lia].
      + destruct (junk_split m (al_t L + 2768) 16 16 CSTATS ltac:(clear; lia) ltac:(clear; lia)) as [J16 _].
        eapply junk_frame; [exact J16 | exact MUALL | exact WMALL | intros _; apply DJt; clear; lia].
      + apply (junk_merge m' (al_t L + 2768 + 16) 8 8); [| | clear; lia | clear; lia].
        * replace (al_t L + 2768 + 16) with (al_t L + 2784) by (clear; lia). pose proof (junk_of_cells m' _ _ STA') as J. cbn in J. exact J.
        * destruct (junk_split m (al_t L + 2768) 24 8 CSTATS ltac:(clear; lia) ltac:(clear; lia)) as [_ J8].
          replace (al_t L + 2768 + 16 + 8) with (al_t L + 2768 + 24) by (clear; lia).
          eapply junk_frame; [exact J8 | exact MUALL | exact WMALL | intros _; apply DJt; clear; lia].
    - exists sj'. split; [exact STATS' | exact LSJ'].
    - eapply cells_frame; [exact UNW | exact MUALL | exact WMALL |]. cbn [cells_size csize Nat.add]. apply DJt; clear; lia. }
  (* [comment removed for export] *)
  pose proof (ao_space L ALO) as RSP.
  set (WH := [(bv_unsigned sp - 688, bv_unsigned sp); (al_t L + 208, al_t L + 3168); (RI, RI + 128); (AB, AB + S);
              (FA + 4 * nf, FA + 536870912); (shad AB, shad AB + shlen S); (SHF0, shad RB + 536870912)]).
  assert (MUH : munch WH m m').
  { eapply munch_weaken; [| exact MUALL]. unfold sub_fp. intros x Hx. subst WH. cbn [outside] in Hx. destruct Hx as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & _).
    apply outside_app. split.
    - cbn [outside]. clear -O1 O2 O3 O4 O5 O6 O7 RZ1 RZS SHE0 SGF SH5 SB3 FB2 NEWB CAE HC SG2 GE SG0 SH10 SH9 SHE1 NEWM A5 A6.
      pose proof (shlen_nonneg (536870912 - mfa') ltac:(lia)). repeat split; try exact I; lia.
    - apply ic_W_outside; [unfold acache_addr; clear -O2; lia | clear; cbn; lia | clear; lia]. }
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
  assert (HQ0 : AQdr (qr_drop R pend') 0 0 L st X' m) by (subst X'; eapply AQdr_drop_prim; [exact HQ | exact EP | exact XB | exact WF]).
  assert (QU : quar_untouched L X' WH).
  { unfold quar_untouched. subst WH. unfold AINSTANCE in *.
    repeat (apply Forall_cons; [cbn [fst snd];
      split; [clear -CEIL LO TL1 TL1u TL4u TL2 TSP SP1 SP2 RIE RBE FAE HC A1 A2 A5 G1 G2 G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 FB5 SB2 SH6 NEWB; lia|];
      split; [clear -CEIL LO TL1 TL1u TL4u TL2 TSP SP1 SP2 RIE RBE FAE HC A1 A2 A5 G1 G2 G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 FB5 SB2 SH6 NEWB; lia|];
      split; [clear -CEIL LO TL1 TL1u TL4u TL2 TSP SP1 SP2 RIE RBE FAE HC A1 A2 A5 G1 G2 G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 FB5 SB2 SH6 NEWB; lia|];
      split; [clear -CEIL LO TL1 TL1u TL4u TL2 TSP SP1 SP2 RIE RBE FAE HC A1 A2 A5 G1 G2 G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 FB5 SB2 SH6 NEWB; lia|];
      intros b Hb; destruct (BB b Hb) as (Bb1 & Bb2 & Bb3); destruct (xb_st b); [exact I| |];
      clear -Bb1 Bb2 Bb3 CEIL LO TL1 TL1u TL4u TL2 TSP SP1 SP2 RIE RBE FAE HC A1 A2 A5 G1 G2 G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 FB5 SB2 SH6 NEWB; lia |]).
    apply Forall_nil. }
  assert (QSM : quar_same st st_r X' X').
  { unfold quar_same. rewrite EF3, EF4, EF5, EF6, EF10. repeat (split; [reflexivity|]).
    split; intros b Hb; destruct (xb_st b); first [exact I | exact Hb]. }
  assert (HQ' : AQdr (qr_drop R pend') 0 0 L st_r X' m').
  { eapply AQdr_frame; [exact HQ0 | exact MUH | exact WMALL | exact QU | exact QSM]. }
  assert (SU : sec_untouched L WH).
  { unfold sec_untouched, aknown. subst WH. unfold AINSTANCE, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 4 right; left; clear -Ha CEIL LO; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 5 right; left; clear -Ha TL1 TL1u TL4u TL2; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 7 right; left; clear -Ha RSP RIE HC; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 7 right; left; clear -Ha RSP RBE HC G5 G6; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 7 right; left; clear -Ha RSP RBE FAE HC A5; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; right; left; clear -Ha HC SH9 SH10 SH11 SH13 SH1 SH2 SH3 SH4 SB2 FB5; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; right; left; clear -Ha HC SH9 SH10 SH11 SH13 SH1 SH2 SH3 FB5; lia |].
    apply Forall_nil. }
  assert (SSM : sec_same st st_r).
  { unfold sec_same. rewrite EF7, EF8, EF9, EF1. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [intros; first [apply iff_refl | clear; tauto | tauto]|].   (* [comment removed for export] *)
    rewrite (sec_chunks_of_eq st st_r EF1 EF3 EF5). apply Permutation_refl. }
  assert (HS' : ASECc cs L st_r X' m').
  { eapply (hs_frame _ (HL (qr_drop R pend') cs) L st st_r X X' m m'); [exact HS | exact MUH | exact WMALL | exact SU | exact SSM]. }
  assert (HD' : AD L m').
  { eapply (hd_frame _ (HL R cs) L m m'); [exact HD | exact MUH | exact WMALL |]. subst WH.
    pose proof (ao_nodes L ALO) as (_ & ON1 & ON3 & ONs & _). pose proof (ao_store L ALO) as (_ & OS1 & OS3 & OSs & _). unfold sclr, KLS in ONs, OSs.
    pose proof (ad_nodes_res L ALO) as DNR. pose proof (ad_store_res L ALO) as DSR. pose proof (ad_t_nodes L ALO) as DTN. pose proof (ad_t_store L ALO) as DTS.
    unfold adisj, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
    (* [comment removed for export] *)
    repeat (apply Forall_cons; [cbn [fst snd]; intros a Ha; split; [| split];
      [ clear -Ha CEIL LO TL4u TL2 SP1 SP2 RSP RIE RBE FAE HC A5 A6 NEWB G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 SB2 SH6 FB5; lia
      | clear -Ha CEIL LO TL2 SP1 SP2 RSP RIE RBE FAE HC A5 A6 NEWB G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 SB2 SH6 FB5 ON1 ON3 ONs DNR DTN; lia
      | clear -Ha CEIL LO TL2 SP1 SP2 RSP RIE RBE FAE HC A5 A6 NEWB G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 SB2 SH6 FB5 OS1 OS3 OSs DSR DTS; lia ] |]). apply Forall_nil. }
  assert (AR' : AREP (AHr (qr_drop R pend') cs) L st_r X' m').
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
    destruct AM as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & RC & RPA & RSC & RPSH).
    unfold arng. split; [exact Z1|]. split; [exact Z2|]. split; [exact Z3|]. split; [exact Z4|]. split; [exact Z5|].
    split; [exact Z6|]. split; [exact Z7|]. split; [exact Z8|]. split; [exact Z9|].
    split; [| split; [rewrite EF8; exact RPA| split; [rewrite (sec_chunks_of_eq st st_r EF1 EF3 EF5); exact RSC| exact RPSH]]].
    intros c' Hc'. cbv zeta. destruct (Z.eq_dec c' c) as [->|NE].
    - rewrite GR. cbn [c_mapped_user c_mapped_free_array]. fold RB FA.
      destruct (RC c HC) as (Q1 & Q2 & Q3 & Q4). fold RB FA mu mfa in Q1, Q2, Q3, Q4.
      split; [exact Q1|]. split; [exact Q2|]. split.
      + destruct MFD as [Emfa|(_ & _ & Emfa & _ & RF & RSF & BW)]; [rewrite Emfa; exact Q3|].
        replace mfa' with (mfa + (mfa' - mfa)) by (clear; lia). apply rng_merge; [exact BW | clear -A5 A6; lia | clear -NEWM; lia | exact Q3 | exact RF].
      + destruct MFD as [Emfa|(_ & _ & Emfa & _ & RF & RSF & BW)]; [rewrite Emfa; exact Q4|].
        assert (M8c : mfa mod 8 = 0 /\ mfa' mod 8 = 0) by (clear -A7 NEWMOD; Z.div_mod_to_equations; lia). destruct M8c as [M8c M8d].
        replace (shlen mfa') with (shlen mfa + shlen (mfa' - mfa)) by (rewrite !shlen_div; clear -M8c M8d; Z.div_mod_to_equations; lia).
        apply rng_merge; [exact BW | rewrite shlen_div; clear -A5 A6; Z.div_mod_to_equations; lia | rewrite shlen_div; clear -NEWM; Z.div_mod_to_equations; lia | exact Q4 |].
        rewrite SHE4. exact RSF.
    - rewrite (GO c' NE). exact (RC c' Hc'). }
  (* [comment removed for export] *)
  exists X', mfa'.
  split. { unfold rec_W. cbv zeta. fold AB rz. eapply munch_trans; [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MU2]].
           - unfold sub_fp. intros x Hx. apply outside_app in Hx. destruct Hx as [H5 _]. cbn [outside] in H5 |- *. subst SHUB. clear -H5. lia.
           - unfold sub_fp. intros x Hx. apply outside_app in Hx. destruct Hx as [_ HW]. exact HW. }
  split; [exact WMALL|]. split; [clear -NEWB NEWM; lia|]. split; [exact AR'|]. split; [exact ARNG'|]. split; [exact CIR|].
  split; [exact EF1|]. split; [exact EF2|]. split; [exact EF3|]. split; [exact EF4|]. split; [exact EF5|]. split; [exact EF6|].
  split; [exact EF7|]. split; [exact EF8|]. split; [exact EF9|]. split; [exact EF10|]. split; [exact GO|].
  split; [rewrite GR; reflexivity|]. split; [rewrite GR; reflexivity|].
  split; [intros b Hb; subst X'; exact (xrec_sub st X BQuar c k n b1 ctx l1 l2 drained XB b Hb)|].
  intros b p Hb Sb. subst X'. exact (xrec_live st X BQuar c k n b1 ctx l1 l2 drained XB ltac:(intros p'; discriminate) b p Hb Sb).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem arecyc1 :
  forall {RT} (k : astate -> AM RT) (Q : RT -> footprint -> machine_state -> Prop)
         (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (X : aconc) (R : qrconc) (pend' : list (achunk * Z)) (cs : list achunk)
         (c kk n CBA lo : Z) (cbs : word),
  alayout_ok L -> arng L RNG st -> AREP (AHr R cs) L st X m ->
  qr_pend R = (CPrim c n, kk) :: pend' ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - RECYC1_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 CBA -> a1 = Z_to_bv 64 (qhdr L (CPrim c n) kk) ->
  rw_cells bsegs m CBA [C8 (Z_to_bv 64 (al_t L + 208)); C8 cbs] -> bv_unsigned sp <= CBA -> CBA + 16 <= 2^47 ->
  rng RNG lo (bv_unsigned sp - lo) -> rng RNG CBA 16 ->
  (forall stX X' RNG' ms', arecyc1_ret L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st X R pend' cs c kk n lo m stX X' RNG' ms' ->
     implS bsegs RNG' (aembed ATOP (k stX)) (epostF Q) ms') ->
  implS bsegs RNG (aembed ATOP (cache_dealloc st c k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 recyc1_entry) fc None m (seg_rom bsegs)).
Proof.
  intros RT k Q L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st X R pend' cs
         c kk n CBA lo cbs ALO ARNG AR EP MI ST CEIL LO TP Ha0 Ha1 CBC CB0 CB1 RSTK RCB KONT.
  pose proof AR as AR0. destruct AR0 as (WF & RT0 & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  cbn [ah_quar ah_sec ah_depot AHr] in HQ, HS, HD.
  destruct (pend_head_busy L st X R m c n kk pend' HQ EP) as (b1 & ctx & l1 & l2 & XB).
  destruct (any_range L st X BQuar c kk n b1 ctx l1 l2 XB WF) as [HC KR].
  pose proof (any_facts L st X BQuar c kk n b1 ctx l1 l2 XB WF ltac:(discriminate)) as (N0 & FIT0 & B10 & AT0 & CTX0).
  destruct THR as (T0c & T40 & CACHES & CSTATS & [sj [STATS LSJ]] & UNW).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  destruct (PERC c HC) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
  destruct (CLS c HC) as (RCELLS & FARR & SLOTS & SSH). destruct (AVL c HC) as [AZU AZF].
  destruct RCELLS as (MTX16 & REG & RJ4 & EXH & RJ56). destruct FARR as (FL & FJ & FSJ).
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof TL1 as TL1u. pose proof TL4 as TL4u. pose proof CL1 as CL1u. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in TL1u, TL4u, CL1u.   (* [comment removed for export] *)
  pose proof (alayout_res_disj L ALO) as [SCX TSP].
  pose proof ARNG as ARNG0. destruct ARNG0 as (RIMG & RT4 & RCTX & RNO & RSTO & RRI & RFK & RSFK & RDTLS & RCLS & RPA & RSECS & RPSH).
  destruct (RCLS c HC) as (RREG & RSREG & RFA & RSFA).
  pose proof RT0 as RT1.
  destruct RT1 as (GPG & GOT & GOT80 & RIC & LS1 & REAL & IMAX4 & FLG5 & FLG & HPP & SHB & CANP & TI & TK & INI2 & LAY & MCS & OOM3
                    & PGC & HK2 & CF8 & CF34 & CSMT & T88 & TSD & LS2 & CT8 & CT).
  destruct RT2 as (DPM & MLIM & RWCS).
  destruct INST as (I32 & I48 & I64 & I72 & I112 & I680 & I984 & I40 & I56).
  (* [comment removed for export] *)
  assert (MC : m3_cells L m).
  { unfold m3_cells, poison_cells, rmap_cells, AINSTANCE in *. repeat lazymatch goal with |- _ /\ _ => split end; assumption. }
  pose proof MTX16 as MTX. rw_split MTX 1%nat MTX MTXb. clear MTXb.
  destruct (junk_split m (al_t L + 2768) 16 16 CSTATS ltac:(lia) ltac:(lia)) as [_ CSb].
  destruct (junk_split m (al_t L + 2768 + 16) 8 8 CSb ltac:(lia) ltac:(lia)) as [CS8 _].
  replace (al_t L + 2768 + 16) with (al_t L + 2784) in CS8 by lia. destruct (c8_of_junk m _ CS8) as [sta STA].
  destruct (CACHES c HC) as [tail (RECc & CH & LCH)]. cbv zeta in CH. cbv zeta in LCH.
  pose proof (cache_vals_lt L st X c tail WF HC LCH) as CH31.
  destruct (nf_bound L st X c WF HC) as [NFA NFN].
  destruct (read_qchunk L st X m c kk n b1 ctx l1 l2 ALO WF XB SLOTS SSH) as (HDR & UJ & MAG & SHA & SHU & SHR).
  destruct (slot_rng L st X c kk ALO WF HC KR RNG ARNG) as [RAB RSAB].
  pose proof (slot_geo L st X c kk ALO WF HC KR) as (S1 & S2 & AL16 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & R8 & M8).
  (* [comment removed for export] *)
  eapply (recyc1_spec RNG k Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L st c kk n b1 ctx CBA lo
            sj (map (fun k0 => Z_to_bv 64 (acompact c k0)) (xc_cache (x_cls X c)) ++ tail) sta cbs (repeat (Z_to_bv 8 0xfd) (Z.to_nat (granules n))));
  try lazymatch goal with
       | |- forall stX RNG' m' t0', _ => idtac
       | |- stk _ _ _ _ => exact ST
       | |- ATOP <= _ => exact CEIL
       | |- _ <= bv_unsigned _ - _ => exact LO
       | |- mem_inv _ _ => exact MI
       | |- m3_cells _ _ => exact MC
       | |- rw_cells _ _ CBA _ => exact CBC
       | |- rw_cells _ _ (aregion_info _ _) _ => exact MTX
       | |- rw_cells _ _ (aregion_info _ _ + 16) _ => exact REG
       | |- junk_at _ (aregion_info _ _ + 72) _ => exact RJ56
       | |- junk_at _ (afreearr _ _ + _) _ => exact FJ
       | |- rw_cells _ _ (al_t _ + 2784) _ => exact STA
       | |- u64arr _ _ _ _ => exact STATS
       | |- u32arr _ _ _ _ => exact CH
       | |- Forall _ _ => exact CH31
       | |- length (map _ _ ++ _) = _ => rewrite length_app, length_map; exact LCH
       | |- length _ = _ => exact LSJ
       | |- azero _ (shad (afreearr _ _ + _)) _ => exact AZF
       | |- rw_cells _ _ (aslot_addr _ _ _ + rz_size _ - 16) _ => exact HDR
       | |- 16 < _ -> _ => intros H16; exact (proj1 (MAG H16))
       | |- rw_cells _ _ (shad _) _ => exact SHU
       | |- a_space_beg _ = _ => exact SBE
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (bv_unsigned _ - _) => exact RSTK
       | |- rng _ CBA _ => exact RCB
       | |- rng _ (aregion_info _ _) _ => eapply rng_sub'; [exact RRI|]; unfold aregion_info, ARI_STRIDE, K_SPACE_EXTRA; clear -HC; unfold K_NUM_CLASSES in HC; lia
       | |- rng _ (afreearr _ _) _ => exact RFA
       | |- rng _ (aslot_addr _ _ _) _ => exact RAB
       | |- rng _ (shad (aslot_addr _ _ _)) _ => exact RSAB
       | |- rng _ (al_ctx _) _ => eapply rng_sub'; [exact RCTX|]; clear; lia
       | |- rng _ (al_t _) _ => exact RT4
       | |- @eq word _ _ => first [exact TP | exact Ha0 | rewrite Ha1; unfold qhdr; reflexivity]
       | |- _ \/ _ => first [exact CL5 | exact TSP | clear -SCX; unfold K_SPACE_SIZE, K_SPACE_EXTRA in *; lia]
       | |- forall j, _ -> arec_hdr _ _ _ _ _ _ => intros j Hj; destruct (CACHES j ltac:(unfold K_NUM_CLASSES; clear -Hj; lia)) as [tl (RH & _ & _)]; exact RH
       | |- forall j, _ -> 0 <= _ <= _ => intros j Hj; destruct (PERC j ltac:(unfold K_NUM_CLASSES; clear -Hj; lia)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CB2 & _); exact CB2
       end.
  all: lazymatch goal with
       | |- forall stX RNG' m' t0', _ => idtac
       | |- (_ + 1) * _ <= _ =>
           unfold ndist in KR; transitivity (c_allocated_user (get_cls st c) / size_of_class c * size_of_class c);
           [apply Z.mul_le_mono_nonneg_r; [clear -S1; lia| clear -KR; lia]
           | rewrite Z.mul_comm; pose proof (Z.mul_div_le (c_allocated_user (get_cls st c)) (size_of_class c) ltac:(clear -S1; lia)); clear -A1 H; lia]
       | |- 1 <= _ => first [assumption | idtac]; destruct (BUSY (bany BQuar c kk n b1 ctx) ltac:(rewrite XB; apply in_app_iff; right; left; reflexivity)) as [_ M]; cbn in M; clear -M; lia
       | |- rz_size _ + _ <= _ => pose proof (rounded_size_ge n); clear -FIT0 H; lia
       | |- 0 <= _ < _ => first [assumption | clear -CTX0; lia]
       | |- al_ctx _ + 4096 <= _ => clear -CL2; atop_facts; lia
       | |- 0 <= _ => first [assumption | exact (proj1 KR)]
       | |- ?g => first [assumption | idtac]
       end.
  (* [comment removed for export] *)
  intros stX RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' RR.
  destruct (rec1_store L RNG RNG' sp m m' st stX X R pend' cs c kk n b1 ctx lo l1 l2 tail ALO ARNG AR EP XB CEIL LO CH LCH RR)
    as (X' & mfa' & MU & WM & MFB & AR' & ARNG' & CIN & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & GC & MU1 & AU1 & XS & XL).
  destruct RR as (m1 & _ & _ & CDR & _). destruct CDR as (FPLE & dr & mfa2 & sj2 & sta2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & MIT & STT & _).
  eapply KONT. unfold arecyc1_ret. split; [exact FPLE|]. do 16 eexists. exists mfa'. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MIT|]. split; [exact STT|]. split; [exact MFB|]. split; [exact AR'|]. split; [exact ARNG'|].
  split; [exact CIN|]. split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|]. split; [exact L5|]. split; [exact L6|].
  split; [exact L7|]. split; [exact L8|]. split; [exact L9|]. split; [exact L10|]. split; [exact GC|]. split; [exact MU1|]. split; [exact AU1|].
  split; [exact XS| exact XL].
Qed.
End P.
End CANSEC1.
