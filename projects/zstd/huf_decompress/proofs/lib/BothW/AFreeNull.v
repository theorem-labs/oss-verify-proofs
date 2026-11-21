(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (1 recorded proof replaced by written proofs (AQUAR_null)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF ITreeA StepF.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import ASecFacts BImg AProto ABase ABytes AQConst AKitQ AMalloc_iface ADepot_iface ARep ARepQ ARepQP ALayout AHeapP ARepKit ARepFrame
     AKit AKit2 AModelFacts F_aalloc_s F_aalloc1 F_aunwind F_afree_iseg F_afree_null F_afree_arep.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AFreeNull () := "I47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib4Spec8AsanCtrl4aptrC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List8map_consC46Stdlib5Lists4List7existsbC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib5BothW5ARepQ8AQUAR_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ@aquar_glob_constC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7AQConst9aq_tcacheC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_qlocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ5q_locC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<a_qloc_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ7aqcacheC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ8qcoupledC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ4qnumC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib5BothW5ABase4al_tC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib5BothW4ARep5xb_stC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8xb_allocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8xb_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=size_of_classC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9AFreeNull8q_set_iaC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02I47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib5Lists4List;Forall_implC59OSSVerify5KrLib5BothW6ARepQPDdisjoint_from_ForallC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega6VarMap1t01C59OSSVerify5KrLib5BothW5ARepQ6q_globC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ARepQPCqcoupled_bslot_busyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7xb_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ7qb_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ;abatch_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6x_busyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep:aslot_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7a_qglobC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=a_qglob_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ARepQPFaquar_glob_const_frameC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C46Stdlib5Lists4List:in_app_iffK47Corelib4Init5Logic2or01C59OSSVerify5KrLib5BothW6ARepQP=aqcache_frameC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02C59OSSVerify5KrLib5BothW5ARepQ9qentry_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ8qentriesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ9qprim_idsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib5BothW5ARepQ6q_pendC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List5NoDup00K47Corelib4Init5Logic3and01C59OSSVerify5KrLib5BothW5ARepQ4q_iaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ6aintalC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstK46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08C47Corelib4Init9Datatypes3appI47Corelib4Init5Logic2ex00C47Corelib4Init9Datatypes6lengthC47Corelib5Lists7ListDef3mapC47Corelib4Init5Logic3iffC59OSSVerify5KrLib5BothW7AQConst9AQ_GCACHEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4BImg5bsegsC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I59OSSVerify5KrLib5BothW4ARep5xbusy00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I59OSSVerify5KrLib5BothW5ARepQ7qbatchc00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep6bstate00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW4ARep6bstate03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_BATCH_CLASSC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I59OSSVerify5KrLib4Spec8AsanCtrl6abatch00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW5ABase7alayout00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6astate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep5aconc00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW5ARepQ5qconc00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib3Lib5Frame3ivlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase9AINSTANCEC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib7Numbers7BinNums1Z01C59OSSVerify5KrLib5BothW7AQConst6AQ_MAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7AQConst8AQ_MUTEXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=Q_BATCH_BYTESC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ARepQP@size_of_class_24C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8nil_consI59OSSVerify5KrLib4Spec8AsanCtrl6achunk00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW4ARep6bstate02C1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall02I59OSSVerify5KrLib5BothW7ALayout:alayout_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<F_afree_arep3AHQC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep4AREPC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9AFreeNull5WnullC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvK59OSSVerify5KrLib3Lib5Cells4cell04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout=alayout_spaceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase<al_space_begC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib5BothW7ALayout4ao_tC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout4aobjC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout6ao_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase6al_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout6ao_resC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout6al_resC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout8ao_nodesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase8al_nodesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout8ao_storeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase8al_storeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout7ao_fakeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7al_fakeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout7ao_dtlsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout7al_dtlsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout8ao_spaceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout9ao_res_hiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout8ad_t_resC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout5adisjC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout8ad_t_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout:ad_t_nodesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout:ad_t_storeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout9ad_t_fakeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout9ad_t_dtlsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC59OSSVerify5KrLib4Spec9AsanEmbed5shlenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed4shadC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof03C56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib5BothW9ARepFrame9shlen_divC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame8shad_divC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib5BothW4ARep3awfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7arep_rtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep9ainstanceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7athreadC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep<aslot_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep=ashadow_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7ah_quarC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6ah_secC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8ah_depotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6arelroC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8arep_rt2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8arep_rt3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;a_space_begC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;a_ptr_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase<al_ptr_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7get_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5x_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl@c_allocated_userC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=c_mapped_userC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;c_num_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrlCc_mapped_free_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7xc_freeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8xc_cacheC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7c_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep4xb_nC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<rounded_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7rz_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5xb_b1C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC59OSSVerify5KrLib5BothW4ARep6xb_ctxC1?~~~~~~~~~~~~~~~I35stdpp4gmap4gmap00C35stdpp4gmap;gmap_lookupC59OSSVerify5KrLib4Spec8AsanCtrl6a_liveC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8AsanCtrl6achunk01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01K59OSSVerify5KrLib5BothW4ARep6bstate01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrameCsize_of_class_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep:busy_slotsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:in_map_iffC56Stdlib6ZArith6BinInt1Z3eqbC46Stdlib5Lists4List6filterC46Stdlib5Lists4List9filter_InC56Stdlib6ZArith6BinInt1Z8eqb_reflK47Corelib4Init5Logic2ex01C47Corelib4Init5Logic5proj1C59OSSVerify5KrLib5BothW9ARepFrame>slot_in_regionC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7aregionC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr07K47Corelib5Lists7ListDef6Forall01c59OSSVerify5KrLib5BothW9AFreeNull:AQUAR_nullC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame8rt_hullsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame=arep_rt_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_nresC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_nsecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame?ainstance_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase6al_topC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase6al_botC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep<acache_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7junk_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame;cells_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7a_cinitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep;acache_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrameBacache_cells_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame:junk_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame<u64arr_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep=aregion_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep:afreearrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6aslotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame;aregion_modC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep<aregion_infoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrameCaregion_cells_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8afreearrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame9shad_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame<shlen_nonnegC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame>shad_add_shlenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame@afreearray_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5ndistC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7busy_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame7xb_fitsC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbC46Stdlib5Lists4List9find_someC46Stdlib4Bool4Bool=andb_true_iffC56Stdlib6ZArith6BinInt1Z6eqb_eqC59OSSVerify5KrLib5BothW9ARepFrame8awf_fitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep:aslot_busyC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC59OSSVerify5KrLib5BothW9ARepFrame=aslots_updateC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame<slot_alignedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame>mod16_of_classC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC59OSSVerify5KrLib5BothW4ARepAslot_shadow_bytesC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrameCaslot_shadow_updateC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP=sec_untouchedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP=sec_same_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP8hs_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP8hd_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame<arelro_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame>arep_rt2_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrameCashadow_avail_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame>arep_rt3_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega7EnvRing5PExpr04C59OSSVerify5KrLib4Spec8AsanCtrl9max_countC1?~~~~~~~~~~~~~~~C35stdpp4base6lookupC59OSSVerify5KrLib4Spec8AsanCtrl6a_nextC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2ltK59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr6u64arrC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<K_SPACE_SIZEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_SPACE_EXTRAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7K_ALIGNC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op205C59OSSVerify5KrLib5BothW5ABase7AIMG_HIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_NUM_CLASSESC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_OFFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl:K_USER_MAPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_MAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_MAPC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6aclass00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7aclass0C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C59OSSVerify5KrLib5BothW4ARep<ASTATS_WORDSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl8K_REGIONC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed6ASHOFFC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01I59OSSVerify5KrLib5BothW4ARep6xclass00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7AREQMAXC1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableC59OSSVerify5KrLib5BothW5ABase3KLSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase9ARELRO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase9ARELRO_HIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ARepFrame9rt3_hullsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP7AHEAP_PC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC59OSSVerify5KrLib5BothW=AMalloc_iface4aunwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4al_UC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5AKitQ9afree_unwC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW5ABase6uchain00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=AMalloc_iface?afree_null_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP4arngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP7ablocksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7ah_fakeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF3rngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout9alayout_tC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4sclrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4iclrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout;alayout_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout=alayout_stackC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5AKitQ>afree_unw_sp47C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell03C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ABytes<rw_cells_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le8C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW4AKit5boxed01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4AKit5boxed00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<F_afree_null>free_null_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9F_aalloc1<allocA_cellsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC59OSSVerify5KrLib4LibA5ExecF7rng_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<F_afree_null>free_null_specC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState6ret_pcC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9AFreeNull9AREP_nullC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=AMalloc_iface:aheap_presC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=AMalloc_iface<aclient_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC59OSSVerify5KrLib3Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC59OSSVerify5KrLib5BothW5ABase9in_rangesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase8in_blockC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List=Forall_forallC59OSSVerify5KrLib5BothW5ABase7ab_addrC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW5ABase6ablock01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7ab_sizeC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW5ABase6abkind01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8AsanCtrl6achunk02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW5ABase6abkind02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase6hb_idsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7xb_userC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP7sec_wf1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4ablkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<sec_map_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP9sec_clearC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ASecFacts9sec_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;needed_sizeC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC47Corelib4Init5Logic5proj2C59OSSVerify5KrLib5BothW5ABase7in_fakeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem;wa_unsignedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP>fake_untouchedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP8hf_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF9evtF_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=AMalloc_iface?afree_null_stmtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C59OSSVerify5KrLib4LibA5ExecF4evtFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP=sec_chunks_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP4RSECC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl:is_primaryC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase8AFREE_PCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase6UDEPTHC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase5ATP88C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4ATSDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7AQConst8AIA_BASEC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I59OSSVerify5KrLib5BothW5ABase6ablock00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP8SEC_UOFFC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib4LibA5ExecF9footprintC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase;AFREE_STACKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase3ATPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase9AFREE_SYMC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C59OSSVerify5KrLib5BothW7AQConst8AIA_FLAGC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7AQConst8AIA_SIZEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7AQConst<AIA_MAP1_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7AQConst8AIA_MAP1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7AINITEDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:F_aalloc_s7ARSSLIMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase5ATSDIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase5ATSDKC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW5ABase6abkind00C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition q_set_ia (Q : qconc) : qconc := mkQConc (q_loc Q) (q_glob Q) true (q_pend Q).

(* [comment removed for export] *)
Lemma AQUAR_null : forall L st X Q m m' W,
  AQUAR_at L st X Q m -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv => (snd iv <= al_t L + 80 \/ al_t L + 208 <= fst iv)
                 /\ (snd iv <= AINSTANCE + 728 \/ AINSTANCE + 984 <= fst iv)
                 /\ (forall b, In b (x_busy X) -> match xb_st b with BLive _ => True | _ =>
                       snd iv <= xb_alloc L b \/ xb_alloc L b + size_of_class (xb_class b) <= fst iv end)) W ->
  aintal true m' ->
  AQUAR_at L st X (q_set_ia Q) m'.
Proof.
  intros L st X Q m m' W (GC & TC & GL & IA & CP & NUM) MU WM UT IA'.
  unfold AQUAR_at. cbn [q_loc q_glob q_ia q_pend q_set_ia].
  assert (DT : disjoint_from W (aq_tcache L) 32).
  { apply ARepQP.disjoint_from_Forall. eapply Forall_impl; [| exact UT]. intros iv (A & _). unfold aq_tcache. cbn in A |- *. lia. }
  assert (DG : disjoint_from W AQ_MAX 24 /\ disjoint_from W AQ_MUTEX 4 /\ disjoint_from W AQ_GCACHE 32).
  { unfold AQ_MAX, AQ_MUTEX, AQ_GCACHE, AINSTANCE in *.
    repeat split; apply ARepQP.disjoint_from_Forall; eapply Forall_impl; try exact UT; intros iv (_ & A & _); unfold AINSTANCE in A; cbn in A |- *; lia. }
  destruct DG as (DG1 & DG2 & DG3).
  assert (DQ : forall q, In q (q_loc Q ++ q_glob Q) -> disjoint_from W (abatch_addr L (qb_slot q)) Q_BATCH_BYTES).
  { intros q Hq. destruct (qcoupled_bslot_busy L st X Q q CP Hq) as (b & Hb & Sb & Cb & Kb).
    apply ARepQP.disjoint_from_Forall. eapply Forall_impl; [| exact UT]. intros iv (_ & _ & A).
    specialize (A b Hb). rewrite Sb in A. unfold xb_alloc in A. rewrite Cb, Kb, size_of_class_24 in A.
    unfold abatch_addr, Q_BATCH_BYTES. cbn. exact A. }
  split; [| split; [| split; [| split; [exact IA'| split; [| exact NUM]]]]].
  - eapply aquar_glob_const_frame; eassumption.
  - eapply aqcache_frame; [exact MU | exact WM | exact TC | exact DT |]. intros q Hq. apply DQ. apply in_app_iff. left. exact Hq.
  - eapply aqcache_frame; [exact MU | exact WM | exact GL | exact DG3 |]. intros q Hq. apply DQ. apply in_app_iff. right. exact Hq.
  - (* [comment removed for export] *)
    destruct CP as (LN1 & LN2 & OK & ND1 & ND2 & BS & PS & NN).
    unfold qcoupled. cbn [q_loc q_glob q_pend]. cbv zeta.
    split; [exact LN1|]. split; [exact LN2|]. split; [exact OK|]. split; [exact ND1|]. split; [exact ND2|].
    split; [exact BS|]. split; [exact PS| exact NN].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition Wnull (SP t : Z) : list (Z * Z) :=
  [(SP - 4096, SP); (0xbb500, 0xbb500 + 0x81030); (0x149d88, 0x149d88 + 4); (t + 3168, t + 3169)]%Z.

Section S.
Variable DI : ADepotIface.
Variables (ASEC : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Hypothesis HL : ahole_laws (AHQ DI ASEC AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                                  /\ (snd iv <= 0xb6f70 \/ 0xb7030 <= fst iv)
                                  /\ (snd iv <= 0xbb500 \/ 0x13c530 <= fst iv)
                                  /\ (snd iv <= 0x149d88 \/ 0x149d8c <= fst iv)) CI.

Lemma AREP_null : forall L st X Q m m' SP,
  alayout_ok L -> AREP (AHQ DI ASEC AFK) L st X m -> AQUAR_at L st X Q m ->
  munch (Wnull SP (al_t L)) m m' -> wmono bsegs m m' -> ATOP + 4096 <= SP ->
  rw_cells bsegs m' (al_t L + 3168) [C1 (Z_to_bv 8 0)] -> aintal true m' ->
  AREP (AHQ DI ASEC AFK) L st X m' /\ AQUAR_at L st X (q_set_ia Q) m'.
Proof.
intros L st X Q m m' SP ALO AR AQ MU WM HSP UNW' IA'.
set (W := Wnull SP (al_t L)) in *.
pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
pose proof (ao_t L ALO) as OT. pose proof (ao_ctx L ALO) as OC. pose proof (ao_res L ALO) as ORS. pose proof (ao_nodes L ALO) as ON.
pose proof (ao_store L ALO) as OS. pose proof (ao_fake L ALO) as OFK. pose proof (ao_dtls L ALO) as ODT.
unfold aobj in OT, OC, ORS, ON, OS, OFK, ODT. pose proof (ao_space L ALO) as RSP.
pose proof (ao_res_hi L ALO) as RHI. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in OT, OC, ORS, ON, OS, OFK, ODT.
pose proof (ad_t_res L ALO) as D_t_res. pose proof (ad_t_ctx L ALO) as D_t_c. pose proof (ad_t_nodes L ALO) as D_t_n.
pose proof (ad_t_store L ALO) as D_t_s. pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_t_dtls L ALO) as D_t_d.
unfold adisj in D_t_res, D_t_c, D_t_n, D_t_s, D_t_f, D_t_d.
assert (SHRES : 2201439137792 <= shad (al_res L) /\ shad (al_res L) + shlen 137439023104 = shad (al_res L + 137439023104)
/\ shad (al_res L + 137439023104) <= 17594332446720).
{ rewrite !shad_div, shlen_div. unfold ASHOFF in *. clear -ORS RHI. Z.div_mod_to_equations. lia. }
destruct SHRES as (SR1 & SR2 & SR3).
assert (Kimg : forall A k, 0x10000 <= A -> 0 <= k -> A + k <= AIMG_HI ->
(A + k <= 0xbb500 \/ 0x13c530 <= A) -> (A + k <= 0x149d88 \/ 0x149d8c <= A) -> disjoint_from W A k).
{ intros A k H1 H2 H3 H4 H5. unfold W, Wnull. cbn. unfold AIMG_HI in *. clear -H1 H2 H3 H4 H5 HSP OT. lia. }
assert (Kobj : forall A k, AIMG_HI <= A -> 0 <= k -> A + k <= ATOP -> (A + k <= al_t L + 3168 \/ al_t L + 3169 <= A) -> disjoint_from W A k).
{ intros A k H1 H2 H3 H4. unfold W, Wnull. cbn. unfold AIMG_HI in *. clear -H1 H2 H3 H4 HSP. lia. }
assert (Kres : forall A k, al_res L <= A -> 0 <= k -> A + k <= al_res L + 137439023104 -> disjoint_from W A k).
{ intros A k H1 H2 H3. apply Kobj; unfold AIMG_HI in *; [clear -H1 ORS; lia | exact H2 | clear -H3 ORS; lia | clear -H1 H3 D_t_res; lia]. }
assert (Kres_sh : forall A k, shad (al_res L) <= A -> 0 <= k -> A + k <= shad (al_res L + 137439023104) -> disjoint_from W A k).
{ intros A k H1 H2 H3. apply Kobj; unfold AIMG_HI in *; [clear -H1 SR1; lia | exact H2 | clear -H3 SR3; lia | clear -H1 H3 SR1 SR3 OT; lia]. }
assert (Kt : forall A k, al_t L <= A -> 0 <= k -> A + k <= al_t L + 3168 -> disjoint_from W A k).
{ intros A k H1 H2 H3. unfold W, Wnull. cbn. unfold AIMG_HI in *. clear -H1 H2 H3 HSP OT. lia. }
assert (Kctx : forall A k, al_ctx L <= A -> 0 <= k -> A + k <= al_ctx L + 65536 -> disjoint_from W A k).
{ intros A k H1 H2 H3. apply Kobj; unfold AIMG_HI in *; [clear -H1 OC; lia | exact H2 | clear -H3 OC; lia | clear -H1 H3 D_t_c; lia]. }
pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
assert (BB : forall b, In b (x_busy X) -> al_res L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_res L + 137439023104).
{ intros b Hb. destruct (BUSY b Hb) as [CLB _].
destruct (PERC (xb_class b) CLB) as (Q1 & Q2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & QR).
pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
{ apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as (P5 & P4 & P0).
unfold xb_alloc, aregion, K_REGION, K_FREEARR_OFF, K_NUM_CLASSES in *. clear -P5 P4 Q1 Q2 CLB RSP. lia. }
assert (AQ' : AQUAR_at L st X (q_set_ia Q) m').
{ eapply AQUAR_null; [exact AQ | exact MU | exact WM | | exact IA'].
unfold W, Wnull. unfold AINSTANCE, AIMG_HI in *.
repeat (apply Forall_cons; [cbn [fst snd]; split; [clear -OT HSP; lia|]; split; [clear -OT HSP; lia|];
intros b Hb; destruct (BB b Hb) as [B1 B2]; destruct (xb_st b); [exact I| |]; clear -B1 B2 ORS OT HSP D_t_res; lia |]).
apply Forall_nil. }
split; [| exact AQ'].
split; [exact WF|].
split. { eapply arep_rt_frame; [exact MU | exact WM | exact RT |]. unfold rt_hulls, ATP88, ATSD.
repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia] |]). apply Forall_nil. }
split. { eapply ainstance_frame; [exact MU | exact WM | exact INST | reflexivity | reflexivity | | |]; apply Kimg; clear; unfold AINSTANCE, AIMG_HI; lia. }
split.
{ destruct THR as (T0 & T40 & CACHES & CSTATS & [sj [STATS LSJ]] & UNW). unfold athread.
split; [eapply cells_frame; [exact T0 | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply Kt; clear; lia]|].
split; [eapply cells_frame; [exact T40 | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply Kt; clear; lia]|].
split. { intros c Hc. eapply acache_cells_frame; [exact MU | exact WM | exact (CACHES c Hc) | reflexivity | reflexivity | reflexivity |].
unfold acache_addr. unfold K_NUM_CLASSES in Hc. apply Kt; clear -Hc; lia. }
split; [eapply junk_frame; [exact CSTATS | exact MU | exact WM | intros _; apply Kt; clear; lia]|].
split; [exists sj; split; [eapply u64arr_frame; [exact STATS | exact MU | exact WM | replace (8 * Z.of_nat (length sj)) with 368 by (rewrite LSJ; reflexivity); apply Kt; clear; lia] | exact LSJ]|].
exact UNW'. }
split.
{ intros c Hc. destruct (CLS c Hc) as (REG & FARR & SLOTS & SHADOW).
destruct (PERC c Hc) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & QLENF & QLENC & QCNTB & QND & QRANGE).
pose proof (size_of_class_facts c Hc) as [QS QS16]. pose proof (aregion_mod L c SAL) as RM. unfold K_NUM_CLASSES in Hc.
assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
/\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
{ unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP. lia. }
destruct RI as (RI1 & RI2 & RI3). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
split; [| split; [| split]].
- eapply aregion_cells_frame; [exact MU | exact WM | exact REG | reflexivity | reflexivity | reflexivity | reflexivity |].
apply Kres; unfold aregion_info, ARI_STRIDE, K_SPACE_SIZE; change (2^37) with 137438953472; clear -Hc RSP; lia.
- eapply afreearray_frame; [exact MU | exact WM | exact FARR | reflexivity | reflexivity | reflexivity | exact QLENF | exact Q5 | | clear -Q6; lia |].
+ apply Kres; unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *; [clear -RI1; lia | clear -Q5 Q6; lia | clear -RI2 RI3 Q6; lia].
+ apply Kres_sh; [apply shad_mono; unfold afreearr, K_FREEARR_OFF; clear -RI1; lia | apply shlen_nonneg; clear -Q5 Q6; lia |].
rewrite <- shad_add_shlen by (unfold afreearr, K_FREEARR_OFF; clear -RM; Z.div_mod_to_equations; lia). apply shad_mono.
unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *. clear -RI2 RI3 Q6. lia.
- eapply (aslots_update L W m m' MU WM st st X X c (-1)); [exact SLOTS | reflexivity | reflexivity | reflexivity | | | intros Hk; exfalso; clear -Hk; lia].
+ intros k Hk _. pose proof (slot_in_region L st c k ltac:(clear -QS; lia) (proj1 Q1) Hk) as (P5 & P4 & P0).
split; [reflexivity|]. split.
* apply Kres; [clear -P5 RI1; lia | clear -QS; lia | clear -P4 Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF in *; lia].
* intros b Hb. pose proof Hb as Hb'. unfold busy_of in Hb'. apply find_some in Hb'. destruct Hb' as [HIn HP].
apply andb_true_iff in HP. destruct HP as [HP1 HP2]. apply Z.eqb_eq in HP1. apply Z.eqb_eq in HP2.
split; [exact HP1|]. split; [exact HP2|]. exact (awf_fits L st X b WF HIn).
+ intros POS. apply Kres; [clear -Q1 RI1; lia | clear -POS; lia | clear -Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF in *; lia].
- eapply (aslot_shadow_update L W m m' MU WM st st X X c (-1)); [exact SHADOW | reflexivity | reflexivity | reflexivity | | | intros Hk; exfalso; clear -Hk; lia | apply shlen_nonneg; clear -QS; lia].
+ intros k Hk _. pose proof (slot_in_region L st c k ltac:(clear -QS; lia) (proj1 Q1) Hk) as (P5 & P4 & P0).
pose proof (slot_aligned L c k SAL ltac:(unfold K_NUM_CLASSES; clear -Hc; lia)) as AL.
split; [reflexivity|]. apply Kres_sh; [apply shad_mono; clear -P5 RI1; lia | apply shlen_nonneg; clear -QS; lia |].
rewrite <- shad_add_shlen by (clear -AL; Z.div_mod_to_equations; lia). apply shad_mono. clear -P4 Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia.
+ intros POS. apply Kres_sh; [apply shad_mono; clear -Q1 RI1; lia | clear -POS; lia |].
rewrite <- shad_add_shlen by (pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM; clear -AM RM; Z.div_mod_to_equations; lia).
apply shad_mono. clear -Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia. }
split; [exists (q_set_ia Q); exact AQ'|].
split.
{ cbn [ah_sec AHQ]. cbn [ah_sec AHQ] in HS.
eapply (hs_frame _ HL L st st X X m m' W); [exact HS | exact MU | exact WM | |].
- unfold sec_untouched, aknown, W, Wnull. unfold AINSTANCE, AIMG_HI in *.
apply Forall_cons; [cbn [fst snd]; intros a Ha; do 4 right; left; clear -Ha HSP; lia|].
do 2 (apply Forall_cons; [cbn [fst snd]; intros a Ha; left; clear -Ha; lia|]).
apply Forall_cons; [cbn [fst snd]; intros a Ha; do 5 right; left; clear -Ha OT; lia|].
apply Forall_nil.
- apply sec_same_refl. }
split.
{ cbn [ah_depot AHQ]. cbn [ah_depot AHQ] in HD.
eapply (hd_frame _ HL L m m' W); [exact HD | exact MU | exact WM |].
unfold W, Wnull. unfold AIMG_HI in *.
repeat (apply Forall_cons; [cbn [fst snd]; intros a Ha; clear -Ha OT ON OS HSP D_t_n D_t_s; lia|]). apply Forall_nil. }
split; [eapply arelro_frame; [exact MU | exact HRO | apply Kimg; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI; lia]|].
split; [eapply arep_rt2_frame; [exact MU | exact WM | exact RT2 | | |]; apply Kimg; clear; unfold AIMG_HI; lia|].
split; [| eapply arep_rt3_frame; [exact MU | exact WM | exact RT3 |]; unfold rt3_hulls; repeat (apply Forall_cons; [cbn [fst snd]; apply Kimg; clear; unfold AIMG_HI; lia|]); apply Forall_nil].
intros c Hc. destruct (PERC c Hc) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & _). unfold K_NUM_CLASSES in Hc.
assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
/\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
{ unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP. lia. }
destruct RI as (RI1 & RI2 & RI3). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
eapply (ashadow_avail_frame L W m m' MU WM st); [exact (AVL c ltac:(unfold K_NUM_CLASSES; clear -Hc; lia)) | reflexivity | reflexivity | |].
- intros POS. apply Kres_sh; [apply shad_mono; unfold aregion in *; clear -Q1 RI1; lia | clear -POS; lia |].
rewrite <- shad_add_shlen by (pose proof (aregion_mod L c SAL) as RM; clear -RM Q4; unfold K_USER_MAP in *; Z.div_mod_to_equations; lia).
apply shad_mono. unfold K_FREEARR_OFF, K_REGION in *. clear -Q1 Q2 RI2 RI3. lia.
- intros POS. apply Kres_sh; [apply shad_mono; unfold afreearr, K_FREEARR_OFF, aregion in *; clear -Q5 Q6 RI1; lia | clear -POS; lia |].
rewrite <- shad_add_shlen by (pose proof (aregion_mod L c SAL) as RM; unfold afreearr, K_FREEARR_OFF; clear -RM Q7; unfold K_FREEARR_MAP in *; Z.div_mod_to_equations; lia).
apply shad_mono. unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q5 Q6 RI2 RI3. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem afree_nullP : afree_null_stmt CI (AHEAP_P (AHQ DI ASEC AFK)).
Proof.
unfold afree_null_stmt. intros until tr. intros AH MI ST BOT LO TP Ha0 AUNW S0NE RA4 RANE SP16 RSTK.
assert (UNWX : exists trt, afree_unw RNG lo m (al_top L) sp s0 ra trt /\ In (AFREE_PC :: trt) (al_U L)).
{ destruct AUNW as [(BT & UC & LTR & TRU & RTOP)|(TOPLE & SPLT & TRU)]; [exists (bv_unsigned ra :: tr); split; [left; exists tr; split; [reflexivity|]; split; [exact UC|]; split; [exact LTR|]; split; [exact BT| exact RTOP]| exact TRU] | exists (@nil Z); split; [right; auto| exact TRU]]. }
destruct UNWX as (trt & FUNW & TRU).
destruct AH as (ALO & ARNG & [X [AR BL]] & HFK).
pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & HRT2 & AVL & RT3).
cbn [ah_quar ah_sec ah_depot ah_fake AHQ] in HQ, HS, HD, HFK. destruct HQ as [Q AQ].
pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVEB & FRESH & UNIQ).
pose proof ARNG as ARNG0. destruct ARNG0 as (RIMG & RT4 & RCTX & RNO & RSTO & RRI & RFK & RSFK & RDT & RCLS & RPA & RSECS & RPSH).
pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4). pose proof TL1 as TL1u. pose proof TL4 as TL4u. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in TL1u, TL4u.
pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
pose proof (alayout_stack L ALO) as (STK1 & STK2 & STK3).
assert (SP47 : bv_unsigned sp < 2^47) by (eapply afree_unw_sp47; [exact FUNW| exact STK2]).
pose proof (ao_t L ALO) as OT. pose proof (ao_res L ALO) as ORS. pose proof (ao_fake L ALO) as OFK. pose proof (ao_dtls L ALO) as ODT.
unfold aobj in OT, ORS, OFK, ODT. pose proof (ao_space L ALO) as RSP. pose proof (ao_res_hi L ALO) as RHI. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in OT, ORS, OFK, ODT.
pose proof (ad_t_res L ALO) as D_t_res. pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_t_dtls L ALO) as D_t_d.
unfold adisj in D_t_res, D_t_f, D_t_d.
pose proof RT as RT0.
destruct RT0 as (GPG & GOT & GOT80 & RIC & LS1 & REAL & IMAX4 & FLG5 & FLG & HPP & SHB & CANP & TI & TK & INI2 & LAY & MCS & OOM3
& PGC & HK2 & CF8 & CF34 & CSMT & T88 & TSD & LS2 & CT8 & CT).
pose proof INI2 as INI. rw_split INI 1%nat INI1 INIx. clear INIx.
pose proof OOM3 as OOM. rw_split OOM 2%nat OOMx RSS0. clear OOMx.
pose proof IMAX4 as IMAX. rw_split IMAX 3%nat IMAX3 IMAXx. clear IMAXx.
destruct THR as (T0 & T40 & CACHES & CSTATS & [sj [STATS LSJ]] & UNW).
pose proof AQ as AQ0. destruct AQ0 as (_ & _ & _ & (FL & IAS & IAM) & CP & _).
unfold AIA_FLAG, AIA_BASE, AIA_SIZE, AIA_MAP1, AIA_MAP1_LEN in FL, IAS, IAM.
unfold AIMG_HI, AFREE_STACK, UDEPTH in *.
box CL5.
eapply evtF_mono.
{ eapply (free_null_spec (q_ia Q) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m
(al_t L) (al_ctx L) lo (al_top L) (al_bot L) trt).
all: try lazymatch goal with
| |- stk _ _ _ _ => first [exact ST | exact IAS]
| |- mem_inv _ _ => exact MI
| |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
| |- afree_unw _ _ _ _ _ _ => exact FUNW
| |- _ = true -> _ => exact IAM
end.
all: try lazymatch goal with
| |- rw_cells _ _ _ [C8 _; C8 _; C8 _] => exact T0
| |- rw_cells _ _ _ _ => assumption
| |- @eq word _ _ => first [exact TP | exact Ha0 | reflexivity]
| |- _ \/ _ => first [unboxed CL5 | pose proof CL5 as Y; unbox Y; lia]
| |- rng _ _ _ => first [assumption | eapply rng_sub; [exact RCTX| lia| lia] | solve_rng]
end.
all: try assumption.
all: unfold AIMG_HI, UDEPTH in *.
all: try (generalize LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 RA4; clear; intros; lia).
all: match goal with |- ?G => idtac "REMF" G end. }
cbv beta. intros ms' PM.
destruct PM as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & ST' & UNW' & FL' & IAS' & IAM').
change (munch (Wnull (bv_unsigned sp) (al_t L)) m m') in MU.
assert (IA' : aintal true m').
{ unfold aintal, AIA_FLAG, AIA_BASE, AIA_SIZE, AIA_MAP1, AIA_MAP1_LEN. split; [exact FL'|]. split; [exact IAS'|]. intros _. exact IAM'. }
destruct (AREP_null L st X Q m m' (bv_unsigned sp) ALO AR AQ MU WM ltac:(atop_facts; clear -LO BOT STK3; lia) UNW' IA') as [AR' AQ'].
exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split.
{
intros a Ha CLA. split; [| intros Hw; apply WM; exact Hw]. apply MU. rewrite wa_unsigned by exact Ha.
word_range sp SPR.
unfold Wnull. cbn [outside].
destruct CLA as [SK | [CIa | [BLK | SH]]].
- clear -SK Ha LO BOT STK3 TL2. lia.
- destruct CIa as (iv & Hiv & R). pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6). cbn [fst snd] in *.
unfold AIMG_HI in *. clear -R Q1 Q3 Q5 Q6 LO BOT STK3 TL4u. lia.
- destruct BLK as ([[q|cls] A' n'] & Hin & R); cbn [ab_addr ab_size] in R.
+ destruct (proj1 BL q A' n' Hin) as [(b & Hb & Sb & Ub & Nb)|(mb & msz & Lp & EUA & Gs)].
* destruct (BUSY b Hb) as [CLB _].
destruct (PERC (xb_class b) CLB) as (P1 & P2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & PR).
pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
{ apply PR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 P1) KB) as (P5 & P4 & P0).
pose proof (awf_fits L st X b WF Hb) as FIT. unfold xb_fits in FIT. rewrite Sb in FIT.
subst A' n'. unfold xb_user, xb_alloc, aregion, K_REGION, K_FREEARR_OFF, K_NUM_CLASSES in *.
clear -R P5 P4 P1 P2 CLB RSP FIT ORS D_t_res LO BOT STK3. lia.
*
cbn [sec_wf1] in Gs. destruct Gs as (Gs1 & Gs2 & Gs3 & Gs4 & Gs5 & Gs6 & (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd)).
pose proof (sec_facts n' ltac:(clear -Gs5; lia) Gs6) as SF. subst A'. unfold SEC_UOFF, K_HIGH_MEM in *.
unfold ablk, KLS, AIMG_HI in Gs2.
clear -R Gs2 Gs3 Gs4 Gs5 SF Ct LO BOT STK3. lia.
+ destruct (proj1 (proj2 BL) cls A' n' Hin) as (K1 & K2 & K3).
clear -R K1 K2 K3 OFK D_t_f LO BOT STK3. lia.
- destruct SH as (a' & Ha' & ->). rewrite shad_div in Ha |- *. unfold ASHOFF in *.
assert (A47 : 0 <= a' < 2^47).
{ destruct Ha' as [SK | [CIa | FK]].
- atop_facts. clear -SK SPR. lia.
- destruct CIa as (iv & Hiv & R). pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as (Q1 & Q2 & Q3 & _). cbn [fst snd] in *.
unfold AIMG_HI in *. clear -R Q1 Q3. lia.
- destruct FK as (cls & FA & sz & Hin & R). destruct (proj1 (proj2 BL) cls FA sz Hin) as (K1 & K2 & K3). clear -R K1 K3 OFK. lia. }
clear -A47 LO BOT STK3 TL1u. Z.div_mod_to_equations. lia. }
split; [exact ALO|]. split; [exact ARNG|]. split; [exists X; split; [exact AR'| exact BL]|].
cbn [ah_fake AHQ].
assert (SF : 0x800b6e00 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 17594332446720).
{ rewrite shad_div, shlen_div. unfold ASHOFF in *. pose proof atop_range as AR8. clear -OFK AR8. Z.div_mod_to_equations. lia. }
eapply (hf_frame _ HL L LB m m'); [exact HFK | exact MU | exact WM |].
unfold fake_untouched, Wnull.
repeat (apply Forall_cons; [cbn [fst snd]; clear -OFK ODT OT SF D_t_f D_t_d LO BOT STK3; lia|]). apply Forall_nil.
Qed.
End S.
End CANSEC1.
