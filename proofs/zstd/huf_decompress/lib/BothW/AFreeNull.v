(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF ITreeA StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import ASecFacts BImg AProto ABase ABytes AQConst AKitQ AMalloc_iface ADepot_iface ARep ARepQ ARepQP ALayout AHeapP ARepKit ARepFrame
     AKit AKit2 AModelFacts F_aalloc_s F_aalloc1 F_aunwind F_afree_iseg F_afree_null F_afree_arep.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AFreeNull () := "I47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3sndC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl4aptrC46Stdlib5Lists4List2InC47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List8map_consC46Stdlib5Lists4List7existsbC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C5ARocqVerifyHarness?AgentSubmission5BothW5ARepQ8AQUAR_atC5ARocqVerifyHarness?AgentSubmission5BothW5ARepQ@aquar_glob_constC5ARocqVerifyHarness?AgentSubmission5BothW7AQConst9aq_tcacheC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6a_qlocC5ARocqVerifyHarness?AgentSubmission5BothW5ARepQ5q_locC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl<a_qloc_bytesC5ARocqVerifyHarness?AgentSubmission5BothW5ARepQ7aqcacheC5ARocqVerifyHarness?AgentSubmission5BothW5ARepQ8qcoupledC5ARocqVerifyHarness?AgentSubmission5BothW5ARepQ4qnumC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchI47Corelib4Init9Datatypes4prod00C5ARocqVerifyHarness?AgentSubmission5BothW5ABase4al_tK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3addC5ARocqVerifyHarness?AgentSubmission5BothW4ARep5xb_stC5ARocqVerifyHarness?AgentSubmission5BothW4ARep8xb_allocC5ARocqVerifyHarness?AgentSubmission5BothW4ARep8xb_classC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl=size_of_classc5ARocqVerifyHarness?AgentSubmission5BothW9AFreeNull8q_set_iaK47Corelib7Numbers7BinNums1Z02I47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib5Lists4List;Forall_implC5ARocqVerifyHarness?AgentSubmission5BothW6ARepQPDdisjoint_from_ForallC5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromC56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega6VarMap1t01C5ARocqVerifyHarness?AgentSubmission5BothW5ARepQ6q_globC5ARocqVerifyHarness?AgentSubmission5BothW6ARepQPCqcoupled_bslot_busyC5ARocqVerifyHarness?AgentSubmission5BothW4ARep7xb_slotC5ARocqVerifyHarness?AgentSubmission5BothW5ARepQ7qb_slotC5ARocqVerifyHarness?AgentSubmission5BothW5ARepQ;abatch_addrC5ARocqVerifyHarness?AgentSubmission5BothW4ARep6x_busyC5ARocqVerifyHarness?AgentSubmission5BothW4ARep:aslot_addrC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl7a_qglobC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl=a_qglob_bytesC5ARocqVerifyHarness?AgentSubmission5BothW6ARepQPFaquar_glob_const_frameI47Corelib4Init5Logic2or00C46Stdlib5Lists4List:in_app_iffK47Corelib4Init5Logic2or01C5ARocqVerifyHarness?AgentSubmission5BothW6ARepQP=aqcache_frameK47Corelib4Init5Logic2or02C5ARocqVerifyHarness?AgentSubmission5BothW5ARepQ9qentry_okC5ARocqVerifyHarness?AgentSubmission5BothW5ARepQ8qentriesC5ARocqVerifyHarness?AgentSubmission5BothW5ARepQ9qprim_idsK47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission5BothW5ARepQ6q_pendI46Stdlib5Lists4List5NoDup00K47Corelib4Init5Logic3and01C5ARocqVerifyHarness?AgentSubmission5BothW5ARepQ4q_iaC5ARocqVerifyHarness?AgentSubmission5BothW5ARepQ6aintalC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC47Corelib4Init9Datatypes3fstK46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08C47Corelib4Init9Datatypes3appI47Corelib4Init5Logic2ex00C47Corelib4Init9Datatypes6lengthC47Corelib5Lists7ListDef3mapC47Corelib4Init5Logic3iffC5ARocqVerifyHarness?AgentSubmission5BothW7AQConst9AQ_GCACHEC5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsI47Corelib7Numbers7BinNums1Z00I5ARocqVerifyHarness?AgentSubmission5BothW4ARep5xbusy00K47Corelib4Init9Datatypes4bool01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I5ARocqVerifyHarness?AgentSubmission5BothW5ARepQ7qbatchc00I5ARocqVerifyHarness?AgentSubmission5BothW4ARep6bstate00K5ARocqVerifyHarness?AgentSubmission5BothW4ARep6bstate03C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl=K_BATCH_CLASSI47Corelib4Init9Datatypes3nat00I5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6abatch00I5ARocqVerifyHarness?AgentSubmission5BothW5ABase7alayout00I5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6astate00I5ARocqVerifyHarness?AgentSubmission5BothW4ARep5aconc00I5ARocqVerifyHarness?AgentSubmission5BothW5ARepQ5qconc00K47Corelib7Numbers7BinNums8positive03C5ARocqVerifyHarness?AgentSubmission3Lib5Frame3ivlC5ARocqVerifyHarness?AgentSubmission5BothW5ABase9AINSTANCEI47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib7Numbers7BinNums1Z01C5ARocqVerifyHarness?AgentSubmission5BothW7AQConst6AQ_MAXC5ARocqVerifyHarness?AgentSubmission5BothW7AQConst8AQ_MUTEXC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl=Q_BATCH_BYTESC5ARocqVerifyHarness?AgentSubmission5BothW6ARepQP@size_of_class_24C46Stdlib5Lists4List8nil_consI5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6achunk00K5ARocqVerifyHarness?AgentSubmission5BothW4ARep6bstate02K47Corelib5Lists7ListDef6Forall02I5ARocqVerifyHarness?AgentSubmission5BothW7ALayout:alayout_ok00C5ARocqVerifyHarness?AgentSubmission5BothW<F_afree_arep3AHQC5ARocqVerifyHarness?AgentSubmission5BothW4ARep4AREPc5ARocqVerifyHarness?AgentSubmission5BothW9AFreeNull5WnullC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC45stdpp9bitvector;definitions7Z_to_bvK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell04C5ARocqVerifyHarness?AgentSubmission5BothW7ALayout=alayout_spaceC5ARocqVerifyHarness?AgentSubmission5BothW5ABase<al_space_begC56Stdlib6ZArith6BinInt1Z3powC5ARocqVerifyHarness?AgentSubmission5BothW7ALayout4ao_tC5ARocqVerifyHarness?AgentSubmission5BothW7ALayout4aobjC5ARocqVerifyHarness?AgentSubmission5BothW7ALayout6ao_ctxC5ARocqVerifyHarness?AgentSubmission5BothW5ABase6al_ctxC5ARocqVerifyHarness?AgentSubmission5BothW7ALayout6ao_resC5ARocqVerifyHarness?AgentSubmission5BothW7ALayout6al_resC5ARocqVerifyHarness?AgentSubmission5BothW7ALayout8ao_nodesC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8al_nodesC5ARocqVerifyHarness?AgentSubmission5BothW7ALayout8ao_storeC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8al_storeC5ARocqVerifyHarness?AgentSubmission5BothW7ALayout7ao_fakeC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7al_fakeC5ARocqVerifyHarness?AgentSubmission5BothW7ALayout7ao_dtlsC5ARocqVerifyHarness?AgentSubmission5BothW7ALayout7al_dtlsC5ARocqVerifyHarness?AgentSubmission5BothW7ALayout8ao_spaceC5ARocqVerifyHarness?AgentSubmission5BothW7ALayout9ao_res_hiC5ARocqVerifyHarness?AgentSubmission5BothW7ALayout8ad_t_resC5ARocqVerifyHarness?AgentSubmission5BothW7ALayout5adisjC5ARocqVerifyHarness?AgentSubmission5BothW7ALayout8ad_t_ctxC5ARocqVerifyHarness?AgentSubmission5BothW7ALayout:ad_t_nodesC5ARocqVerifyHarness?AgentSubmission5BothW7ALayout:ad_t_storeC5ARocqVerifyHarness?AgentSubmission5BothW7ALayout9ad_t_fakeC5ARocqVerifyHarness?AgentSubmission5BothW7ALayout9ad_t_dtlsC56Stdlib6ZArith6BinInt1Z3divC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed5shlenC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed4shadC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof03C56Stdlib6ZArith6BinInt1Z3mulC5ARocqVerifyHarness?AgentSubmission5BothW9ARepFrame9shlen_divC5ARocqVerifyHarness?AgentSubmission5BothW9ARepFrame8shad_divC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneK46Stdlib9micromega5Tauto8GFormula01C56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init9Datatypes4list02C5ARocqVerifyHarness?AgentSubmission5BothW4ARep3awfC5ARocqVerifyHarness?AgentSubmission5BothW4ARep7arep_rtC5ARocqVerifyHarness?AgentSubmission5BothW4ARep9ainstanceC5ARocqVerifyHarness?AgentSubmission5BothW4ARep7athreadC5ARocqVerifyHarness?AgentSubmission5BothW4ARep<aslot_shadowC5ARocqVerifyHarness?AgentSubmission5BothW4ARep=ashadow_availC5ARocqVerifyHarness?AgentSubmission5BothW4ARep7ah_quarC5ARocqVerifyHarness?AgentSubmission5BothW4ARep6ah_secC5ARocqVerifyHarness?AgentSubmission5BothW4ARep8ah_depotC5ARocqVerifyHarness?AgentSubmission5BothW4ARep6arelroC5ARocqVerifyHarness?AgentSubmission5BothW4ARep8arep_rt2C5ARocqVerifyHarness?AgentSubmission5BothW4ARep8arep_rt3C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl;a_space_begC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl;a_ptr_arrayC5ARocqVerifyHarness?AgentSubmission5BothW5ABase<al_ptr_arrayC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl7get_clsC5ARocqVerifyHarness?AgentSubmission5BothW4ARep5x_clsC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl@c_allocated_userC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl=c_mapped_userC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl;c_num_freedC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrlCc_mapped_free_arrayC5ARocqVerifyHarness?AgentSubmission5BothW4ARep7xc_freeC5ARocqVerifyHarness?AgentSubmission5BothW4ARep8xc_cacheC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl7c_countC5ARocqVerifyHarness?AgentSubmission5BothW4ARep4xb_nC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl<rounded_sizeC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl7rz_sizeC5ARocqVerifyHarness?AgentSubmission5BothW4ARep5xb_b1C56Stdlib6ZArith6BinInt1Z4landC5ARocqVerifyHarness?AgentSubmission5BothW4ARep6xb_ctxI35stdpp4gmap4gmap00C35stdpp4gmap;gmap_lookupC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6a_liveK5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6achunk01K47Corelib4Init9Datatypes6option01K5ARocqVerifyHarness?AgentSubmission5BothW4ARep6bstate01C5ARocqVerifyHarness?AgentSubmission5BothW9ARepFrameCsize_of_class_factsC5ARocqVerifyHarness?AgentSubmission5BothW4ARep:busy_slotsC46Stdlib5Lists4List:in_map_iffC56Stdlib6ZArith6BinInt1Z3eqbC46Stdlib5Lists4List6filterC46Stdlib5Lists4List9filter_InC56Stdlib6ZArith6BinInt1Z8eqb_reflK47Corelib4Init5Logic2ex01C47Corelib4Init5Logic5proj1C5ARocqVerifyHarness?AgentSubmission5BothW9ARepFrame>slot_in_regionC5ARocqVerifyHarness?AgentSubmission5BothW4ARep7aregionK46Stdlib9micromega7EnvRing5PExpr07K47Corelib5Lists7ListDef6Forall01c5ARocqVerifyHarness?AgentSubmission5BothW9AFreeNull:AQUAR_nullC5ARocqVerifyHarness?AgentSubmission5BothW9ARepFrame8rt_hullsC5ARocqVerifyHarness?AgentSubmission5BothW9ARepFrame=arep_rt_frameC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6a_nresC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6a_nsecC5ARocqVerifyHarness?AgentSubmission5BothW9ARepFrame?ainstance_frameC5ARocqVerifyHarness?AgentSubmission5BothW5ABase6al_topC5ARocqVerifyHarness?AgentSubmission5BothW5ABase6al_botC5ARocqVerifyHarness?AgentSubmission5BothW4ARep<acache_cellsC5ARocqVerifyHarness?AgentSubmission5BothW4ARep7junk_atC56Stdlib6ZArith6BinInt1Z6of_natC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission5BothW9ARepFrame;cells_frameC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl7a_cinitC5ARocqVerifyHarness?AgentSubmission5BothW4ARep;acache_addrC5ARocqVerifyHarness?AgentSubmission5BothW9ARepFrameBacache_cells_frameC5ARocqVerifyHarness?AgentSubmission5BothW9ARepFrame:junk_frameC5ARocqVerifyHarness?AgentSubmission5BothW9ARepFrame<u64arr_frameC5ARocqVerifyHarness?AgentSubmission5BothW4ARep=aregion_cellsC5ARocqVerifyHarness?AgentSubmission5BothW4ARep:afreearrayC5ARocqVerifyHarness?AgentSubmission5BothW4ARep6aslotsC5ARocqVerifyHarness?AgentSubmission5BothW9ARepFrame;aregion_modC5ARocqVerifyHarness?AgentSubmission5BothW4ARep<aregion_infoC5ARocqVerifyHarness?AgentSubmission5BothW9ARepFrameCaregion_cells_frameC5ARocqVerifyHarness?AgentSubmission5BothW4ARep8afreearrC5ARocqVerifyHarness?AgentSubmission5BothW9ARepFrame9shad_monoC5ARocqVerifyHarness?AgentSubmission5BothW9ARepFrame<shlen_nonnegC5ARocqVerifyHarness?AgentSubmission5BothW9ARepFrame>shad_add_shlenC5ARocqVerifyHarness?AgentSubmission5BothW9ARepFrame@afreearray_frameC5ARocqVerifyHarness?AgentSubmission5BothW4ARep5ndistC5ARocqVerifyHarness?AgentSubmission5BothW4ARep7busy_ofC5ARocqVerifyHarness?AgentSubmission5BothW9ARepFrame7xb_fitsC47Corelib4Init9Datatypes4andbC46Stdlib5Lists4List9find_someC46Stdlib4Bool4Bool=andb_true_iffC56Stdlib6ZArith6BinInt1Z6eqb_eqC5ARocqVerifyHarness?AgentSubmission5BothW9ARepFrame8awf_fitsC5ARocqVerifyHarness?AgentSubmission5BothW4ARep:aslot_busyC47Corelib4Init5Logic9False_indC5ARocqVerifyHarness?AgentSubmission5BothW9ARepFrame=aslots_updateC5ARocqVerifyHarness?AgentSubmission5BothW9ARepFrame<slot_alignedC5ARocqVerifyHarness?AgentSubmission5BothW9ARepFrame>mod16_of_classC56Stdlib6ZArith6BinInt1Z6to_natC5ARocqVerifyHarness?AgentSubmission5BothW4ARepAslot_shadow_bytesK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05C5ARocqVerifyHarness?AgentSubmission5BothW9ARepFrameCaslot_shadow_updateC5ARocqVerifyHarness?AgentSubmission5BothW6AHeapP=sec_untouchedC5ARocqVerifyHarness?AgentSubmission5BothW6AHeapP=sec_same_reflC5ARocqVerifyHarness?AgentSubmission5BothW6AHeapP8hs_frameC5ARocqVerifyHarness?AgentSubmission5BothW6AHeapP8hd_frameC5ARocqVerifyHarness?AgentSubmission5BothW9ARepFrame<arelro_frameC5ARocqVerifyHarness?AgentSubmission5BothW9ARepFrame>arep_rt2_frameC5ARocqVerifyHarness?AgentSubmission5BothW9ARepFrameCashadow_avail_frameC5ARocqVerifyHarness?AgentSubmission5BothW9ARepFrame>arep_rt3_frameC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsK46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega7EnvRing5PExpr04C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl9max_countC35stdpp4base6lookupC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6a_nextC56Stdlib6NArith6BinNat1N2ltK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C5ARocqVerifyHarness?AgentSubmission3Lib3Arr6u64arrI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl<K_SPACE_SIZEC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl=K_SPACE_EXTRAC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl7K_ALIGNK46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op205C5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AIMG_HIC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl=K_NUM_CLASSESC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl=K_FREEARR_OFFC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl:K_USER_MAPC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl=K_FREEARR_MAXC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl=K_FREEARR_MAPI5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6aclass00C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl7aclass0I47Corelib7Numbers7BinNums1N00C5ARocqVerifyHarness?AgentSubmission5BothW4ARep<ASTATS_WORDSC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl8K_REGIONC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed6ASHOFFK47Corelib4Init9Datatypes3nat01I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01I5ARocqVerifyHarness?AgentSubmission5BothW4ARep6xclass00C5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AREQMAXC45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableC5ARocqVerifyHarness?AgentSubmission5BothW5ABase3KLSC5ARocqVerifyHarness?AgentSubmission5BothW5ABase9ARELRO_LOC5ARocqVerifyHarness?AgentSubmission5BothW5ABase9ARELRO_HIC5ARocqVerifyHarness?AgentSubmission5BothW9ARepFrame9rt3_hullsC5ARocqVerifyHarness?AgentSubmission5BothW6AHeapP7AHEAP_PC45stdpp9bitvector;definitions;bv_unsignedC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface4aunwC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4al_UC5ARocqVerifyHarness?AgentSubmission5BothW5AKitQ9afree_unwI5ARocqVerifyHarness?AgentSubmission5BothW5ABase6uchain00C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface?afree_null_postC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSC5ARocqVerifyHarness?AgentSubmission5BothW6AHeapP4arngC5ARocqVerifyHarness?AgentSubmission5BothW6AHeapP7ablocksC5ARocqVerifyHarness?AgentSubmission5BothW4ARep7ah_fakeC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF3rngC5ARocqVerifyHarness?AgentSubmission5BothW7ALayout9alayout_tC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4sclrC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4iclrC5ARocqVerifyHarness?AgentSubmission5BothW7ALayout;alayout_ctxC5ARocqVerifyHarness?AgentSubmission5BothW7ALayout=alayout_stackC5ARocqVerifyHarness?AgentSubmission5BothW5AKitQ>afree_unw_sp47K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell03K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell02C5ARocqVerifyHarness?AgentSubmission5BothW6ABytes<rw_cells_appC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8K5ARocqVerifyHarness?AgentSubmission5BothW4AKit5boxed01I5ARocqVerifyHarness?AgentSubmission5BothW4AKit5boxed00C5ARocqVerifyHarness?AgentSubmission5BothW<F_afree_null>free_null_postC5ARocqVerifyHarness?AgentSubmission5BothW9F_aalloc1<allocA_cellsC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF7rng_subC5ARocqVerifyHarness?AgentSubmission5BothW<F_afree_null>free_null_specC5ARocqVerifyHarness?AgentSubmission3Lib6MState6ret_pcc5ARocqVerifyHarness?AgentSubmission5BothW9AFreeNull9AREP_nullC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface:aheap_presC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface<aclient_addrC5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC5ARocqVerifyHarness?AgentSubmission3Lib5Frame7outsideC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC5ARocqVerifyHarness?AgentSubmission5BothW5ABase9in_rangesC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8in_blockC46Stdlib5Lists4List=Forall_forallC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7ab_addrK5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock01C5ARocqVerifyHarness?AgentSubmission5BothW5ABase7ab_sizeK5ARocqVerifyHarness?AgentSubmission5BothW5ABase6abkind01K5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6achunk02K5ARocqVerifyHarness?AgentSubmission5BothW5ABase6abkind02C5ARocqVerifyHarness?AgentSubmission5BothW5ABase6hb_idsC5ARocqVerifyHarness?AgentSubmission5BothW4ARep7xb_userC5ARocqVerifyHarness?AgentSubmission5BothW6AHeapP7sec_wf1C5ARocqVerifyHarness?AgentSubmission5BothW5ABase4ablkC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl<sec_map_sizeC5ARocqVerifyHarness?AgentSubmission5BothW6AHeapP9sec_clearC5ARocqVerifyHarness?AgentSubmission5BothW9ASecFacts9sec_factsC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl;needed_sizeC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC47Corelib4Init5Logic5proj2C5ARocqVerifyHarness?AgentSubmission5BothW5ABase7in_fakeC5ARocqVerifyHarness?AgentSubmission3Lib3Mem;wa_unsignedC5ARocqVerifyHarness?AgentSubmission5BothW6AHeapP>fake_untouchedC5ARocqVerifyHarness?AgentSubmission5BothW6AHeapP8hf_frameC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9evtF_monoC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface?afree_null_stmtC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkI47Corelib4Init5Peano2le00C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFC5ARocqVerifyHarness?AgentSubmission5BothW6AHeapP=sec_chunks_ofC5ARocqVerifyHarness?AgentSubmission5BothW6AHeapP4RSECC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl:is_primaryC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8AFREE_PCC5ARocqVerifyHarness?AgentSubmission5BothW5ABase6UDEPTHC5ARocqVerifyHarness?AgentSubmission5BothW5ABase5ATP88C5ARocqVerifyHarness?AgentSubmission5BothW5ABase4ATSDC5ARocqVerifyHarness?AgentSubmission5BothW7AQConst8AIA_BASEI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock00C5ARocqVerifyHarness?AgentSubmission5BothW6AHeapP8SEC_UOFFK47Corelib4Init9Datatypes4bool02C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9footprintC5ARocqVerifyHarness?AgentSubmission5BothW5ABase;AFREE_STACKC5ARocqVerifyHarness?AgentSubmission5BothW5ABase3ATPC5ARocqVerifyHarness?AgentSubmission5BothW5ABase9AFREE_SYMI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C5ARocqVerifyHarness?AgentSubmission5BothW7AQConst8AIA_FLAGC5ARocqVerifyHarness?AgentSubmission5BothW7AQConst8AIA_SIZEC5ARocqVerifyHarness?AgentSubmission5BothW7AQConst<AIA_MAP1_LENC5ARocqVerifyHarness?AgentSubmission5BothW7AQConst8AIA_MAP1C5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AINITEDC5ARocqVerifyHarness?AgentSubmission5BothW:F_aalloc_s7ARSSLIMC5ARocqVerifyHarness?AgentSubmission5BothW5ABase5ATSDIC5ARocqVerifyHarness?AgentSubmission5BothW5ABase5ATSDKI5ARocqVerifyHarness?AgentSubmission5BothW5ABase6abkind00".
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
ltac2:(KReplay.run1 (kr_t_AFreeNull ()) ["CANSEC1"] "p'0h01bh11kh21Hh32ivh41ch51Ah64__x1h74__x2h82_Hh93_H0h:7__arithh;4__ffh<8__varmaph=5__with>1qh?2Hqh@1zhA4__x3hB1ahC1lhD2l'hE2BShF2CPhG2CbhH2DGhI3DG1hJ3DG2hK3DG3hL2DQhM2DThN2GChO2GLhP2HbhQ2IAhR3IA'hS2KbhT1LhU3LN1hV3LN2hW2MUhX3ND1hY3ND2hZ2NNh[3NUMh\2OKh]2PSh^1Qh_2Sbh`2TCha2UThb1Whc2WMhd1Xhe1ehf1mhg2m'hh2sti001pi011xp%0p&0p;1p;5p;6p;4p;3p;2p;7p;8p;=p-1R0g0000R1p4p710p8P0g000QR2p4p710p8P0P2p4p7210p8p1000np4p70R0g001eR3p4p710p8P0g002<R4p4p710p8P0p1002Xp4p710p8P0p10035p4p710p8p1003Qp4p7210p1004=p4p710p8g004[j1?Tg005@k10FTg005^k10BTg006Ak10tTg006ck101Tg007Cj5nTg008<j1tTg009=j1QTg00:9j1FTg00;2j13Tg00;hj1fTg00<gj6PTg00=_j4RTg00>Xj1BTg00?Mj3vTg00@Ak20ITg00@aj1:Tg00AVj1lTg00B;j24Tg00BXj1jTg00CMj28Tg00DEj1NTg00E=j1pTP1j3=Tg00F=j1KTg00G:k103Tg00GXR1j20Tg00H3k10nTg00HSk20KTg00I1k40JTg00IOk10dTg00Imk10cTg00JXk20;Tg00K;k10bTg00K]k20aTg00L?k20`Tg00LYk20_Tg00MEj3oTg00M_k30^Tg00N>k40]Tg00O0j6{Tg00OPj4zTg00PVj37Tg00QRj29Tg00Qnk10[Tg00RLj16TP3j3>Tg00SCk70YTg00THj1WTg00U?R3j1rTg00V7k208Tg00W3k107TP4j6}Tg00Wij3qTg00Xcj1ZTg00Y]k10CTg00Z]k80VTg00[ej2]Tg00\?k40UTg00\^k30TTg00]8m=0ATg00^7k30STg00^Qj1iTg00_Kj2;Tg00`Dj1\Tg00a>k40QTg00a^k10:Tg00bUk204Tg00c1j4~Tg00cLk10oTg00dAk20MTg00e8k30mTP2k30lTg00elk30kTg00fIk20jTg00flk30gTg00gOk40fTg00h:k70eTg00h^k70hTg00iBk80iTg00ifj3ATg00jCS00k202Tg00j]k20LTg00k=k40<Tg00kYk20=Tf0R2#?#?p=Of4R4f3R0g00l2R5f2R6#Zf1R7#6&0C2EPp=T&0o700M2p=Y1072,06,00,04p=Xg00ln@0m72p=ug00mcR8@0l82p=C%?2#?#?$03p=U%l2#?p=JB0k882p=@%l2#lp=S19061972']p=2g00nAR9&0727>7p=519401467/92']p=1f7R:f6R;f5R<'4'91440/96']1072'0p=_g00o8R=00M2p=[P4P0P6P7CR/02p=m1072,06p=<20j82p=MB0g872p=dP6g00oXR>g0107R?P?g010WR@P8P7g0117P2H0fg011^K0ep=LP6P>P?P?P@P7P2K0hp=wP0P>P?P?P@P6P7P2L0ip>00%?2#lp=V%?2$03p>0\1]061072'0p>0H1]67/02p>0GP;P<P4P0P6P7P2C~C~p=sg012>R>?A72p>0Zg0138RAg0140S017o2p=xg014hRB9o82p=k%r29o87p=b20292p>0XAo872p>09A>972p>0E%r2-087p=a1972,]6p>0DP4P0P5P6P7P2EPp>0WP0P6P7%K2CRp=`AA6729>40p>06g015h20L>7g016G00L23op=g1;67=A02p>0@&0:29A67-040p=eP>P8P3P2H0<p>0R20482p=hP>P8P3AA>72H0<p=EA>86720292+0=p=I1;06%Z7/;25A4p>0P%\6&0:75A09><420292+0=p=DA=872,06,00p=^%F6/;7=A02p>05%F0/;6%Z7/;25A4p=H&0779>96/02p=G20487/02p=|A=872p=y%F7/;2p>0?%Z7/;2p>0>AA672#\p>0O1;06=A47#\=A<2p>0sA>06720292+0=p>0rP>P8P3%37%625A>H0<p=cA=872,06p>0N%62,;7p>0q%37,;6=A02p>0pg017Bg018<g0197g019ng01:fR3#?RC#?RD#?RE#ORF#?S02$0F$0B&0FE$0B$0t[S03Q03g01;K$01P;P<P4P0P6DnP1%t0P:P0%Q:%F;%34%f;EPP:P0P;P4P;DT1Y40P:P;P<P4CR%B;DXAv6401u<420I88RE%C2RGf;RH#:RI%lCRJ#?#URKPI%l3RI#?RL#J#URM%@2RNPGg01<=RO%JJ#S#US04'4S05%lI#J#S#US06,4OS07PNC2ROf:RJ,52PAp-0RP%j7RQg01=7RR%C6RSf=RT/87RUPU%N7S08#pRU%@6RVD1RWPWn011010003101000000[^09G_X3E;=4%[;f<RWPHPJf9RX#KP:Dn[[[[P2%t<PJP;%QJ%FX%3:%fXEPPJP;PXP:PXDT1Y:;PJPXf8RYP:CR%BXDXP1PHP:%QH%FJ%3Y%fJEPPHP:PJPYPJDT1YY:PHPJPXPY%BJDm3<Av;Y:1uXYPGf?RZ#:R[PKP[PMPNPOf>R[,52PAPPPQPRPSfAR\/87R]P]PUPVD1R]P]n011010003101000000[^09G_X3E==EY%[Jf@R]PZP[%KTPHDn[[[[P2PTPX%QT%FW%3J%fWEPP[PJPTPHPTDT1YHJP[PTPWPH%BTDm3<P1PZPHP[PWP[DT1YWHPZP[PTPWCR%B[3<AvJWH1uTWPGfCR^#:R_PKP_PMPNPOfBR_,52PAPPPQPRPSfER`/87RaPaPUPVD1RaPan011010003101000000[^09G_X3E==EW%[[fDRaP^P_%K\PZDn[[[[P2P\PTP]P[P]DT1YZ[P_P\P]PZCR%B\3<P11Y]ZP^P_P\P]%B_DmAv[]Z1u\]PGfGRb#:RcPKPcPMPNPOfFRc,52PAPPPQPRPSfIRd/87RePePUPVD1RePen011010003101000000[^09G_X3E==E]%[_fHRePbPc%K`P^Dn[[[[P21Y_\PcP`PaP^%B`DmP1PbPcP`PaCR%BcAv_a^1u`aPGfKRf#:RgPKPgPMPNPOfJRg,52PAPPPQPRPSfMRh/87RiPiPUPVD1RiPin011010003101000000[^09G_X3E==Ea%[cfLS09PfPg%KdPbDn[[[[P2PdPePbPcCR%BdAv`bc1uebPGfNRc#:RaPKPaPMPNPO152hPAPPPQPRPSfPRa/87RiPiPUPVD1RiPin011010003101000000[^09G_X3E==Eb%[dPdfORi#QS0:&03FRFPEPG%:aRjPKPjPMPNPO152iPAPPPQPRPSfRRj/87RkPkPUPVD1RkPkn011010003101000000[^09G_X3EPG%QaRkPkPFPND1X3EPGfQRk#:Rl/4KRm14lMRlPNC2Rn152aRoPAPPPQPRPSfSRp/87Rq14qURrPVC2RsPsn011010003101000000[^09Rs7<OX3EP2O1P1%C7RtPmPl%@7RlC2PtQ05Q07PlC2S0;PAPPPQPR%C0RmPqPr%@0RrC2RqPqn011010003101000000\o^09'0PS%QjS0<Q0<PFPVD1P2Pm%:pRo/4KPoPMPrD1%C4RoQ05Q07%@4RqC2S0=152pPAPPPQPR%C;RufVRv/87RwPwPU%@;RwD1RxPxn011010003101000000[^09'0g01=SRx$0nS0>&01xS0?P820K86S0@P720K80H0J&0d8S0A&0c8Rx20;83Ry20;8CRC%MK'dRz5LxR{%MM,dC20;8IRI5Lx5wx&0b?S0B%MFS0C,dz=LxI9wx{H0020ax@S0DP2P6g01>?R@00`=20_26=o@=dg01>_S0E>0^87H0]S0Fb;b<b=X68X78XA8P2147KP7PMP6D1P7146KR@P@PFP0D1[^68^78^A8P2Pw%:vPuP6O4b:%C<S0GfUR@#:/4KR=P=PF%@<S0HD1eQ0G%Q@R=P=PFQ0HD1eW8W5P7P2O2n2001000000121000000W2X3EPdP7E{CzQ0:=7dF%V3#J#S#V#S#S#V#J#UR=%?L$0\RL57g%V3#J#S#J#O#O#O#V#UR{&03DRD57gS0I%V3#J#S#J#O#O#O#J#URI=7gFS0J'0PgP=PLPEPG%V3#J#S#V#J#V#O#S#UR3Q04'4RzQ06,43R?PNC2R|=<nsX3ES0KPGP=14=LRsPNC2X3E%:jRn/4KS0L,9G14nMS0M/9NP|152kR|PAPPPQPRPSfTRn/87R}14}US0NPVC2R~P~n011010003101000000[^09H0HX3EP2O1S0OP1PtQ0LQ0MPlC2S0M19tz19?lPAPPPQPRPmP}Q0NPrC2R}P}n011010003101000000\|^0940GS0NPSP=PsPVC2P2Pm%:nR|/4KP|PMPrD1S0L19oz19?q152nPAPPPQPRPufWRq/87RoPoPUPwD1RoPon011010003101000000[^0940GS0PP1Q0GPzP?Q0HC2S0Q152@PAPPPQPR%C:S0RfXRo/87R|P|PU%@:S0SD1R|P|n011010003101000000[^09S0TPuP=PsPwC2P2Q0RPzP?Q0SC2R|152oPAPPPQPR%CJS0Uf[R}/87R~P~PU%@JS0VD1R~P~n011010003101000000[^09R~Q0>Q0?P8Q0@P7&0[8H0JS0@Q0APx%M3R3Q04#M'd9LxyQ06#M,d3=LxC5wxS06Q0B%M=R39Lxy%ML,d3=LxC5wxH00Q0DQ0Fb;b<b=X68X78P2PzP?P7C2R?P7P=PsP6C2[^68^78P2Q0VQ0UP6O3Rzb:%CXS04P=Ps%@XS0WC2eW9W5P7P2O2n2001000000121000000W2W8P7P2O2n2001000000121000000W2X3EPgP6E{CzQ0IQ0JPgP{PDPEQ0KPGP{14{DRsPNC2X3EQ0OP1Q0MQ0NPSP{PsPVC2P2Q0LQ0PP1Q0QQ0TPuP{PsPwC2P2Q0>Q0?Q0@Q0APxQ06Q0B%M{R=9Lxy%MD,d==LxC5wxH00Q0DQ0Fb;b<b=X68X78P7P{PsP6C2\?^68^78Pzb:Q04P{PsQ0WC2eX9~X5|P7P2O2n2001000000121000000W2W8P7P2O2n2001000000121000000W2X3EPgP6E{CzPgPIPFPEQ0KPGPI14IFRsPNC2X3EQ0OP1Q0MQ0NPSPIPsPVC2P2Q0LQ0PP1Q0QQ0TPuPIPsPwC2P2Q0>Q0?Q0@Q0APxQ06Q0B%MIR{9LxyQ0C,d{=LxC5wxH00Q0DQ0Fb;b<b=X68X78P7PIPsP6C2\?^68^78Pzb:Q04PIPsQ0WC2eX9~X5|P7P2O2n2001000000121000000W2W8P7P2O2n2001000000121000000W2X3EPgP6E{CzFsg01?=R|=7gLg01@6R~=7gDA7g5F3<RsePsP1A7f|LA7f~DA7f5F'0%thPjPhQ0<%Fk%3i%fkEPPjPhPkPiPkDT%[hPjPkPa%Ki%BkDmDXP2A7h|LA7c~DA7c5F'0P1A7i~DA7i5F%tkPvPk%Qv%F@%3p%f@EPPvPkP@PpP@DT%[kPvP@Pn%Kp%B@DmDXP2A7k~DA7j5F%3qRj%6qRF+0ZS0<9>>2S0OP}fZR~fYRDPoP7P\P2K0Y152~S0L%j2S0P#xRp%N2S0F#kR|%W2RL/b6'03<X09$0XQ00P9152}S00%r0Rf-09L,0|7<pX09f]Rs008fg01A1Rf57qP2152sS0D1bL<,0|7<pP1f^RI$07S0C-0E7%xQQ08#k%W7/b;3<faRz/a:=7}fP2f`R?,50%j4#x%N4#k%W4/bX3<P1%j<#x%N<#k%W</bJ'0f_RxfeRC/aH;7fP2%j:#x%NY#k%WY/bT'0P1%NX#k%WX/b[fcRYfiR:/aZ;7fP2%NH#k%WW/b\ffR{flRy/a_PfPEPGfmR_#:R=PKP=PMPNPO152yPAPPPQPRPSfoR=/87R3P3PUPVD1R3P3n011010003101000000[^09G_X3EPG1a_^R3P3PfPND1X3EfnR3#:S08/4KS0B,9GQ08/4MS08/9NPO152_ROPAPPPQPRPSfpRN/87RG14GUS06PVC2S0AQ0An011010003101000000[^09H0HX3EP2O1P1PtQ0BQ08PlC2Q0;PAPPPQPRPmPGQ06PrC2RGPGn011010003101000000\O^09'0PS1a=`RSPSPfPVD1P2Pm%:NRm/4KPmPMPrD1Q0=152NRrPAPPPQPRPufsRM/87RmPmPUPwD1RmPmn011010003101000000[^09'0P1Q0GQ05Q07Q0HC2fqRm,52PAPPPQPRQ0RftRK/87RVPVPUQ0SD1RVPVn011010003101000000[^09Pu1aMdRuPuPfPwD1P2Q0RQ05Q07Q0SC2152KPAPPPQPRQ0UfwRQ/87RwPwPUQ0VD1RUPUn011010003101000000[^09P2PbP^O2PAPP%jbPRQ04fvR^/8bRUPU%Nb#pQ0WD1RbPbn011010003101000000PA%jePAPPP2PR%CHRRfxRP/8dRbPb%NdRb#p%@HRUD1RwPwn011010003101000000X0AP2Q01P]E}Q0U18QeRwPw%Ne#pQ0VD1P8Pb%CWRbfyRw%WgRu7q2RVPV%p2%@WRWD1X@8P2PBPTE}PR%Wd9qPBRPPP%pBRPPUD1P8Pu%CTRufzRU?qB2RRPRPP%@TRRD1X@8P2%riRVPTE}PbAqwBVRVPVPPPWD1P8PP%C[RPf{RW%rkRk7qBRV'9Rw14V2%@[Rb40DX@8P2Q02#O#O#URSg01B1E}Pu%ra9qUBRUPUPSPRD1P214VS>0DwbePP208WkRkPkPfPbD1eb5b5b5b5b5W5W9P7P2O2n2001000000121000000W2W8P7P2O2n2001000000121000000W2X3EP{PcE{CzWSWGP7P2O2n2001000000121000000W2W_P7P2O2n2001000000121000000W2WPP7P2O2n2001000000121000000W2X09P7P2O2n2001000000121101000beW?X>>Q0O1a}7=7@f[^>>%t@P~P@%Q~Rf%FDRbPj%fDRkEPRWP~P@%ZDRPPF&0CDRwI0WRS%[@RVP~PDPoPqC`RR%BDRU'0RB'0Ru'0RG'0PnPvP@P[PTPaP;P6L0VPWPGP~PnPvP@P[PTPfPbPjPkQ09PJ%3oRJ9>>2P6P7g01C3p4p710Rk&012Rf&017RGP1P0P2P0P6P7I06A>470A>476']RW[A>026A>027']P4P7P4P0P6I06[R;P<P6P<P4P0I06\WP0P6P7P2H0UP2n2001000000120000000XB6WDWCW5R0P;^B6^DG^Cf^5kRkP2P>%3~Rf%6~RGP6A>>6fR;A>>6GRW<0T7O5b2O2W?X>>N=0APSPuP~PnPvP@P[PTP5PPPFPwPeP7%6oRe9>>2P6P7P0PkP2P>PfPGP6B0S;W7O5b2O2W?X>>N=0APVPBPHPRPUP11gjb1gFPg01CP00I8RU%ioPUPbPj1;PFH0@RP3=PEPE%\PPqCeQ0<$0RRq#h1EJeQ0L209L7RL9<p|R|'0X095I2^18PEP8P8P7P2H0QRpPEPU%F}Re%3DRJP}%6DI0PPDQ00Q0Pg01DK5oAQ0F0096;<LRL'0X09ED^18^48Q0E/92X18R6PqC^DXP}P~PDPoC`P]1gJef\RJ#ZRe,gG%i}PUPJPf1;eGH05Re5=UPEPE%\eP~Ce1EfGRG#h%3}Rf%6}R~'EReQ0D/0|X095I2^18PEPpPEPUPI%3JR]PI%6JRoDHPJQ0C-0E2RD/0LX09ED^18^48P6PGC^DXP1%ZsRG,g~%iJPUPsPf1;G~H05RG5=UPEPE%\GP}Ce1E]o10D|X095I2^18PEPpPEPUPx%3s%ZxRD%6sRo';H05PsAG2xLX09ED^18^48P6PeC^,|e3<PxPIPsPJC`P21goD%ixPUP?%3IRoP?%6IRDDHRJ5=UPEPE%\JPICe1EoDRD%3xRo%6xRI'ERJAG2z|X095I2^18PEPpPEPUfbRs%3?RePs%6?R]DHP?152sR}/0LX09ED^18^48P6PDC^'|3<P1%i?PUPzPoPzPIDHRI5=UPEPE%\IPxCe%hJ1Ee]10}|X095I2^18PEPpPEPUPY%3zPY%6zDHR}PzAG2YLX09ED^18^481y6JDXPYPsPzP?C`P2%is==U}PEPEfdR}%3sR?+0?%6sRz-0>}60OUPsCe1E?zRz#h%3YR?%6YRs'ERJAG2C|X095I2^18PEPpPEPUP{%3}R]P{%6}ReDHP}152{Rx/0LX09ED^18^481y6zDXP1PEPE20?C?20>Cs60OUPYCe1E]e10x|X095I2^18PEPpPEPUfgRx#F%3C%6C-0>x&0:CJ0sReAG2xLX09H0r^18^48P6PJC^,|JPxP{PCP}C`P2204Ee1c{{R{1cxxRxAG2:|X095I2^18PEPpPEPUfjRefhR}#3RCPe%6}RJDHP}152eR]/0LX09ED^18^48P6P{C^'|P1%hx1ECJ10]|X095I2^18PEPpPEPUfkR]%3:RJP]%6:RCDHP:AG2]LX09ED^18^48P6PxC^P]PeP:P}C`P21EJC#h1c]]R]10O|X095I2^18PEPpPEPUP3%3yROP3%6yRCDHPy1523RJ/0LX09ED^18^48P61ceeC^P11EOC10J|X095I2^18PEPpPEPUP=%3_P=%6_DHP_AG2=LX09ED^18^48@0N6]P=P3P_PyC`P21c33R310r|X095I2^18PEPpPEPUfrRr%3NPr%6NDHPNAG2rLX09ED^18^48@0N63P1PEPpPEPUPM%3mPM%6mDHPmAG2MLX09ED^18^481c==,y6PMPrPmPNC`P2PEPpPEPUfuRN#FRmPM%ZNR=00qMH0pPMAG2NLX09ED^18^481crr,y6%KMRM#3Rr/gmR1%6MR3/g=Ry%iKPUPmPr1;=3H0@R=5=URmPEPE%\=PMCeR=1Er3R3#hRr%KKR_/c_AG2^|X095I2^18R|PEPpPEPUPQ%KNRU#3PQ%6UDHPUAG2QLX09ED^18^48R81y63R3'0R6'0R9'0RL'0RQ'0RU'0REPdPyPUP`PmPQP\P=PLPTPrP9PXP|P6P<P8P3P7P2C~FsFsFs101EREePEeP^PNPKPMCReWZW]P7P2O2n2001000000121000000W2WEP7P2O2n2001000000121000000W2WYP7P2O2n2001000000121000000W2WXP7P2O2n2001000000121000000W2W\P7P2O2n2001000000121000000W2WVP7P2O2n2001000000121000000W2WUP7P2O2n2001000000121000000PZC~FsFsbLWKWJP7P2O2n2001000000121000000W2WIP7P2O2n2001000000121000000bHbM%tgPiPgQ0:%FcQ09#KRZ#3%fcEPPiPgPcPZPcDT1YZgPiPcPhPZ%BcDmDXePiPcPhPZPgDneWRWaWcWWW[WFP7P2O2n2001000000121000000W2WQP7P2O2n2001000000121000000W2WOP7P2O2n2001000000121000000W2W`P7P2O2n2001000000121000000W2WNP7P2O2n2001000000121000000W2WbWgWfW^WdWhWTo"). Qed.

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
