(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (8 recorded proofs replaced by written proofs (AHr_laws, ASECc_wf1', ASECc_disj' and 5 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF ITreeA StepF SysStepF.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg AProto ABase ABytes AQConst AKitQ AMalloc_iface ADepot_iface ARep ARepQ ARepQP ARepQR ARepQD ALayout AHeapP ARepKit ARepFrame
     AKit AKit2 AModelFacts ASec ASecStore AFreeModel AFreeModelR AFreeRep AFreeGeo AFreeRead F_apoison F_aalloc_s F_aalloc1 F_afree_tail F_afree_icpt F_afree_arep
     F_afreeC_iface F_afree_icptC ASecRecycle_iface ASecRecycle ARecyc1P ARecGeo F_adorec F_aqrec_iface F_aqrec AQrecP ASF_kit ASF_refill AFreeC_kit_iface
     AFreeModelC AFreeReadC ASecFacts ASF_read ASF_fast ASF_C_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ASF_fastC () := "I47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstI59OSSVerify5KrLib4Spec5STree5stree00C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rI35stdpp9countable9Countable00C35stdpp4base;RelDecisionC59OSSVerify5KrLib4Spec8AsanCtrl2AMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl4aptrC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2hdC35stdpp8fin_maps:map_deleteC35stdpp4gmap;gmap_lookupC35stdpp4gmapBgmap_partial_alterC35stdpp4base6LookupC35stdpp4base6DeleteI35stdpp4gmap4gmap00C35stdpp4base4fmapC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC59OSSVerify5KrLib5BothW5ABase4sclrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01I47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3mulI47Corelib4Init5Logic2ex00K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr05C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init5Logic2ex01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic2or00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib5BothW5ABase4iclrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4ablkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega5Tauto8GFormula03I59OSSVerify5KrLib3Lib8RunConst9runConstT00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C59OSSVerify5KrLib5BothW7ALayout4aobjC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06K47Corelib4Init5Logic3and01K47Corelib4Init5Logic4True01C46Stdlib5Lists4List2InC59OSSVerify5KrLib5BothW4ASec7ASEC_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<F_afree_arep3AHQC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW6AHeapP:ahole_laws00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ASec5ASECcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<ADepot_iface6ADEPOTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW8ARecyc1P3AHrC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib5BothW4ARep7ah_quarC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP>quar_untouchedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP9quar_sameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6ah_secC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP=sec_untouchedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP8sec_sameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8ah_depotC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib5BothW5ABase8al_nodesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase8al_storeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7ah_fakeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP>fake_untouchedC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW5ABase6abkind02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW5ABase6ablock01C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffC59OSSVerify5KrLib5BothW6ARepQD4AQdrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ARepQD:AQdr_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:ASF_refill<sec_same0_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ASF_kit;asecc_frameC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW6AHeapP:ahole_laws01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW6ARepQR6qrconc00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6achunk00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW5ABase7alayout00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6astate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep5aconc00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3ivlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4BImg5bsegsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW5ABase6ablock00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ASec7asec_wfC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW7ALayout:alayout_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;a_ptr_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase<al_ptr_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_nresC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_nsecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ASec<sec_disjointC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ASec6aprim0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ASec4ashzC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ASec8asec_arrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ASec9asec_instC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP7sec_wf1C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natK46Stdlib9micromega:ZMicromega;ZArithProof03I59OSSVerify5KrLib4Spec8AsanCtrl6abatch00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP6sec_mbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP6sec_msC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF3rngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed4shadC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:Forall_appC47Corelib4Init9Datatypes3appC59OSSVerify5KrLib5BothW6AHeapP4RSECC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF9footprintC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP4arngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4al_tC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase6al_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7al_fakeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed5shlenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7get_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7aregionC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=c_mapped_userC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8afreearrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrlCc_mapped_free_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase<al_space_begC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib5BothW6AHeapP=sec_chunks_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout7al_dtlsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<K_SPACE_SIZEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_SPACE_EXTRAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_NUM_CLASSESC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6aclass00C1?~~~~~~~~~~~~~~~C35stdpp4base6lookupC35stdpp4base6deleteC59OSSVerify5KrLib4Spec8AsanCtrl6a_liveC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8AsanCtrl6achunk02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<a_qloc_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=a_qglob_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP7AHEAP_PC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW5ABase6abkind01C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib5BothW=AMalloc_iface4aunwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase6al_topC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4al_UC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib5BothW5AKitQ9afree_unwC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW5ABase6uchain00C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C59OSSVerify5KrLib4LibA6NodesA8at_nodeAC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=AMalloc_iface:afree_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP7ablocksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep4AREPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep3awfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7arep_rtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep9ainstanceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7athreadC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep<aslot_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep=ashadow_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6arelroC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8arep_rt2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8arep_rt3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ8AQUAR_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ASF_kit?freed_block_secC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ASF_kit>sec_wf1_facts'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<sec_map_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;needed_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl:is_primaryC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP9sec_clearC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase8ablk_linC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9ASF_fastC8ablk_intC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout6al_resC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;Permutation@Permutation_reflC59OSSVerify5KrLib5BothW7ASF_kit>read_chunk_secC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltK59OSSVerify5KrLib3Lib5Cells4cell03C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARepBblock_shadow_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout9alayout_tC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout;alayout_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout=alayout_depotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout=alayout_stackC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase6al_botC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout8ao_spaceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5AKitQ>afree_unw_sp47C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC59OSSVerify5KrLib5BothW7ASF_kit:rup8_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl3rupC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC59OSSVerify5KrLib5BothW9ASecFacts9sec_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<rounded_sizeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01C59OSSVerify5KrLib5BothW9ARepFrame8shad_divC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;a_space_begC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5x_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=size_of_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl@c_allocated_userC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;c_num_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7xc_freeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8xc_cacheC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7c_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8xb_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5xb_stC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep4xb_nC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7rz_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5xb_b1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6xb_ctxC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8AsanCtrl6achunk01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6x_busyC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW4ARep6bstate01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ;abatch_addrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C59OSSVerify5KrLib5BothW9ARepFrame>slot_in_regionC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indK46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib5BothW4ARep:aslot_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase8ablk_subC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ABytes<rw_cells_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep<acache_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7a_cinitC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC59OSSVerify5KrLib5BothW7ARepKit:junk_splitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7junk_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ARepKit:c8_of_junkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ@aquar_glob_constC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7AQConst9aq_tcacheC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_qlocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ5q_locC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ7aqcacheC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ4q_iaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ6qfirstC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ5qlastC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ8abatchesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7a_qglobC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ6q_globC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ8qcoupledC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ4qnumC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=batches_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6b_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ARepQP@batches_bytes_lbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AFreeRead<st_enq_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:AFreeModel6st_enqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl:chunk_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AFreeRead5ek_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AFreeRead:enq_is_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<F_afree_tail6ek_preC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<F_afree_icpt7ek_sepsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<F_afree_tail8ek_deltaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<F_afree_tail4ek_bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW8ASF_read<read_ek_appSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7b_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl8b_chunksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ5qb_ksC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib5BothW9AFreeRead?enq_is_app_specC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:AFreeModel7enq_appC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic9False_indC47Corelib4Init5Logic5proj2C59OSSVerify5KrLib5BothW8ASF_read<read_ek_newSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ7qb_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW8ASF_read9read_dkSCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AFreeRead4g_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW>F_afreeC_iface7dk_preCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<F_afree_icpt7dk_sepsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<F_afree_tail5g_lstC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<F_afree_tail7dk_glstC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl4aretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AFreeRead;bslot_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AFreeRead9bslot_geoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:AFreeReadC<qfirst_casesC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9in_or_appC59OSSVerify5KrLib5BothW:AFreeReadC;qlast_casesC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<nth_error_InC46Stdlib7Sorting;Permutation>Permutation_inC46Stdlib5Lists4List=Forall_forallC59OSSVerify5KrLib5BothW>F_afreeC_iface?free_torec_postC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC59OSSVerify5KrLib5BothW9F_aalloc1<allocA_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9F_apoison<poison_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF7rng_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=F_afree_icptC:free_torecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase9lb_removeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW@AFreeC_kit_iface;storeC_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:AFreeModel8st_afterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW>F_afreeC_iface9put_frameC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;ASecRecycle4srecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7F_aqrec:qrec_frontC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ASecStore:ASECc_permC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AQrecP9aqrec_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA:fp_le_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF9evtF_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF8evtF_cutC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA8SysStepF?implF_from_evtFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AFreeModelC<afree_rec_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl8set_liveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C59OSSVerify5KrLib4Spec8AsanCtrl5afreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed6aembedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA6epostFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA5implFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6aslotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep:afreearrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep=aregion_cellsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib3Lib3Arr6u64arrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ASec8sec_liveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ASec:asec_chunkC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell04C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC59OSSVerify5KrLib5BothW4ARep7fill_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natI46Stdlib7Sorting;Permutation;Permutation00C46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr04C59OSSVerify5KrLib5BothW4ARep5ndistC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep:busy_slotsC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List5NoDup00C59OSSVerify5KrLib4Spec8AsanCtrl9max_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_nextC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2ltC59OSSVerify5KrLib5BothW4ARep;acache_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8acompactC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr6u32arrC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6mkapp2C59OSSVerify5KrLib5BothW5ARepQ6aintalC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7busy_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ5qhdrsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW<F_afree_tail8enq_kind01C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List4lastK59OSSVerify5KrLib5BothW<F_afree_tail8enq_kind02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<F_afree_tail7g_drainC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7recycleC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW8F_adorec3csxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW@AFreeC_kit_iface3AHcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ARepQR6qr_tmpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ARepQR8qr_pendbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ARepQR7qr_pendC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=AMalloc_iface:aheap_presC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF4evtFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AQrecP5aqrecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl5Q_MAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_BATCH_CLASSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase8AFREE_PCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase6UDEPTHC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AProto6fstepSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7AREQMAXC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib5BothW5ABase7AIMG_HIC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP8SEC_UOFFC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega=RingMicromega3Op205C59OSSVerify5KrLib4Spec9AsanEmbed6ASHOFFC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201C59OSSVerify5KrLib4Spec8AsanCtrl7K_ALIGNC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_OFFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl:K_USER_MAPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_MAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_MAPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7aclass0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep5xbusy00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C59OSSVerify5KrLib5BothW5ABase5ATP88C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4ATSDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep<ASTATS_WORDSC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC59OSSVerify5KrLib5BothW7AQConst9AQ_GCACHEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7AQConst8AIA_BASEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7Q_CACHEC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW5ARepQ7qbatchc00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW<F_afree_tail8enq_kind00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AFreeRead;dummy_batchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AFreeRead8dummy_qbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl5Q_MINC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00c59OSSVerify5KrLib5BothW9ASF_fastC8AHr_lawsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9ASF_fastC:ASECc_wf1'C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9ASF_fastC;ASECc_disj'C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9ASF_fastC;ASECc_nres'C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9ASF_fastC<ASECc_qglob'C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9ASF_fastC9RSEC_app'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP9RSEC_permC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP9RSEC_monoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9ASF_fastC:RSEC_arng'C1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableC59OSSVerify5KrLib5BothW5ABase;AFREE_STACKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase3ATPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase9AFREE_SYMC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW5ARepQ5qconc00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00I59OSSVerify5KrLib5BothW4ARep6xclass00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep6bstate00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AFreeRead3K24C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ARepQP@size_of_class_24C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C59OSSVerify5KrLib5BothW7AQConst6AQ_MAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7AQConst8AQ_MUTEXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7AQConst8AIA_FLAGC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7AQConst8AIA_SIZEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7AQConst<AIA_MAP1_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7AQConst8AIA_MAP1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=Q_BATCH_BYTESC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List6Exists00C59OSSVerify5KrLib4Spec8AsanCtrl7Q_BATCHC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW<F_afree_tail3gqd00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7AINITEDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:F_aalloc_s7ARSSLIMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase5ATSDIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase5ATSDKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7AQConst7AQUAR_QC1?~~~~~~~~~~~~~~~".
(* [comment removed for export] *)
(* [comment removed for export] *)
Import ListNotations.
Set Keyed Unification.   (* [comment removed for export] *)
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

(* [comment removed for export] *)
Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_ASF_fastC ()) [] "h04__x1h14__x2h21Hh37__arithh44__ffh58__varmaph65__with71kh82G1h92G2h:1ah;1np;2p;1p;4p;3p;7p;8p-1R0p10000p4p710p8P0p1000QR1p4p710p8P0P1p4p7210p8p1000nR1p4p710p1001ep4p710R0p8P1p4p7210P0p8p1002Cp4p710R1p1002aR2p4p710R3p8P1P2p4p7210R2p8p1003:p4p710P0p8p1003op4p70R4p1004fp4p710p8P4p1005=p4p710p8P4p1005Yp4p710p8P4p10062p4p710p8P4p1006Rp4p710p8P4p1006fp4p710p8p1007:p4p710R4P1p8P4P3p8P4P2p8P4p1007Np4p73110p8p1007`p4p7210P0p8g008Lj2WTg009Aj20Tg009]j22Tg00::j11Tg00:_j1;Tg00;=j16Tg00;bj23Tg00<=j29Tg00<Zj2VTg00=4j1UTg00=Tj1TTg00>4j2PTg00>Rj1OTg00?0j4NTg00?Nj1LTg00?lj1KTg00@Wj2:Tg00A:j2ATg00A]j1ITg00B?j3>Tg00Bbj3=Tg00CEj2HTg00Cgj2JTg00DAj2GTg00Dmj3FTg00EGj3MTg00Efj4ETg00FXj4CTg00G2j4QTg00G]j7DTg00HAj7RTg00Hej8STf0R0#1#1#1#1p=?%10#1#1#1#1#1#1#1p=5%10#1p=B%60#6p=@%60#6#6#6p=7f2R4g00IIR2g00IhR3P3g00JHR1g00JhR5f1R6g00KFP0CQg00KmFDp=4P4P2P3P3P1P6P0FRp=8f3R7P2P3P3P1P4P6P0GSp=<1W60g00LMR2/041274g00LkR8#1R9#?#5R:#1#B#5#5#5#5#5#5#;R;'0g00MPf4R</27%@8#7#7#7#1#6#@#?#5#;R='0%7:#7#7#7#1#B#?#5#;R:/0<1020R>%;8R?,00'3R@f6RAf5RB'2190;,2=RC'019:0RD/0A'3'3X75,V5P412B</0=P5f7RE/2A/0C10DE'3,3@X75R@P2g00MjRD#URC%TDRDP51P54P6%O5CNRF%L5RG%K5RH1:52RI1A58R854H%I3R3PH1A599>58R91:5=RJ54HP3A4HII1:5?RK94HIRL58H1:5;RM9=5I9>5J94H91:5:RN==5I=4H858H58HC<C<1HH1R1P0P4g00NVRIg00O6RO'J1G04=FIOdAM526CEROb4b5b6X05X151264/0=1022102?RI'31247RP192;,2='019:2/04'3'3[\>^05^15P0PAPEP<P6O4b3CCW2P0O110:BP5P@P?PCPDPFPGPHA4H9MP3PHA4HN8P3A4HKK98HLA=5KM9>5J94H9A=5NK=4H858H58HC<C<P1POb4b5b6X05X151206/0;10:610??,3I19?;,2=,0P19:?/04'3'3[[^05^15P0PAPEP7P6O4b3CCW2P0O1n200100001021100011000W9W8W2X;5X:5o"). Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6352896 * k <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_ASF_fastC ()) [] "h04__x1h14__x2h22H0h31kh41Hh57__arithh64__ffh78__varmaph85__with92G2h:1ah;1np;2p;1p;4p;3p;7p;8p-1R0p10000p4p710p8P0p1000QR1p4p710p8P0P1p4p7210p8p1000nR1p4p710p1001ep4p710R0p8P1p4p7210P0p8p1002Cp4p710R1p1002aR2p4p710R3p8P1P2p4p7210R2p8p1003:p4p710P0p8p1003op4p70R4p1004fp4p710p8P4p1005=p4p710p8P4p1005Yp4p710p8P4p10062p4p710p8P4p1006Rp4p710p8P4p1006fp4p710p8p1007:p4p710R4P1p8P4P3p8P4P2p8P4p1007Np4p73110p8p1007`p4p7210P0p8g00OVj2YTg00::j11Tg00:_j1<Tg009Aj20Tg00;=j1:Tg00MPR0j2DTg009]j23Tg00<=j27Tg00<Zj2ETg00=4j1VTg00=Tj1UTg00>4j2TTg00>Rj1RTg00?0j4QTg00?Nj1PTg00?lj1NTg00A:j2BTg00B?j3@Tg00@Wj28Tg00A]j1KTg00Bbj3>Tg00CEj2JTg00Cgj2ITg00DAj2HTg00Dmj3MTg00EGj3GTg00Efj4OTg00FXj4CTg00;bR4j2?Tg00G2j4FTg00G]j7STg00HAj7XTg00Hej8WTf0R2#1#1p=L%12#1#1#1#1#1#1#1p=5%12#1#1#1p=Af2R3f1R1'3/02p=;1031/?2p=61?12,?3p==P3g00IIR5g00IhR6P6g00JHR7g00JhR8P1g00KFP2CFg00KmFSp=2P3P5P6P6P7P1P2FXp=4f3R9P5P6P6P7P3P1P2GWp=91Y12g00LkR5#1R:#1#L#5R;#AR<#5#5#5#5#5#5#<R=9;31P4%<;R;/09R4%<<R<9;93%:5#1#A#:#:#:#:#A#5#<R>/09'Dg00LMR?%<5R@,02762RAf5RB,0;RCf4RD,3B172=,3<RE17>2RF/0B363=X38,E8P1f6RG?;B<10>G'DP0f7R0?;G<10>0f9RG,0;f8RB,3G10FG76E5=AX38,E8P2A;B0<P8f:RH,0;13HG10FH76E5=AX38RAP?g00MjRE#VRF%UEREP81T83P1%R8CQRI%P8RJ%N8RK1B85R51B8:5@8R:188<RL52K%K6R6PK188;=2K5RMP6188?RN=2KN188@RO92KNRP54K188=RQ9>8N9@8L92K:188>RR=>8N=2K554K94KM54KC9C91JK7R7P2P3g00NVRNg00O6RS'I1H23=MNSdAG8?1CORSb6b7b8X08X181321RN/0<10;110?@RT96??10;3R;133917?=,3<17>?/03363=[[^08^18P2PGPHP1PDO4b5CCW2P2O110>BP8PAP@PFPEPIPJPKA2K:QP6PKA2KR5P6PKPMP6A2KOO94KPA>8OQ9@8L92K:A>8RO=2K554K94KM54KC9C9C9P7PSb6b7b8X08X1810N=10>110@@,?T139D17@=,3<17>@/09367=4\;[[^08^18P2PGPHP0P1PDO5b5CCW2P2O1n200100000021100011000W2X4CP1P2O2n2001000000121000000W9W4X;8X:8o"). Qed.
Local Lemma ablk_int {rc : runConstT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6352896 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof.
ltac2:(KReplay.run1 (kr_t_ASF_fastC ()) [] "h01Hh14__p1h24__x1h34__x2h44__x3h51kh62rch72H1h87__arithh94__ffh:8__varmaph;5__with<2H0h=2hih>2lop;3p;1p;2p;4p;6p;7p;8p-1R0p10000p4p710p8P0p1000QR1p4p710p8P0P1p4p7210p8p1000nR1p4p710p1001ep4p710R0p8P1p4p7210P0p8p1002Cp4p710R1p1002aR2p4p710R3p8P1P2p4p7210R2p8p1003:p4p710P0p8p1003op4p70R4p1004fp4p710p8P4p1005=p4p710p8P4p1005Yp4p710p8P4p10062p4p710p8P4p1006Rp4p710p8P4p1006fp4p710p8p1007:p4p710R4P1p8P4P3p8P4P2p8P4p1007Np4p73110p8p1007`p4p7210P0p8g00PKj3bTg00Q@j1aTg00;=j15Tg00::j11Tg00:_j19Tg00R>j18Tg009Aj20Tg00;bR0j2>Tg00<=j2=Tg009]j2ETg00<Zj2JTg00S4j1DTg00SSj2CTg00T<j3ITg00Tej2VTg00=4j1UTg00UQj3TTg00=Tj1STg00>4j2GTg00?0j4RTg00?Nj1QTg00?lj1PTg00A:j2BTg00V1j6OTg00A]j1NTg00@Wj2FTg00Bbj3ATg00B?j3HTg00CEj2MTg00Cgj2`Tg00DAj2_Tg00Dmj3^Tg00EGj3[Tg00Efj4ZTg00FXj4KTg00G2j4YTg00G]j7\Tg00HAj7WTg00Hej8]Tf0R4#5#5#5#5p=7%54#5p=X%14#1p=@%14#1#1#1p=:%14#1#1#1#1#1#1#1p=3f2R2f1R3'0/>4p=21>34,>2p=?g00JhR1/F4p=;P2g00IIR5g00IhR6P6g00JHR7P1P3g00KFP4CYg00KmF\p=4P2P5P6P6P7P3P4FWp=6f3R8P5P6P6P7P2P3P4G]p=<1034,>2p=Lg00VUR9Ab234%a8g00LkR:#5R;#5#7#7#7R<#1#5#XR=#5#7#1#@#:#3#3#9R>%88R?%5<#7#7#1#@#:#3#3#9R<,0?32g00MP%5:#1#:#7#:#3#9R?/08R@%:=#3#9R=,02RA'>%1:RB#:#3RC#7#7#7#7#1#@#:#3#9RDf4RE#8,02728g00LMRF%9:RG,04724RHf5RI,0?RJ1=D4RK%1C#@#3#3#3#3#3#3#9RC,=4,E=RLf6RM#8,0ERN52E72I3?X51,J1P3108=92?EP0PJ10E=f7RJ,0?ROf8#8,0M92ML92KJ5?HX51,J1RMP410J=P1f:RP,0?f9RQf;#8RR,0Q72L92KP5?HX51RHPFp-0RKg00MjRLg00WRRS#D#DRT#D,C11C1T1C1S5I15I1g00X1'V%UL3TRS%SLRLP11G12P31G18CRRT%Q1RU%P1RV%;>1B1;R;54VPVP5P6P6P7PIEOR556V%N6R6PV1B1BRB%;=RW54VP6PV%;?1B1:R:54VRXP61F1FRY=4VY%;GRZ94VYR[56V%;DR\=A1Y=4V:%;CR]9A1Y9H1W94VBA4VB;RY56V56V96VX56VC<C<C<1MV7R7P4P2g00NVR^g00O6R_'`1_42=^^_dA[1F3CZR_b9b:b;X21X31X41W1A2>2810?210FGR?92FF1=DF1=FC,E=10EIRF52E7287?@[\A[^21^31^41^1KP410R<PRPQPPPJP3P2O7b8CKW7X0OP3P4O2n2001000010121000000W0P4O1%8I,0892DEP010DIPNPMP410DJ%8Q,0JP1PHPGPSPLPTPUPV%;<94V;96V5P6PVPYP6PVA4V\:P6A4VZZ96V[AA1\Z=4V:AA1Z]9H1W94VB=6VY56V96VX56VC<C<C<P7P_b9b:b;X21X31X41X1KAL82<102810D2AL?GG1=DG1=GC,E==2EF7287?@[[[^21^31^41^1KP410>RPRPQPPPJP3P2O7b8CKW7W0P3P4O2n2001000010121000000W0P4O1n200100001021100011000b<W0X=1X>1X69P4O1X69P4O1W6o"). Qed.
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
(* [comment removed for export] *)
Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
  6352896 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_ASF_fastC ()) ["CANSEC1"] "h04__x1h14__x2h21Hh31kh47__arithh54__ffh68__varmaph75__with84__x3h94__p1h:2H0h;2H1h<3H10h=2H2h>2H3h?2H4h@2H5hA2H6hB2H7hC2H8hD2H9hE2HnhF6__sat6hG1ahH1np;3p;1p;2p;4p;7p;6p;8p-1R0p10000p4p710p8P0p1000QR1p4p710p8P0P1p4p7210p8p1000nR1p4p710p1001ep4p710R0p8P1p4p7210P0p8p1002Cp4p710R1p1002aR2p4p710R3p8P1P2p4p7210R2p8p1003:p4p710P0p8p1003op4p70R4p1004fp4p710p8P4p1005=p4p710p8P4p1005Yp4p710p8P4p10062p4p710p8P4p1006Rp4p710p8P4p1006fp4p710p8p1007:p4p710R4P1p8P4P3p8P4P2p8P4p1007Np4p73110p8p1007`p4p7210P0p8g00X]j3yTg00::j12Tg00:_j1;Tg009Aj20Tg00Q@j1oTg00;=j17Tg00R>j1^Tg00YTj2BTg009]j21Tg00<=j2?Tg00;bR0j28Tg00Z4j2dTg00Zej2cTg00[Fj1aTg00[_j2STg00Dmj3LTg00\<j2`Tg00\cj2KTg00]?j2_Tg00]fj2]Tg00^Lj2\Tg00_2j2[Tg00S4j1JTg00SSj2GTg00T<j3NTg00Tej2ZTg00=4j1xTg00UQj3YTg00=Tj1wTg00>Rj1vTg00>4j2XTg00?0j4HTg00?Nj1uTg00?lj1tTg00A:j2PTg00A]j1rTg00B?j3MTg00_nj7qTg00CEj2pTg00Cgj2nTg00DAj2mTg00EGj3lTg00Efj4kTg00@Wj2UTg00Bbj3OTg00FXj4VTg00V1j6iTg00`Rj4TTg00MPR4j2WTg00<Zj2hTg00G2j4gTg00G]j7fTg00HAj7sTg00Hej8eTf0R2#2#2p=D%22#2#2#2#2#2#2#2p=5%72#7#7#7p=9%72#7p=b%22#2#2#2p=@f2R3f1R1/02'8p=Eg00JhR5g00LMR67L2p=Qf3R7/031012'Wp=31812,83p=R1031/82,87p=:1062p=C1131/02p=F1012,83,87p=I1h52p=A1031/82p=61U52p==P3g00IIR8g00IhR9P9g00JHR:P5P1g00KFP2Cgg00KmFfp=4P3P8P9P9P:P1P2Fsp=>P7P8P9P9P:P3P1P2Gep=<1W12,83p=jp,2rcR;?y12g00LkR<#2R=#2R>#D#5R?#2R@#2#DRA#;RB/01RC%o;%7<RD#7#9#9#9RE#2#7#bRF#7#9#2#D#@#5#5#;%^;R;'0RG%7E#9#9#2#D#@#5#5#;RE7E;P0f4RH%;?R?'B#Q10?HRI11H7RJP;PJ%@F#5#;RF%9@#9#9#9#2#D#@#5#;R@PHC3PJPB%7<#2#@#9#@#5#;RJPHC37RIC:f5RI11IH%C2%;<RK7E2RLf6RM%5A#5#5#5#5#5#;RA,?2,1FRN7FI1?@2ROPMCIX35#A76;56JP31BM?#Qf7RP,0?RQ11PMRRP;PRPFP@PPC3PRPBPJPPC37RQC:P0f8RQ,0?RR11QPRPPPPFP@PQC3PPPBPJPQC37RR76;f9RR11RQPLf:RP?FRNPOPPCIX35#A76;56JP210?Pf;RR/1PRPPPPFP@PRC3P?PRPPPBPJPRC3C:76;P0f<RP/1RRR/0;PRPFP@PPC3P?PPPRPBPJPPC3C:f=RR11RPPLf>RS/1RRRPN10OSC:X35#A76;56JP210R;f?RR/1SRSPFP@PRC3P?PRPSPBPJPRC3C:P0f@R0/1RRRPFP@P0C3PRPBPJP0C396?0fARR11R0PLfBR0/1RRSPN10O0C:X35#A76;56JP2PSPFP@P0C3fCRS11S0PBPJPSC356?fDR0,0J110SRT/0;RUPLfERV/10RWPN10OVC:X35#ARX'81d0?%C0%C?fFRY/B?RZ#C[[1cV?%Q?R[#a1SY?,??/1Z9L5Y[1`Y?1K6?fGRZ/B?R\#C1K\?'8[1_Z?1K?6fHR\/B?R],K??E]6[1]\?fIR\/S?#Q\[1\\?fJR]/B?=L5]\[g00`m1[]?R]eP]g00MjR]g00WRR[#JR^#JR_#JR`#J,G51G5^R^1G5_5N55N5g00X1R_'Z%x]Ra3Y%w]RbP5%v5RcP11X53RdCH%u5Re%t5Rf%=BRg1P5DRD54f%r9RhPf%=?1P5<R<54fRiPfP8P9P9P:AM5<D=4fg%=J=4f<RgFq5>fPhPfPiPhPgC<C<C<1pf:RgP2P3g00NVRjg00O6Rk'n1m23=LjkdAl561CkRkb5b6b7X05X1510?1Rj1113Rl/0B10J13j10?310J7[[\C^05^15P2fKRCfLP\PQPRO5b410JCeb<bDbCbBbAb2bFPUPXPaPbP5PdP11X57RXCHPePf1P5=9M5<R==4fDRDPhPDC<PgPkb5b6b7X05X15X851121RD/0310l7[^05^15^85P2P;P0PVPMO4b4P410TF10@0PLAFYVNPOPYCIX35#AP110WFP5PLAFZYNPOPZCIX35ROP6PaPbP5PdP1PcCHPePf%=FRd94f=PhPfPiPh1U56Ri=4fi%=KRN94fiRL5>f%=ARW9O5i9M5d94f=%=@R0=O5i=4f<5>f5>fC<C<PgPkb5b6b7X05X1510DF%CKRD96661137Ri1?6A,1F1?@6/03C:\j[^05^15P2PYPZP1PPO4b4CVW2P2O110@VP5POPKp-0RO1G5`1G5[9N5^5N5/Z_=Y]aPbP5P5PXP3PcCHP1PcCHPePfPfP8P9P9P:PIEi1P5>R>%=E54f5>fPhPfA4f0<PhPfA4f=>PhA4fNN9>fLAO5NW9M5d94f=AO50N=4f<5>f5>fC<C<C<PgPkb5b6b7X05X15X85W9AE73E10@110iHAEDKK1?KA,1F9F7H1?@KP7CI[[[^05^15^85^9OP2PGP;PYPZPSP1PQO7b4CVW2P2O1n200100001021100011000CTCTW@W?P1P2O2n2001000010121000000W2W>P1P2O2n2001000010121000000W2W=P1P2O2n2011000010121000000W2W;P1P2O2n2011000010121000000b:WEW2XH5XG5o"). Qed.
Local Lemma aobj4_int : forall a, aobj a 4096 ->
  4096 <= a /\ a + 4096 <= ATOP
  /\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
  /\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6352896 * j <= a).
Proof.
ltac2:(KReplay.run1 (kr_t_ASF_fastC ()) ["CANSEC1"] "h04__x1h11jh21Hh31kh47__arithh54__ffh68__varmaph75__with84__x2h94__p1h:2H5h;2H0h<2H1h=2H2h>2H3h?2H4h@2_HhA1ap;1p;3p;2p;4p;6p;7p;8p-1R0p10000p4p710p8P0p1000QR1p4p710p8P0P1p4p7210p8p1000nR1p4p710p1001ep4p710R0p8P1p4p7210P0p8p1002Cp4p710R1p1002aR2p4p710R3p8P1P2p4p7210R2p8p1003:p4p710P0p8p1003op4p70R4p1004fp4p710p8P4p1005=p4p710p8P4p1005Yp4p710p8P4p10062p4p710p8P4p1006Rp4p710p8P4p1006fp4p710p8p1007:p4p710R4P1p8P4P3p8P4P2p8P4p1007Np4p73110p8p1007`p4p7210P0p8g00::j12Tg00:_j1>Tg00X]j3mTg00Q@j1lTg00;=j1:Tg00R>j1\Tg009Aj20Tg00YTj2TTg00Dmj3ITg009]j21Tg00<=j2?Tg00;bR0j26Tg00=4j1aTg00=Tj1_Tg00>4j2OTg00?Nj1^Tg00?lj1]Tg00A:j2JTg00A]j1[Tg00CEj2ZTg00Cgj2YTg00DAj2XTg00EGj3WTg00Efj4VTg00>Rj1UTg00?0j4STg00B?j3ETg00@Wj2RTg00FXj4GTg00S4j1NTg00SSj2KTg00T<j3QTg00Tej2kTg00UQj3jTg00V1j6iTg00`Rj4MTg00MPR4j2gTg00<Zj2fTg00G2j4eTg00G]j7dTg00Hej8cTg00HAj7hTg00Bbj3bTf0R2#2#2p=F%22#2#2#2#2#2#2#2p=8%:2#:#:#:p=<%:2#:p=`%22#2#2#2p=Bf2R3f1R1/02'6p=Hf3R5/031012'gp=41612,63p=L1031/62,65p=D1031/62p=7f4R610531012'6'6p=5g00JhR7/f2p=91R72p=@P3g00IIR8g00IhR9P9g00JHR:P7P1g00KFP2Ceg00KmFdp=3P5P8P9P9P:P3P1P2Gcp=;1131/02p=CP3P8P9P9P:P1P2Fhp==Ab712p=A1012,63,65p=Pp,2rcR;g00LkR<#2R=#2#F#8R>#>R?7m2%l;%:<R@#:#<#<#<RA#2#:#`RB#:#<#2#F#B#8#8#>%\;R;'0RC%:A#<#<#2#F#B#8#8#>RA7H;P01T3?g00LMRD5I710?3RE113?RFP;PF%BB#8#>RB%2>R>#<#<#<#<#2#F#B#8#>RGP3C4PF%2>#FR>#>RH%:<#2#B#<#B#8#>RIP3C47LECD115?RE%><RJ,0297D2RK116?RL%8>#8#8#8#8#8#>R>,?2RM,1BRN1?G2ROP6D5X37#9PKPL11HMRM1?I2RLP6D5X17#9'677;97?5P11T6?=I7Df5RP,0?RQ11P?RRP;PRPBPGPPC4PRPHPIPPC47LQCDP0f6RQ,0?RP11Q?RRPRPBPGPQC4PRPHPIPQC47LP77;f7RP11P?PKf8RP/1?RRPNPOPPD5X37#9PKPRPMPLPPD5X17#9'677;57?P210?Pf9RR/1?RSPSPBPGPRC4P?PRPSPHPIPRC4CD77;P0f:RR/1?RS/0;PSPBPGPRC4P?PRPSPHPIPRC4CDf;RS11S?PKf<RS/1?RTPNPOPSD5X37#9PKPTPMPLPSD5X17#9'677;57?P210T;f=RT/1?RUPBPGPTC4P?PTPUPHPIPTC4CDP0f>RT/1?RUPBPGPTC4PUPHPIPTC497?Tf?RT11T?PKf@RT/1?RUPNPOPTD5X37#9PKPUPMPLPTD5X17#9'677;57?P2PUPBPGPTC4fARU11U?PHPIPUC457?fBRU,0?RV11U?RW/0;RXPKfCRY/1?RZPNPOPYD5X37#9R[PKPZPMPLPYD5X17#9R\'6R]'6g00MjR^#aR_%_^R`1O71Ra%^7Rb%]7Rc%@?Rd1J7<R<53cRe%[9RfPeC;1Zc:RgP2P3g00NVRhg00O6Ri'Y1X23=IhidAW7D1CVRib5b6b7X0710?210?1Rh[^07P2PYPRO2b4PXP]P_P`P71O73R]P1%U7RXCSPbPcAE7<dRd1J7=53cR=PfP=C;PgPib5b6b7X07X87112?R=/01AC1?3[^07^87P2P;PYPQO3b4P[P\P410WB10GUPKfDR\/1?R[PNPOP\D5X37#9P110ZBP7PKfERZ/1?RQPNPOPZD5X37ROPDP_P`PaPbPc%@BRN93cdPfPcPePf1R7DRR=3cR%@JRj93cRRk5=cRl%@>Rm,ARRn9E7N93cd%@GRo/AR=3c<5=c5=cC;C;PgPib5b6b7X0710=B10DJRp97DDRqPF1?D>Rr,1B1?GDP3D5\h[^07P2PZP1PSO3b4CGW2P2O110GYP7POPJp-0ROg00WRRs#NRt#N#N,K71K7t1K7s5Q75Q7g00X1'k=j^_R^P`P7PXP1P]CSR]PbPcPcP8P9P9P:P6Ei1J7@R@%@A53c5=cR6PfPcA3co<PfPcA3cd@R@PfA3cjj9=ckRk1AjmRm9E7N93cd1Aoj=3c<5=c5=cC;C;C;PgPib5b6b7X07X87W9AH31ARA10G110F5RoAHpJJRpPE1?J>R>,1B1?GJP5D5[[[^07^87^9OP2PCP;PZPYP1PPO6b4CGW2P2O1n200100001021100011000P0PVPWPHPIPUC4PKP[PMPLP\D5X17#9P210?\PQPHPIPZC4P4fFR4?C?H10I4PKfHR4?C?MPLP4CPX17#9P2fGR4?C?HP7PKfIRK?C?MPLPKCPX17RLPDP_P`PaPbPc%@HRa93cdPfPcPePfAE7an93cd%@IRn/AR=3c<5=c9=clC;C;PgPib5b6b7X0710=HPqPF11Hr1?IDP3D5\h[^07P2PKP1PTO3b4CGW:P2O110I4P7PLPJP^P`P]PbPcP6PfPcA3cn<PfPcP@PfAE7am93cd1Anj=3c<5=c9=ckC;C;C;PgPib5b6b7X07X87X9O10I1PpPE11H>1?IJP5D5\o[\A^07^87^9OP2PCP;PKP4P1PSO6b4CGW:P2O1n200100000021100011000W2W@P1P2O2n2001000000121000000CMCMCMW:W?P1P2O2n2001000010121000000W2W>P1P2O2n2011000010121000000W2W=P1P2O2n2011000010121000000W2W<P1P2O2n2011000010121000000b;W2XA7o"). Qed.

Section S.
Variable DI : ADepotIface.
Variable AFK : alayout -> list ablock -> amem -> Prop.
Hypothesis HL : ahole_laws (AHQ DI ASEC_of AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                                  /\ (snd iv <= 0xb6f70 \/ 0xb7030 <= fst iv)
                                  /\ (snd iv <= 0xbb500 \/ 0x13c530 <= fst iv)
                                  /\ (snd iv <= 0x149d88 \/ 0x149d8c <= fst iv)) CI.
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.
Hypothesis DEPD : depot_frameD_law (ADEPOT DI).
Hypothesis AFKD : fake_frameD_law AFK.
Hypothesis STOREC : store_freeSC_stmt DI AFK CI.
Hypothesis BACK : afree_back_stmt DI AFK CI.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma AHr_laws : forall R cs, ahole_laws (ARecyc1P.AHr ASECc (ADEPOT DI) AFK R cs).
Proof.
  intros R cs. destruct HL as [HQF HSF HDF HFF HFB].
  constructor; cbn [ah_quar ah_sec ah_depot ah_fake ARecyc1P.AHr AHQ] in *; try assumption.
  - intros L st st' X X' m m' W AQ MU WM UT QS. eapply AQdr_frame; eassumption.
  - intros L st st' X X' m m' W AS MU WM SU SS. eapply asecc_frame; [exact AS| exact MU| exact WM| exact SU| apply sec_same0_of; exact SS].
Qed.

Lemma ASECc_wf1' : forall cs L st X m, ASECc cs L st X m -> Forall (sec_wf1 L) cs.
Proof. intros cs L st X m ((_ & _ & _ & _ & _ & WF1 & _) & _). exact WF1. Qed.
Lemma ASECc_disj' : forall cs L st X m, ASECc cs L st X m -> sec_disjoint cs.
Proof. intros cs L st X m ((_ & _ & _ & _ & _ & _ & WD) & _). exact WD. Qed.
Lemma ASECc_nres' : forall cs L st X m, ASECc cs L st X m -> 0 <= a_nres st /\ 8 * a_nres st <= 8388608.
Proof. intros cs L st X m ((_ & _ & (_ & NR) & _) & _). lia. Qed.
Lemma ASECc_qglob' : forall cs L st X X' m g gb, ASECc cs L st X m -> ASECc cs L (set_qglob g gb st) X' m.
Proof. intros cs L st X X' m g gb HS. exact HS. Qed.
Lemma RSEC_app' : forall a b RNG, RSEC (a ++ b) RNG <-> RSEC a RNG /\ RSEC b RNG.
Proof. intros. unfold RSEC. apply Forall_app. Qed.
Lemma RSEC_arng' : forall L RNG st, arng L RNG st -> RSEC (sec_chunks_of st) RNG.
Proof. intros L RNG st (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RS & _). exact RS. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem afree_sec_recfast : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo : Z) (tr : list Z) (mb ms : Z),
  (* [comment removed for export] *)
  (a_live st) !! p = Some (CSec mb ms n) -> n <= Q_MAX ->
  let st1 := set_live (delete p (a_live st)) st in
  let st2 := st_enq st1 (CSec mb ms n) in
  (enq_app st1 (CSec mb ms n) = None -> 0 < c_count (get_cls st K_BATCH_CLASS)) ->
  Q_CACHE < a_qloc_bytes st2 -> Q_MAX < a_qglob_bytes st2 + a_qloc_bytes st2 ->
  (* [comment removed for export] *)
  AHEAP_P (AHQ DI ASEC_of AFK) L RNG st LB m -> In (HB p A n) LB ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 A ->
  aunw m L RNG lo AFREE_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  implS bsegs RNG (aembed ATOP (afree st (Some p)))
        (epostF (afree_post CI (AHEAP_P (AHQ DI ASEC_of AFK)) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom bsegs)).
Proof.
  intros until ms. intros LIVE NQM st1 st2 CNT QC1 REC AH HIN MI ST BOT LO TP Ha0 AUNW S0NE RA4 RANE SP16 RSTK.
  assert (UNWX : exists trt, afree_unw RNG lo m (al_top L) sp s0 ra trt /\ In (AFREE_PC :: trt) (al_U L)).
  { destruct AUNW as [(BT & UC & LTR & TRU & RTOP)|(TOPLE & SPLT & TRU)]; [exists (bv_unsigned ra :: tr); split; [left; exists tr; split; [reflexivity|]; split; [exact UC|]; split; [exact LTR|]; split; [exact BT| exact RTOP]| exact TRU] | exists (@nil Z); split; [right; auto| exact TRU]]. }
  destruct UNWX as (trt & FUNW & TRU).
  destruct AH as (ALO & ARNG & [X [AR BL]] & HFK).
  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & HRT2 & AVL & RT3).
  cbn [ah_quar ah_sec ah_depot AHQ] in HQ, HS, HD. destruct HQ as [Q AQ].
  (* [comment removed for export] *)
  destruct (freed_block_sec L st X LB p mb ms n A n WF BL HIN LIVE) as (EA & _ & WFch).
  destruct (sec_wf1_facts' L mb ms n WFch) as (MAL & MLO & MCE & MSE & NB & RZ & MSB & MSAL & NMS & NS0 & SCL & NPR & N6).
  pose proof (ablk_lin _ _ MLO) as (ML1 & ML2 & ML3 & ML4). unfold AIMG_HI in ML1. pose proof (ablk_int _ _ MLO) as (kM & KAM & KBM & KEM & KCM & KDM).   (* [comment removed for export] *)
  pose proof SCL as (SC_t & SC_c & SC_s & SC_p & SC_n & SC_st & SC_f & SC_d).
  destruct (read_chunk_sec _ L st X m p mb ms n HS (Permutation_refl _) LIVE)
    as (order & i & b1 & cx & uw & PO & NTH & IL & LENO & WF1o & WDo & U64 & JK & PER & CH & H1 & H5 & B1 & B3 & CX & HUW & UJ & S1 & S2 & S3).
  cbv zeta in H5, HUW, UJ, S2, S3.
  set (hm := mb + 6128) in *.
  (* [comment removed for export] *)
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof (alayout_depot L ALO) as (DL1 & DL2 & DL3 & DL4 & DL5 & DL6 & DL7 & DL8 & DL9 & DL10).
  pose proof (alayout_stack L ALO) as (STK1 & STK2 & STK3).
  pose proof (ao_space L ALO) as RSP.
  assert (SP47 : bv_unsigned sp < 2^47) by (eapply afree_unw_sp47; [exact FUNW| exact STK2]).
  pose proof (rup8_facts n ltac:(lia)) as (RUP & RUP8 & RUPS).
  assert (SHGEO : shad (hm + 16) = shad mb + 768 /\ shlen (rup n 8) <= ms / 8 - 768 /\ 0 < shlen (rup n 8)).
  { subst hm. rewrite !shad_div, RUPS. pose proof (sec_facts n ltac:(lia) NPR) as (_ & _ & _ & RS1 & _ & NSE & _). clear -MAL RUP RUP8 RS1 NSE NMS N6 NB. Z.div_mod_to_equations. lia. }
  destruct SHGEO as (SHE & SHL & SHP).
  (* [comment removed for export] *)
  assert (HMSEP : forall kk, 0 <= kk < ndist st K_BATCH_CLASS -> hm + 24 <= abatch_addr L kk \/ abatch_addr L kk + 8192 <= hm).
  { intros kk KK. pose proof WF as WF0. destruct WF0 as (_ & _ & _ & _ & _ & PERC & _).
    destruct (PERC K_BATCH_CLASS (K24)) as (Q1 & Q2 & _).
    pose proof (slot_in_region L st K_BATCH_CLASS kk ltac:(rewrite size_of_class_24; lia) (proj1 Q1) KK) as (P5 & P4 & _).
    rewrite size_of_class_24 in P4. subst hm. unfold abatch_addr, aregion, K_REGION, K_FREEARR_OFF, K_BATCH_CLASS in *.
    clear -P5 P4 Q1 Q2 RSP SC_s MSB. lia. }
  assert (HM0' : ablk hm (hm + 24)) by (subst hm; eapply ablk_sub; [exact MLO| clear; lia| clear -NMS MSB; lia]).   (* [comment removed for export] *)
  (* [comment removed for export] *)
  pose proof RT as RT0.
  destruct RT0 as (GPG & GOT & GOT80 & RIC & LS1 & REAL & IMAX4 & FLG5 & FLG & HPP & SHB & CANP & TI & TK & INI2 & LAY & MCS & OOM3
                    & PGC & HK2 & CF8 & CF34 & CSMT & T88 & TSD & LS2 & CT8 & CT).
  pose proof INI2 as INI. rw_split INI 1%nat INI1 INIx. clear INIx.
  pose proof OOM3 as OOM. rw_split OOM 2%nat OOMx RSS0. clear OOMx.
  pose proof IMAX4 as IMAX. rw_split IMAX 3%nat IMAX3 IMAXx. clear IMAXx.
  pose proof HK2 as HK. rw_split HK 1%nat HK1 HKF.
  pose proof GOT as GOT6. rw_split GOT 1%nat GOTa GOTr. rw_split GOTr 1%nat GF GOTx. clear GOTa GOTx.
  destruct THR as (T0 & T40 & CACHES & CSTATS & [sj [STATS LSJ]] & UNW).
  destruct (CACHES K_BATCH_CLASS (K24)) as [tail (CR & CHc & LCH)].
  replace (acache_addr L K_BATCH_CLASS) with (al_t L + 2128) in CR by (unfold acache_addr, K_BATCH_CLASS; lia).
  destruct (junk_split m (al_t L + 2768) 16 16 CSTATS ltac:(lia) ltac:(lia)) as [CSa CSb].
  destruct (junk_split m (al_t L + 2768 + 16) 8 8 CSb ltac:(lia) ltac:(lia)) as [CS8 CSc].
  replace (al_t L + 2768 + 16) with (al_t L + 2784) in CS8 by lia.
  destruct (c8_of_junk m _ CS8) as [stj STS].
  (* [comment removed for export] *)
  pose proof AQ as AQ0. destruct AQ0 as ([QK MX] & [QC ABL] & [GCQ ABG] & (FL & IAS & IAM) & CP & NUM).
  destruct NUM as (NB1 & NB2 & NF & NC & NM).
  pose proof (batches_bytes_lb (a_qloc st) ltac:(apply Forall_app in NF; exact (proj1 NF))) as LLB. rewrite <- NB1 in LLB.
  (* [comment removed for export] *)
  assert (EKX : exists k24 chunks, let ek := ek_of L st X Q n k24 stj chunks in
       ek_pre ek RNG (al_t L) (Z.of_nat (length (a_qloc st))) (qlast L (q_loc Q)) n hm m
    /\ ek_seps ek L hm (qlast L (q_loc Q))
    /\ 0 <= ek_delta ek n /\ a_qloc_bytes st2 = a_qloc_bytes st + ek_delta ek n /\ a_qglob_bytes st2 = a_qglob_bytes st
    /\ (ek_b ek (qlast L (q_loc Q)) = qlast L (q_loc Q)
        \/ exists kk, ek_b ek (qlast L (q_loc Q)) = abatch_addr L kk /\ 0 <= kk < ndist st K_BATCH_CLASS /\ ~ In kk (map qb_slot (q_loc Q ++ q_glob Q)))
    /\ (enq_is_app st = false ->
          nth_error (xc_cache (x_cls X K_BATCH_CLASS)) (Z.to_nat (c_count (get_cls st K_BATCH_CLASS) - 1)) = Some k24
       /\ busy_of X K_BATCH_CLASS k24 = None /\ 0 <= k24 < ndist st K_BATCH_CLASS
       /\ ~ In k24 (map qb_slot (q_loc Q ++ q_glob Q))
       /\ junk_at m (abatch_addr L k24) 8192 /\ fill_at m (shad (abatch_addr L k24)) (shlen 8192) 0xfa
       /\ a_cinit st = true /\ 0 < c_count (get_cls st K_BATCH_CLASS))).
  { pose proof (st_enq_bytes st p (CSec mb ms n) L X Q) as SB.
    destruct (enq_is_app st) eqn:EAPP.
    - destruct (read_ek_appS (AHQ DI ASEC_of AFK) L st X Q m RNG hm n ALO ARNG AR AQ NQM HMSEP stj [] 0 EAPP
                (Z_to_bv 64 0) (Z_to_bv 64 0) 0 CR STS) as (EK & ES & ED & EB & _).
      specialize (SB 0 stj [] ltac:(intros E; exfalso; change (enq_app st1 (CSec mb ms n) = None) in E; assert (EA1 : enq_is_app st1 = true) by exact EAPP;
                    destruct (proj1 (enq_is_app_spec st1 (CSec mb ms n)) EA1) as [s Hs]; congruence)).
      cbn [chunk_size] in SB. destruct SB as (SB1 & SB2 & _).
      exists 0, []. cbv zeta. split; [exact EK|]. split; [exact ES|]. split; [rewrite ED; lia|]. split; [exact SB1|]. split; [exact SB2|].
      split; [left; exact EB|]. intros; discriminate.
    - assert (POS : 0 < c_count (get_cls st K_BATCH_CLASS)).
      { apply CNT. destruct (enq_app st1 (CSec mb ms n)) eqn:E; [| reflexivity]. exfalso.
        assert (EA1 : enq_is_app st1 = true) by (apply (proj2 (enq_is_app_spec st1 (CSec mb ms n))); eexists; exact E).
        change (enq_is_app st1) with (enq_is_app st) in EA1. congruence. }
      destruct (read_ek_newS (AHQ DI ASEC_of AFK) L st X Q m RNG hm n ALO ARNG AR AQ HM0' HMSEP stj EAPP POS STS)
        as (k24 & chunks & EK & ES & ED & EB & NK & NBk & KK & NIB & JKb & FSH & CIN & _).
      specialize (SB k24 stj chunks ltac:(intros _; exact POS)). cbn [chunk_size] in SB. destruct SB as (SB1 & SB2 & _).
      exists k24, chunks. cbv zeta. split; [exact EK|]. split; [exact ES|]. split; [rewrite ED; lia|]. split; [exact SB1|]. split; [exact SB2|].
      split; [right; exists k24; split; [exact EB|]; split; [exact KK| exact NIB]|].
      intros _. repeat (split; [assumption|]). exact POS. }
  destruct EKX as (k24 & chunks & EKX). cbv zeta in EKX. destruct EKX as (EK & ES & ED0 & SB1 & SB2 & EBB & NEWF).
  set (ek := ek_of L st X Q n k24 stj chunks) in *.
  (* [comment removed for export] *)
  assert (DELTA0 : ek_delta ek n <= n + 8192) by (subst ek; unfold ek_of; destruct (enq_is_app st); cbn [ek_delta]; lia).
  destruct (read_dkSC (AHQ DI ASEC_of AFK) L st X Q m RNG hm ALO ARNG AR AQ HMSEP (ek_b ek (qlast L (q_loc Q))) (ek_delta ek n) ek ED0
              ltac:(unfold Q_MAX in *; clear -DELTA0 NQM; lia) EBB
              ltac:(rewrite <- SB1; exact QC1) ltac:(rewrite <- SB1, <- SB2; clear -REC; lia) eq_refl) as (DK & DS & GL & GLST & GDR).
  set (g := g_of L st Q (ek_delta ek n)) in *.
  (* [comment removed for export] *)
  rewrite (afree_rec_eq st p (CSec mb ms n) LIVE ltac:(cbn [chunk_size]; exact NQM) CNT QC1 REC).
  (* [comment removed for export] *)
  assert (AB64 : forall q, In q (q_loc Q ++ q_glob Q) -> 0 <= abatch_addr L (qb_slot q) < 2^64).
  { intros q Hq. pose proof (bslot_geo L st X ALO WF (qb_slot q) (bslot_range L st X Q WF CP q Hq)) as (B0 & B1' & _). atop_facts. lia. }
  assert (LF64 : 0 <= qfirst L (q_loc Q) < 2^64).
  { destruct (qfirst_cases L (q_loc Q)) as [-> |(q & Hq & ->)]; [lia| apply AB64; apply in_or_app; left; exact Hq]. }
  assert (LL64 : 0 <= qlast L (q_loc Q) < 2^64).
  { destruct (qlast_cases L (q_loc Q)) as [-> |(q & Hq & ->)]; [lia| apply AB64; apply in_or_app; left; exact Hq]. }
  pose proof DELTA0 as DELTA.
  (* [comment removed for export] *)
  pose proof ARNG as ARNG0. destruct ARNG0 as (RIMG & RT4 & RCTX & RNO & RSTO & RRI & RFK & RSFK & RDT & RCLS & RPA & RSECS & RPSH).
  assert (IN : In (CSec mb ms n) (sec_chunks_of st)) by (eapply Permutation_in; [exact PO| eapply nth_error_In; exact NTH]).
  pose proof (proj1 (Forall_forall _ _) RSECS _ IN) as [RMB RSH]. cbn [sec_mb sec_ms] in RMB, RSH.
  (* [comment removed for export] *)
  unfold AIMG_HI, AFREE_STACK, UDEPTH, Q_MAX, Q_CACHE, K_HIGH_MEM, AREQMAX in *.
  iprefix. eapply evtF_cut.
  { eapply (free_torec DI L (q_ia Q) ek g RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m
              (al_t L) (al_ctx L) hm n b1 cx lo (al_top L) (al_bot L)
              (Z.of_nat (length (a_qloc st))) (qfirst L (q_loc Q)) (qlast L (q_loc Q)) (a_qloc_bytes st) uw sj (block_shadow_bytes n) trt).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact ST | exact IAS]
         | |- ablk _ (_ + 16 + rup _ 8) => first [assumption | exact HM0' | (try subst hm; eapply ablk_sub; [exact MLO| clear; lia| clear -NMS MSB MSAL N6 NB; unfold rup; Z.div_mod_to_equations; lia])]   (* [comment removed for export] *)
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- poison_cells _ => unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- ADEPOT _ _ _ => exact HD
         | |- afree_unw _ _ _ _ _ _ _ _ => exact FUNW
         | |- In _ _ => exact TRU
         | |- u64arr _ _ _ _ => exact STATS
         | |- ek_pre _ _ _ _ _ _ _ _ => exact EK
         | |- ek_seps _ _ _ _ => exact ES
         | |- dk_preC _ _ _ _ _ _ _ _ => exact DK
         | |- dk_seps _ _ _ => exact DS
         | |- _ = true -> _ => exact IAM
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact H5
         | |- rw_cells _ _ (shad _) _ => exact S2
         | |- rw_cells _ _ (_ + 80) _ => exact QC
         | |- rw_cells _ _ (_ + 16) [C8 _] => exact HUW
         end.
    all: try lazymatch goal with
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _] => first [exact T0 | exact QK]
         | |- rw_cells _ _ _ _ => assumption
         | |- @eq word _ _ => first [exact TP | rewrite Ha0, EA; subst hm; unfold SEC_UOFF; f_equal; clear; lia | reflexivity]
         | |- _ \/ _ => first [exact CL5 | exact DL7 | exact DL8 | exact DL9 | exact DL10
                             | subst hm; clear -SC_t MSB; lia | subst hm; clear -SC_c MSB; lia | subst hm; clear -SC_n MSB; lia | subst hm; clear -SC_st MSB; lia]
         | |- rng _ (shad _) _ => rewrite SHE; eapply rng_sub; [exact RSH| clear; lia| clear -SHL; lia]
         | |- rng _ _ 24 => subst hm; eapply rng_sub; [exact RMB| clear; lia| clear -MSB; lia]
         | |- rng _ (al_ctx _) _ => eapply rng_sub; [exact RCTX| clear; lia| clear; lia]
         | |- rng _ _ _ => assumption
         | |- rng_aimg _ => exact RIMG
         end.
    all: try assumption.
    all: subst hm; unfold AIMG_HI, Q_MAX, Q_CACHE, Q_BATCH_BYTES, UDEPTH in *.
    all: try (generalize NB N6 NMS NQM MLO ML1 ML3 MCE MAL MSAL RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6
                         B1 CX LLB NC NM LF64 LL64 ED0 DELTA RA4 RUP; clear; intros; Z.div_mod_to_equations; lia).
    }
  cbv beta. intros ms1 PT.
  (* [comment removed for export] *)
  pose proof (STOREC L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st LB X Q p mb ms n b1 cx A lo k24 stj chunks
                ALO ARNG AR AQ BL HFK LIVE HIN NQM H5 B1 B3 CX NEWF QC1 REC EK DK ltac:(atop_facts; clear -LO BOT STK3; lia) ltac:(unfold AFREE_STACK; clear -LO; lia) TP ms1 PT) as SP.
  fold st1 st2 ek g in SP. unfold storeC_post in SP.
  destruct SP as (X' & R & m1 & id & t0' & t1' & t2' & xs0 & xs1 & xs2 & xs3 & xs4 & xs5 & xs6 & ps0 & ps1 & ps2 & ps3 & ps4 & ps5 & spv & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6'
                  & csA & csT & junk2 & -> & AR1 & RT1 & RB1 & RE1 & ARNG1 & BL1 & HFK1 & GB56 & QL1 & QLB1 & MI1 & ST1 & HP1 & ID1 & PF1 & FA1 & SZA & FT1 & SZT & FS1).
  apply evtF_done.
  (* [comment removed for export] *)
  subst tp.
  eapply (AQrecP.aqrec ASECc (ADEPOT DI) AFK RSEC AHr_laws ASecRecycle.srec F_aqrec.qrec_front DEPD AFKD
            ASECc_perm ASECc_wf1' ASECc_disj' ASECc_nres' ASECc_qglob' RSEC_app' RSEC_perm RSEC_mono RSEC_arng'
            (fun st3 => aret st3) _ L RNG (lb_remove p LB) R X' (st_after st2) m1 lo Q_MIN);
    try lazymatch goal with
    | |- alayout_ok _ => exact ALO
    | |- arng _ _ _ => exact ARNG1
    | |- AREP _ _ _ _ _ => exact AR1
    | |- qr_tmp _ = _ => exact RT1
    | |- qr_pendb _ = _ => exact RB1
    | |- qr_pend _ = _ => exact RE1
    | |- ablocks _ _ _ _ => exact BL1
    | |- mem_inv _ _ => exact MI1
    | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SP47 LO BOT STK3; atop_facts; lia); exact ST1
    | |- ATOP <= _ => atop_facts; clear -LO BOT STK3; lia
    | |- _ <= bv_unsigned _ - _ => rewrite unsigned_lit by (clear -SP47 LO BOT STK3; lia); clear -LO BOT STK3; lia
    | |- bv_unsigned _ <= 2 ^ 47 => rewrite unsigned_lit by (clear -SP47 LO BOT STK3; lia); clear -SP47 LO BOT STK3; lia
    | |- _ < 2 ^ 56 => exact GB56
    | |- 0 <= Q_MIN < _ => unfold Q_MIN; clear; lia
    | |- rng _ lo _ => rewrite unsigned_lit by (clear -SP47 LO BOT STK3; lia); eapply rng_sub; [exact RSTK| clear; lia| clear -LO BOT STK3; lia]
    | |- AFK _ _ _ => exact HFK1
    end.
  (* [comment removed for export] *)
  intros st3 X3 RNG3 ms3 RET3.
  eapply (BACK L RNG RNG RNG3 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xs0 xs1 xs2 xs3 xs4 xs5 xs6 ps0 ps1 ps2 ps3 ps4 ps5 spv a3' F fc
            m m1 st (st_after st2) X' R LB p (al_t L) lo csA csT junk2 st3 X3 ms3);
    try lazymatch goal with
    | |- alayout_ok _ => exact ALO
    | |- ATOP <= _ => atop_facts; clear -LO BOT STK3; lia
    | |- _ <= bv_unsigned _ - AFREE_STACK => unfold AFREE_STACK; clear -LO; lia
    | |- Forall _ CI => first [exact CI_OK| exact CI_OK2]
    | |- fp_le _ _ => apply fp_le_refl
    | |- awf _ _ _ => exact (proj1 AR1)
    | |- ablocks _ _ _ _ => exact BL1
    | |- aheap_pres _ _ _ _ _ => exact HP1
    | |- cells_size _ = _ => first [exact SZA| exact SZT]
    | |- rng _ lo _ => exact RSTK
    | |- rng _ _ _ => exact RIMG
    | |- aqrec_ret _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact RET3
    | |- a_qloc _ = _ => exact QL1
    | |- a_qloc_bytes _ = _ => exact QLB1
    | |- rw_cells _ _ _ _ => first [exact PF1| exact FA1| exact FT1| exact FS1]
    end.
Qed.
End S.
End CANSEC1.
