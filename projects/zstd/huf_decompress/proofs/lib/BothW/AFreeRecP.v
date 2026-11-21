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
     AFreeModelC AFreeReadC.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AFreeRecP () := "I47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstI59OSSVerify5KrLib4Spec5STree5stree00C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib4Spec8AsanCtrl2AMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl4aptrC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List8nil_consC35stdpp8fin_maps:map_deleteC47Corelib4Init9Datatypes3appC35stdpp4gmap;gmap_lookupC35stdpp4gmapBgmap_partial_alterC35stdpp4base6LookupC35stdpp4base6DeleteC4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib5BothW4ASec7ASEC_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<F_afree_arep3AHQC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW6AHeapP:ahole_laws00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ASec5ASECcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<ADepot_iface6ADEPOTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW8ARecyc1P3AHrC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib5BothW4ARep7ah_quarC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP>quar_untouchedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP9quar_sameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6ah_secC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP=sec_untouchedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP8sec_sameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8ah_depotC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C56Stdlib6ZArith6BinInt1Z2leC47Corelib4Init9Datatypes3sndC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C47Corelib4Init5Logic3notC59OSSVerify5KrLib5BothW5ABase8al_nodesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib5BothW5ABase8al_storeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7ah_fakeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP>fake_untouchedC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW5ABase6abkind02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW5ABase6ablock01C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffC59OSSVerify5KrLib5BothW6ARepQD4AQdrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ARepQD:AQdr_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:ASF_refill<sec_same0_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ASF_kit;asecc_frameC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW6AHeapP:ahole_laws01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW6ARepQR6qrconc00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6achunk00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW5ABase7alayout00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6astate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep5aconc00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib3Lib5Frame3ivlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4BImg5bsegsC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I59OSSVerify5KrLib5BothW5ABase6ablock00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01C46Stdlib5Lists4List2hdC59OSSVerify5KrLib5BothW4ASec7asec_wfC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW7ALayout:alayout_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;a_ptr_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase<al_ptr_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_nresC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib4Spec8AsanCtrl6a_nsecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ASec<sec_disjointC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ASec6aprim0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ASec4ashzC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ASec8asec_arrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ASec9asec_instC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP7sec_wf1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3mulK46Stdlib9micromega=RingMicromega5Psatz02K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I59OSSVerify5KrLib4Spec8AsanCtrl6abatch00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP6sec_mbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP6sec_msC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF3rngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed4shadC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC46Stdlib5Lists4List:Forall_appC59OSSVerify5KrLib5BothW6AHeapP4RSECC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF9footprintC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP4arngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4al_tC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase6al_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7al_fakeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed5shlenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7get_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7aregionC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=c_mapped_userC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8afreearrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrlCc_mapped_free_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase<al_space_begC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib5BothW6AHeapP=sec_chunks_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout7al_dtlsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<K_SPACE_SIZEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_SPACE_EXTRAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_NUM_CLASSESC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6aclass00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8in_splitC35stdpp4base6lookupC35stdpp4base6deleteI35stdpp4gmap4gmap00C59OSSVerify5KrLib4Spec8AsanCtrl6a_liveC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8AsanCtrl6achunk01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<a_qloc_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=a_qglob_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP7AHEAP_PC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW5ABase6abkind01C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib5BothW=AMalloc_iface4aunwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase6al_topC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4al_UC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib5BothW5AKitQ9afree_unwC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00I59OSSVerify5KrLib5BothW5ABase6uchain00C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01K47Corelib4Init5Logic2or01K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2or02C59OSSVerify5KrLib4LibA6NodesA8at_nodeAC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=AMalloc_iface:afree_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP7ablocksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep4AREPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep3awfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7arep_rtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep9ainstanceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7athreadC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep<aslot_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep=ashadow_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6arelroC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8arep_rt2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8arep_rt3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ8AQUAR_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6x_busyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5xb_stC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep4xb_nC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8AsanCtrl6achunk02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase6hb_idsC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List5NoDup00C59OSSVerify5KrLib4Spec8AsanCtrl;a_space_begC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5x_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=size_of_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl@c_allocated_userC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;c_num_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7xc_freeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8xc_cacheC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7c_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8xb_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5xb_b1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6xb_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7xb_userC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW4ARep6bstate01C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalK59OSSVerify5KrLib5BothW4ARep5xbusy01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AFreeRead;freed_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW8AFreeRep:freed_liveC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C59OSSVerify5KrLib5BothW8AFreeGeo9chunk_geoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep:aslot_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7rz_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl3rupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW8AFreeGeo@slot_sep_objectsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW8AFreeGeo8slot_rngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW8AFreeGeo@chunk_shadow_geoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8granulesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout9alayout_tC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4iclrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4sclrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout;alayout_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout=alayout_depotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout=alayout_stackC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase6al_botC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5AKitQ>afree_unw_sp47C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t01C59OSSVerify5KrLib5BothW9AFreeRead3fhmC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell03C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ABytes<rw_cells_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep<acache_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7a_cinitC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC59OSSVerify5KrLib5BothW7ARepKit:junk_splitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7junk_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ARepKit:c8_of_junkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6aslotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep:afreearrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep=aregion_cellsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C59OSSVerify5KrLib5BothW9AFreeRead:read_chunkC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef6repeatC59OSSVerify5KrLib5BothW4ARepBblock_shadow_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ@aquar_glob_constC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7AQConst9aq_tcacheC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_qlocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ5q_locC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ7aqcacheC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ4q_iaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ6qfirstC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ5qlastC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ8abatchesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7a_qglobC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ6q_globC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ8qcoupledC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ4qnumC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=batches_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6b_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ARepQP@batches_bytes_lbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AFreeRead<st_enq_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:AFreeModel6st_enqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl:chunk_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AFreeRead5ek_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AFreeRead:enq_is_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<F_afree_tail6ek_preC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<F_afree_icpt7ek_sepsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<F_afree_tail8ek_deltaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<F_afree_tail4ek_bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ;abatch_addrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC59OSSVerify5KrLib5BothW9AFreeRead;read_ek_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7b_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl8b_chunksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ5qb_ksC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib5BothW9AFreeRead?enq_is_app_specC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:AFreeModel7enq_appC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic8eq_transI47Corelib4Init5Logic2or00C59OSSVerify5KrLib5BothW9AFreeRead;read_ek_newC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ7qb_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:AFreeReadC8read_dkCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AFreeRead4g_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW>F_afreeC_iface7dk_preCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<F_afree_icpt7dk_sepsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<F_afree_tail5g_lstC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<F_afree_tail7dk_glstC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl4aretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AFreeModelC<after_rec_eqC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC59OSSVerify5KrLib4Spec8AsanCtrl5drainC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:AFreeModel8st_afterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AFreeRead;bslot_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AFreeRead9bslot_geoC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib5BothW:AFreeReadC<qfirst_casesC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9in_or_appC59OSSVerify5KrLib5BothW:AFreeReadC;qlast_casesC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW4AKit5boxed01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4AKit5boxed00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW>F_afreeC_iface?free_torec_postC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C59OSSVerify5KrLib3Lib7ZBridge;Z_to_bv_eqmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9F_aalloc1<allocA_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9F_apoison<poison_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<F_afree_arep@rw_cells_addr_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4ablkC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC59OSSVerify5KrLib4LibA5ExecF7rng_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=F_afree_icptC:free_torecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase9lb_removeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW@AFreeC_kit_iface;storeC_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW>F_afreeC_iface9put_frameC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;ASecRecycle4srecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7F_aqrec:qrec_frontC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ASecStore:ASECc_permC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AQrecP9aqrec_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA:fp_le_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF9evtF_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF8evtF_cutC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA8SysStepF?implF_from_evtFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW;AFreeModelC<afree_rec_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl8set_liveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C59OSSVerify5KrLib4Spec8AsanCtrl5afreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed6aembedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA6epostFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA5implFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep:busy_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5ndistC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl9max_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<rounded_sizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC59OSSVerify5KrLib4Spec8AsanCtrl6a_nextC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2ltK46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04K59OSSVerify5KrLib3Lib5Cells4cell04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr6u64arrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep;acache_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8acompactC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib3Lib3Arr6u32arrC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC59OSSVerify5KrLib5BothW5ARepQ6aintalC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC59OSSVerify5KrLib5BothW4ARep7fill_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7busy_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ5qhdrsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW<F_afree_tail8enq_kind01C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List4lastK59OSSVerify5KrLib5BothW<F_afree_tail8enq_kind02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<F_afree_tail7g_drainC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7recycleC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula06C59OSSVerify5KrLib5BothW8F_adorec3csxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW@AFreeC_kit_iface3AHcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ARepQR6qr_tmpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ARepQR8qr_pendbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ARepQR7qr_pendC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=AMalloc_iface:aheap_presC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF4evtFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AQrecP5aqrecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_BATCH_CLASSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase8AFREE_PCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase6UDEPTHC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AProto6fstepSC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep6bstate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep5xbusy00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7K_ALIGNC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7aclass0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7AREQMAXC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C59OSSVerify5KrLib4Spec8AsanCtrl5Q_MAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7AIMG_HIC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase5ATP88C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4ATSDC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C59OSSVerify5KrLib5BothW4ARep<ASTATS_WORDSC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC59OSSVerify5KrLib5BothW7AQConst9AQ_GCACHEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7AQConst8AIA_BASEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7Q_CACHEC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW5ARepQ7qbatchc00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02K59OSSVerify5KrLib5BothW4ARep6bstate03C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01I59OSSVerify5KrLib5BothW<F_afree_tail8enq_kind00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AFreeRead;dummy_batchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AFreeRead8dummy_qbC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op205C59OSSVerify5KrLib4Spec8AsanCtrl5Q_MINC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00c59OSSVerify5KrLib5BothW9AFreeRecP8AHr_lawsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9AFreeRecP:ASECc_wf1'C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9AFreeRecP;ASECc_disj'C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9AFreeRecP;ASECc_nres'C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9AFreeRecP<ASECc_qglob'C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9AFreeRecP9RSEC_app'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP9RSEC_permC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP9RSEC_monoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW9AFreeRecP:RSEC_arng'C1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableC59OSSVerify5KrLib5BothW5ABase;AFREE_STACKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase3ATPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase9AFREE_SYMC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW5ARepQ5qconc00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP8SEC_UOFFC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep6xclass00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_OFFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl:K_USER_MAPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_MAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_MAPC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C59OSSVerify5KrLib5BothW9AFreeRead3K24C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6AMAGICC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7AQConst6AQ_MAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7AQConst8AQ_MUTEXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7AQConst8AIA_FLAGC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7AQConst8AIA_SIZEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7AQConst<AIA_MAP1_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7AQConst8AIA_MAP1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=Q_BATCH_BYTESC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List6Exists00I47Corelib4Init5Logic5False00C59OSSVerify5KrLib4Spec8AsanCtrl7Q_BATCHC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW<F_afree_tail3gqd00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7AINITEDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:F_aalloc_s7ARSSLIMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase5ATSDIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase5ATSDKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase3KLSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7AQConst7AQUAR_QC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Set Keyed Unification.   (* [comment removed for export] *)
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

Section CANSEC1. Context {rc : runConstT}.
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
Hypothesis STOREC : store_freeC_stmt DI AFK CI.
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
Theorem afree_recP : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo : Z) (tr : list Z) (c : Z),
  (* [comment removed for export] *)
  (a_live st) !! p = Some (CPrim c n) -> 1 <= n ->
  let st1 := set_live (delete p (a_live st)) st in
  let st2 := st_enq st1 (CPrim c n) in
  (enq_app st1 (CPrim c n) = None -> 0 < c_count (get_cls st K_BATCH_CLASS)) ->
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
  intros until c. intros LIVE N1 st1 st2 CNT QC1 REC AH HIN MI ST BOT LO TP Ha0 AUNW S0NE RA4 RANE SP16 RSTK.
  assert (UNWX : exists trt, afree_unw RNG lo m (al_top L) sp s0 ra trt /\ In (AFREE_PC :: trt) (al_U L)).
  { destruct AUNW as [(BT & UC & LTR & TRU & RTOP)|(TOPLE & SPLT & TRU)]; [exists (bv_unsigned ra :: tr); split; [left; exists tr; split; [reflexivity|]; split; [exact UC|]; split; [exact LTR|]; split; [exact BT| exact RTOP]| exact TRU] | exists (@nil Z); split; [right; auto| exact TRU]]. }
  destruct UNWX as (trt & FUNW & TRU).
  destruct AH as (ALO & ARNG & [X [AR BL]] & HFK).
  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & HRT2 & AVL & RT3).
  cbn [ah_quar ah_sec ah_depot AHQ] in HQ, HS, HD. destruct HQ as [Q AQ].
  (* [comment removed for export] *)
  pose proof BL as BL0. destruct BL0 as (BH & _).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVEB & FRESH & UNIQ).
  destruct (BH p A n HIN) as [(y & Hy & Sy & Uy & Ny)|(mb & msz & Lp & _)]; [| exfalso; rewrite LIVE in Lp; discriminate].
  destruct (BUSY y Hy) as [CLy My]. rewrite Sy in My. destruct My as (_ & _ & _ & _ & _ & M5). rewrite LIVE in M5.
  injection M5 as Cy Ny'. clear Ny'.
  destruct (in_split _ _ Hy) as (l1 & l2 & XB).
  destruct y as [yc yk yn yst yb1 yctx]. cbn in Sy, Uy, Ny, Cy, CLy. subst yst yn yc.
  rename yk into k. rename yb1 into b1. rename yctx into ctx.
  change ({| xb_class := c; xb_slot := k; xb_n := n; xb_st := BLive p; xb_b1 := b1; xb_ctx := ctx |}) with (bfreed p c k n b1 ctx) in XB.
  unfold xb_user, xb_alloc in Uy. cbn [xb_class xb_slot xb_n] in Uy.
  (* [comment removed for export] *)
  destruct (freed_range L st X p c k n b1 ctx l1 l2 WF XB) as [HC KR].
  pose proof (freed_live L st X p c k n b1 ctx l1 l2 XB WF) as (_ & N0 & FIT0 & B10 & AT0 & CTX0).
  pose proof (chunk_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as (HM16 & UB16 & ABUB & ABHM & HLO & UBS & ABCE & HHI & N65 & NQM & ABLO & RUP & RUP8 & S8).
  pose proof (slot_sep_objects L st X c k ALO WF HC KR) as (DT & DC & DN & DSO & DF).
  destruct (slot_rng L st X c k ALO WF HC KR RNG ARNG) as [RSL RSS].
  pose proof ARNG as ARNG0. destruct ARNG0 as (RIMG & RT4 & RCTX & RNO & RSTO & RRI & RFK & RSFK & RDT & RCLS & RPA & RSECS & RPSH).
  pose proof (chunk_shadow_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as (SE & G2 & GE & G0 & GFS & SHLO & SHHI & _).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof (alayout_depot L ALO) as (DL1 & DL2 & DL3 & DL4 & DL5 & DL6 & DL7 & DL8 & DL9 & DL10).
  pose proof (alayout_stack L ALO) as (STK1 & STK2 & STK3).
  assert (SP47 : bv_unsigned sp < 2^47) by (eapply afree_unw_sp47; [exact FUNW| exact STK2]).
  set (AB := aslot_addr L c k) in *. set (UB := AB + rz_size n) in *.
  assert (EHM : fhm L c k n = UB - 16) by (unfold fhm; subst AB UB; lia).
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
  destruct (CACHES K_BATCH_CLASS (K24)) as [tail (CR & CH & LCH)].
  replace (acache_addr L K_BATCH_CLASS) with (al_t L + 2128) in CR by (unfold acache_addr, K_BATCH_CLASS; lia).
  destruct (junk_split m (al_t L + 2768) 16 16 CSTATS ltac:(lia) ltac:(lia)) as [CSa CSb].
  destruct (junk_split m (al_t L + 2768 + 16) 8 8 CSb ltac:(lia) ltac:(lia)) as [CS8 CSc].
  replace (al_t L + 2768 + 16) with (al_t L + 2784) in CS8 by lia.
  destruct (c8_of_junk m _ CS8) as [stj STS].
  (* [comment removed for export] *)
  destruct (read_chunk L st X m p c k n b1 ctx l1 l2 ALO WF XB (conj (proj1 (proj2 (proj2 (CLS c HC)))) (proj2 (proj2 (proj2 (CLS c HC))))))
    as (HDR & [uw HUW] & UJR & LH & SHA & SHU & SHR).
  fold AB in HDR, HUW, UJR, LH, SHA, SHU, SHR. fold UB in HDR, HUW, UJR, LH, SHU, SHR.
  (* [comment removed for export] *)
  pose proof AQ as AQ0. destruct AQ0 as ([QK MX] & [QC ABL] & [GCQ ABG] & (FL & IAS & IAM) & CP & NUM).
  destruct NUM as (NB1 & NB2 & NF & NC & NM).
  pose proof (batches_bytes_lb (a_qloc st) ltac:(apply Forall_app in NF; exact (proj1 NF))) as LLB. rewrite <- NB1 in LLB.
  (* [comment removed for export] *)
  assert (EKX : exists k24 chunks, let ek := ek_of L st X Q n k24 stj chunks in
       ek_pre ek RNG (al_t L) (Z.of_nat (length (a_qloc st))) (qlast L (q_loc Q)) n (fhm L c k n) m
    /\ ek_seps ek L (fhm L c k n) (qlast L (q_loc Q))
    /\ 0 <= ek_delta ek n /\ a_qloc_bytes st2 = a_qloc_bytes st + ek_delta ek n /\ a_qglob_bytes st2 = a_qglob_bytes st
    /\ (ek_b ek (qlast L (q_loc Q)) = qlast L (q_loc Q)
        \/ exists kk, ek_b ek (qlast L (q_loc Q)) = abatch_addr L kk /\ 0 <= kk < ndist st K_BATCH_CLASS /\ ~ In kk (map qb_slot (q_loc Q ++ q_glob Q)))
    /\ (enq_is_app st = false ->
          nth_error (xc_cache (x_cls X K_BATCH_CLASS)) (Z.to_nat (c_count (get_cls st K_BATCH_CLASS) - 1)) = Some k24
       /\ busy_of X K_BATCH_CLASS k24 = None /\ 0 <= k24 < ndist st K_BATCH_CLASS
       /\ ~ In k24 (map qb_slot (q_loc Q ++ q_glob Q))
       /\ junk_at m (abatch_addr L k24) 8192 /\ fill_at m (shad (abatch_addr L k24)) (shlen 8192) 0xfa
       /\ a_cinit st = true /\ 0 < c_count (get_cls st K_BATCH_CLASS))).
  { pose proof (st_enq_bytes st p (CPrim c n) L X Q) as SB.
    destruct (enq_is_app st) eqn:EA.
    - destruct (read_ek_app (AHQ DI ASEC_of AFK) L st X Q m RNG (BLive p) c k n b1 ctx l1 l2 ALO ARNG AR AQ XB ltac:(discriminate) stj [] 0 EA
                (Z_to_bv 64 0) (Z_to_bv 64 0) 0 CR STS) as (EK & ES & ED & EB & _).
      specialize (SB 0 stj [] ltac:(intros E; exfalso; change (enq_app st1 (CPrim c n) = None) in E; assert (EA1 : enq_is_app st1 = true) by exact EA;
                    destruct (proj1 (enq_is_app_spec st1 (CPrim c n)) EA1) as [s Hs]; congruence)).
      cbn [chunk_size] in SB. destruct SB as (SB1 & SB2 & _).
      exists 0, []. cbv zeta. split; [exact EK|]. split; [exact ES|]. split; [rewrite ED; lia|]. split; [exact SB1|]. split; [exact SB2|].
      split; [left; exact EB|]. intros; discriminate.
    - assert (POS : 0 < c_count (get_cls st K_BATCH_CLASS)).
      { apply CNT. destruct (enq_app st1 (CPrim c n)) eqn:E; [| reflexivity]. exfalso.
        assert (EA1 : enq_is_app st1 = true) by (apply (proj2 (enq_is_app_spec st1 (CPrim c n))); eexists; exact E).
        change (enq_is_app st1) with (enq_is_app st) in EA1. congruence. }
      destruct (read_ek_new (AHQ DI ASEC_of AFK) L st X Q m RNG (BLive p) c k n b1 ctx l1 l2 ALO ARNG AR AQ XB ltac:(discriminate) stj EA POS STS)
        as (k24 & chunks & EK & ES & ED & EB & NK & NB & KK & NIB & JK & FSH & CIN & _).
      specialize (SB k24 stj chunks ltac:(intros _; exact POS)). cbn [chunk_size] in SB. destruct SB as (SB1 & SB2 & _).
      exists k24, chunks. cbv zeta. split; [exact EK|]. split; [exact ES|]. split; [rewrite ED; lia|]. split; [exact SB1|]. split; [exact SB2|].
      split; [right; exists k24; split; [exact EB|]; split; [exact KK| exact NIB]|].
      intros _. repeat (split; [assumption|]). exact POS. }
  destruct EKX as (k24 & chunks & EKX). cbv zeta in EKX. destruct EKX as (EK & ES & ED0 & SB1 & SB2 & EBB & NEWF).
  set (ek := ek_of L st X Q n k24 stj chunks) in *.
  assert (DELTA : ek_delta ek n <= n + 8192) by (subst ek; unfold ek_of; destruct (enq_is_app st); cbn [ek_delta]; lia).
  (* [comment removed for export] *)
  destruct (read_dkC (AHQ DI ASEC_of AFK) L st X Q m RNG (BLive p) c k n b1 ctx l1 l2 ALO ARNG AR AQ XB ltac:(discriminate) (ek_b ek (qlast L (q_loc Q))) (ek_delta ek n) ek ED0
              ltac:(unfold Q_MAX, Q_BATCH_BYTES in *; clear -DELTA NQM; lia) EBB
              ltac:(rewrite <- SB1; exact QC1) ltac:(rewrite <- SB1, <- SB2; clear -REC; lia) eq_refl) as (DK & DS & GL & GLST & GDR).
  set (g := g_of L st Q (ek_delta ek n)) in *.
  (* [comment removed for export] *)
  rewrite (afree_rec_eq st p (CPrim c n) LIVE ltac:(cbn [chunk_size]; exact NQM) CNT QC1 REC).
  pose proof (after_rec_eq st2 QC1 REC) as (_ & TQL & TQB & TQG & TQGB). fold st1 st2.
  (* [comment removed for export] *)
  assert (AB64 : forall q, In q (q_loc Q ++ q_glob Q) -> 0 <= abatch_addr L (qb_slot q) < 2^64).
  { intros q Hq. pose proof (bslot_geo L st X ALO WF (qb_slot q) (bslot_range L st X Q WF CP q Hq)) as (B0 & B1 & _). atop_facts. lia. }
  assert (LF64 : 0 <= qfirst L (q_loc Q) < 2^64).
  { destruct (qfirst_cases L (q_loc Q)) as [-> |(q & Hq & ->)]; [lia| apply AB64; apply in_or_app; left; exact Hq]. }
  assert (LL64 : 0 <= qlast L (q_loc Q) < 2^64).
  { destruct (qlast_cases L (q_loc Q)) as [-> |(q & Hq & ->)]; [lia| apply AB64; apply in_or_app; left; exact Hq]. }
  (* [comment removed for export] *)
  unfold AIMG_HI, AFREE_STACK, UDEPTH, Q_MAX, Q_CACHE in *.
  box DT. box DC. box DN. box DSO. box DF. box CL5. box DL7. box DL8. box DL9. box DL10.
  iprefix. eapply evtF_cut.
  { eapply (free_torec DI L (q_ia Q) ek g RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m
              (al_t L) (al_ctx L) (fhm L c k n) n b1 ctx lo (al_top L) (al_bot L)
              (Z.of_nat (length (a_qloc st))) (qfirst L (q_loc Q)) (qlast L (q_loc Q)) (a_qloc_bytes st) uw sj (block_shadow_bytes n) trt).
    all: rewrite ?EHM.
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact ST | exact IAS]
         | |- ablk _ (_ + 16 + rup _ 8) => first [assumption | unfold ablk; right; generalize HLO HHI; try generalize EHM; clear; unfold fhm; intros; lia]   (* [comment removed for export] *)
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- poison_cells _ => unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- ADEPOT _ _ _ => exact HD
         | |- afree_unw _ _ _ _ _ _ => exact FUNW
         | |- In _ _ => exact TRU
         | |- u64arr _ _ _ _ => exact STATS
         | |- ek_pre _ _ _ _ _ _ _ _ => exact EK
         | |- ek_seps _ _ _ _ => exact ES
         | |- dk_preC _ _ _ _ _ _ _ _ => exact DK
         | |- dk_seps _ _ _ => exact DS
         | |- _ = true -> _ => exact IAM
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HDR
         | |- rw_cells _ _ (shad _) _ => eapply rw_cells_addr_eq; [exact SHU| f_equal; lia]
         | |- rw_cells _ _ (_ + 80) _ => exact QC
         | |- rw_cells _ _ (_ - 16 + 16) [C8 _] => eapply rw_cells_addr_eq; [exact HUW| lia]
         end.
    all: try lazymatch goal with
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _] => first [exact T0 | exact QK]
         | |- rw_cells _ _ _ _ => assumption
         | |- @eq word _ _ => first [exact TP | rewrite Ha0, <- Uy; subst AB UB; apply Z_to_bv_eqm; first [(generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LL64 ED0 DELTA RA4; clear; intros; lia) | lia] | reflexivity]   (* [comment removed for export] *)
         | |- _ \/ _ => first [unboxed DT | unboxed DC | unboxed DN | unboxed DSO | unboxed CL5 | unboxed DL7 | unboxed DL8 | unboxed DL9 | unboxed DL10
                             | ub DT; (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LL64 ED0 DELTA RA4; clear -Y; intros; lia) | ub DC; (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LL64 ED0 DELTA RA4; clear -Y; intros; lia) | ub DN; (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LL64 ED0 DELTA RA4; clear -Y; intros; lia) | ub DSO; (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LL64 ED0 DELTA RA4; clear -Y; intros; lia)
                             | ub DT; lia | ub DC; lia | ub DN; lia | ub DSO; lia]
         | |- rng _ (shad _) _ => replace (UB - 16 + 16) with UB by (clear; lia); eapply rng_sub; [exact RSS| rewrite SE; first [(generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LL64 ED0 DELTA RA4; clear; intros; lia) | lia]| rewrite SE, GE; first [(generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LL64 ED0 DELTA RA4; clear; intros; lia) | lia]]
         | |- rng _ _ _ => first [assumption | eapply rng_sub; [exact RSL| (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LL64 ED0 DELTA RA4; clear; intros; lia)| (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LL64 ED0 DELTA RA4; clear; intros; lia)] | eapply rng_sub; [exact RCTX| (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LL64 ED0 DELTA RA4; clear; intros; lia)| (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LL64 ED0 DELTA RA4; clear; intros; lia)] | eapply rng_sub; [exact RSL| lia| lia] | eapply rng_sub; [exact RCTX| lia| lia] | solve_rng]
         end.
    all: try assumption.
    all: unfold AIMG_HI, Q_MAX, Q_CACHE, Q_BATCH_BYTES, UDEPTH in *.
    all: try (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6
                         B10 LLB NC NM LF64 LL64 ED0 DELTA RA4; clear; intros; lia).
    all: rewrite Ha0, <- Uy; subst AB UB; f_equal; clear; lia. }
  cbv beta. intros ms1 PT. rewrite EHM in PT.
  (* [comment removed for export] *)
  pose proof (STOREC L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st LB X Q p c k n b1 ctx A lo k24 l1 l2 stj chunks
                ALO ARNG AR AQ BL HFK XB HIN N1 NEWF QC1 REC EK DK ltac:(atop_facts; lia) ltac:(unfold AFREE_STACK; lia) TP ms1 PT) as SP.
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
