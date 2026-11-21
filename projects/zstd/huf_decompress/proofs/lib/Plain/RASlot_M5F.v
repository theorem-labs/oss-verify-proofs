(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (5 recorded proofs replaced by written proofs (rlowW_meta, rfailW_shape, rfailW_low and 2 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import PImg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A MallocKit_AB MallocKit_A2 MallocKit_A3 MallocKit_B MallocKit_B3.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W0 ASlot_W1 ASlot_W9 ASlot_W18 ASlot_I ASlot_M0 ASlot_M5D.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import RMallocRep RMallocTree RF_get_meta RMallocKit_B RMallocKit_B2 RMallocKit_B3 RMallocKit_A RMallocKit_A2 RMalloc_fp RAllocSlot_iface RASlot_I RASlot_W2 RASlot_W4 RASlot_W18 RASlot_W19 RASlot_M0 RASlot_M2 RASlot_M5D.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require MallocFacts_inv4.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RASlot_M5F () := "I59OSSVerify5KrLib4Spec5STree5stree00C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC59OSSVerify5KrLib4Spec6Malloc1MC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib5Plain:RMallocRep5rmrepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep9meta_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain<RMallocKit_BArmeta_slot_boundsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4concC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z2gec59OSSVerify5KrLib5Plain:RASlot_M5F5rlowWC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndI47Corelib4Init9Datatypes4prod00C56Stdlib6ZArith6BinInt1Z3subI47Corelib4Init5Logic2eq00C59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03K47Corelib4Init9Datatypes6option02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init5Logic2or01I47Corelib4Init5Logic2or00K47Corelib4Init9Datatypes4prod01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib5Plain:RMallocRep4RCTXC1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib4Spec6Malloc3ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_free_meta_headC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01c59OSSVerify5KrLib5Plain:RASlot_M5F6rmetaWC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02I47Corelib4Init5Logic2ex00K47Corelib4Init5Logic2or02K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01I47Corelib5Lists7ListDef6Forall00K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C59OSSVerify5KrLib5Plain:RASlot_W186rfailWC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_prevC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain:RASlot_M5F:rlowW_metaC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain:RASlot_M5F<rfailW_shapeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List;Forall_implK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega7EnvRing5PExpr04C59OSSVerify5KrLib6Malloc:MallocTreeDForall_disjoint_fromC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C59OSSVerify5KrLib5Plain;RMallocTree6rimplTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9ASlot_W18?as_free_meta_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RASlot_M5D;rNFAIL_stmtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain;RMallocTree?rimplT_from_evtC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03C59OSSVerify5KrLib5Plain:RASlot_M5D9rnest_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc>MallocFacts_AS7ta_failC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Malloc8ASlot_W06ta_rel00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocNat2kSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocNat2bSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:alloc_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib6Malloc9ASlot_M5D4nclsC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC59OSSVerify5KrLib4Spec6PState4ps_mC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState5ps_faC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState5ps_soC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib5Plain9RASlot_M24rFRMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMalloc_fp:rmalloc_fpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc7ASlot_I5as_kqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9free_metaC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib5Plain:RASlot_M5D:rnest_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Malloc>MallocFacts_AS3IST00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Malloc7ASlot_I9ENTRY_REL00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc7ASlot_I4ALLCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep8ticks_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>c_mmap_counterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain;RMallocTree8rauxv_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9Malloc_fp9unk_agreeC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Malloc9Malloc_fp4mrel00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree;brk_link_psC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC59OSSVerify5KrLib5Plain@RAllocSlot_iface<RAS_STACK_geC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain@RAllocSlot_iface9RAS_STACKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RASlot_M5D;rerrno_lit5C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9ASlot_M5D:nest_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9ASlot_M5D4nreqC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr05C59OSSVerify5KrLib6Malloc>MallocFacts_AS6req_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc>MallocFacts_AS4ISTRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc@MallocFacts_inv4@istr_facts_proofC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Malloc>MallocFacts_AS6ISTF_g00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc>MallocFacts_AS6isf_mfC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Malloc=MallocFacts_A8MFACTS_g00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc@MallocFacts_inv4@nest_facts_proofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc>MallocFacts_AS7nest_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc7ASlot_I8ai_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9ASlot_M5D>meta_slot_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RASlot_M5DBrconc_meta_stable'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5stripC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc>MallocFacts_AS6isf_lfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc>MallocFacts_AS;lf_freelistC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc>MallocFacts_AS=fact_freelistC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC59OSSVerify5KrLib6Malloc9ASlot_W188as_fm_stC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep2wzC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain9RASlot_W29rta_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RASlot_W18<rfailm1_walkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain8RASlot_I9ras_post2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain:RASlot_M5F:rfailW_lowC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain:RASlot_M5F>rlowW_disjointC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5FrameFstk_transport_disjointC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib3Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain:RASlot_M5FBrlowW_disjoint_imgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5FrameBrw_cells_transportC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState6ret_pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RASlot_W198ras_ret0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ASlot_M07fm_projC1?~~~~~~~~~~~~~~~I35stdpp4gmap4gmap00C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_shadowC1?~~~~~~~~~~~~~~~C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_tickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_next_ridC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_reservedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_brkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ASlot_W0:tr_regionsC1?~~~~~~~~~~~~~~~C35stdpp4gmap;gmap_lookupC59OSSVerify5KrLib6Malloc9Malloc_fp<mrel_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMalloc_fp?rmalloc_fp_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain;RMallocTreeArpres_except_monoC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith4Znat3N2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith4Znat3N2Z9is_nonnegC59OSSVerify5KrLib5Plain:RASlot_M5D@rmalloc_fp_widenC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC46Stdlib5Lists4List=Forall_forallC47Corelib4Init5Logic5proj1C59OSSVerify5KrLib5Plain;RMallocTree9ralloc_fpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9Malloc_fp<new_reg_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9Malloc_fp>free_slot_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9Malloc_fp<grp_hdr_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree:fresh_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep5lr_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc;MallocKit_BDmeta_slot_same_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMalloc_fpArmeta_chunk_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep:meta_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain<RMallocKit_BFrpres_except_of_munch'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain;RMallocTreeBrpres_except_transC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain;RMallocTree<rpres_exceptC1?~~~~~~~~~~~~~~~C35stdpp4gmap:gmap_emptyC35stdpp4base5emptyI59OSSVerify5KrLib6Malloc7ASlot_I7as_inv200C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain9RASlot_M0Erauxv_ok_malloc_fp_ERC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ASlot_M0=ticks_ok_sameC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffC47Corelib4Init5Logic6or_indC59OSSVerify5KrLib4Spec6Malloc:get_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9cell_readC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc7cellval02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9Malloc_fp;grp_hdr_covC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep;rregions_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep9rmrep_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep=rmrep_globalsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep;rmrep_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep<rmrep_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep<rmrep_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep8rstaticsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMalloc_fp=rregion_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc;MallocKit_B9ivs_avoidC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc;MallocKit_B=avoid_outsideC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib3Lib3Mem;wa_unsignedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ASlot_M0>unk_agree_xferC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree;amr_regionsC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2leC59OSSVerify5KrLib6Malloc:MallocTree<amr_next_ridC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ASlot_W07tr_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9Malloc_fp9mrel_nextC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib6Malloc8ASlot_W0;tr_reservedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree<amr_reservedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9Malloc_fp=mrel_reservedC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Malloc9Malloc_fp4mrel01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState6ps_brkC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc8brkstate03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6activeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07C59OSSVerify5KrLib6Malloc8ASlot_W09tr_activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree:amr_activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc7ASlot_I6ai_actC1?~~~~~~~~~~~~~~~C35stdpp4base6lookupC35stdpp4base7is_SomeC59OSSVerify5KrLib6Malloc8ASlot_W08tr_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree9amr_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ASlot_W07tr_tickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree8amr_tickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc7ASlot_I7ai_tickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc7ASlot_I8ret_spanC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7r_cellsC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2ltC47Corelib4Init5Logic9False_indC56Stdlib6ZArith6BinInt1Z3divC59OSSVerify5KrLib4Spec6Malloc5r_havC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_havpC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Malloc7ASlot_I7as_inv201C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec8evt_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec7evt_cutC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:alloc_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree7leaf_ofC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Malloc:MallocTree6am_rel00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec3evtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7bouncesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9unmap_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_seqC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelC59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc@F_malloc_enframe3rdvC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Malloc9Malloc_fp7slot_ok00C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7and_indC59OSSVerify5KrLib4Spec6Malloc;ranges_freeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8full_layC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain4PImg5psegsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5Stdio9stdout_st00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5meta0C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K46Stdlib9micromega=RingMicromega3Op201I59OSSVerify5KrLib4Spec6Malloc8brkstate00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree3memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree8pans_memC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep<ref_reservedC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat3N2Z6inj_leC45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableI59OSSVerify5KrLib4Spec6PState6PState00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc2IBC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes3nat00I47Corelib4Init5Logic5False00C59OSSVerify5KrLib5Plain:RMallocRep:RSSP_GUARDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep6RMLOCKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep=RSIZE_CLASSESC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep4RATPC1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableI59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc7cellval00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc8brkstate01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc8brkstate02C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition rlowW (spv : Z) (iv : Z * Z) : Prop :=
  (0 <= fst iv /\ snd iv <= ATOP /\ (snd iv <= 0x10000 \/ 0x59000 <= fst iv \/ (RCTX <= fst iv /\ snd iv <= RCTX + 928)))
  \/ iv = (spv - 144, spv).

Lemma rlowW_meta spv st m' q : rmrep st m' -> meta_slot st q -> rlowW spv (conc st q, conc st q + 40).
Proof.
  intros MR MS. destruct (rmeta_slot_bounds st m' q MR MS) as (Gpos & GC & GI & _). left. atop_facts. cbn [fst snd]. lia.
Qed.

Definition rmetaW (spv : Z) (st : mstate) (iv : Z * Z) : Prop :=
  (exists q, meta_slot st q /\ fst iv = conc st q /\ snd iv = conc st q + 40) \/ iv = (RCTX + 16, RCTX + 24) \/ iv = (spv - 144, spv).

Lemma rfailW_shape st mt spv :
  meta_slot st mt ->
  (forall h, c_free_meta_head (ctx st) = Some h -> meta_slot st h /\ forall p, m_prev (get_meta_rec st h) = Some p -> meta_slot st p) ->
  Forall (rmetaW spv st) (rfailW st mt spv).
Proof.
  intros MS FL. unfold rfailW.
  constructor; [right; right; reflexivity|].
  constructor; [left; exists mt; auto|].
  constructor; [right; left; reflexivity|].
  destruct (c_free_meta_head (ctx st)) as [h|] eqn:FH; [|constructor].
  destruct (FL h eq_refl) as [MSh FP].
  constructor; [left; exists h; auto|].
  destruct (m_prev (get_meta_rec st h)) as [p|] eqn:HP; [|constructor].
  constructor; [left; exists p; auto| constructor].
Qed.

Lemma rfailW_low st mt m' spv :
  rmrep st m' -> meta_slot st mt ->
  (forall h, c_free_meta_head (ctx st) = Some h -> meta_slot st h /\ forall p, m_prev (get_meta_rec st h) = Some p -> meta_slot st p) ->
  Forall (rlowW spv) (rfailW st mt spv).
Proof.
  intros MR MS FL. eapply Forall_impl; [| exact (rfailW_shape st mt spv MS FL)].
  intros [lo hi] [(q & MSq & E1 & E2)|[E|E]]; [cbn in E1, E2; subst; eapply rlowW_meta; eassumption| inversion E; subst; left; unfold RCTX; cbn; lia| inversion E; subst; right; reflexivity].
Qed.

Lemma rlowW_disjoint spv W a n : Forall (rlowW spv) W -> ATOP <= a -> (a + n <= spv - 144 \/ spv <= a) -> disjoint_from W a n.
Proof. intros FW Ha Hs. eapply Forall_disjoint_from; [exact FW|]. intros lo hi [(H1 & H2 & H3)|E]; [cbn in *; lia| inversion E; subst; lia]. Qed.

Lemma rlowW_disjoint_img spv W a n : Forall (rlowW spv) W -> 0x10000 <= a -> a + n <= 0x59000 -> (a + n <= RCTX \/ RCTX + 928 <= a) ->
  ATOP <= spv - 144 -> disjoint_from W a n.
Proof.
ltac2:(KReplay.run1 (kr_t_RASlot_M5F ()) ["CANSEC1"] "p'0h01Hh11Eh24__x1h34__x2h44__x3h54__x4h62H0h75ATOPRh82H5h91Wh:7__arithh;4__ffh<4__p1h=4__p2h>8__varmaph?5__with@4__x5hA1ahB1ehC2hihD2lohE1nhF3spvhG1zi001zhH2FWhI2H1hJ2H2hK2H3hL2H4hM2H6hN2X1hO2X2hP2X3hQ1pi011pp;2p;1p;3p;4p;6p;7p;8g00B>R0j2xTg00E3j1YTg00?nj1Zj2oTg00_Vj3bTg005dj12Tg00>Tj1CTg00>8j20Tg00<@j16Tg00<ej2FTg00=Bj1wTg00B^j24Tg00@iR1j2;Tg00C;R2j37Tg00CUj1cTg00fKj1BTg00h<j2ITg00fjj2RTg00DSj1`Tg00ESj2PTg00F1j1_Tg00FOj4NTg00Fmj1^Tg00GKj1]Tg00H6j2LTg00HYj2KTg00I<j3\Tg00I_j1vTg00KPj2uTg00L2j2XTg00LLj2rTg00M8j3qTg00MWj4pTg002:j6STg00hhj3nTg000gj7Uj6TTg00iKj6jTg00NcR3j2QTg00O=j4iTg00ADj3kTg00Aaj3hTg00gSj3lTg00]Mj3mTg00JAj4gTg00O]j7fTg00Pej7eTg00PAj7dTg00QIj8sTg00Jlj6tTf0R4#2#2p=M%24#2#2#2p=E%24#2#2#2#2#2#2#2p=A%64#6p=af2R5f1R6'F/04p=Of4R7f3R8'F/051064'Qp=9g00QmR9P9P6P4Cip=1Ak994p=<Ah994p==g00VmR:/04p=G1056/Q4p=31056/;4p=:%64#6#6#6p=@1R94p=HAl964p=8g00WgR;?m64p=?P5g00SPR<g00SoR=P=g00TOR>P9P6g00RiP4Cgg00ToFfp=5P5P<P=P=P>P6P4Fep=[P5P<P=P=P>P6P4Fdp=JP8P<P=P=P>P5P6P4Gsp=>1F85/06/Q4p=WA7964p=DP6P<P=P=P>P4Etp=V1x99R<#YR?%Z8=b<5g00VHR@#2RA#2RB#M#E#A#CRC/05%2@#a#M#6#E#A#CRD9O85P7P8P:%6@RE#6RF#2#6#2#E#CRG,F:RHP7D9p,2rcRI#wRJf7RK%6B#E#CRL'4'0f8RM#ZPKf6RNf5ROP7f:RP1164'oP3g00RKR31156RQ#<RR%=QRS%GR10SH';93DR93SC7:J3:f;RS/4L/1S97<QPPf9RQP8P5PPD9P41185RR#<RT%=RRU%GT10UH';93DT93UC7:J5:3P11178RU#<RT,03%=URV%GT10VH';93DT93VC7:Jf<RVPSPOP7PVD9P411NORT#<,0311KNRW#=RX%<WRY%GY10XH';53D93XC7:JP111MKR1#=RX/0J%<1R1%G110XH';53D93XCf@RXf?R1PQPMPXD9P411PQ#=/0J11SPRY#=RZ%<YRY%GY10ZH';53D73C%cIRI%@F#@#@RF#2#@#@#2#M#E#A#A#CRZ%6F#@#@#2#M#E#A#A#C,0JRF7:JRHg00jVRY#BR[#BR\#BR]#BR^#BR_#HR`%H]R]%H[R['8'8g00k5Ra'IRb%B_#H%H^R^/8['8/Ia1R9YRY,8^,8`/Ia%H\R\/8Y,8`/IaR`%`;R^,?`'?'?'?,?b'?%Y;R;P9P91P97P5%_9RbCNR`P6P91P9OP8PbCNCN%^9Rb%]9R_1L9BRB1K9CRc55_1K9DRd1L9ERE55_%6A,L9Re=5_E1K9G9\9eRf95_B5[_5J_5J_%v=R=P_1L9@R@1L9A5\9RA=5_eA5_f@5J_P=P_A5_AdRdP=P_A5_c@P=A5_AEA5_B@5J_C>C>C>C>1u_>R>P4P5g00Y:R@g00YZRc'X1r45=7@cdAq936CpR3b;b>b?X29X39X49X59X@91F7G,089:7593D5938CP6P5POAOOG6CWAO58DRD10C8P7POPNPKP7D9[[[[^29^39^49^59^@9P4P:f=R:f>RCfDRGfERcP5PXfAR@fBRfO9b:b7fCRe/FfRg10SeRh73VeWPWOP6P4O2n2001000000121000000W0WNP6P4O2n2001000000121000000W0P4O114VL/1V97<RP2P<PU141L/11R297<6PCP:PKPNPCD9[P414:L/1:RR97<U11O714CL/1CRC57<P<P9P0P9P9P9P4P4n2001101000120100100XB<PTP2P4ES1DO1P<P9P0P9P9P9P4P6n2001101000120100100XB<PW14XLRW/1XP6ES1DKW14@L,DMP414fL,DQP914eL1DPGRfA3g6h[XG91DQeP4PfP9PcPGPefFRf/4LRQP4PGD9XG9P914cLRh114V11QfRQ57<PcPGfGRG/4LRgPGPcD9]1XD911hS11hc57<P9Pf11g411gG57<PfPcfHRc/4LPcPfD9]1XC9A7<QQPIPHp-0RH18[Y,8\,8]/Ia/?^P;P9P`P61P98CNPbP_1K9Z=5_B1V_N5[_P=P_1K9L9n9ERE95_BP=P_PdP=A5_AE1V_K5J_C>C>C>P>P3b;b>b?X29X39X49X59X<HW=A:Z87148L,07P8P714OLPMCW\D[[^29^39^49^59^<H^=HP4fIRH/0GPFPJPHPfPGP6P@PeO9b:b7W1PVP5P4FUW1PVP8PMFUPSP4ETbMW8PPP4ETb8W6P4O1b6P4O1b6W0P4O1W0n2002101000000101A7<4CP:PVPNPOP:D9[XQ<PRO1P41X<CO1b0W1P4O1n200100000021100011000W0XC9XD9EjWLWKWJWIWHXE9XA9X9?XF9P8P5P6P4O4XE9XA9W9XF9o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section LEVEL.
Context {R : Type}.
Variables (f : nat) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (st0 st : mstate) (LB : list block) (lo sc req : Z) (errv : word).
Hypothesis AR : RAREACH st0 LB.
Hypothesis IS : IST st0 st.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis AC : ALLC st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req < 2^32.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
Hypothesis MR : rmrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis UA : unk_agree st o m.
Hypothesis BL : brk_link_ps st s.
Hypothesis AUX : rauxv_ok m (bv_unsigned sp).
Hypothesis ST : stk psegs m lo (bv_unsigned sp).
Hypothesis CLO : ATOP <= lo.
Hypothesis LO : lo <= bv_unsigned sp - RAS_STACK sc.
Hypothesis ERR : rw_cells psegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv psegs m.
Hypothesis TP : tp = Z_to_bv 64 RATP.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Hypothesis HK : forall st1 idx s' ms',
  ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
  rimplT o (k st1 idx) s' Q ms'.
Let F0 : RISTF st LB := MallocFacts_inv4.ist_facts_proof st0 LB st AR IS.

Lemma rnfail_ok : rNFAIL_stmt f k bail o s Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st lo sc.
Proof.
  intros st1 st2 mm cnt1 st3 m4 m'' s' s'' errv'' junk oo o3 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' NC.
  destruct NC as (TF & TR & ACT0 & LF & IS2 & ER2 & AC2 & REL & G0 & MSL & C1R & SMc & LEAF & MI'' & ST'' & ERR'' & AUX'' & MR'' & TK'' & UA''
                  & PE'' & MREL'' & BL'' & PSM'' & PSF'' & PSO'' & AI'' & CTR'' & FR'' & PE04 & MR4).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (RAS_STACK_ge sc) as ASG. pose proof CLO as CLO'. atop_facts.
  pose proof (rerrno_lit5 tp TP) as EA.
  destruct (nest_class sc SC cnt1 C1R SMc) as (ENR & JR & FITN & SCJ & NRR & NFIT).
  (* [comment removed for export] *)
  assert (RQ3 : req_ok (ncls sc cnt1) (nreq sc cnt1)) by (split; [lia| unfold IB, UNIT; lia]).
  assert (IS3 : ISTR st0 st3) by (exists o3, st2, f, (ncls sc cnt1), (nreq sc cnt1), (-1); split; [exact IS2|]; split; [lia|]; split; [exact RQ3| exact LEAF]).
  pose proof (MallocFacts_inv4.istr_facts_proof st0 LB st3 AR IS3) as F3. pose proof (isf_mf _ _ F3) as MF3.
  pose proof (MallocFacts_inv4.nest_facts_proof st0 LB st sc st1 oo st2 mm f (ncls sc cnt1) (nreq sc cnt1) o3 st3 (-1) AR IS SC TF LF ltac:(lia) RQ3 LEAF) as [G3 NFL].
  assert (MS3 : meta_slot st3 mm) by (eapply meta_slot_mono; [apply (ai_areas _ _ _ _ _ AI'')| exact MSL]).
  assert (GE : conc st3 mm = conc st2 mm) by (apply (rconc_meta_stable' st2 st3 m4 mm MR4 MREL'' MSL)).
  pose proof (rmeta_slot_bounds st2 m4 mm MR4 MSL) as (Gpos & GC & GI & _).
  (* [comment removed for export] *)
  pose proof (lf_freelist _ (isf_lf _ _ F3)) as FFL. change (fact_freelist (strip st3)) with (fact_freelist st3) in FFL.
  assert (FL : forall h, c_free_meta_head (ctx st3) = Some h ->
            meta_slot st3 h /\ h <> mm /\ exists p, m_prev (get_meta_rec st3 h) = Some p /\ meta_slot st3 p /\ p <> mm).
  { intros h Hh. destruct (FFL h Hh) as (MSh & MEMh & NXh & p & HP & MSp & MEMp & NXp). destruct (NFL h Hh) as [NE1 NE2].
    change (meta_slot (strip st3) h) in MSh. change (get_meta_rec (strip st3) h) with (get_meta_rec st3 h) in MEMh, NXh, HP.
    change (meta_slot (strip st3) p) in MSp.
    split; [exact MSh|]. split; [exact NE1|]. exists p. split; [exact HP|]. split; [exact MSp|]. intros ->. apply NE2. exact HP. }
  rewrite as_free_meta_eq. cbn [as_kq].
  riprefixT. unfold rnest_regs.
  eapply evt_cut.
  { rewrite <- GE. unfold rFRM in FR''. replace (bv_unsigned sp - 144) with (bv_unsigned sp + -144) in FR'' by lia.
    eapply (rfailm1_walk st3 mm MS3 FL); [exact MR''| exact MI''| exact FR''| lia]. }
  cbv beta. intros ms' (a1x & s6x & m7 & junk' & -> & FR7 & MU7 & WM7 & MI7 & MR7).
  assert (LW : Forall (rlowW (bv_unsigned sp)) (rfailW st3 mm (bv_unsigned sp))).
  { eapply (rfailW_low st3 mm m'' _ MR'' MS3). intros h Hh. destruct (FL h Hh) as (MSh & _ & p & HP & MSp & _).
    split; [exact MSh|]. intros p' Hp'. rewrite HP in Hp'. inversion Hp'; subst. exact MSp. }
  assert (ST7 : stk psegs m7 lo (bv_unsigned sp + -144)).
  { eapply stk_transport_disjoint; [| exact MU7| exact WM7| apply (rlowW_disjoint (bv_unsigned sp)); [exact LW| lia| lia]].
    replace (bv_unsigned sp + -144) with (bv_unsigned sp - 144) by lia. exact ST''. }
  assert (ERR7 : rw_cells psegs m7 (errno_addr tp) [C4 errv'']).
  { eapply rw_cells_transport; [exact ERR''| exact MU7| exact WM7|]. rewrite EA. apply (rlowW_disjoint_img (bv_unsigned sp)); [exact LW| lia| cbn; lia| unfold RCTX; cbn; lia| lia]. }
  eapply evt_cut. { eapply (ras_ret0 sp gp tp); [exact MR7| exact MI7| exact FR7| exact ST7| exact CLO| lia]. }
  cbv beta. intros ms' (a1y & a2y & -> & ST8). apply evt_done.
  (* [comment removed for export] *)
  set (stF := as_fm_st st3 mm) in *.
  destruct (fm_proj st3 mm) as (PF1 & PF2 & PF3 & PF4 & PF5 & PF6 & PF7 & PF8 & PF9 & PF10 & PF11 & PF12 & _). fold stF in PF1, PF2, PF3, PF4, PF5, PF6, PF7, PF8, PF9, PF10, PF11, PF12.
  assert (REG1 : s_regions st1 = s_regions st) by apply (tr_regions _ _ _ TR).
  assert (FS : Forall (rmetaW (bv_unsigned sp) st3) (rfailW st3 mm (bv_unsigned sp))).
  { apply (rfailW_shape st3 mm _ MS3). intros h Hh; destruct (FL h Hh) as (MSh & _ & p & HP & MSp & _); split; [exact MSh|]; intros p' Hp'; rewrite HP in Hp'; inversion Hp'; subst; exact MSp. }
  assert (PE07 : rpres_except (rmalloc_fp st0 stF lo (bv_unsigned sp)) m m7).
  { eapply rpres_except_trans.
    - eapply rpres_except_mono; [exact PE04|]. intros a Ha. eapply rmalloc_fp_mono; [| exact Ha]. intros rid r Hr.
      destruct (mrel_regions _ _ MREL'' rid r Hr) as (r' & Hr' & K' & B' & L'). exists r'. rewrite PF1. auto.
    - eapply rpres_except_trans.
      + eapply rpres_except_mono; [exact PE''|]. intros a Ha. eapply (rmalloc_fp_widen st0 st3 stF lo (bv_unsigned sp) (bv_unsigned sp - 144) a ltac:(lia)); [| exact Ha].
        intros rid r Hr. exists r. rewrite PF1. repeat split; auto. lia.
      + eapply rpres_except_of_munch'; [exact MU7| exact WM7|].
        intros lo' hi' HI x Hx. pose proof (proj1 (Forall_forall _ _) FS _ HI) as [(q & MSq & E1 & E2)|[E|E]].
        * cbn in E1, E2. subst lo' hi'. left. do 3 right.
          assert (MSq' : meta_slot stF q) by (eapply meta_slot_same_areas; [rewrite PF4; reflexivity| exact MSq]).
          destruct (rmeta_chunk_facts stF m7 q MR7 MSq') as (_ & _ & _ & _ & _ & _ & (rid0 & r0 & H0 & K0 & L0 & H0')).
          exists rid0, r0. split; [exact H0|]. split; [exact K0|].
          assert (EC : conc stF q = conc st3 q) by (unfold conc, get_region; rewrite PF1; reflexivity). rewrite EC in L0, H0'. lia.
        * inversion E; subst. left. right. right. left. unfold RCTX in *. atop_facts. lia.
        * inversion E; subst. left. left. lia. }
  apply HK. unfold ras_post2.
  do 14 eexists. exists m7, errv''. split; [reflexivity|].
  split; [exact MI7|]. split; [exact ST8|]. split; [exact ERR7|].
  split; [eapply (rauxv_ok_malloc_fp_ER st0 st m MR ER stF m7); [exact MR7| exact AUX| exact PE07| exact CLO| lia]|].
  split; [exact MR7|].
  split; [eapply ticks_ok_same; [rewrite PF2; reflexivity| rewrite PF6; reflexivity| exact TK'']|].
  split. { eapply (unk_agree_xfer o st3 m'' stF m7 UA'').
    - exact PF2.
    - intros rid r Hk Hr. rewrite PF1 in Hr. exact Hr.
    - intros b. rewrite PF3. tauto.
    - intros rid r off h Hr Hk Ho Hc NG.
      pose proof MR'' as (WF3 & _). pose proof WF3 as (_ & WR3 & DJ3 & _). destruct (WR3 _ _ Hr) as (R0 & _ & _ & RC & _). atop_facts.
      destruct (rregion_facts st3 m'' rid r MR'' Hr) as (_ & _ & _ & RI1 & RI2). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)).
      apply MU7. rewrite wa_unsigned by lia. eapply (avoid_outside _ (fun y => y = r_base r + off)); [| reflexivity]. intros lo' hi' a' HI Ha ->.
      pose proof (proj1 (Forall_forall _ _) FS _ HI) as [(q & MSq & E1 & E2)|[E|E]].
      + cbn in E1, E2. subst lo' hi'.
        destruct (rmeta_chunk_facts st3 m'' q MR'' MSq) as (_ & _ & _ & _ & _ & GRG & _). destruct (GRG rid r Hr Hk); lia.
      + inversion E; subst. unfold RCTX in Ha. lia.
      + inversion E; subst. lia. }
  split; [exact PE07|].
  split. { split.
    - intros rid r Hr. rewrite <- REG1 in Hr. destruct (amr_regions _ _ _ REL rid r Hr) as (r' & H' & K' & B' & L' & _).
      destruct (mrel_regions _ _ MREL'' rid r' H') as (r'' & H'' & K'' & B'' & L''). exists r''. rewrite PF1. repeat split; auto; [congruence| congruence| lia].
    - rewrite PF7. pose proof (amr_next_rid _ _ _ REL). pose proof (tr_next _ _ _ TR). pose proof (mrel_next _ _ MREL''). lia.
    - rewrite PF8, (mrel_reserved _ _ MREL''), (amr_reserved _ _ _ REL). apply (tr_reserved _ _ _ TR). }
  split. { unfold brk_link_ps in BL'' |- *. rewrite PF11. destruct (c_brk (ctx st3)) as [| |brid boff]; auto.
           unfold conc, get_region. rewrite PF1. exact BL''. }
  split; [exact PSM''|]. split; [exact PSF''|]. split; [exact PSO''|].
  split. { constructor.
    - intros c' Hc'. rewrite PF9, (ai_act _ _ _ _ _ AI'') by lia. rewrite (amr_active _ _ _ REL). apply (tr_active _ _ _ TR). lia.
    - intros a Ha. rewrite PF4. apply (ai_areas _ _ _ _ _ AI''). apply (amr_areas _ _ _ REL). rewrite (tr_areas _ _ _ TR). exact Ha.
    - rewrite PF6, (ai_tick _ _ _ _ _ AI''), (amr_tick _ _ _ REL). apply (tr_tick _ _ _ TR).
    - intros H; exfalso; lia.
    - intros _ H; exfalso; lia. }
  split; [rewrite PF12; exact CTR''|].
  left. reflexivity.
Qed.
End LEVEL.
End CANSEC1.
