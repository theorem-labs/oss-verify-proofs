(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (5 recorded proofs replaced by written proofs (rraw_malloc_bridge2, rimplT_silent, rheap_pres_of_fp and 2 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import PImg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A MallocBlocks MallocHINV Malloc_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import Malloc_fp F_malloc_enf F_malloc_join F_malloc_small F_malloc_entry F_malloc_core F_malloc_top.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import RMallocRep RMallocTree RF_get_meta RMallocKit_B RMallocKit_B2 RMallocKit_A RMalloc_fp RF_enframe RF_malloc_enf RAllocSlot_iface RF_malloc_entry RF_malloc_join RF_malloc_small RF_malloc_core RMalloc_iface RMalloc_ifaceP.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require MallocFacts_inv2.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_malloc_top () := "I59OSSVerify5KrLib4Spec5STree5strel00C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad:implM_bindC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalI35stdpp9countable9Countable00C59OSSVerify5KrLib5Plain;RMallocTree6rimplTC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=RF_malloc_topDrmembed_strel_followC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree4mrunC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4bindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ProgDeps6membedC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib4Spec5Monad5implMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad9implM_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain;RMallocTree?rimpl_bind_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad:implM_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4implC1?~~~~~~~~~~~~~~~C35stdpp4base;RelDecisionC59OSSVerify5KrLib5Plain;RMallocTreeCrimplM_membed_sbindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5STree;eruns_sbindC1?~~~~~~~~~~~~~~~C35stdpp4gmap;gmap_lookupC59OSSVerify5KrLib3Lib5ITree5epostC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree?impl_epost_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrl6followC1?~~~~~~~~~~~~~~~C35stdpp4base4fmapC35stdpp4base6LookupC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8nil_consC59OSSVerify5KrLib4Spec5STree9strel_indC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ProgDeps4bptrC1?~~~~~~~~~~~~~~~I46Stdlib7Sorting;Permutation;Permutation00C59OSSVerify5KrLib4Spec5Monad9implM_evtC1?~~~~~~~~~~~~~~~I35stdpp4gmap4gmap00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC59OSSVerify5KrLib4Spec6Malloc4cptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4mretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5mbindC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib4Spec6Malloc5stripC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState4ps_mC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C59OSSVerify5KrLib4Spec6Malloc6s_atopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6mallocC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib6Malloc:MallocTree7ptr_relC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib4Spec6PState5set_mC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4mgetC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7cmallocC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01C59OSSVerify5KrLib3Lib4Exec8evt_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad9implM_getC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib4Spec:MallocCtrl4MRELC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrl>malloc_controlC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib4Spec5Monad9implM_updC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib6Malloc8ProgDeps:raw_mallocC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib6Malloc8ProgDeps9fresh_offC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad4mupdC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstI59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree3memC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I59OSSVerify5KrLib4Spec6PState6PState00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4unit00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C59OSSVerify5KrLib5Plain4PImg5psegsC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C59OSSVerify5KrLib6Malloc:MallocTree8pans_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree8pupd_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree>pans_mem_rangeC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc2ev00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K59OSSVerify5KrLib4Spec5STree5stree01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<F_malloc_top;follow_steqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<F_malloc_top<follow_sbindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<F_malloc_top8mrun_fstC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocBlocks5blockC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC46Stdlib7Sorting;Permutation>Permutation_inK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I59OSSVerify5KrLib6Malloc=MallocFacts_A8MFACTS_g00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep5rmrepC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Malloc9Malloc_fp4mrel00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMalloc_fp:rmalloc_fpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain;RMallocTree<rpres_exceptC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib5Plain=RMalloc_iface<rclient_addrC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C59OSSVerify5KrLib5Plain=RMalloc_iface=ralloc_staticC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC59OSSVerify5KrLib6Malloc<Malloc_iface8in_blockC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>RF_malloc_join@rmalloc_fp_casesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega7EnvRing5PExpr02C59OSSVerify5KrLib5Plain>RF_malloc_join@rmalloc_fp_imageC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C59OSSVerify5KrLib6Malloc<MallocBlocks8blk_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocBlocks8blk_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>RMalloc_ifaceP=rblock_insideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocBlocks8blk_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep;rregions_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep9rmrep_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep=rmrep_globalsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep;rmrep_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep<rmrep_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep<rmrep_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep8rstaticsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib4Spec6Malloc;ranges_freeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep5lr_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_next_ridC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2leC59OSSVerify5KrLib4Spec6Malloc:s_reservedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9Malloc_fp@round_up_pg_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep;lr_lo_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain;RMallocTree9ralloc_fpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9Malloc_fp<new_reg_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9Malloc_fp>free_slot_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9Malloc_fp<grp_hdr_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree:fresh_addrC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6NArith6BinNat1N6eq_decI47Corelib4Init6Specif7sumbool00C47Corelib4Init5Logic9False_indK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C59OSSVerify5KrLib6Malloc9MallocRep8lr_lo_geC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_A=mf_free_clearC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_A9sstart_ofC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith4Znat3N2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat3N2Z9is_nonnegK46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_A<mf_hdr_clearC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTreeAfresh_live_regionC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain=RMalloc_iface:rheap_presC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula06C59OSSVerify5KrLib4Spec6Malloc7s_slotsC1?~~~~~~~~~~~~~~~C35stdpp4base6lookupC59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7testbitC59OSSVerify5KrLib4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelK47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindK46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00C59OSSVerify5KrLib5Plain:RMallocRep4RCTXC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201C59OSSVerify5KrLib4Spec6Malloc2IBC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib5Plain:RMallocRep<ref_reservedC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableC45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableK47Corelib4Init5Logic4True01C59OSSVerify5KrLib4Spec6Malloc:get_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9cell_readC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc7cellval01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep2b8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>RMalloc_ifacePBrregion_addr_factsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natK59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=F_malloc_free9wr_at_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRepBrwr_at_bytes_existC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC59OSSVerify5KrLib3Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC46Stdlib5Lists4List9app_nil_rC59OSSVerify5KrLib3Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith4Znat5Z2Nat2idC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib5Arith8PeanoNat3Nat7add_0_rC59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=F_malloc_freeArw_cells_of_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep<conc_region'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappI59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqI59OSSVerify5KrLib4Spec6Malloc7cellval00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain=RMalloc_iface5RHEAPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain;RMallocTree8rauxv_okC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC59OSSVerify5KrLib5Plain;RMallocTree?rauxv_ok_weakenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain=RMalloc_iface<rmalloc_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState6ps_brkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocBlocks8brk_linkC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Malloc<MallocBlocks;AREACH_from00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc@MallocFacts_inv2Bareach_facts_proofC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;Permutation?Permutation_symC59OSSVerify5KrLib6Malloc:MallocTree;brk_link_psC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocHINV?brk_link_ps_iffC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr03K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC59OSSVerify5KrLib3Lib6MState;lift_resultC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_signedC59OSSVerify5KrLib3Lib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4StepDunsigned_Z_to_bv_addC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4sextC45stdpp9bitvector;definitions6bv_addC59OSSVerify5KrLib3Lib8PropExec9b_addsextC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC59OSSVerify5KrLib3Lib6MState8step_genC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec8evt_stepC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C59OSSVerify5KrLib5Plain:RMallocRep@rregions_wf_atopC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=RF_malloc_top5rmidQC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5STree5stree00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>RF_malloc_core6rcoreQC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_tickC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N4succC59OSSVerify5KrLib4Spec:MallocCtrl4CRELC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8set_tickC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrl@malloc_core_ctrlC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrl>strip_set_tickC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2ltC46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib5Plain>RF_malloc_coreBrmalloc_core_implTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep2wzC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep8ticks_okC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9Malloc_fp9expo_condC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState5ps_faC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState5ps_soC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7slot_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep2pwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9Malloc_fp9unk_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>c_mmap_counterC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Malloc9Malloc_fp7slot_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC59OSSVerify5KrLib6Malloc9MallocRep9meta_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_freeableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8m_maplenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1ZAmul_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z=add_le_mono_rC56Stdlib6ZArith6BinInt1ZDmul_le_mono_nonneg_lC56Stdlib6ZArith6BinInt1Z7mul_1_rC56Stdlib6ZArith6BinInt1Z?mul_add_distr_lC59OSSVerify5KrLib5Plain;RMallocTreeArpres_except_reflC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C59OSSVerify5KrLib5Plain=RF_malloc_enf:renf_implTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5havocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<enframe_fullC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain=RF_malloc_enf9renf_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<F_malloc_topAmrun_enframe_fullC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC59OSSVerify5KrLib4Spec6Malloc:enframe_atC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=RF_malloc_top=rimplT_silentC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<F_malloc_enf8enf_leafC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState6ret_pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrl@strip_enframe_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrl;strip_havocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<F_malloc_top=strip_eq_projC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5s_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_metasC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC59OSSVerify5KrLib4Spec:MallocCtrl4pselC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrl;strip_stripC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Malloc<MallocBlocks;AREACH_from02C1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05c59OSSVerify5KrLib5Plain=RF_malloc_top;ruser_chunkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain=RMalloc_iface<rblock_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain=RMalloc_iface=raddr_exposedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ProgDeps8ptr_addrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain;RMallocTreeErpres_except_rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=F_malloc_join9mrel_sameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9Malloc_fp:mrel_transC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain;RMallocTreeArpres_except_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain;RMallocTreeBrpres_except_transC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMalloc_fp?rmalloc_fp_monoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=RF_malloc_top@rheap_pres_of_fpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain>RF_malloc_joinBrauxv_ok_malloc_fpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain=RMalloc_ifaceArheap_pres_weakenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<F_malloc_top:mod16_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep>round_up_pg_geC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib7Sorting;Permutation;Permutation02C59OSSVerify5KrLib4Spec6Malloc5c_brkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Image9reservedZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState7ps_initC1?~~~~~~~~~~~~~~~C35stdpp4gmap:gmap_emptyC35stdpp4base5emptyC47Corelib4Init9Datatypes2idC35stdpp6option;from_optionC59OSSVerify5KrLib4Spec6Malloc4aaddC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8fold_offC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC59OSSVerify5KrLib3Lib4Exec8evt_monoC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib6Malloc<MallocBlocks;AREACH_from03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain=RMalloc_iface<rmalloc_stmtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocHINV9HINV_fromC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec3evtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;malloc_coreC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrl4prunC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc@F_malloc_enframe3rdvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<F_malloc_enf8enf_off0C1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr05C59OSSVerify5KrLib4Spec5STree5erunsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5STree5sbindC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07C59OSSVerify5KrLib4Spec6Malloc8lay_noneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8full_layC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat3N2Z8inj_succC56Stdlib6ZArith4Znat3N2Z6inj_ltI59OSSVerify5KrLib4Spec5Stdio9stdout_st00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain=RMalloc_iface=RMALLOC_STACKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep4RATPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain=RMalloc_iface;RMALLOC_SYMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep=rmalloc_entryC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00C59OSSVerify5KrLib5Plain:RMallocRep6RMLOCKC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4mctx00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc8brkstate00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>MMAP_THRESHOLDC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
Lemma rmembed_strel_follow {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : Malloc.M R1) (t2 : Malloc.M R2) :
  strel RR t1 t2 ->
  forall s (Q1 : R1 -> PState -> machine_state -> Prop) ms,
  implM psegs (membed ATOP t1) s Q1 ms ->
  implM psegs (membed ATOP t2) s
        (fun r2 s' ms' => exists r1 ans, follow t1 ans = Some r1 /\ follow t2 ans = Some r2 /\ RR r1 r2 /\ Q1 r1 s' ms') ms.
Proof.
  induction 1 as [r1 r2 Hr | e k1 k2 Hk IH]; intros s Q1 ms H.
  - cbn [membed] in *. unfold implM, mret in *. cbn in *. eapply evt_mono; [exact H|]. intros ms' H1.
    exists r1, []. cbn. auto.
  - cbn [membed] in *. unfold implM, mbind in *. unfold ebind in *.
    assert (UNR : forall A B (f : exc A -> itree node (exc B)) Qx msx,
              impl psegs (at_node psegs) (ITree.bind _ (Ret Unr) f) Qx msx = impl psegs (at_node psegs) (f Unr) Qx msx) by reflexivity.
    destruct e as [addr|addr len prot flags|addr len|addr len prot|p c h|w].
    5:{ cbn [ev_step] in *. unfold munr in *. cbn [ITree.bind] in *. exact H. }
    5:{ cbn [ev_step] in *. unfold munr in *. cbn [ITree.bind] in *. exact H. }
    all: eapply rimpl_bind_mono; [exact H|]; intros [|[z s']] ms' H1; cbn in H1 |- *; [exact H1|];
         eapply impl_epost_mono; [eapply IH; exact H1|];
         intros [r2' s2] ms2; cbn; intros (r1' & ans & F1 & F2 & HR & HQ);
         exists r1', (z :: ans); cbn; auto.
Qed.

Lemma rraw_malloc_bridge2 : forall st s n (o : mem) Q1 Q ms,
  strip st = ps_m s -> s_atop (ps_m s) = ATOP ->
  rimplT o (malloc st n) s Q1 ms ->
  (forall st' (p : optr) s' ms' (r : option bptr) ans o' cst c,
     Q1 (st', p) s' ms' -> ptr_rel p r ->
     follow (mrun o (malloc st n)) ans = Some (o', (st', p)) ->
     follow (cmalloc (strip st) n) ans = Some (cst, c) ->
     cst = strip st' ->
     r = match c with Some slot => Some (slot, fresh_off cst slot n) | None => None end ->
     Q r (set_m (strip st') s') ms') ->
  implM psegs (raw_malloc n) s Q ms.
Proof.
  intros st s n o Q1 Q ms Hst Hat H HQ. unfold raw_malloc.
  eapply (implM_bind psegs _ _ _ (fun a s1 ms1 => a = s /\ s1 = s /\ ms1 = ms)).
  { apply implM_get. apply evt_done. repeat split; reflexivity. }
  intros s0 s1 ms1 (-> & -> & ->). cbv beta. rewrite Hat.
  eapply (implM_bind psegs _ _ _ (fun r s' ms' => exists st' p ans o', Q1 (st', p) s' ms' /\ MREL (o', (st', p)) r
             /\ follow (mrun o (malloc st n)) ans = Some (o', (st', p)) /\ follow (cmalloc (strip st) n) ans = Some r)).
  { rewrite <- Hst. unfold rimplT in H.
    eapply implM_mono.
    - eapply (rmembed_strel_follow MREL (mrun o (malloc st n)) (cmalloc (strip st) n)); [| exact H].
      unfold mrun. apply malloc_control. apply pans_mem_range.
    - intros [cs c] s' ms' ([o1 [st' p]] & ans & F1 & F2 & HR & H1). cbn in H1.
      exists st', p, ans, o1. auto. }
  intros [cs c] s' ms' (st' & p & ans & o' & H1 & HR & F1 & F2). cbv beta iota.
  eapply (implM_bind psegs _ _ _ (fun _ s2 ms2 => s2 = set_m cs s' /\ ms2 = ms')).
  { apply implM_upd. apply evt_done. split; reflexivity. }
  intros [] s2 ms2 [-> ->]. apply implM_ret. apply evt_done.
  unfold MREL in HR. cbn in HR. destruct HR as [Hs Hp]. subst cs.
  eapply (HQ st' p s' ms' _ ans o' (strip st') c H1); [| exact F1| exact F2| reflexivity| reflexivity].
  destruct p as [pf|], c as [c|]; cbn in Hp |- *; try exact Hp.
Qed.

(* [comment removed for export] *)
Lemma rimplT_silent {R} o (t : Malloc.M R) o' (x : R) s Q ms :
  mrun o t = SRet (o', x) -> rimplT o t s Q ms -> evt psegs (Q x s) ms.
Proof. intros E H. unfold rimplT in H. rewrite E in H. cbn [membed] in H. unfold implM, mret in H. cbn in H. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rheap_pres_of_fp st st' LB lo sp m m' :
  RMFACTS st LB -> rmrep st m -> rmrep st' m' -> mrel st st' ->
  rpres_except (rmalloc_fp st st' lo sp) m m' -> ATOP <= lo -> lo <= sp ->
  rheap_pres LB sp m m'.
Proof.
  intros MF MR MR' REL PE CLO LS a Ha Hc. apply PE; [exact Ha|]. intros Hfp.
  destruct Hc as [Hsp | [[Himg Hns] | (blk & Hin & Hblk)]].
  - destruct (rmalloc_fp_cases st st' lo sp m m' a MR MR' Hfp); atop_facts; lia.
  - destruct (rmalloc_fp_image st st' lo sp m m' a MR MR' Hfp CLO Himg); apply Hns; unfold ralloc_static, RERRNO, RATP, RLIBC, RCTX, RSSP_GUARD, RGOT_SSP in *; lia.
  - destruct (rblock_inside st LB m blk MF MR Hin) as (r & g & idx & Hr & Hk & SL & LOB & HIB & BZ & R4 & RC & RI1).
    atop_facts.
    pose proof MR' as (WF' & _). pose proof WF' as (_ & WR' & DISJ' & _).
    pose proof MR as (WF & _). pose proof WF as (_ & WR & DISJ & _).
    destruct REL as [RREG _ _]. destruct (RREG _ _ Hr) as (r1 & Hr1 & K1 & B1 & L1).
    pose proof (round_up_pg_mono _ _ L1) as RL1.
    pose proof (lr_lo_group r1 ltac:(rewrite K1; exact Hk)) as LR1. pose proof (lr_lo_group r Hk) as LR.
    destruct Hfp as [[H|[H|[H|(rid & rx & Hrx & Hkx & Hax)]]]|[(rid & rx & Hrx & Hn & Hax)|[(g' & b' & r' & i & Hm' & Hr' & Hk' & I0 & TB & Har & Has)|[(b' & gh & r' & Hg' & Hr' & Hk' & Har & Has)|FRESH]]]].
    + lia.
    + rewrite unsigned_lit in H by lia. lia.
    + unfold RCTX in H. lia.
    + (* [comment removed for export] *)
      destruct (N.eq_dec rid (fst (blk_slot blk))) as [->|NE]; [rewrite Hr1 in Hrx; inversion Hrx; subst; congruence|].
      destruct (DISJ' _ _ _ _ Hrx Hr1 NE); lia.
    + (* [comment removed for export] *)
      destruct (N.eq_dec rid (fst (blk_slot blk))) as [->|NE]; [rewrite Hr in Hn; discriminate|].
      pose proof (lr_lo_ge rx). destruct (DISJ' _ _ _ _ Hrx Hr1 NE); lia.
    + (* [comment removed for export] *)
      destruct (N.eq_dec (fst b') (fst (blk_slot blk))) as [E|NE].
      * destruct (mf_free_clear _ _ MF g' b' i Hm' I0 TB) as [_ HB].
        destruct (HB blk Hin (eq_sym E)) as (r'' & Hr'' & DJ). change (s_regions (strip st)) with (s_regions st) in Hr''.
        rewrite Hr' in Hr''. inversion Hr''; subst r''. change (get_meta_rec (strip st) g') with (get_meta_rec st g') in DJ. lia.
      * pose proof (lr_lo_group r' Hk'). destruct (DISJ _ _ _ _ Hr' Hr NE); lia.
    + (* [comment removed for export] *)
      destruct (N.eq_dec (fst b') (fst (blk_slot blk))) as [E|NE].
      * pose proof (mf_hdr_clear _ _ MF b' gh blk r' Hg' Hin (eq_sym E) Hr') as DJ. lia.
      * pose proof (lr_lo_group r' Hk'). destruct (DISJ _ _ _ _ Hr' Hr NE); lia.
    + (* [comment removed for export] *)
      exfalso. pose proof (fresh_live_region st a _ r FRESH Hr) as X. rewrite LR in X. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ruser_chunk st' m' (p : aptr) r n :
  rmrep st' m' -> (s_regions st') !! (fst p) = Some r -> r_kind r = RKGroup ->
  16 <= snd p -> snd p + n <= round_up_pg (r_len r) -> 0 <= n ->
  exists junk, rw_cells psegs m' (conc st' p) [CB (Z.to_nat n) junk].
Proof.
  intros MR Hr Hk P0 PN N0.
  pose proof MR as (WF & _ & _ & _ & _ & SH). destruct (SH (fst p) r Hr Hk) as [HW _].
  pose proof (rregion_addr_facts st' m' (fst p) r MR Hr) as (R4 & _ & RC & RI). atop_facts.
  rewrite (conc_region' st' p r Hr).
  assert (W : wr_at psegs m' (r_base r + snd p) n) by (eapply wr_at_sub; [exact HW| lia| lia]).
  destruct (rwr_at_bytes_exist m' (r_base r + snd p) n W N0 ltac:(lia)) as (bs & L & B).
  exists bs. apply rw_cells_of_bytes; cbn; [| rewrite app_nil_r; exact B| rewrite Nat.add_0_r, Z2Nat.id by lia; exact W].
  split; [exact L| exact I].
Qed.

Section TOPLEVEL.
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis RAS : ralloc_slot_stmt as_pre as_inv.
Hypothesis AS_PRE : forall st LB t sc n, RAREACH st LB -> RMFACTS st LB -> (s_tick st < t)%N -> 0 <= sc < 48 -> 0 <= n < 2^32 ->
  n + 4 <= 16 * size_class sc -> as_pre st (set_tick t st) sc n FUEL.
Hypothesis RBIG : rbig_stmt.

(* [comment removed for export] *)
Definition rmidQ (o : mem) (st : mstate) (LB : list block) (s : PState)
    (ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z)
    (res : mstate * option cptr) (s' : PState) (ms' : machine_state) : Prop :=
  exists st2 r ans o1,
    fst res = strip st2
    /\ snd res = match r with Some (g, idx) => Some (slot_of st2 g idx) | None => None end
    /\ follow (mrun o (malloc_core full_lay (set_tick (N.succ (s_tick st)) st) n)) ans = Some (o1, (st2, r))
    /\ follow (malloc_core lay_none (strip st) n) ans = Some (strip st2, r)
    /\ rcoreQ o o st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo (st2, r) s' ms'.

Theorem rmalloc_spec_proof : rmalloc_stmt.
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo B errv.
  intros HEAP AUXB SB ST CLO LO ERR MI TP HA N. unfold RMALLOC_STACK in LO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR0.
  assert (AUX : rauxv_ok m (bv_unsigned sp)) by (eapply rauxv_ok_weaken; [exact AUXB| atop_facts; lia]).
  destruct HEAP as (st & LB0 & HPERM & Hst & MR & [BLK AR]). rename LB into LBc. rename LB0 into LB.
  pose proof (MallocFacts_inv2.areach_facts_proof _ _ AR) as MF.
  assert (HIN : forall b, In b LBc -> In b LB) by (intros b Hb; eapply Permutation.Permutation_in; [apply Permutation.Permutation_sym; exact HPERM| exact Hb]).
  pose proof (proj2 (brk_link_ps_iff st s) BLK) as BL.
  (* [comment removed for export] *)
  eapply (implM_evt psegs _ _ _ (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                                   F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom psegs))).
  { unfold RMALLOC_SYM. step. apply evt_done. reflexivity. }
  intros ms' ->.
  unfold raw_malloc.
  eapply (implM_bind psegs _ _ _ (fun a sa msa => a = s /\ sa = s /\ msa = _)).
  { apply implM_get. apply evt_done. repeat split; reflexivity. }
  intros s0' s1' ms1 (-> & -> & ->). cbv beta.
  replace (s_atop (ps_m s)) with ATOP by (rewrite <- Hst; symmetry; exact (rregions_wf_atop _ (proj1 MR))).
  eapply (implM_bind psegs _ _ _ (rmidQ m st LB s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo)).
  { rewrite <- Hst. unfold cmalloc.
    eapply (rimplM_membed_sbind _ _ s (fun x s' ms' => exists st2 r ans o1,
              x = (strip st2, r)
              /\ follow (mrun m (malloc_core full_lay (set_tick (N.succ (s_tick st)) st) n)) ans = Some (o1, (st2, r))
              /\ follow (malloc_core lay_none (strip st) n) ans = Some (strip st2, r)
              /\ rcoreQ m m st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo (st2, r) s' ms')).
    - eapply implM_mono.
      + eapply (rmembed_strel_follow CREL).
        * pose proof (malloc_core_ctrl pans_mem pupd_mem n m (set_tick (N.succ (s_tick st)) st) (strip st)) as X.
          unfold mrun. apply X. rewrite strip_set_tick. reflexivity.
        * unfold rimplT in |- *.
          pose proof (rmalloc_core_implT as_pre as_inv RAS AS_PRE RBIG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
                        m st LB s n lo errv (N.succ (s_tick st)) AR MF MR BL AUX ST CLO ltac:(lia) ERR MI TP HA N ltac:(lia)) as X.
          unfold rimplT in X. exact X.
      + intros [cst2 r'] s' ms'' ([o1 [st2 r]] & ans & F1 & F2 & HC & CQ). unfold CREL in HC. cbn in HC, CQ. destruct HC as [Hs Hr]. subst cst2 r'.
        exists st2, r, ans, o1. split; [reflexivity|]. split; [exact F1|]. split; [exact F2| exact CQ].
    - intros [cst2 r'] s' ms'' (st2 & r & ans & o1 & E & F1 & F2 & CQ). inversion E; subst. clear E.
      apply implM_ret. apply evt_done. unfold rmidQ. exists st2, r, ans, o1. cbn [fst snd].
      split; [reflexivity|]. split; [destruct r as [[g idx]|]; reflexivity|]. split; [exact F1|]. split; [exact F2| exact CQ]. }
  intros [cs c] s' ms'' MQ. cbv beta iota.
  destruct MQ as (st2 & r & ans & o1 & Ecs & Ec & F1 & F2 & CQ). cbn [fst snd] in Ecs, Ec. subst cs c.
  pose proof (mrun_fst _ _ _ _ _ F1) as Eo1. subst o1.
  eapply (implM_bind psegs _ _ _ (fun _ sx msx => sx = set_m (strip st2) s' /\ msx = ms'')).
  { apply implM_upd. apply evt_done. split; reflexivity. }
  intros [] sx msx [-> ->]. apply implM_ret.
  (* [comment removed for export] *)
  assert (FC : forall y, (forall ans', follow ((fun '(st1, r0) => ret (strip st1, match r0 with
                                   | Some (g, idx) => Some (slot_of st1 g idx) | None => @None aptr end)) (strip st2, r)) ans' = Some y) ->
               follow (cmalloc (strip st) n) ans = Some y).
  { intros y Hy. unfold cmalloc. eapply follow_sbind; [exact F2| exact Hy]. }
  destruct r as [[g idx]|].
  - (* [comment removed for export] *)
    cbn [rcoreQ] in CQ.
    destruct CQ as (b & rg & m1 & errv1 & u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & s4' & u3 & u4 & u5 & u6 & ra' & -> &
                    MR2 & TK2 & UA2 & MI2 & ST2 & FR2 & ERR2 & AUX2 & PE2 & SPANFP & CTR2 & SO & EXPO & MREL & BL2 & PSM & PSF & PSO).
    pose proof SO as [Hmem Hr Hk B0 B16 IDX LI32 SPAN S16 SMOD S31 N0' NS NOGRP HDR0 Q16 SSL MSL AVr FRr FBr MPL SCr].
    pose proof (rregion_addr_facts st2 m1 (fst b) rg MR2 Hr) as (R4 & RAL & RC & RI1).
    assert (SK : 0 <= get_stride (get_meta_rec st2 g) * idx) by (apply Z.mul_nonneg_nonneg; lia).
    assert (SKL : get_stride (get_meta_rec st2 g) * idx + get_stride (get_meta_rec st2 g) <= get_stride (get_meta_rec st2 g) * (m_last_idx (get_meta_rec st2 g) + 1)).
    { rewrite Z.mul_add_distr_l, Z.mul_1_r. apply Z.add_le_mono_r. apply Z.mul_le_mono_nonneg_l; lia. }
    set (stride := get_stride (get_meta_rec st2 g)) in *.
    set (lo_s := r_base rg + snd b + 16 + stride * idx - 4) in *.
    set (hi_s := r_base rg + snd b + 16 + stride * idx + stride - 4) in *.
    set (Cf := fun a => lo <= a < bv_unsigned sp \/ lo_s <= a < hi_s).
    atop_facts. unfold RMALLOC_STACK in LO.
    pose proof (renf_implT sp gp tp u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 s4' s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 ra' ra s0 s1 s2 s3 s4 F fc m m1 m1 s' st2 g b rg idx n lo Cf
                  MR2 TK2 UA2 MI2 ST2 ltac:(atop_facts; lia) ltac:(lia) FR2 (rpres_except_refl _ _)
                  ltac:(intros a Ha; left; exact Ha) ltac:(intros a Ha; right; subst lo_s hi_s stride; exact Ha) CTR2 SO) as ENF.
    pose proof (mrun_enframe_full m st2 g b idx n (c_mmap_counter (ctx st2)) Hmem) as RUN. cbv zeta in RUN.
    pose proof (rimplT_silent _ _ _ _ _ _ _ RUN ENF) as EV. clear ENF. cbv beta in EV.
    eapply evt_mono; [exact EV|]. clear EV.
    intros msf [_ EP]. unfold renf_post in EP.
    destruct EP as (st' & p & w0 & w1 & w2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & w3 & w4 & w5 & w6 & m' & ER & -> & MI' & ST' & MR' & TK' & PE' & LEAF).
    destruct LEAF as (off & OFF0 & FIT & Ep & Est' & Ep2 & Eoff).
    assert (SE : strip st' = strip st2) by (rewrite Est', strip_havoc, strip_enframe_at; reflexivity).
    pose proof (strip_eq_proj _ _ SE) as (Ec & Er & En & Em & _ & _ & Esl & Es).
    assert (HrS : (s_regions st') !! (fst p) = Some rg) by (rewrite Er, Ep; cbn [fst]; exact Hr).
    assert (EA : conc st' p = r_base rg + snd b + 16 + stride * idx + 16 * off).
    { rewrite (conc_region' st' p rg HrS). rewrite Ep. cbn [snd]. subst stride. lia. }
    set (A := conc st' p) in *.
    (* [comment removed for export] *)
    assert (FF : follow (mrun m (malloc st n)) ans = Some (m, (st', Some p))).
    { unfold malloc, mrun, prun. rewrite (follow_steq _ _ (eruns_sbind _ _ _ _ _) ans).
      eapply follow_sbind; [exact F1|]. intros ans'. cbn [fst snd]. unfold mrun, prun in RUN. rewrite RUN. cbn. rewrite ER. reflexivity. }
    pose proof (FC (strip st2, Some (slot_of st2 g idx)) ltac:(intros ans'; cbn; rewrite strip_strip; reflexivity)) as FC1.
    pose proof (areach_malloc_some st LB n m m ans st' p (strip st2) (slot_of st2 g idx) AR ltac:(lia) FF FC1) as AR'.
    destruct (ruser_chunk st' m' p rg n MR' HrS Hk ltac:(rewrite Ep; cbn [snd]; lia) ltac:(rewrite Ep; cbn [snd]; subst stride; lia) ltac:(lia)) as (ujunk & UCH).
    fold A in UCH.
    unfold rmalloc_post. do 15 eexists. exists m', errv1.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
    split. { eapply rpres_except_rw_cells; [exact PE'| exact ERR2|]. rewrite TP. unfold RATP. rewrite unsigned_lit by lia.
             change (Z.of_nat (cells_size [C4 errv1])) with 4. intros a Ha [X|X]; subst lo_s hi_s.
             - lia.
             - lia. }
    assert (MRELf : mrel st st') by (eapply mrel_trans; [exact MREL|]; apply mrel_same; assumption).
    assert (PEf : rpres_except (rmalloc_fp st st' lo (bv_unsigned sp)) m m').
    { eapply rpres_except_mono.
      + eapply rpres_except_trans; [exact PE2|].
        eapply rpres_except_mono; [exact PE'|]. intros a [X|X]; [left; left; exact X| apply SPANFP; subst lo_s hi_s stride; exact X].
      + intros a Ha. eapply rmalloc_fp_mono; [|exact Ha]. intros rid r1 H1. exists r1. rewrite Er. repeat split; auto; lia. }
    pose proof (rheap_pres_of_fp st st' LB lo (bv_unsigned sp) m m' MF MR MR' MRELf PEf CLO ltac:(lia)) as HPf.
    split. { eapply (rauxv_ok_malloc_fp st st' lo (bv_unsigned sp) m m' m m' B); [exact MR| exact MR'| exact AUXB| exact PEf| exact CLO| exact SB]. }
    split. { eapply (rheap_pres_weaken LB LBc (bv_unsigned sp) (bv_unsigned sp)); [exact HPf| lia| exact HIN]. }
    split; [exact PSF|]. split; [exact PSO|].
    exists A, ujunk.
    split; [reflexivity|].
    split. { unfold rblock_range. atop_facts. rewrite EA.
             split; [lia|]. split; [apply mod16_slot; [exact RAL| exact B16| exact SMOD| lia]|]. subst lo_s hi_s.
             specialize (RI1 ltac:(pose proof (round_up_pg_ge (r_len rg)); lia)). lia. }
    split. { exists st'. eexists. split; [apply Permutation.perm_skip; exact HPERM|]. split; [exact SE|]. split; [exact MR'|]. split.
             - apply (proj1 (brk_link_ps_iff st' _)). cbn. unfold brk_link_ps in *. unfold ctx in *. rewrite Ec. unfold conc, get_region. rewrite Er. exact BL2.
             - exact AR'. }
    split; [exact UCH|].
    (* [comment removed for export] *)
    intros AE. unfold ptr_addr. cbn [ps_m set_m fst snd].
    assert (X0 : rdv pans_mem m st2 (fst b, snd b + (16 + stride * idx) + -3) = 0).
    { apply EXPO. destruct AE as [AE|AE]; [left; exact AE| right].
      pose proof (f_equal s_regions Hst) as E0. rewrite AE in E0. cbn in E0. exact E0. }
    unfold slot_of, slot_start'. rewrite Hmem. cbn [default from_option id]. unfold aadd. cbn [fst snd].
    match goal with |- context [conc (strip st2) ?q] => change (conc (strip st2) q) with (conc st2 q) end.
    rewrite (conc_region' st2 (fst b, snd b + (UNIT + get_stride (get_meta_rec st2 g) * idx)) rg Hr). cbn [snd].
    unfold fresh_off. cbn [s_slots strip].
    replace (snd b + (UNIT + get_stride (get_meta_rec st2 g) * idx)) with (snd b + 16 + stride * idx) by (subst stride; unfold UNIT; lia).
    rewrite SSL. change (c_mmap_counter (s_ctx (strip st2))) with (c_mmap_counter (ctx st2)).
    rewrite EA, Eoff. unfold enf_off0. rewrite X0. cbn [Z.eqb]. subst stride. unfold IB, UNIT.
    change (get_meta_rec (strip st2) g) with (get_meta_rec st2 g). lia.
  - (* [comment removed for export] *)
    cbn [rcoreQ] in CQ.
    destruct CQ as (m1 & errv1 & u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & -> &
                    MR2 & TK2 & MI2 & ST2 & ERR2 & AUX2 & PE2 & MREL & BL2 & PSM & PSF & PSO).
    apply evt_done. unfold rmalloc_post. do 15 eexists. exists m1, errv1.
    pose proof (rheap_pres_of_fp st st2 LB lo (bv_unsigned sp) m m1 MF MR MR2 MREL PE2 CLO ltac:(lia)) as HPf.
    split; [reflexivity|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact ERR2|].
    split. { eapply (rauxv_ok_malloc_fp st st2 lo (bv_unsigned sp) m m1 m m1 B); [exact MR| exact MR2| exact AUXB| exact PE2| exact CLO| exact SB]. }
    split. { eapply (rheap_pres_weaken LB LBc (bv_unsigned sp) (bv_unsigned sp)); [exact HPf| lia| exact HIN]. }
    split; [exact PSF|]. split; [exact PSO|].
    split; [reflexivity|].
    exists st2, LB. split; [exact HPERM|]. split; [reflexivity|]. split; [exact MR2|].
    split.
    + apply (proj1 (brk_link_ps_iff st2 _)). cbn. exact BL2.
    + eapply (areach_malloc_none st LB n m m ans st2 AR ltac:(lia)).
      unfold malloc, mrun, prun. rewrite (follow_steq _ _ (eruns_sbind _ _ _ _ _) ans).
      eapply follow_sbind; [exact F1|]. intros ans'. reflexivity.
Qed.
End TOPLEVEL.

End CANSEC1.
