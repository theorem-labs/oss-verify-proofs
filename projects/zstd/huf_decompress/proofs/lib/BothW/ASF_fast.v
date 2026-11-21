(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (1 recorded proof replaced by written proofs (afree_sec_fast)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF ITreeA StepF.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg AProto ABase ABytes AQConst AKitQ AMalloc_iface ADepot_iface ARep ARepQ ARepQP ALayout AHeapP ARepKit ARepFrame
     AKit AKit2 AModelFacts ASecFacts ASec AFreeModel AFreeRep AFreeGeo AFreeRead F_apoison F_aalloc_s F_aalloc1 F_afree_tail F_afree_icpt
     ASF_kit ASF_read F_afree_arep.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ASF_fast () := "I47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstC35stdpp4base6lookupI59OSSVerify5KrLib4Spec5STree5stree00C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib4Spec8AsanCtrl2AMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl4aptrC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC35stdpp8fin_maps:map_deleteC35stdpp4gmap;gmap_lookupC35stdpp4gmapBgmap_partial_alterC35stdpp4base6deleteK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00I35stdpp4gmap4gmap00C59OSSVerify5KrLib4Spec8AsanCtrl6a_liveC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8AsanCtrl6achunk02C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib4Spec8AsanCtrl<a_qloc_bytesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib4Spec8AsanCtrl=a_qglob_bytesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib5BothW4ASec7ASEC_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<F_afree_arep3AHQC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP7AHEAP_PC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW5ABase6abkind01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW5ABase6ablock01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2leC45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init5Logic2eq00C59OSSVerify5KrLib5BothW=AMalloc_iface4aunwC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC59OSSVerify5KrLib5BothW5ABase6al_topC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C59OSSVerify5KrLib5BothW5ABase4al_UC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powK47Corelib4Init9Datatypes4list01C59OSSVerify5KrLib5BothW5AKitQ9afree_unwC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00I59OSSVerify5KrLib5BothW5ABase6uchain00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic2ex01K47Corelib4Init5Logic2or01K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2or02C59OSSVerify5KrLib4LibA6NodesA8at_nodeAC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=AMalloc_iface:afree_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW7ALayout:alayout_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP4arngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP7ablocksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7ah_fakeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep4AREPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep3awfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7arep_rtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep9ainstanceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7athreadC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep<aslot_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep=ashadow_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7ah_quarC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6ah_secC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8ah_depotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6arelroC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8arep_rt2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8arep_rt3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ8AQUAR_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ASF_kit?freed_block_secC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP7sec_wf1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ASF_kit>sec_wf1_facts'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4ablkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<sec_map_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;needed_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl:is_primaryC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP9sec_clearC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4al_tC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase6al_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout6al_resC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase<al_ptr_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase8al_nodesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase8al_storeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7al_fakeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout7al_dtlsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP=sec_chunks_ofC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;Permutation@Permutation_reflC59OSSVerify5KrLib5BothW7ASF_kit>read_chunk_secC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib4Spec8AsanCtrl6a_nsecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ASec<sec_disjointC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP6sec_mbC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed4shadC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib5BothW4ARepBblock_shadow_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout9alayout_tC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4iclrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4sclrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout;alayout_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout=alayout_depotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ALayout=alayout_stackC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase6al_botC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib5BothW7ALayout8ao_spaceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase<al_space_begC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5AKitQ>afree_unw_sp47C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegI46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC59OSSVerify5KrLib5BothW7ASF_kit:rup8_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl3rupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed5shlenC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega6VarMap1t01C59OSSVerify5KrLib5BothW9ASecFacts9sec_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<rounded_sizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz05K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr04C59OSSVerify5KrLib5BothW9ARepFrame8shad_divC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;a_space_begC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;a_ptr_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7get_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5x_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=size_of_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl@c_allocated_userC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=c_mapped_userC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;c_num_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrlCc_mapped_free_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7xc_freeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8xc_cacheC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7c_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8xb_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5xb_stC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep4xb_nC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7rz_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5xb_b1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6xb_ctxC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8AsanCtrl6achunk01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6x_busyC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW4ARep6bstate01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ;abatch_addrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C59OSSVerify5KrLib5BothW9ARepFrame>slot_in_regionC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indK46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib5BothW4ARep:aslot_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase8ablk_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase8ablk_linC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ABytes<rw_cells_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep<acache_cellsC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC59OSSVerify5KrLib4Spec8AsanCtrl7a_cinitC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC59OSSVerify5KrLib5BothW7ARepKit:junk_splitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7junk_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ARepKit:c8_of_junkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ@aquar_glob_constC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7AQConst9aq_tcacheC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_qlocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ5q_locC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ7aqcacheC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ4q_iaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ6qfirstC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ5qlastC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ8abatchesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7a_qglobC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ6q_globC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ8qcoupledC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ4qnumC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=batches_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6b_sizeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:Forall_appC59OSSVerify5KrLib5BothW6ARepQP@batches_bytes_lbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AFreeRead<st_enq_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:AFreeModel6st_enqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl:chunk_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AFreeRead5ek_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AFreeRead:enq_is_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<F_afree_tail6ek_preC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<F_afree_icpt7ek_sepsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<F_afree_tail8ek_deltaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<F_afree_tail4ek_bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW8ASF_read<read_ek_appSC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib4Spec8AsanCtrl7b_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl8b_chunksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ5qb_ksC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib5BothW9AFreeRead?enq_is_app_specC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:AFreeModel7enq_appC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic9False_indI47Corelib4Init5Logic2or00C47Corelib4Init5Logic5proj2C59OSSVerify5KrLib5BothW8ASF_read<read_ek_newSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ7qb_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW8ASF_read8read_dkSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AFreeRead4g_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<F_afree_tail6dk_preC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<F_afree_icpt7dk_sepsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<F_afree_tail5g_lstC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<F_afree_tail7dk_glstC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl4aretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AFreeRead;bslot_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AFreeRead9bslot_geoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF3rngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AFreeRead<qfirst_casesC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9in_or_appC59OSSVerify5KrLib5BothW9AFreeRead;qlast_casesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7aregionC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8afreearrC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List<nth_error_InC46Stdlib7Sorting;Permutation>Permutation_inC59OSSVerify5KrLib5BothW6AHeapP6sec_msC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List=Forall_forallC59OSSVerify5KrLib5BothW<F_afree_icpt>free_fast_postC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC59OSSVerify5KrLib5BothW9F_aalloc1<allocA_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9F_apoison<poison_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF7rng_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<F_afree_icpt>free_fast_specC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF9evtF_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AProto9implS_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:AFreeModel=afree_fast_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl8set_liveC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C59OSSVerify5KrLib4Spec8AsanCtrl5afreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed6aembedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA6epostFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA5implFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6aslotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep:afreearrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep=aregion_cellsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib3Lib3Arr6u64arrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_nresC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ASec8sec_liveC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffC59OSSVerify5KrLib5BothW4ASec:asec_chunkC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell04C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC59OSSVerify5KrLib5BothW4ARep7fill_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natK59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~I46Stdlib7Sorting;Permutation;Permutation00C46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03C59OSSVerify5KrLib5BothW4ARep5ndistC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep:busy_slotsC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List5NoDup00C59OSSVerify5KrLib4Spec8AsanCtrl9max_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_nextC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2ltK46Stdlib9micromega5Tauto8GFormula06C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep;acache_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8acompactC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr6u32arrC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6mkapp2C59OSSVerify5KrLib5BothW5ARepQ6aintalC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7busy_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ARepQ5qhdrsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW<F_afree_tail8enq_kind01C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List4lastK59OSSVerify5KrLib5BothW<F_afree_tail8enq_kind02C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC59OSSVerify5KrLib5BothW:AFreeModel8st_afterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP4RSECC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF4evtFC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6achunk00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl5Q_MAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_BATCH_CLASSC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00C59OSSVerify5KrLib5BothW5ABase8AFREE_PCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase6UDEPTHC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4BImg5bsegsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AProto6fstepSC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6astate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep5aconc00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7AREQMAXC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02K47Corelib4Init9Datatypes4bool01I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP8SEC_UOFFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7AIMG_HIC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203C59OSSVerify5KrLib4Spec9AsanEmbed6ASHOFFC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201C59OSSVerify5KrLib4Spec8AsanCtrl7K_ALIGNC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_OFFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl:K_USER_MAPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_MAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_MAPC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6aclass00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7aclass0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep5xbusy00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C59OSSVerify5KrLib4Spec8AsanCtrl<K_SPACE_SIZEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_SPACE_EXTRAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase5ATP88C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase4ATSDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep<ASTATS_WORDSC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC59OSSVerify5KrLib5BothW7AQConst9AQ_GCACHEC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6abatch00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7AQConst8AIA_BASEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7Q_CACHEC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW5ARepQ7qbatchc00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW<F_afree_tail8enq_kind00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AFreeRead;dummy_batchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AFreeRead8dummy_qbC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW5ABase7alayout00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF9footprintC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I59OSSVerify5KrLib5BothW5ABase6ablock00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableC59OSSVerify5KrLib5BothW5ABase;AFREE_STACKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase3ATPC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C59OSSVerify5KrLib5BothW5ABase9AFREE_SYMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_NUM_CLASSESC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW5ARepQ5qconc00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00I59OSSVerify5KrLib5BothW4ARep6xclass00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep6bstate00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AFreeRead3K24C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6ARepQP@size_of_class_24C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C59OSSVerify5KrLib5BothW7AQConst6AQ_MAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl5Q_MINC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7AQConst8AQ_MUTEXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7AQConst8AIA_FLAGC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7AQConst8AIA_SIZEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7AQConst<AIA_MAP1_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7AQConst8AIA_MAP1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=Q_BATCH_BYTESC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List6Exists00C59OSSVerify5KrLib4Spec8AsanCtrl7Q_BATCHC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01I59OSSVerify5KrLib5BothW<F_afree_tail3gqd00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7AINITEDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:F_aalloc_s7ARSSLIMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase5ATSDIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase5ATSDKC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00".
Import ListNotations.
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition store_freeS_stmt : Prop :=
  forall (L : alayout) (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : amem) (st : astate) (LB : list ablock) (X : aconc) (Q : qconc) (p : aptr) (mb ms n b1 ctx A lo k24 : Z)
         (stj : word) (chunks : list word),
  let ch := CSec mb ms n in
  let hm := mb + 6128 in
  let st1 := set_live (delete p (a_live st)) st in
  let st2 := st_enq st1 ch in
  let ek := ek_of L st X Q n k24 stj chunks in
  let g := g_of L st Q (ek_delta ek n) in
  alayout_ok L -> arng L RNG st -> AREP (AHQ DI ASEC_of AFK) L st X m -> AQUAR_at L st X Q m -> ablocks L st X LB -> AFK L LB m ->
  (a_live st) !! p = Some ch -> In (HB p A n) LB -> n <= Q_MAX ->
  rw_cells bsegs m hm [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 ctx)] ->
  0 <= b1 < 256 -> Z.land b1 3 = 1 -> 0 <= ctx < 2^31 ->
  (enq_is_app st = false ->
        nth_error (xc_cache (x_cls X K_BATCH_CLASS)) (Z.to_nat (c_count (get_cls st K_BATCH_CLASS) - 1)) = Some k24
     /\ busy_of X K_BATCH_CLASS k24 = None /\ 0 <= k24 < ndist st K_BATCH_CLASS
     /\ ~ In k24 (map qb_slot (q_loc Q ++ q_glob Q))
     /\ junk_at m (abatch_addr L k24) 8192 /\ fill_at m (shad (abatch_addr L k24)) (shlen 8192) 0xfa
     /\ a_cinit st = true /\ 0 < c_count (get_cls st K_BATCH_CLASS)) ->
  (Q_CACHE < a_qloc_bytes st2 -> a_qglob_bytes st2 + a_qloc_bytes st2 <= Q_MAX) ->
  ek_pre ek RNG (al_t L) (Z.of_nat (length (a_qloc st))) (qlast L (q_loc Q)) n hm m ->
  dk_pre ek g RNG (al_t L) (qlast L (q_loc Q)) hm (a_qloc_bytes st + ek_delta ek n) m ->
  ATOP <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  forall ms',
    free_fast_post DI L ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (al_t L) hm n
                   (Z.of_nat (length (a_qloc st))) (qfirst L (q_loc Q)) (qlast L (q_loc Q)) (a_qloc_bytes st) b1 ctx lo m ms' ->
    afree_post CI (AHEAP_P (AHQ DI ASEC_of AFK)) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m (st_after st2) RNG ms'.
Hypothesis STORE : store_freeS_stmt.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem afree_sec_fast : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo : Z) (tr : list Z) (mb ms : Z),
  (* [comment removed for export] *)
  (a_live st) !! p = Some (CSec mb ms n) -> n <= Q_MAX ->
  let st1 := set_live (delete p (a_live st)) st in
  let st2 := st_enq st1 (CSec mb ms n) in
  (enq_app st1 (CSec mb ms n) = None -> 0 < c_count (get_cls st K_BATCH_CLASS)) ->
  (Q_CACHE < a_qloc_bytes st2 -> a_qglob_bytes st2 + a_qloc_bytes st2 <= Q_MAX) ->
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
  intros until ms. intros LIVE NQM st1 st2 CNT NOREC AH HIN MI ST BOT LO TP Ha0 AUNW S0NE RA4 RANE SP16 RSTK.
  assert (UNWX : exists trt, afree_unw RNG lo m (al_top L) sp s0 ra trt /\ In (AFREE_PC :: trt) (al_U L)).
  { destruct AUNW as [(BT & UC & LTR & TRU & RTOP)|(TOPLE & SPLT & TRU)]; [exists (bv_unsigned ra :: tr); split; [left; exists tr; split; [reflexivity|]; split; [exact UC|]; split; [exact LTR|]; split; [exact BT| exact RTOP]| exact TRU] | exists (@nil Z); split; [right; auto| exact TRU]]. }
  destruct UNWX as (trt & FUNW & TRU).
  destruct AH as (ALO & ARNG & [X [AR BL]] & HFK).
  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & HRT2 & AVL & RT3).
  cbn [ah_quar ah_sec ah_depot AHQ] in HQ, HS, HD. destruct HQ as [Q AQ].
  (* [comment removed for export] *)
  destruct (freed_block_sec L st X LB p mb ms n A n WF BL HIN LIVE) as (EA & _ & WFch).
  destruct (sec_wf1_facts' L mb ms n WFch) as (MAL & MLO & MCE & MSE & NB & RZ & MSB & MSAL & NMS & NS0 & SCL & NPR & N6).
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
  pose proof (ablk_lin _ _ MLO) as (ML1 & ML2 & ML3 & ML4). unfold AIMG_HI in ML1.
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
  destruct (read_dkS (AHQ DI ASEC_of AFK) L st X Q m RNG hm ALO ARNG AR AQ HMSEP (ek_b ek (qlast L (q_loc Q))) (ek_delta ek n) ek ED0 EBB
              ltac:(rewrite <- SB1, <- SB2; exact NOREC) eq_refl) as (DK & DS & GL & GLST).
  set (g := g_of L st Q (ek_delta ek n)) in *.
  (* [comment removed for export] *)
  rewrite (afree_fast_eq st p (CSec mb ms n) LIVE ltac:(cbn [chunk_size]; exact NQM) CNT NOREC).
  apply implS_ret.
  (* [comment removed for export] *)
  assert (AB64 : forall q, In q (q_loc Q ++ q_glob Q) -> 0 <= abatch_addr L (qb_slot q) < 2^64).
  { intros q Hq. pose proof (bslot_geo L st X ALO WF (qb_slot q) (bslot_range L st X Q WF CP q Hq)) as (B0 & B1' & _). atop_facts. lia. }
  assert (LF64 : 0 <= qfirst L (q_loc Q) < 2^64).
  { destruct (qfirst_cases L (q_loc Q)) as [-> |(q & Hq & ->)]; [lia| apply AB64; apply in_or_app; left; exact Hq]. }
  assert (LL64 : 0 <= qlast L (q_loc Q) < 2^64).
  { destruct (qlast_cases L (q_loc Q)) as [-> |(q & Hq & ->)]; [lia| apply AB64; apply in_or_app; left; exact Hq]. }
  assert (DELTA : ek_delta ek n <= n + 8192) by (subst ek; unfold ek_of; destruct (enq_is_app st); cbn [ek_delta]; lia).
  (* [comment removed for export] *)
  pose proof ARNG as ARNG0. destruct ARNG0 as (RIMG & RT4 & RCTX & RNO & RSTO & RRI & RFK & RSFK & RDT & RCLS & RPA & RSECS & RPSH).
  assert (IN : In (CSec mb ms n) (sec_chunks_of st)) by (eapply Permutation_in; [exact PO| eapply nth_error_In; exact NTH]).
  pose proof (proj1 (Forall_forall _ _) RSECS _ IN) as [RMB RSH]. cbn [sec_mb sec_ms] in RMB, RSH.
  (* [comment removed for export] *)
  unfold AIMG_HI, AFREE_STACK, UDEPTH, Q_MAX, Q_CACHE, K_HIGH_MEM, AREQMAX in *.
  eapply evtF_mono.
  { eapply (free_fast_spec DI L (q_ia Q) ek g RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m
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
         | |- dk_pre _ _ _ _ _ _ _ _ => exact DK
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
  cbv beta. intros ms' PM.
  (* [comment removed for export] *)
  eapply (STORE L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st LB X Q p mb ms n b1 cx A lo k24 stj chunks).
  all: try lazymatch goal with
       | |- free_fast_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact PM
       | |- alayout_ok _ => exact ALO
       | |- arng _ _ _ => exact ARNG
       | |- AREP _ _ _ _ _ => exact AR
       | |- AQUAR_at _ _ _ _ _ => exact AQ
       | |- ablocks _ _ _ _ => exact BL
       | |- In _ _ => exact HIN
       | |- _ !! _ = _ => exact LIVE
       | |- _ = false -> _ => exact NEWF
       | |- ek_pre _ _ _ _ _ _ _ _ => exact EK
       | |- dk_pre _ _ _ _ _ _ _ _ => exact DK
       | |- rw_cells _ _ _ _ => exact H5
       end.
  all: try assumption.
  all: try (generalize NQM LO BOT STK3; clear; intros; unfold AFREE_STACK, Q_MAX in *; lia).
Qed.
End S.
End CANSEC1.
