(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF ITreeA StepF SysStepF.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AsanW Require Import AImg AProto ABase ABytes ASecFacts AMalloc_iface ADepot_iface APoisonR_iface ARep ALayout AHeapP
     ARepKit ARepFrame ARepExt ARepExt2 AKit AKit2 AKitQ AModelFacts APrimFacts ASec ASecFrame ASecModel ASecStore
     F_apoison F_ammap F_aalloc1 F_amalloc_icpt F_amalloc_preS F_alarge F_acallocS F_amalloc_tailS F_amalloc_arep.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AMallocS () := "I47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstI59OSSVerify5KrLib4Spec5STree5stree00C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib4Spec8AsanCtrl2AMC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5ITree5itree00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl4aptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed6aembedC1?~~~~~~~~~~~~~~~C35stdpp4gmap9gmap_foldC59OSSVerify5KrLib3Lib5ITree5ebindC1?~~~~~~~~~~~~~~~C35stdpp8fin_maps:map_eq_iffC35stdpp4gmap;gmap_finmapI35stdpp8fin_maps6FinMap00C35stdpp8fin_maps7MapFoldC35stdpp8fin_maps:map_insertC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base6LookupC35stdpp4base6InsertC35stdpp4base<PartialAlterC35stdpp4base5MergeC35stdpp4base;RelDecisionI35stdpp4gmap4gmap00I35stdpp9countable9Countable00C35stdpp4base4fmapC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC35stdpp8fin_maps@lookup_insert_eqC35stdpp4gmap;gmap_lookupC35stdpp4gmap:gmap_emptyC35stdpp4gmapBgmap_partial_alterC59OSSVerify5KrLib5AsanW5ABase4ablkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init5Logic2ex00K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init5Logic2ex01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib5AsanW5ABase4sclrC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t01C59OSSVerify5KrLib5AsanW5ABase4iclrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr04C59OSSVerify5KrLib4Spec9AsanEmbed4shadC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6Shadow8shad_divC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201C59OSSVerify5KrLib4Spec9AsanEmbed6ASHOFFC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init5Logic5False00C59OSSVerify5KrLib5AsanW7ALayout4aobjC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06K47Corelib4Init5Logic3and01K47Corelib4Init5Logic4True01C59OSSVerify5KrLib4LibA8SysStepF?implF_from_evtFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA5implFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA6epostFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA=implF_ret_unrC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib5AsanW4ARep7arep_rtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep8arep_rt2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep8arep_rt3C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvK59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW>APoisonR_iface<premap_cellsC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib5AsanW6ABytes<rw_cells_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW>APoisonR_ifaceBpremap_word_212a00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW>APoisonR_ifaceBpremap_word_212a18C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4AImg5asegsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5AsanW5ABase7alayout00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C56Stdlib6ZArith6BinInt1Z3powK59OSSVerify5KrLib3Lib5Cells4cell03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase6al_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9F_apoison<poison_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase4al_tC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase5ATP88C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase4ATSDC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions=bv_wrap_smallC45stdpp9bitvector;definitions@Z_to_bv_unsignedI47Corelib7Numbers7BinNums1N00C59OSSVerify5KrLib5AsanW:F_acallocS?calloc_sec_specC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib5AsanW4ASec7ASEC_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW>F_amalloc_arep2AHC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6AHeapP7AHEAP_PC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW=AMalloc_iface4aunwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW=AMalloc_iface8aresv_okC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5AsanW7ALayout:alayout_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6AHeapP4arngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6AHeapP7ablocksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep7ah_fakeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C59OSSVerify5KrLib5AsanW7ALayout=alayout_stackC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase6al_botC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase6al_topC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase4al_UC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InI47Corelib4Init5Peano2le00K47Corelib4Init5Logic2or01C46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega;ZifyClasses;rew_iff_revK47Corelib4Init5Logic2or02C59OSSVerify5KrLib4LibA6NodesA8at_nodeAC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7amallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW=AMalloc_iface<amalloc_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep4AREPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9ASecFacts9sec_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<rounded_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;needed_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<sec_map_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep3awfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep9ainstanceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep<aslot_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep7ah_quarC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep=ashadow_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep7athreadC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep6ah_secC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep8ah_depotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep6arelroC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep<acache_cellsC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC59OSSVerify5KrLib4Spec8AsanCtrl;a_space_begC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase<al_space_begC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;a_ptr_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase<al_ptr_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7get_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep5x_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=size_of_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl@c_allocated_userC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=c_mapped_userC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;c_num_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrlCc_mapped_free_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep7xc_freeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep8xc_cacheC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7c_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep8xb_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep5xb_stC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep4xb_nC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7rz_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep5xb_b1C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC59OSSVerify5KrLib5AsanW4ARep6xb_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_liveC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8AsanCtrl6achunk01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib5AsanW4ARep6x_busyC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5AsanW4ARep6bstate01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW7ALayout=alayout_spaceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW7ALayout9alayout_tC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW7ALayout;alayout_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW7ALayout=alayout_depotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase8al_nodesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase8al_storeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW7ALayout6ao_ptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW7ALayout8ad_t_ptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW7ALayout5adisjC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW7ALayout:ad_ctx_ptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW7ALayout4ao_tC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW8AMallocS9aobj4_intC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW7ALayout6ao_ctxC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW8AMallocS8aobj_intC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW7ALayout8ao_nodesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW7ALayout8ao_storeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase7al_fakeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW7ALayout7ao_fakeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW7ALayout9ao_res_hiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW7ALayout6al_resC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF3rngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed5shlenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep7aregionC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep8afreearrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF8rng_sub'C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions:bv_modulusK59OSSVerify5KrLib5AsanW4AKit5boxed01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5AsanW4AKit5boxed00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed9adec_mmapC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9ASecModel2KSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW>F_amalloc_preS@malloc_pre_postSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9F_aalloc1<allocA_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW>F_amalloc_preSCmalloc_pre_spec_secC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW8ARepExt24apreC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C59OSSVerify5KrLib5AsanW8ARepExt2>AREP_frame_preC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_nresC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6AHeapP=sec_chunks_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ASec7asec_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ASec8asec_arrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ASec9asec_instC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ASec6aprim0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ASec4ashzC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_nsecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ASec<sec_disjointC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep7junk_atC1?~~~~~~~~~~~~~~~I46Stdlib7Sorting;Permutation;Permutation00C59OSSVerify5KrLib5AsanW6AHeapP6sec_mbC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC47Corelib4Init5Logic5proj2C46Stdlib6ZArith:ZArith_dec;Z_lt_le_decI47Corelib4Init6Specif7sumbool00C59OSSVerify5KrLib5AsanW7ARepKit:junk_splitC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6repeatC47Corelib4Init5Logic9False_indC59OSSVerify5KrLib5AsanW7F_ammap:rmap_cellsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW8AMallocSCpoison_cells_of_rt'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW8F_alarge;large_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9ASecModel6sfreshC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9ASecStore9valid_geoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW8AMallocS8ablk_intC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW8AMallocS=ablk_shad_intC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9ASecStore;valid_clearC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6AHeapP9sec_clearC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW7ALayout7al_dtlsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9ASecStore;valid_hullsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9ASecStore<valid_chunksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9ASecStore:ashz_azeroC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9ARepFrame8azero_cbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW8F_alarge:large_postC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4lnotC59OSSVerify5KrLib4LibA6ITreeA5fp_leC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6AProto5fp_bwC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC59OSSVerify5KrLib5AsanW4ARep7fill_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA9rng_fp_leC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6AProto9rng_mergeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9ASecStore8wt_factsC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega5Tauto8GFormula01C59OSSVerify5KrLib3Lib5Frame6sub_fpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame<munch_weakenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;munch_transC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;wmono_transC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9ASecStore2WTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW7ARepExtEmunch_filter_nonemptyC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6filterC59OSSVerify5KrLib5AsanW9ASecStore5KT_rtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9ASecStore6KT_rt2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9ASecStore6KT_rt3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9ASecStore8KT_relroC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW8AMallocS=premap_of_rt'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9ASecStore6KT_imgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9ARepFrame;cells_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9ASecStore4KT_tC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6AHeapP8hd_frameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW7ALayout<ad_nodes_ptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW7ALayout<ad_store_ptrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC59OSSVerify5KrLib5AsanW<ADepot_iface6ADEPOTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr@u64arr_transportC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW7ALayout6ao_resC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW7ALayout8ao_spaceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW?F_amalloc_tailS<malloc_postSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep8granulesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARepBblock_shadow_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9ARepFrame:junk_frameC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC56Stdlib6ZArith6BinInt1Z3maxC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses8or_morphC56Stdlib6ZArith6BinInt1Z8max_specK46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02K46Stdlib9micromega:ZMicromega;ZArithProof04C46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses5mkrelC59OSSVerify5KrLib5AsanW7ARepKit=junk_of_cellsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Z2Nat2idC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib5Arith8PeanoNat3Nat7add_0_rC56Stdlib6ZArith6BinInt1Z8min_specC56Stdlib6ZArith6BinInt1Z3minC59OSSVerify5KrLib5AsanW7ARepKit:junk_mergeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA;fp_le_transC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9ASecStore9store_secC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9ASecModel6st_secC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_nextC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5AsanW5ABase6abkind01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5AsanW5ABase6ablock01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW=AMalloc_iface:aheap_presC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState6ret_pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase<ablock_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase8ablk_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9ARepFrame9shlen_divC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9ASecModel=st_sec_fieldsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl>chunk_user_begC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7a_cinitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl5a_clsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8AsanCtrl6achunk02C1?~~~~~~~~~~~~~~~C35stdpp4base6insertC35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC59OSSVerify5KrLib4LibA5ExecF9evtF_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6AProto9implS_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW?F_amalloc_tailS?malloc_tail_secC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9ASecModel3KS2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW8AMallocSDZ_to_bv8_bv_unsignedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9ASecModelBsfresh_false_casesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl>mmap_answer_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6is_errC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib3Lib5ITree3Exc3exc01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9ASecModel:KS_unr_badC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltC59OSSVerify5KrLib5AsanW9ASecModel>KS_unr_phantomC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl8set_nsecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9ASecModel7fin_secC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9ASecModel@fin_sec_nocommitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9ASecModelAKS_fresh_nocommitC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node0:C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9ASecModel?KS_fresh_commitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9ASecModelAKS_fresh_overflowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9ASecModel9KS2_otherC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl8set_nresC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9ASecModel>fin_sec_commitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9ASecModel;KS2_grantedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF8evtF_cutC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9ASecModel>amalloc_sec_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl:is_primaryC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5AsanW5ABase6uchain00C1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib5AsanW4ARep6aslotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep:afreearrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep=aregion_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr6u64arrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep:busy_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep5ndistC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List5NoDup00C59OSSVerify5KrLib4Spec8AsanCtrl9max_countC1?~~~~~~~~~~~~~~~C35stdpp4base6lookupC56Stdlib6NArith6BinNat1N2ltC59OSSVerify5KrLib5AsanW6AHeapP4RSECC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5enodeC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C47Corelib5Lists7ListDef6firstnC59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF4evtFC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib5AsanW6AHeapP7sec_wf1C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC59OSSVerify5KrLib5AsanW4ASec8sec_liveC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffC59OSSVerify5KrLib5AsanW4ASec:asec_chunkC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indK46Stdlib9micromega:ZMicromega;ZArithProof03C59OSSVerify5KrLib4Spec8AsanCtrl4aretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7poison0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame7outsideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW9ARepFrame8shad_divC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5FrameBrw_cells_transportC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3subC46Stdlib9micromega;ZifyClasses6mkapp2C59OSSVerify5KrLib4Spec8AsanCtrl9aptr_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7a_qglobC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=a_qglob_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_qlocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<a_qloc_bytesC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N4succC59OSSVerify5KrLib4Spec8AsanCtrl;asec_rangesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl:avoids_allC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib5AsanW5ABase7AREQMAXC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5AsanW4ARep5aconc00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase:AMALLOC_PCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase6UDEPTHC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith4Znat5Nat2Z6inj_leI59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6AProto6fstepSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep<ASTATS_WORDSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<K_SPACE_SIZEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_SPACE_EXTRAC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6aclass00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7aclass0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5AsanW4ARep5xbusy00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6achunk00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7K_ALIGNC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase7AIMG_HIC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C59OSSVerify5KrLib5AsanW5ABase9AINSTANCEC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6astate00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl2PGC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z7inj_addI59OSSVerify5KrLib5AsanW5ABase6ablock00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF9footprintC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase=AMALLOC_STACKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase3ATPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase;AMALLOC_SYMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_NUM_CLASSESC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5AsanW4ARep6xclass00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_OFFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl:K_USER_MAPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_MAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_MAPC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5AsanW4ARep6bstate00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableC59OSSVerify5KrLib4Spec8AsanCtrl=K_BATCH_CLASSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase7AINITEDC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW:F_aalloc_s7ARSSLIMC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase5ATSDIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase5ATSDKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW7ARepExt8nonemptyC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZC45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableI59OSSVerify5KrLib4Spec8AsanCtrl6abatch00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl>K_CHUNKS_BLOCKC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Local Lemma ablk_int : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6344704 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof.
ltac2:(KReplay.run1 (kr_t_AMallocS ()) ["CANSEC1"] "h01Hh14__p1h24__x1h34__x2h44__x3h51kh62H1h77__arithh84__ffh98__varmaph:5__with;2H0h<2hih=2lop;3p;1p;2p;4p;6p;7p;8p-1R0p10000p4p710p8P0p1000QR1p4p710p8P0P1p4p7210p8p1000nR1p4p710p1001ep4p710R0p8P1p4p7210P0p8p1002Cp4p710P0p8p10038p4p710P0p8p1003np4p70R1P0p8P1p1004ep4p7210p8P1p1005_R2p4p710p8P1p10066p4p73110p8P1p1006jR3p4p710p8P1p1007Fp4p710p8p1007_R1p4p73101R4p10089R5p4p73110p8P4p1008RR6p4p73110p8P4p1008np4p710p8P4p1009AR7p4p7201p8P4p1009Sp4p7201p8P4p1009eR8p4p73110p8P4p100:9R9p4p73110p8P4p100:MR:p4p73110p8P4p100:gp4p7201p8P1p4p710R4P5p4p710p8P4P6p4p710p8P4p100;:R6p4p710R5p8P4P6p4p7210R6p8P4P8p4p710p8P4P9p4p710p8P4P:p4p710p8p100;SR:p4p710R4p100;gp4p710p8P4P5p8P4P6p8P4p100<Ep4p73110p8P:p4p741110R:P3p4p73101p8p100<Wp4p7210P0p8p100=Cp4p7<111111111110P0p8p100=ep4p741110R0P1p4p7511100R3p8P3P0p8p100>>p4p741110R0P1p4p76111100R3p8P3P0p8p100>Vp4p741110R0P1p4p771111100R3p8P3P0p8P2p4p741110R2P1p4p7:1111111100R1p8P1P2p8P7p4p7200R7P:p8P:P7p8g00?6j3bTg00?kj1aTg00@ij15Tg00ANj11Tg00B3j1:Tg00BQj1PTg00CGj20Tg00CcR7j2<Tg00D>j2=Tg00D[j2DTg00E8j2ITg00ERj1CTg00F1j2BTg00FZj3HTg00GCj2WTg00Goj1VTg00HOj3UTg00Hoj1TTg00IOj2GTg00Imj4STg00JKj1RTg00Jij1QTg00KTj2ATg00L7j6OTg00L[j1NTg00M=j2ETg00M`j3@Tg00NCj3FTg00Nfj2MTg00OHj2`Tg00Obj2_Tg00PNj3^Tg00Phj3]Tg00QGj4\Tg00R9j4KTg00RSj4ZTg00S>j7[Tg00Sbj7YTg00TFj8XTf0R:#5#5#5#5p=7%5:#5p=L%1:#1p=?%1:#1#1#1p=8%1:#1#1#1#1#1#1#1p=3f2R2f1R1'0/<:p=21<1:,<2p=>g00TjR0/E:p=9P2g00UHR3g00UgR4P4g00VGR6P0P1g00VgP:CZg00WNF[p=4P2P3P4P4P6P1P:FYp=6f3R5P3P4P4P6P2P1P:GXp=;101:,<2p=Jp,2rcR9?b1:%a9g00WnR8#5R;#5#7#7#7R<#1#5#LR=#5#7#1#?#8#3#3#:R>%P9R9'0R?%5<#7#7#1#?#8#3#3#:R<,09R@'<g00XS%58#1#8#L#1#5#8#3#:RA/05RB%8=#3#:R=,02RC'<%18RD#8#3RE#7#7#7#7#1#?#8#3#:RF1029725g00XmRG%:8RH,0:72:RIf5RJ,0ARK1=F:RLf4RM%1E#?#3#3#3#3#3#3#:RE,=:,D=RN10M9RO3272J3>X50,I0P1105=92AMP7PK10M=f7RK,0ARPf6RQ10Q972N92LK5>IX50,I0RQP:10K=P0f:RR,0Af9RS10S972N92LR5>IX50RIPGp-0RLg00YKRNg00Z7RT#C#CRU#C,B01B0U1B0T5H05H0g00ZV'W%VN3URT%TNRNP01G02P11G05CSRU%R0RV%Q0RW%9>1A0;R;54WPWP3P4P4P6PJEOR356W%N4R4PW1A0DRD%9=RX54WP4PW%9A1A08R854WRYP41E0GRZ=4WZ%9HR[94WZR\56W%9FR]=@0Z=4W8%9ER^9@0Z9F0X94WDA4WD;RZ56W56W96WY56WC;C;C;1MW6R6P:P2g00[BR_g00[bR`'`1_:2=^_`dA]0G1C\R`b8b9b:X20X30X40W1A2>2510A210GHRA92GG1=FG1=GE,D=10MJRG52M7257>B[\C[^20^30^40^1LP:P@P9PSPRPKP1P2O7b7CKW6X0PP1P:O2n2001000010121000000W0P:O1105992FMP710FJPOPQP:10FK10K9P0PIPHPTPNPUPVPW%9<94W;96W3P4PWPZP4PWA4W]8P4A4W[[96W\A@0][=4W8A@0[^9F0X94WD=6WZ56W96WY56WC;C;C;P6P`b8b9b:X20X30X40X1LAJ52<102510F2AJAHH1=FH1=HE,D==2MG7257>B[[[^20^30^40^1LP:P?P9PSPRPKP1P2O7b7CKW6W0P1P:O2n2001000010121000000W0P:O1n200100001021100011000b;W0X<0X=0o"). Qed.
Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_AMallocS ()) ["CANSEC1"] "h04__x1h14__x2h21Hh37__arithh44__ffh58__varmaph65__with71kh82G1h92G2h:1ah;1np;2p;1p;4p;3p;7p;8g00\Bj2WTg00CGj20Tg00D[j22Tg00ANj11Tg00B3j1;Tg00@ij16Tg00Ccj23Tg00D>j29Tg00E8j2VTg00Goj1UTg00Hoj1TTg00IOj2PTg00]7j1OTg00Imj4NTg00JKj1LTg00Jij1KTg00M=j2:Tg00KTj2ATg00L[j1ITg00NCj3>Tg00M`j3=Tg00Nfj2HTg00OHj2JTg00Obj2GTg00PNj3FTg00Phj3MTg00QGj4ETg00R9j4CTg00RSj4QTg00S>j7DTg00Sbj7RTg00TFj8STf0R0#1#1#1#1p=?%10#1#1#1#1#1#1#1p=5%10#1p=B%60#6p=@%60#6#6#6p=7f2R1g00UHR2g00UgR3P3g00VGR4g00TjR5f1R6g00VgP0CQg00WNFDp=4P1P2P3P3P4P6P0FRp=8f3R7P2P3P3P4P1P6P0GSp=<1W60g00XmR2/011271g00WnR8#1R9#?#5R:#1#B#5#5#5#5#5#5#;R;'0g00XSf4R</27%@8#7#7#7#1#6#@#?#5#;R='0%7:#7#7#7#1#B#?#5#;R:/0<1020R>%;8R?,00'3R@f6RAf5RB'2190;,2=RC'019:0RD/0A'3'3X75,V5P112B</0=P5f7RE/2A/0C10DE'3,3@X75R@P2g00YKRD#URC%TDRDP51P51P6%O5CNRF%L5RG%K5RH1:52RI1A58R854H%I3R3PH1A599>58R91:5=RJ54HP3A4HII1:5?RK94HIRL58H1:5;RM9=5I9>5J94H91:5:RN==5I=4H858H58HC<C<1HH4R4P0P1g00[BRIg00[bRO'J1G01=FIOdAM526CEROb4b5b6X05X151261/0=1022102?RI'31217RP192;,2='019:2/01'3'3[\>^05^15P0PAPEP<P6O4b3CCW2P0O110:BP5P@P?PCPDPFPGPHA4H9MP3PHA4HN8P3A4HKK98HLA=5KM9>5J94H9A=5NK=4H858H58HC<C<P4POb4b5b6X05X151206/0;10:610??,3I19?;,2=,0P19:?/01'3'3[[^05^15P0PAPEP7P6O4b3CCW2P0O1n200100001021100011000W9W8W2X;5X:5o"). Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6344704 * k <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_AMallocS ()) ["CANSEC1"] "h04__x1h14__x2h22H0h31kh41Hh57__arithh64__ffh78__varmaph85__with92G2h:1ah;1np;2p;1p;4p;3p;7p;8g00]Uj2YTg00ANj11Tg00B3j1;Tg00CGj20Tg00@ij1>Tg00XSR0j2DTg00D[j23Tg00D>j27Tg00E8j2ETg00Goj1VTg00Hoj1UTg00IOj2TTg00]7j1RTg00Imj4QTg00JKj1PTg00Jij1NTg00KTj2BTg00NCj3@Tg00M=j28Tg00L[j1KTg00M`j3=Tg00Nfj2JTg00OHj2ITg00Obj2HTg00PNj3MTg00Phj3GTg00QGj4OTg00R9j4CTg00CcR1j2?Tg00RSj4FTg00S>j7STg00Sbj7XTg00TFj8WTf0R2#1#1p=L%12#1#1#1#1#1#1#1p=5%12#1#1#1p=Af2R3f1R4'3/02p=:1034/?2p=61?42,?3p=<P3g00UHR5g00UgR6P6g00VGR7g00TjR8P4g00VgP2CFg00WNFSp=2P3P5P6P6P7P4P2FXp=4f3R9P5P6P6P7P3P4P2GWp=91Y42g00WnR5#1R:#1#L#5R;#AR<#5#5#5#5#5#5#;R=9:34P1%;;R;/09R1%;<R<9:93%>5#1#A#>#>#1#>#A#5#;R>/09'Dg00XmR?%;5R@,02762RAf5RB,0;RCf4RD,3B172=,3<RE17>2RF/0B363<X38,E8P4f6RG?:B<10>G'DP0f7R0?:G<10>0f9RG,0;f8RB,3G10FG76E5<AX38,E8P2A:B0<P8f:RH,0;13HG10FH76E5<AX38RAP?g00YKRE#VRF%UEREP81T83P4%R8CQRI%P8RJ%N8RK1B85R51B8:5@8R:188<RL52K%K6R6PK188;=2K5RMP6188?RN=2KN188@RO92KNRP54K188=RQ9=8N9@8L92K:188>RR==8N=2K554K94KM54KC9C91JK7R7P2P3g00[BRNg00[bRS'I1H23=MNSdAG8?4CORSb6b7b8X08X181324RN/0<10;410?@RT96??10;3R;133917?=,3<17>?/03363<[[^08^18P2PGPHP4PDO4b5CCW2P2O110>BP8PAP@PFPEPIPJPKA2K:QP6PKA2KR5P6PKPMP6A2KOO94KPA=8OQ9@8L92K:A=8RO=2K554K94KM54KC9C9C9P7PSb6b7b8X08X1810N=10>410@@,?T139D17@=,3<17>@/09367<1\;[[^08^18P2PGPHP0P4PDO5b5CCW2P2O1n200100000021100011000W2X4CP4P2O2n2001000000121000000W9W4X;8X:8o"). Qed.
(* [comment removed for export] *)
Local Lemma ablk_shad_int : forall a ms, ablk a (a + ms) -> a mod 8 = 0 -> 0 <= ms ->
  exists k, 0 <= k <= 1 /\ a + ms <= shad a + k * 18446744073709551616 /\ shad a + ms / 8 + 8 <= a + (1 - k) * 18446744073709551616
            /\ 2148227584 <= shad a /\ shad a + ms / 8 <= 17594333495296.
Proof.
ltac2:(KReplay.run1 (kr_t_AMallocS ()) ["CANSEC1"] "h01Hh11kh24__p1h34__x1h44__x2h54__x3h64__x4h74__x5h84__x6h92H1h:3H10h;3H11h<2H2h=2H3h>2H4h?2H5h@2H6hA2H7hB2H8hC2H9hD7__arithhE4__ffhF4__p2hG8__varmaphH5__withI4__x7hJ1qhK2q0hL1rhM2r0hN2A8hO2H0hP2M0hQ1ahR2mshS1zp%0p&0p;2p;3p;1p;4p;6p;7p;8g00D[j20Tg00?6k30<Tg00ANj11Tg00B3j1ZTg00^Jj29Tg00?kj1{Tg00@ij13Tg00BQk10;Tg00CGj22Tg00^jj27Tg00D>j2>Tg00_Gj2\Tg00E8j2UTg00_dj2jTg00`Ej1qTg00`^j2eTg00aEj2FTg00CcR0j2<Tg00aaj2dTg00bHj2cTg00bnj2bTg00ERj1ITg00cTj2nTg00d=j3YTg00F1j2mTg00dfk10:Tg00eDk209Tg00eej3XTg00Gok108Tg00Hok105Tg00IOj2WTg00]7k104Tg00JKk103Tg00Jik102Tg00M=j2iTg00RSj4^Tg00L[k100Tg00fNj6~Tg00KTj2gTg00g2j3fTg00Nfj2zTg00OHj2yTg00Obj2xTg00PNj3[Tg00Phj3wTg00QGj4vTg00R9j4hTg00gUj1uTg00hMj1|Tg001ej6}Tg00FZj3`Tg00GCj2tTg00HOk301Tg00Imj4sTg00S>j7lTg00L7j6rTg00Sbk706Tg00TFj8aTg00M`k307Tg00NCj3pTg00TjR1f0R2g00XmR33[p=N1232p=K%32#3#3#3p=;%32#3p=o%12#1#1#1#1#1#1#1p=6%12#1#1#1#1#1#1#Zp=Af2R4f1R5/22'<p=B%12#1p=k%12#1#1#1p=V1052,24p=]%32#1p=Gf3R6/241252'<p=?1245/<2p=@1<52,<4p=E1045/22p=MA[152p=T1m12p=HA`152p=DA`1529`14p=:g00YKR7g00ZV,t5<012p=CP1P4P5P2Csp=R1i12p==P5g00UHR8g00UgR9P9g00VGR:P2g00WNR;Flp=J1g12p=SP4P8P9P9P:P1P5g00VgP2C^P;Flp=4P5P8P9P9P:P2Erp=_P4P8P9P9P:P5P2K06p=5P6P8P9P9P:P4P5P2Gap=LP1P5g00iFP2C^p=PB07152p=QAp152p=8f6R;P8P9P9P:f5R<f4R=P6P8P9P9P:P4P5P2GaGap=Op,2rcR>105280<5g00WnR?#1R@#1RA#1RB#ZRC,94#N%K4%{>%3?RD#3RE#;#;#;RF#1#3#oRG#3#;#6#6#A&0;>R>'2S00%3FRF#;#;#6#6#ARH7B>P1g00imRI17<CRJ'0%K2%Z?RK7B2RLf7RM/0;RN%6BRB#kRO#V#6#6#6#6#6#ARP,>2RQ7]517;CRR,05RS/0C1\K2/>PRT,0MRU%GB#3#G#G#3#G#3#k#ARBP5PS%;O#;#;#;#6#AROC?3@3EX11,U1XS1g00XS%G?#V#3#G#G#V#ARS/2<RV10<=RW%1G#V#ARG3BPOP<PWP>C?%6F#ARF17MC'0RW=]NQ10WRRX/0CPBPWPXPOC?7@U5ELX11,U1P6PSP;10;<RUPGC?P012SM12NGf9RXf8RW17XC,0FRY/0Q3M17WC,0YRZ/0C10XTPBPYPZPOC?3@5ELX11,U1S01P212SXf:RZ/0XRY/2GP1f<R[f;R\17[CR],0FR^/0Q3M17\C,0^R_/0C10[TPBP^P_POC?3@5ELX11S02P31j\CS03%NCR_#qR^1>C]19[C'0,T[[S041e[CS051F3CR[f=R]/9CR`#K1F`C'<[S061d]CS071FC3R]f>R`/9CRa,FC?Ba3[S081c`CS09f?Ra/7C#N\_S0:1baCS0;f@Rb/9C/Tb\_S0<17bCS0=P1fARc/9CS0>P11jcCS0?fBRc17cC,>C19cC'0'T\^S0@1ecCS0AfCRc/9CR^#K1F^C'<\[S0B1dcCS0CfDRc/9CR^,FC?B^3\]S0D1ccCS0EfERc/7C#N\_S0F1bcCS0GfFR]/9C/T]\_S0H17]CS0IP1fGR]/9CS0JP1p-0R^g00Z7Rd#IRe#IRf#IRg#IRh#HRi%HgRg1n1CRj%HfRf5Y1%HeRe1m1d9Y1jRd'DRk3:Rl'D%IhRh#IRm#HRn&0:?-091Ro%HhRh5X1RpAX1oiRqAX1ogRrAY1je/Dd7:fRe'D3:1DgkRk,DiA:rfdRr,Dq9:np&087Rq'C'C'C'C&057S0K1W1=R7&0417R41W1<Rd1W1;Rf7R67R5&031S0L&021RgPgP11i13Rsg00jg%=CRtC^,JgS0M&009Ru%SERE94gsRv1_gW55gCLPuPgPgPgP8P9P9P:1Pts,JgE~R9Pu%S@R8%SARA,Qt/8E'P,JgCLS0NPuPgPgP9Pu1g1?R?%SDRE,QtRw%3@#SR@'8'P,JgCLPuPg1P@s,JgPuPg18?8R8%=G54gPuPg%=S=4g?PuA4gss%=KRS94gsRx55g%=F/8ERE%=PRy,Qs'894g818EARA/8tRtAf1Ss/Qy,8?54g%=B=4gE%=ORz94gA55gRA55g55g55gFOFOFO1zg:R:P2P4g00[BR{g00[bR|'y1x24=[{|dAw135CvR|bEbGbHX31X41X51X61X71X81W2%K;/<M\[g00kN\_R_1>C<R{/0M,T6[R}%NMAM=<G%KKRG9@3310FWR=1>3P'09M;M10=XR~/0C1\K3/>P,0;PBP=P~POC?3@3E\V[[\}[[^31^41^51^61^71^81^2^P21F5CR}P5PWP4PXfIRVfJR~P;PMP`P]PaPbO=bDbMbKb;b:bCbBbAbLbJb@b?b>b=b<ChW9W0P5P2O2n2001000010121000000W0P2O112O;R=?BU>P012OM12N>Q01P212OX12Y>P1Q02PKQ03Q04Q05Q06Q07Q08Q09Q0:Q0;Q0<Q0=P1Q0>P1Q0?Q0@Q0AQ0BQ0CQ0DQ0EQ0FQ0GQ0HQ0IP1Q0JP1%Im#HRmAX1onRoA:pir3:1DhkA:pie9:moAY1ji=:hl/Cq'C'C'CQ0KAR74f1W1M9Rd67R5Q0LPgPgQ0MPu1_gX95gvCLPuPgQ0NPuPgPgP9Pu%1D#SRD,8w,P?,JgCLPuPg1_gZ%=H94g@55gPuPg1PDs,JgPuPgA4g8@PuPgA4gz?PuA4gSS95gx1QSy,8E94g8Af1SS/Qy,8?94gt=5gA55g55gCLFOFOFOP:P|bEbGbHX31X41X51X61X71X81XI1X2^XF^%KM/<W\[10{W,T6\_R_AB\MH%NXAM<;XABGKK10FXRF1>KP'09MMW10FZRZ/0C1\KK/>P,0MPBPFPZPOC?3@3E\=[[[\_[[^31^41^51^61^71^81^I1^2^^F^P2Q00P}P5PWP>P4PXPVP~P;PMP`PcP]PaPbO@bDbMbKb;b:bCbBbAbLbJb@b?b>b=b<ChW9W0P5P2O2n2001000010121000000W0P2O1n20010000102110001100010IRRR=]UQ10RJRJ/0C10;TPBPRPJPOC?3@5ELX11,U1e%u<%|<E}bOWPWNW0XR1XQ1o"). Qed.
Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
  6344704 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_AMallocS ()) ["CANSEC1"] "h04__x1h14__x2h21Hh31kh47__arithh54__ffh68__varmaph75__with84__x3h94__p1h:2H0h;2H1h<3H10h=2H2h>2H3h?2H4h@2H5hA2H6hB2H7hC2H8hD2H9hE2HnhF6__sat6hG1ahH1np;3p;1p;2p;4p;7p;6p;8g00kkj3yTg00ANj11Tg00B3j1:Tg00CGj20Tg00?kj1oTg00@ij16Tg00BQj1_Tg00^Jj2ATg00D[j22Tg00D>j2?Tg00CcR0j28Tg00lbj2dTg00_dj2cTg00`Ej1bTg00^jj2STg00PNj3LTg00`^j2aTg00aEj2KTg00aaj2`Tg00bHj2^Tg00bnj2]Tg00mSj2\Tg00ERj1JTg00F1j2DTg00FZj3OTg00GCj2[Tg00Goj1xTg00HOj3ZTg00Hoj1wTg00]7j1vTg00IOj2YTg00Imj4HTg00JKj1uTg00Jij1tTg00KTj2PTg00L[j1rTg00NCj3MTg00nOj7qTg00Nfj2pTg00OHj2nTg00Obj2mTg00Phj3lTg00QGj4kTg00M=j2VTg00M`j3NTg00R9j4WTg00L7j6iTg00o3j4UTg00XSR1j2XTg00E8j2hTg00RSj4gTg00S>j7fTg00Sbj7sTg00TFj8eTf0R2#1#1p=E%12#1#1#1#1#1#1#1p=5%62#6#6#6p=9%62#6p=T%12#1#1#1p=@f2R3f1R4/02'8p=Fg00TjR5g00XmR67L2p=Qf3R7/031042'Xp=41842,83p=R1034/82,87p=<1062p=B1234/02p=G1042,83,87p=I1h52p=C1034/82p=71V52p=>P3g00UHR8g00UgR9P9g00VGR:P5P4g00VgP2Cgg00WNFfp=3P3P8P9P9P:P4P2Fsp==P7P8P9P9P:P3P4P2Gep=;1X42,83p=jp,2rcR;?y42g00WnR<#1R=#1R>#E#5R?#1R@#1#ERA#:RB/04RC%o;%6<RD#6#9#9#9RE#1#6#TRF#6#9#1#E#@#5#5#:%_;R;'0RG%6E#9#9#1#E#@#5#5#:RE7F;P0f4RH%:?R?'A#Q10?HRI12H7RJP;PJ%@F#5#:RF%9@#9#9#9#1#E#@#5#:R@PHC4PJPB%6<#1#@#T#1#6#@#5#:RJPHC47RIC<f5RI12IH%B2%:<RK7F2RLf6RM%5A#5#5#5#5#5#:RA,?2,2FRN7GI1?@2ROPMCIX35#C77;57JP31AM?#Qf7RP,0?RQ12PMRRP;PRPFP@PPC4PRPBPJPPC47RQC<P0f8RQ,0?RR12QPRPPPPFP@PQC4PPPBPJPQC47RR77;f9RR12RQPLf:RP?GRNPOPPCIX35#C77;57JP210?Pf;RR/2PRPPPPFP@PRC4P?PRPPPBPJPRC4C<77;P0f<RP/2RRR/0;PRPFP@PPC4P?PPPRPBPJPPC4C<f=RR12RPPLf>RS/2RRRPN10OSC<X35#C77;57JP210R;f?RR/2SRSPFP@PRC4P?PRPSPBPJPRC4C<P0f@R0/2RRRPFP@P0C4PRPBPJP0C497?0fARR12R0PLfBR0/2RRSPN10O0C<X35#C77;57JP2PSPFP@P0C4fCRS12S0PBPJPSC457?fDR0,0J120SRT/0;RUPLfERV/20RWPN10OVC<X35#CRX'81d0?%B0%B?fFRY/A?RZ#B[[1cV?%Q?R[#b1SY?,??/2Z9L5Y[1aY?1K6?fGRZ/A?R\#B1K\?'8[1`Z?1K?6fHR\/A?R],K??F]6[1^\?fIR\/S?#Q\[1]\?fJR]/A?=L5]\[g00oN1\]?R]eP]g00YKR]g00Z7R[#JR^#JR_#JR`#J,D51D5^R^1D5_5O55O5g00ZVR_'[%x]Ra3Z%w]RbP5%v5RcP41Y53RdCH%u5Re%t5Rf%>BRg1P5DRD53f%r9RhPf%>?1P5<R<53fRiPfP8P9P9P:AM5<D=3fg%>J=3f<RgFq5=fPhPfPiPhPgC;C;C;1pf:RgP2P3g00[BRjg00[bRk'n1m23=LjkdAl564CkRkb5b6b7X05X1510?4Rj1243Rl/0B10J43j10?310J7[[\C^05^15P2fKRCfLP\PQPRO5b410JCeb<bDbCbBbAb2bFPUPXPaPbP5PdP41Y57RXCHPePf1P5=9M5<R==3fDRDPhPDC;PgPkb5b6b7X05X15X851224RD/0310l7[^05^15^85P2P;P0PVPMO4b4P110TF10@0PLAGYVNPOPYCIX35#CP410WFP5PLAGZYNPOPZCIX35ROP6PaPbP5PdP4PcCHPePf%>FRd93f=PhPfPiPh1V56Ri=3fi%>KRN93fiRL5=f%>ARW9N5i9M5d93f=%>@R0=N5i=3f<5=f5=fC;C;PgPkb5b6b7X05X1510DF%BKRD97661237Ri1?6A,2F1?@6/03C<\j[^05^15P2PYPZP4PPO4b4CWW2P2O110@VP5POPKp-0RO1D5`1D5[9O5^5O5/[_=Z]aPbP5P5PXP3PcCHP4PcCHPePfPfP8P9P9P:PIEi1P5>R>%>E53f5=fPhPfA3f0<PhPfA3f=>PhA3fNN9=fLAN5NW9M5d93f=AN50N=3f<5=f5=fC;C;C;PgPkb5b6b7X05X15X85W9AF73E10@410iHAFDKK1?KA,2F9G7H1?@KP7CI[[[^05^15^85^9OP2PGP;PYPZPSP4PQO7b4CWW2P2O1n200100001021100011000CUCUW@W?P4P2O2n2001000010121000000W2W>P4P2O2n2001000010121000000W2W=P4P2O2n2011000010121000000W2W;P4P2O2n2011000010121000000b:WEW2XH5XG5o"). Qed.
Local Lemma aobj4_int : forall a, aobj a 4096 ->
  4096 <= a /\ a + 4096 <= ATOP
  /\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
  /\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6344704 * j <= a).
Proof.
  intros a H. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. destruct H as (H1 & H2 & H3 & H4 & H5).
  split; [lia|]. split; [lia|]. split; [destruct H4; [exists 0 | exists 1]; lia | destruct H5 as [_ [H5|H5]]; [exists 0 | exists 1]; lia].
Qed.
(* [comment removed for export] *)
Local Ltac dlia := repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Lemma premap_of_rt' : forall L m, arep_rt L m -> arep_rt2 m -> arep_rt3 m -> premap_cells m.
Proof.
  intros L m RT RT2 RT3.
  destruct RT3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R11 & R12 & R13 & R14 & R15 & R16 & R17).
  destruct RT2 as (_ & Q2 & _).
  pose proof R11 as R11a. rw_split R11a 1%nat R11h R11t.
  unfold premap_cells. split; [exact R11h|]. split; [exact R13|]. split; [exact Q2|].
  split; [apply premap_word_212a00; exact R14|]. split; [apply premap_word_212a18; exact R15|]. split; [exact R16| exact R17].
Qed.
Lemma poison_cells_of_rt' : forall L m, arep_rt L m -> poison_cells m.
Proof.
  intros L m RT.
  destruct RT as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R18
                  & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27 & R28).
  unfold poison_cells. repeat lazymatch goal with |- _ /\ _ => split end; assumption.
Qed.

Lemma Z_to_bv8_bv_unsigned : forall (b : byte), Z_to_bv 8 (bv_unsigned b) = b.
Proof.
ltac2:(KReplay.run1 (kr_t_AMallocS ()) ["CANSEC1"] "h02b1h12b2h21nh31Hh41bh51zp;1p;3p;2p;6g00ANj13Tg013Wj1;Tg0145j11Tg00PNj32Tg01L0j20Tg01LZj3:Tg017aj29Tg01M>j25Tg01Mdj26Tg01NWj37Tg01OCj24Tg001ej68Tg00Wn#3#3#3#;R0#1g01P2R1f0R2#1R3f1R4#1R5g00Ccf2R6#1?242g00TjR7f3R8/06108432R9[10641062527%18?264[R:f4#1?286\9A:642P2n2001000000120000000W1W0W2P:^15^03^21P2P01004R1,90R3P4P7150110069272X571604970110031401E8O4b3W4o"). Qed.

Section S.
Variable DI : ADepotIface.
Variables (AQ : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Hypothesis HL : ahole_laws (AH DI AQ ASEC_of AFK).
Hypothesis PR : poison_remap_stmt.
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI) CI.
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.

Theorem amalloc_sec : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (n lo : Z) (tr : list Z) (RESV : list (Z * Z)),
  is_primary n = false ->
  (* [comment removed for export] *)
  AHEAP_P (AH DI AQ ASEC_of AFK) L RNG st LB m ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AMALLOC_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 n -> 1 <= n <= AREQMAX ->
  aunw m L RNG lo AMALLOC_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AMALLOC_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  aresv_ok L RESV ->
  implS asegs RNG (aembed ATOP (amalloc ATOP RESV st n))
        (epostF (amalloc_post CI (AHEAP_P (AH DI AQ ASEC_of AFK)) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AMALLOC_SYM) fc None m (seg_rom asegs)).
Proof.
  intros until RESV. intros PRIM AHP MI ST BOT LO TP Ha0 NR AUNW S0NE RA4 RANE SP16 RSTK ROK.
  assert (N : 1 <= n <= AREQMAX) by exact NR.
  assert (EXARM : exists trc,
      ((bv_unsigned sp + 16 < al_top L /\ uchain m (al_top L) AMALLOC_PC (bv_unsigned sp) (bv_unsigned s0) 28%nat tr /\ (length tr <= 28)%nat /\ trc = bv_unsigned ra :: tr
        /\ rng RNG lo (al_top L - lo))
       \/ (al_top L <= bv_unsigned sp + 16 /\ bv_unsigned sp < 2^47 /\ trc = []))
      /\ In (AMALLOC_PC :: trc) (al_U L) /\ (length trc <= 29)%nat /\ bv_unsigned sp < 2^47).
  { pose proof (alayout_stack L (proj1 AHP)) as (K1 & K2 & K3).
    destruct AUNW as [(T1 & U1 & L1 & I1 & R1)|(T1 & T2 & I1)].
    - exists (bv_unsigned ra :: tr). split; [left; split; [exact T1|]; split; [exact U1|]; split; [exact L1|]; split; [reflexivity| exact R1]|].
      split; [exact I1|]. split; [cbn [length]; clear -L1; lia | clear -T1 K2; lia].
    - exists (@nil Z). split; [right; split; [exact T1|]; split; [exact T2| reflexivity]|]. split; [exact I1|]. split; [cbn [length]; clear; lia | exact T2]. }
  destruct EXARM as (trc & ARM & TRU & LTRC & SP47).
  destruct AHP as (ALO & ARNG & [X [AR BL]] & HFK).
  pose proof (sec_facts n N PRIM) as (NB & RZ & RSE & RSR & RSM & NSE & MSE & MSR & MSM & MSB).
  set (ms := sec_map_size n) in *.
  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  destruct THR as (T0 & T40 & CACHES & CSTATS & [sj [STATS LSJ]] & UNW).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof (alayout_depot L ALO) as (DL1 & DL2 & DL3 & DL4 & DL5 & DL6 & DL7 & DL8 & DL9 & DL10).
  pose proof (alayout_stack L ALO) as (STK1 & STK2 & STK3).
  pose proof (ao_ptr L ALO) as OP. unfold aobj in OP. pose proof (ad_t_ptr L ALO) as D_t_p. pose proof (ad_ctx_ptr L ALO) as D_c_p. unfold adisj in D_t_p, D_c_p.
  pose proof (aobj4_int _ (ao_t L ALO)) as (_ & _ & (kT & TBND & TBNDa & TBNDb) & (jT & TIMG & TIMGa & TIMGb)).
  pose proof (aobj_int _ _ (ao_ctx L ALO) ltac:(clear; lia)) as (CTXi & _ & (kC & CBND & CBNDa & CBNDb)).
  pose proof (aobj_int _ _ (ao_nodes L ALO) ltac:(clear; lia)) as (NODi & _ & (kN & NBND & NBNDa & NBNDb)).
  pose proof (aobj_int _ _ (ao_store L ALO) ltac:(clear; lia)) as (STOi & _ & (kR & SBND & SBNDa & SBNDb)).
  pose proof (aobj_int _ _ (ao_ptr L ALO) ltac:(clear; lia)) as (OPi & _ & (kP & OPs & OPsa & OPsb)).
  pose proof (aobj_int _ _ (ao_fake L ALO) ltac:(clear; lia)) as (OFKi & _ & (kF & OFKs & OFKsa & OFKsb)).
  pose proof (ao_res_hi L ALO) as RHI.
  pose proof RT as RT0.
  destruct RT0 as (GPG & GOT & GOT80 & RIC & LS1 & REAL & IMAX4 & FLG5 & FLG & HPP & SHB & CANP & TI & TK & INI2 & LAY & MCS & OOM3
                    & PGC & HK2 & CF8 & CF34 & CSMT & T88 & TSD & LS2 & CT8 & CT).
  pose proof INI2 as INI. rw_split INI 1%nat INI1 INIx. clear INIx.
  pose proof OOM3 as OOM. rw_split OOM 2%nat OOMx RSS. clear OOMx.
  pose proof IMAX4 as IMAX. rw_split IMAX 3%nat IMAX3 IMAXx. clear IMAXx.
  pose proof T0 as TT0. rw_split TT0 1%nat TTctx TT.
  pose proof ARNG as ARNG0. destruct ARNG as (RIMG & RT4 & RCTX & RNO & RSTO & RRI & RFK & RSFK & RDTLS & RCLS & RPA & RSECS & RPSH).
  assert (RCTX4 : rng RNG (al_ctx L) 4096) by (eapply rng_sub'; [exact RCTX|]; clear; lia).
  word_range sp SPR.
  box CL5. box DL7. box DL8. box DL9. box DL10. box D_t_p. box D_c_p.
  rewrite (amalloc_sec_eq RESV st n N PRIM). fold ms.
  iprefix. eapply evtF_cut.
  { eapply (malloc_pre_spec_sec L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n (al_t L) lo (al_top L) (al_bot L) tr trc).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact ST
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- poison_cells _ => unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- (_ /\ _) \/ (_ /\ _) => exact ARM
         | |- _ \/ _ => unboxed CL5
         | |- @eq word _ _ => first [exact TP | exact Ha0]
         | |- is_primary _ = _ => exact PRIM
         end.
    all: try lazymatch goal with
         | |- rw_cells _ _ _ _ => assumption
         | |- rng _ _ _ => assumption
         end.
    all: try assumption.
    all: try (generalize N NR LO BOT SP47 STK1 STK2 STK3 SP1 SP2 SP4 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 LTRC RA4 SP16;
              clear; intros; unfold AIMG_HI, AMALLOC_STACK, AREQMAX, UDEPTH in *; lia).
    all: match goal with |- ?G => idtac "REMPRE" G end. }
  cbv beta. intros ms4 P4. unfold malloc_pre_postS in P4.
  destruct P4 as (spA & t0c & t1c & t2c & a4c & a5c & a6c & a7c & t3c & t4c & t5c & t6c & s0A & s1A & s2A & s3A & s4A & s5A & s0i & fr0 & junk2 & tb & m4
                  & -> & HspA & MU4 & WM4 & MI4 & ST4 & FRa & FR16 & SS & TB & LTB & TRF & FRS & UW4).
  apply evtF_done.
  assert (AR4 : AREP (AH DI AQ ASEC_of AFK) L st X m4).
  { eapply (AREP_frame_pre _ HL L st X m m4); [exact ALO | exact AR | exact MU4 | exact WM4 | | exact UW4].
    apply Forall_cons; [unfold apre; cbn [fst snd]; intros _; left; unfold AMALLOC_STACK in *; clear -LO BOT STK3; lia|].
    apply Forall_cons; [unfold apre; cbn [fst snd]; intros _; right; split; reflexivity| apply Forall_nil]. }
  pose proof AR4 as AR0. destruct AR0 as (_ & RT' & INST' & THR' & _ & _ & HS' & HD' & HRO' & RT2' & _ & RT3').
  destruct THR' as (T0' & _ & _ & _ & [sj4 [STATS' LSJ']] & _).
  destruct INST' as (I32' & I48' & I64' & I72' & I112' & I680' & I984' & I40' & I56').
  pose proof HS' as HS0. unfold AH in HS0. cbn [ah_sec] in HS0. unfold ASEC_of in HS0.
  destruct HS0 as (WFS & ARR & INST2 & PZ & SHZ). pose proof WFS as (_ & WP & WR & WL & WB & WF1 & WD).
  destruct INST2 as (J80 & [srt J128] & J136 & J168 & J681 & J704).
  destruct ARR as (order & PO & U64 & JK & PER).
  pose proof RT' as RT0.
  destruct RT0 as (GPG' & GOT' & GOT80' & RIC' & LS1' & REAL' & IMAX4' & FLG5' & FLG' & HPP' & SHB' & CANP' & TI' & TK' & INI2' & LAY' & MCS' & OOM3'
                    & PGC' & HK2' & CF8' & CF34' & CSMT' & T88' & TSD' & LS2' & CT8' & CT').
  pose proof T0' as TT0'. rw_split TT0' 1%nat TTctx' TT'.
  destruct J136 as [jstats J136]. destruct J168 as [jbsl J168]. destruct J704 as [jglob J704].
  cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add Nat.mul] in J136, J168, J704.
  assert (MTX : rw_cells asegs m4 0xb45c0 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
  { apply (proj2 (rw_cells_app asegs m4 0xb45c0 [C1 (Z_to_bv 8 0)] [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)])). split; [exact I680'| exact J681]. }
  assert (JSL : exists jslot, a_nsec st < a_nres st -> rw_cells asegs m4 (al_ptr_array L + 8 * a_nsec st) [CB 8 jslot]).
  { destruct (Z_lt_le_dec (a_nsec st) (a_nres st)) as [LT|GE].
    - destruct (junk_split m4 (al_ptr_array L + 8 * a_nsec st) 8 (8 * (a_nres st - a_nsec st) - 8)
                 ltac:(replace (8 + (8 * (a_nres st - a_nsec st) - 8)) with (8 * (a_nres st - a_nsec st)) by (clear; lia); exact JK)
                 ltac:(clear; lia) ltac:(clear -LT; lia)) as [[js J8] _].
      exists js. intros _. exact J8.
    - exists (repeat (Z_to_bv 8 0) 8). intros LT. exfalso. clear -LT GE. lia. }
  destruct JSL as [jslot JSL].
  destruct RT2' as (Q1' & Q2' & Q3').
  pose proof RT3' as RT30. destruct RT30 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R11' & R12' & _).
  pose proof R11' as R11a. rw_split R11a 1%nat R11h NAMEP. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add] in NAMEP.
  assert (I64x : rw_cells asegs m4 0xb4358 [C8 (Z_to_bv 64 4096); C8 (Z_to_bv 64 (al_ptr_array L)); C8 (Z_to_bv 64 (al_ptr_array L))]).
  { apply (proj2 (rw_cells_app asegs m4 0xb4358 [C8 (Z_to_bv 64 4096)] [C8 (Z_to_bv 64 (al_ptr_array L)); C8 (Z_to_bv 64 (al_ptr_array L))])).
    split; [exact I64'|]. apply (proj2 (rw_cells_app asegs m4 _ [C8 (Z_to_bv 64 (al_ptr_array L))] [C8 (Z_to_bv 64 (al_ptr_array L))])).
    split; [exact I72'| exact J80]. }
  assert (LC4 : large_cells (al_ctx L) (al_t L) (al_ptr_array L) m4).
  { unfold large_cells. split; [unfold rmap_cells; split; [exact GPG'| split; [exact PGC'| split; [exact GOT'| split; [exact Q1'| exact Q2']]]]|].
    split; [eapply poison_cells_of_rt'; exact RT'|]. split; [exact NAMEP|]. split; [exact R12'|].
    split; [exact TI'|]. split; [exact TK'|]. split; [exact T88'|]. split; [exact TSD'|]. split; [exact CT'| exact I64x]. }
  assert (FROK : forall a, sfresh RESV st n a = true ->
        ablk a (a + ms) /\ a + ms <= ATOP
     /\ (a + ms <= al_t L \/ al_t L + 4096 <= a) /\ (a + ms <= al_ctx L \/ al_ctx L + 4096 <= a) /\ (a + ms <= al_ptr_array L \/ al_ptr_array L + 8388608 <= a)
     /\ fill_at m4 (shad a) (ms / 8) 0).
  { intros a HF.
    pose proof (valid_geo L RESV st n a N PRIM HF ROK) as (AAL & AHI0 & ACE & MSP & _). fold ms in ACE, MSP.
    destruct (ablk_int _ _ AHI0) as (kA & ABND & ABNDa & ABNDb & ABNDc & ABNDd). pose proof (sec_facts n N PRIM) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & MSBx). fold ms in MSBx.
    destruct (ablk_shad_int _ _ AHI0 ltac:(clear -AAL; first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]) ltac:(clear -MSBx; lia)) as (kS & ASD & ASDa & ASDb & SA1 & SA3).
    pose proof (valid_clear L RESV st n a N PRIM HF ROK) as (C_t & C_c & C_r & C_p & _). fold ms in C_t, C_c, C_p.
    unfold K_HIGH_MEM in AHI0. split; [exact AHI0|]. split; [exact ACE|]. split; [exact C_t|]. split; [clear -C_c; lia|]. split; [exact C_p|].
    unfold fill_at. apply (azero_cb m4 (shad a) (ms / 8) (ms / 8)); [| clear -MSB; first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]].
    eapply (ashz_azero L _ m4 a ms SHZ); [clear -AAL; first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]| exact AHI0| exact ACE| clear -MSB; lia
      | exact (valid_hulls L RESV st n a N PRIM HF ROK)| exact (valid_chunks L RESV st n a N PRIM HF ROK)]. }
  assert (TS : forall (a nres' : Z) RNG' (m1 m' : amem) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    sfresh RESV st n a = true ->
    munch [(bv_unsigned sp - 2320, bv_unsigned sp - 2272)]%Z m4 m1 -> wmono asegs m4 m1 ->
    large_post RNG (Z_to_bv 64 (bv_unsigned sp - 2320)) a n (al_ctx L) (al_t L) (al_ptr_array L) (a_nres st) (a_nsec st) nres' lo m1 RNG' m' ->
    stk asegs m' lo (bv_unsigned sp - 2272) ->
    implS asegs RNG' (aembed ATOP (poison0 (a + PG + rz_size n) (Z.land n (Z.lnot 7)) (aret (st_sec st nres' a ms n, Some (a_next st)))))
          (epostF (amalloc_post CI (AHEAP_P (AH DI AQ ASEC_of AFK)) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m))
          (MS (mkR (Z_to_bv 64 0x31b90) (Z_to_bv 64 (bv_unsigned spA + -128)) gp tp t0' t1' t2'
                   (Z_to_bv 64 0) (Z_to_bv 64 n) (Z_to_bv 64 (a + 4096)) a1' a2' a3' a4' a5' a6' a7'
                   (Z_to_bv 64 8) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n)
                   (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 (al_t L)) (Z_to_bv 64 1)
                   t3' t4' t5' t6')
              F (Z_to_bv 64 0x31b90) fc None m' (seg_rom asegs))).
  { intros a nres' RNG' m1 m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HF MU1 WM1 LP STc.
    pose proof (valid_geo L RESV st n a N PRIM HF ROK) as (AAL & AHI0 & ACE & MSP & _). fold ms in ACE, MSP.
    destruct (ablk_int _ _ AHI0) as (kA & ABND & ABNDa & ABNDb & ABNDc & ABNDd). pose proof (sec_facts n N PRIM) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & MSBx). fold ms in MSBx.
    destruct (ablk_shad_int _ _ AHI0 ltac:(clear -AAL; first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]) ltac:(clear -MSBx; lia)) as (kS & ASD & ASDa & ASDb & SA1 & SA3). unfold K_HIGH_MEM in AHI0.
    pose proof (valid_clear L RESV st n a N PRIM HF ROK) as VC. fold ms in VC. pose proof VC as (C_t & C_c & C_r & C_p & C_n & C_s & C_f & C_d).
    unfold large_post in LP. cbv zeta in LP. fold ms in LP.
    destruct LP as (FPLE & BW & _ & _ & _ & MUL & WML & MIL & STL & HDRP & ZB & SHF1 & SHZ0 & SHF2 & RCH & RSCH & INS & SRT & JST & JBS & MTX9 & JGL
                    & [sj9 [STATS9 LSJ9]] & PAS & DISJ & NRB' & LC').
    rewrite unsigned_lit in MUL, STL by (clear -SPR LO BOT STK3; unfold AMALLOC_STACK in *; lia).
    unfold AINSTANCE in MUL.
    assert (NR' : (a_nsec st <> a_nres st /\ nres' = a_nres st)
                  \/ (a_nsec st = a_nres st /\ nres' = a_nres st + 16384
                      /\ rw_cells asegs m' (al_ptr_array L + 8 * a_nres st + 8) [CB (Z.to_nat (131072 - 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (131072 - 8)))])).
    { destruct DISJ as [D|(D1 & D2 & D3 & _)]; [left; exact D| right; split; [exact D1| split; [exact D2| exact D3]]]. }
    assert (RPA' : rng RNG' (al_ptr_array L) (8 * nres')).
    { destruct DISJ as [[_ ->]|(D1 & -> & _ & RPC)]; [eapply rng_fp_le; [exact FPLE| exact RPA]|].
      replace (8 * (a_nres st + 16384)) with (8 * a_nres st + 131072) by (clear; lia).
      apply rng_merge; [exact BW| clear -WB; lia| clear; lia| eapply rng_fp_le; [exact FPLE| exact RPA]| exact RPC]. }
    clear DISJ.
    assert (WTF : wt_facts L (bv_unsigned sp) lo a ms (a_nsec st) (a_nres st) nres').
    { unfold wt_facts. assert (NSX : 0 <= a_nsec st /\ a_nsec st + 1 <= nres' /\ a_nres st <= nres') by (destruct NR' as [(A1 & A2)|(A1 & A2 & _)]; clear -A1 A2 WB; lia).
      repeat lazymatch goal with |- _ /\ _ => split end; try assumption; try (clear -NSX NRB' WB LO BOT STK3; unfold AMALLOC_STACK in *; lia). }
    set (WS := ((bv_unsigned sp - 2784, bv_unsigned sp - 2272) :: (a, a + ms) :: (shad a, shad a + ms / 8) :: (738072 + 112, 738072 + 720)
                :: (al_t L + 2800, al_t L + 3168) :: (al_ptr_array L + 8 * a_nsec st, al_ptr_array L + 8 * a_nsec st + 8)
                :: (al_ptr_array L + 8 * a_nres st, al_ptr_array L + 8 * nres') :: nil)%Z).
    assert (MUS : munch WS m4 m').
    { subst WS. eapply munch_trans; [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MUL]]; unfold sub_fp; cbn [outside]; clear; intros q Hq; lia. }
    assert (WMS : wmono asegs m4 m') by (eapply wmono_trans; [exact WM1| exact WML]).
    assert (MUT : munch (List.filter nonempty (WT L (bv_unsigned sp) a ms (a_nsec st) (a_nres st) nres')) m4 m').
    { apply munch_filter_nonempty. eapply munch_weaken; [| exact MUS]. subst WS. unfold WT, sub_fp, AINSTANCE. cbn [outside]. clear. intros q Hq. lia. }
    pose proof (KT_rt L _ lo a ms _ _ _ WTF m4 m' MUT WMS RT') as RTL.
    pose proof (KT_rt2 L _ lo a ms _ _ _ WTF m4 m' MUT WMS (conj Q1' (conj Q2' Q3'))) as RT2L.
    pose proof (KT_rt3 L _ lo a ms _ _ _ WTF m4 m' MUT WMS RT3') as RT3L.
    pose proof (KT_relro L _ lo a ms _ _ _ WTF m4 m' MUT HRO') as HROL.
    pose proof (premap_of_rt' L m' RTL RT2L RT3L) as PMC.
    pose proof RTL as RT0.
    destruct RT0 as (_ & _ & _ & _ & LS1L & _ & _ & _ & FLGL & HPPL & _ & _ & _ & _ & _ & _ & _ & _ & _ & HK2L & _ & _ & _ & _ & _ & LS2L & CT8L & _).
    pose proof HK2L as HKL. rw_split HKL 1%nat HK1L HKx. clear HKx.
    destruct LC' as (_ & PCL & _ & _ & TIL & TKL & T88L & TSDL & CTL & I64L).
    pose proof I64L as I64h. rw_split I64h 1%nat I64a I64b. clear I64b.
    assert (I32L : rw_cells asegs m' 0xb4338 [C8 (Z_to_bv 64 (al_space_beg L))]).
    { eapply cells_frame; [exact I32'| exact MUT| exact WMS|]. cbn. eapply KT_img; [exact WTF| | | | |]; clear; unfold AIMG_HI, AINSTANCE; lia. }
    assert (TTL : rw_cells asegs m' (al_t L) [C8 (Z_to_bv 64 (al_ctx L))]).
    { eapply cells_frame; [exact TTctx'| exact MUT| exact WMS|]. cbn. eapply KT_t; [exact WTF| | |]; clear; lia. }
    assert (DEPL : ADEPOT DI L m').
    { pose proof (hd_frame _ HL L m4 m' WS) as HDF. cbn [ah_depot AH] in HDF. apply HDF; [exact HD'| exact MUS| exact WMS|].
      subst WS. pose proof (ad_nodes_ptr L ALO) as D_n_p. pose proof (ad_store_ptr L ALO) as D_s_p. unfold adisj in D_n_p, D_s_p. ub DL7. ub DL8.
      repeat (apply Forall_cons; [cbn [fst snd]; intros x Hx;
        clear -Hx Y Y0 SPR LO BOT STK3 AHI0 ACE TL1 DL1 DL2 DL4 DL5 OP WB NRB' C_n C_s D_n_p D_s_p SA1 SA3 WTF TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi OPs OPsa OPsb OPi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb; unfold wt_facts, AMALLOC_STACK in *; lia|]).
      apply Forall_nil. }
    subst WS.
    xport FRa MUS WMS ltac:(clear -SPR LO BOT STK3 AHI0 ACE TL1 TL2 OP WB NRB' WTF TBND TBNDa TBNDb TIMG TIMGa TIMGb OPs OPsa OPsb OPi ABND ABNDa ABNDb ABNDc ABNDd; unfold wt_facts, AMALLOC_STACK in *; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; dlia).
    xport FR16 MUS WMS ltac:(clear -SPR LO BOT STK3 AHI0 ACE TL1 TL2 OP WB NRB' WTF TBND TBNDa TBNDb TIMG TIMGa TIMGb OPs OPsa OPsb OPi ABND ABNDa ABNDb ABNDc ABNDd; unfold wt_facts, AMALLOC_STACK in *; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; dlia).
    xport SS MUS WMS ltac:(clear -SPR LO BOT STK3 AHI0 ACE TL1 TL2 OP WB NRB' WTF TBND TBNDa TBNDb TIMG TIMGa TIMGb OPs OPsa OPsb OPi ABND ABNDa ABNDb ABNDc ABNDd; unfold wt_facts, AMALLOC_STACK in *; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; dlia).
    xport TB MUS WMS ltac:(rewrite LTB; clear -SPR LO BOT STK3 AHI0 ACE TL1 TL2 OP WB NRB' WTF TBND TBNDa TBNDb TIMG TIMGa TIMGb OPs OPsa OPsb OPi ABND ABNDa ABNDb ABNDc ABNDd; unfold wt_facts, AMALLOC_STACK in *; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; dlia).
    xport FRS MUS WMS ltac:(clear -SPR LO BOT STK3 AHI0 ACE TL1 TL2 OP WB NRB' WTF TBND TBNDa TBNDb TIMG TIMGa TIMGb OPs OPsa OPsb OPi ABND ABNDa ABNDb ABNDc ABNDd; unfold wt_facts, AMALLOC_STACK in *; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; dlia).
    xport UW4 MUS WMS ltac:(ub D_t_p; clear -Y SPR LO BOT STK3 AHI0 ACE TL1 TL2 OP WB NRB' WTF C_t TBND TBNDa TBNDb TIMG TIMGa TIMGb OPs OPsa OPsb OPi ABND ABNDa ABNDb ABNDc ABNDd; unfold wt_facts, AMALLOC_STACK in *; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; dlia).
    pose proof (ao_res L ALO) as ORS. unfold aobj in ORS. pose proof (ao_space L ALO) as RSP.
    assert (DJSB : a + ms <= al_space_beg L \/ al_space_beg L + 137438953472 <= a) by (clear -C_r RSP; lia).
    apply (rng_fp_le _ _ _ _ FPLE) in RIMG. 
    assert (RSTK' : rng RNG' lo (bv_unsigned sp - lo)) by (eapply rng_fp_le; [exact FPLE| exact RSTK]).
    assert (RCTX' : rng RNG' (al_ctx L) 4096) by (eapply rng_fp_le; [exact FPLE| exact RCTX4]).
    assert (RT4' : rng RNG' (al_t L) 4096) by (eapply rng_fp_le; [exact FPLE| exact RT4]).
    assert (RNO' : rng RNG' (al_nodes L) 1048576) by (eapply rng_fp_le; [exact FPLE| exact RNO]).
    assert (RSTO' : rng RNG' (al_store L) 8388608) by (eapply rng_fp_le; [exact FPLE| exact RSTO]).
    replace (a + PG + rz_size n) with (a + 6144) by (unfold PG; rewrite RZ; clear; lia).
    eapply (malloc_tail_sec DI PR L RNG' _ _ _ ra sp gp tp spA t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
              s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0A s1A s2A s3A s4A s5A s0i F fc m' n (al_t L) a ms (a_nsec st) (al_space_beg L) lo
              (1 + Z.of_nat (length trc)) fr0 junk2 tb trc).
    all: try lazymatch goal with
         | |- forall x, _ => first [exact HROL | idtac]
         | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption
         | |- stk _ _ _ _ => exact STc
         | |- bv_unsigned _ = _ => exact HspA
         | |- mem_inv _ _ => exact MIL
         | |- poison_cells _ => exact PCL
         | |- premap_cells _ => exact PMC
         | |- ADEPOT _ _ _ => exact DEPL
         | |- @eq word _ _ => first [reflexivity | exact TP | exact HspA]
         | |- @eq bool _ _ => exact PRIM
         | |- @eq nat _ _ => first [exact LTB | exact LSJ9]
         | |- u64arr _ _ _ _ => exact TB
         | |- exists sjx, _ => exists sj9; split; [exact STATS9| exact LSJ9]
         | |- map _ _ = _ => exact TRF
         | |- In _ _ => exact TRU
         | |- fill_at _ (shad _) 512 _ => exact SHF1
         | |- fill_at _ (shad _ + 512) _ 0 => exact SHZ0
         | |- fill_at _ _ _ _ => exact SHF2
         | |- rw_cells _ _ (shad _) _ => idtac
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _; C8 _; CB _ _] => exact HDRP
         | |- rw_cells _ _ (_ + 4096) [CB _ _] => exact ZB
         | |- rw_cells _ _ _ [C8 (Z_to_bv 64 (al_space_beg _))] => exact I32L
         | |- rw_cells _ _ _ [C8 (Z_to_bv 64 4096)] => exact I64a
         | |- rw_cells _ _ (al_t _) _ => exact TTL
         | |- rw_cells _ _ _ _ => assumption
         | |- rng _ _ _ => first [assumption | exact RCH | exact RSCH]
         | |- _ \/ _ => first [exact DJSB | exact C_t | exact C_n | exact C_s | clear -C_c; lia | unboxed CL5 | unboxed DL7 | unboxed DL8 | unboxed DL9 | unboxed DL10]
         | |- _ = sec_map_size _ => reflexivity
         end.
    all: try lazymatch goal with
         | |- forall x, _ => idtac
         | |- _ => clear -SPR LO BOT STK3 SP47 AAL AHI0 ACE TL1 TL2 TL3 CL1 CL2 CL3 DL1 DL2 DL3 DL4 DL5 DL6 SP1 SP2 SP4 N LTRC TBND TBNDa TBNDb TIMG TIMGa TIMGb CBND CBNDa CBNDb CTXi NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi ABND ABNDa ABNDb ABNDc ABNDd;
                unfold AIMG_HI, AMALLOC_STACK, K_SPACE_SIZE, K_SPACE_EXTRA in *; lia
         end.
    all: match goal with |- forall x, _ => idtac | |- ?G => idtac "REMTS" G end.
    intros RNG5 m5 id sj5 t0d t1d t2d a1d a2d a3d a4d a5d a6d a7d t3d t4d t5d t6d PM.
    unfold malloc_postS in PM. cbv zeta in PM.
    destruct PM as (FPLE5 & MU5 & WM5 & MI5 & ST5 & IDR & STATS5 & LSJ5 & HDR5 & PGJ5 & MAG5 & LCJ5 & AHD5 & USR5 & TLJ5 & SHF5 & SHU5 & SHT5 & DEP5 & PC5 & PMC5).
    apply implS_ret. apply evtF_done.
    pose proof (ad_nodes_ptr L ALO) as D_n_p. pose proof (ad_store_ptr L ALO) as D_s_p. unfold adisj in D_n_p, D_s_p.
    xport UW4 MU5 WM5 ltac:(ub DL7; ub DL8; clear -Y Y0 SPR LO BOT STK3 AHI0 ACE TL1 TL2 SA1 SA3 DL1 DL2 DL4 DL5 C_t TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb; unfold AMALLOC_STACK in *; dlia).
    xport INS MU5 WM5 ltac:(clear -SPR LO BOT STK3 AHI0 ACE TL1 SA1 SA3 DL1 DL4 TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb; unfold AMALLOC_STACK in *; dlia).
    xport SRT MU5 WM5 ltac:(clear -SPR LO BOT STK3 AHI0 ACE TL1 SA1 SA3 DL1 DL4 TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb; unfold AMALLOC_STACK in *; dlia).
    xport MTX9 MU5 WM5 ltac:(clear -SPR LO BOT STK3 AHI0 ACE TL1 SA1 SA3 DL1 DL4 TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb; unfold AMALLOC_STACK in *; dlia).
    xport PAS MU5 WM5 ltac:(ub D_t_p; clear -Y SPR LO BOT STK3 AHI0 ACE TL1 SA1 SA3 DL1 DL2 DL4 DL5 OP WB C_p D_n_p D_s_p WTF TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi OPs OPsa OPsb OPi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb; unfold wt_facts, AMALLOC_STACK in *; dlia).
    assert (JSTq : junk_at m5 738208 32).
    { eapply junk_frame; [exact JST| exact MU5| exact WM5| intros _]. cbn [disjoint_from fst snd]. clear -SPR LO BOT STK3 AHI0 ACE TL1 SA1 SA3 DL1 DL4 TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb; unfold AMALLOC_STACK in *; dlia. }
    assert (JBSq : junk_at m5 738240 512).
    { eapply junk_frame; [exact JBS| exact MU5| exact WM5| intros _]. cbn [disjoint_from fst snd]. clear -SPR LO BOT STK3 AHI0 ACE TL1 SA1 SA3 DL1 DL4 TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb; unfold AMALLOC_STACK in *; dlia. }
    assert (JGLq : junk_at m5 738776 16).
    { eapply junk_frame; [exact JGL| exact MU5| exact WM5| intros _]. cbn [disjoint_from fst snd]. clear -SPR LO BOT STK3 AHI0 ACE TL1 SA1 SA3 DL1 DL4 TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb; unfold AMALLOC_STACK in *; dlia. }
    assert (NR5 : (a_nsec st <> a_nres st /\ nres' = a_nres st)
                  \/ (a_nsec st = a_nres st /\ nres' = a_nres st + 16384
                      /\ rw_cells asegs m5 (al_ptr_array L + 8 * a_nres st + 8) [CB (Z.to_nat (131072 - 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (131072 - 8)))])).
    { destruct NR' as [D|(D1 & D2 & ZC)]; [left; exact D| right]. split; [exact D1|]. split; [exact D2|].
      xport ZC MU5 WM5 ltac:(ub D_t_p; clear -Y SPR LO BOT STK3 AHI0 ACE TL1 SA1 SA3 DL1 DL2 DL4 DL5 OP WB NRB' D2 C_p D_n_p D_s_p WTF TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi OPs OPsa OPsb OPi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb; unfold wt_facts, AMALLOC_STACK in *; dlia). exact ZC. }
    assert (MUW : munch (WT L (bv_unsigned sp) a ms (a_nsec st) (a_nres st) nres') m m5).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU4]|].
      2: eapply munch_trans; [eapply munch_weaken; [| exact MUS]| eapply munch_weaken; [| exact MU5]].
      all: unfold WT, sub_fp, AINSTANCE; cbn [outside]; clear -MSB; intros q Hq; lia. }
    assert (WMW : wmono asegs m m5). { eapply wmono_trans; [exact WM4|]. eapply wmono_trans; [exact WMS| exact WM5]. }
    assert (USR : junk_at m5 (a + 6144) (ms - 6144)).
    { replace (ms - 6144) with (Z.of_nat (cells_size [CB (Z.to_nat n) (repeat (Z_to_bv 8 190) (Z.to_nat (Z.min n 4096)) ++ repeat (Z_to_bv 8 0) (Z.to_nat n - Z.to_nat (Z.min n 4096)))]) + (ms - 6144 - n))
        by (cbn [cells_size csize]; clear -N; lia).
      apply junk_merge; [eapply junk_of_cells; exact USR5| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear -N; lia); exact TLJ5| clear; lia| clear -MSR NSE RSR N; lia]. }
    destruct (store_sec DI AQ AFK HL CI CI_OK CI_OK2 L RNG RNG5 (bv_unsigned sp) lo m m5 st X LB n a nres' id sj5 RESV
                ALO ARNG0 AR BL HFK N PRIM HF ROK) as [PRES AHP5].
    all: try lazymatch goal with
         | |- fp_le _ _ => eapply fp_le_trans; [exact FPLE| exact FPLE5]
         | |- munch _ _ _ => exact MUW
         | |- wmono _ _ _ => exact WMW
         | |- u64arr _ _ _ _ => exact STATS5
         | |- ADEPOT _ _ _ => exact DEP5
         | |- junk_at _ (_ + 6144) _ => exact USR
         | |- junk_at _ _ _ => assumption
         | |- fill_at _ _ _ _ => assumption
         | |- rng _ (shad _) _ => eapply rng_fp_le; [exact FPLE5| exact RSCH]
         | |- rng _ (al_ptr_array _) _ => eapply rng_fp_le; [exact FPLE5| exact RPA']
         | |- rng _ _ _ => eapply rng_fp_le; [exact FPLE5| exact RCH]
         | |- _ \/ _ => exact NR5
         | |- rw_cells _ _ _ _ => assumption
         | |- @eq nat _ _ => exact LSJ5
         | |- _ => clear -LO BOT STK3 SP47 IDR NRB'; unfold AMALLOC_STACK in *; lia
         end.
    all: match goal with |- amalloc_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => idtac | |- ?G => idtac "REMST" G end.
    unfold amalloc_post. split; [eapply fp_le_trans; [exact FPLE| exact FPLE5]|].
    do 15 eexists. exists m5. split; [reflexivity|]. split; [exact MI5|]. split; [exact ST5|]. split; [exact PRES|].
    cbn [fst snd]. eexists (a + 6144), _. split; [reflexivity|].
    split. { unfold ablock_range. atop_facts. pose proof (sec_facts n N PRIM) as (_ & _ & _ & RSRx & _ & NSEx & MSEx & _). fold ms in MSEx. clear -AHI0 ACE AAL N MSR NSE RSR RSRx NSEx MSEx ABND ABNDa ABNDb ABNDc ABNDd.
             split; [eapply ablk_sub; [exact AHI0| lia| lia]|]. split; [lia|]. split; [lia|]. first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]. }
    split; [exact AHP5|]. split; [exact USR5|].
    split; [eapply rng_sub'; [eapply rng_fp_le; [exact FPLE5| exact RCH]|]; clear -N MSR NSE RSR; lia|].
    split. { eapply rng_sub'; [eapply rng_fp_le; [exact FPLE5| exact RSCH]|]. rewrite !shad_div, shlen_div. clear -N MSR NSE RSE RSR AAL MSM. first [ (Z.div_mod_to_equations; lia) | (Z.to_euclidean_division_equations; nia) ]. }
    intros _. unfold aptr_addr. pose proof (st_sec_fields st nres' a ms n) as (_ & _ & _ & _ & _ & _ & E7 & _). rewrite E7, lookup_insert_eq.
    cbn [chunk_user_beg]. unfold PG. rewrite RZ. clear; lia. }
  eapply (calloc_sec_spec RNG (KS RESV st n) (KS2 st n) _ (sfresh RESV st n) _ _ gp tp t0c t1c t2c _ _ _ _ _ _ a4c a5c a6c a7c _ _ _ _ _ _ _ _ _ _ t3c t4c t5c t6c F fc m4 n
            (al_ctx L) (al_t L) (a_ptr_array st) (a_nres st) (a_nsec st) lo sj4 (bv_unsigned srt) jstats jbsl jglob jslot).
  all: rewrite ?PAE.
  all: try lazymatch goal with
       | |- forall x, _ => idtac
       | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia);
                           replace (bv_unsigned spA + -128) with (bv_unsigned sp - 2272) by (clear -HspA; lia); exact ST4
       | |- mem_inv _ _ => exact MI4
       | |- large_cells _ _ _ _ => exact LC4
       | |- u64arr _ _ _ _ => exact STATS'
       | |- @eq word _ _ => first [exact TP | reflexivity]
       | |- @eq bool _ _ => exact PRIM
       | |- @eq nat _ _ => exact LSJ'
       | |- rw_cells _ _ _ [C1 (Z_to_bv 8 (bv_unsigned _))] => rewrite Z_to_bv8_bv_unsigned; exact J128
       | |- rw_cells _ _ _ [C1 _; C1 _; C1 _; C1 _] => exact MTX
       | |- rw_cells _ _ _ [C8 _; C8 _] => exact I112'
       | |- rw_cells _ _ _ [CB 32 _] => exact J136
       | |- rw_cells _ _ _ [CB 512 _] => exact J168
       | |- rw_cells _ _ _ [CB 16 _] => exact J704
       | |- _ mod 16384 = 0 => exact (proj1 WR)
       | |- iclr _ _ => exact TL4 | |- AIMG_HI <= al_ctx _ => exact CL3
       | |- sclr (al_ctx _) _ => exact CL1 | |- sclr (al_t _) _ => exact TL1
       | |- ablk (al_ptr_array _) _ => pose proof (ao_ptr L ALO) as OPx; unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OPx; unfold ablk, KLS, AIMG_HI; clear -OPx; lia
       | |- ablk _ _ => assumption
       | |- _ \/ _ => first [ub D_t_p; clear -Y; lia | ub D_c_p; clear -Y; lia | unboxed CL5]
       | |- rng _ _ (bv_unsigned _ - _) => rewrite unsigned_lit by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia);
                         eapply rng_sub'; [exact RSTK|]; clear -LO HspA SP47 BOT STK3; unfold AMALLOC_STACK in *; lia
       | |- rng _ _ _ => assumption
       end.
  all: try lazymatch goal with
       | |- forall x, _ => idtac
       | |- _ => rewrite ?unsigned_lit by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia);
              unfold AIMG_HI, AREQMAX, AMALLOC_STACK in *; clear -N LO HspA BOT STK3 SPR TL1 TL2 TL4 CL1 CL2 CL3 OP WB WR TBND TBNDa TBNDb TIMG TIMGa TIMGb CBND CBNDa CBNDb CTXi OPs OPsa OPsb OPi; lia
       end.
  all: match goal with |- forall x, _ => idtac | |- ?G => idtac "REMCS" G end.
  - exact JSL.
  - exact FROK.
  -
    intros a RNG' ms' HF A0 AAL ACE LE.
    destruct (sfresh_false_cases RESV st n a HF) as [B|[E|(B1 & B2 & B3)]].
    + rewrite (KS_unr_bad RESV st n a B). apply implF_ret_unr.
    + exfalso. unfold is_err, TWO64 in E. apply Z.ltb_lt in E. atop_facts. clear -E ACE MSB. lia.
    + rewrite (KS_unr_phantom RESV st n a B1 B2 B3). apply implF_ret_unr.
  -
    intros a RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HF HNE (m1 & MU1 & WM1 & LP) STc.
    rewrite unsigned_lit in MU1, LP, STc by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia).
    replace (bv_unsigned spA + -128 - 48) with (bv_unsigned sp - 2320) in MU1, LP by (clear -HspA; lia).
    replace (bv_unsigned spA + -128) with (bv_unsigned sp - 2272) in MU1, STc by (clear -HspA; lia).
    rewrite ?PAE in LP. rewrite ?PAE in HNE.
    rewrite (KS_fresh_nocommit RESV st n a HF HNE), fin_sec_nocommit. fold ms.
    eapply (TS a (a_nres st) RNG' m1 m'); [exact HF| exact MU1| exact WM1| exact LP| exact STc].
  -
    intros a HF HE NRB. rewrite <- ?PAE. apply (KS_fresh_commit RESV st n a HF HE NRB).
  -
    intros a RNG' ms' HF HE OV. rewrite (KS_fresh_overflow RESV st n a HF HE OV). apply implF_ret_unr.
  -
    intros a r RNG' ms' NE R0 RCE. rewrite <- ?PAE in NE. rewrite (KS2_other st n a r NE R0 ltac:(unfold alloc_ceiling; atop_facts; exact RCE)). apply implF_ret_unr.
  -
    intros a RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HF HE (m1 & MU1 & WM1 & LP) STc.
    rewrite unsigned_lit in MU1, LP, STc by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia).
    replace (bv_unsigned spA + -128 - 48) with (bv_unsigned sp - 2320) in MU1, LP by (clear -HspA; lia).
    replace (bv_unsigned spA + -128) with (bv_unsigned sp - 2272) in MU1, STc by (clear -HspA; lia).
    rewrite ?PAE in LP. rewrite ?PAE in HE.
    pose proof LP as LP0. unfold large_post in LP0. cbv zeta in LP0.
    destruct LP0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NRB' & _).
    rewrite <- ?PAE. rewrite (KS2_granted st n a) by (rewrite PAE; unfold alloc_ceiling; atop_facts; clear -OP WB NRB' OPs OPsa OPsb OPi; lia).
    rewrite fin_sec_commit. fold ms. unfold K_CHUNKS_BLOCK.
    eapply (TS a (a_nres st + 16384) RNG' m1 m'); [exact HF| exact MU1| exact WM1| exact LP| exact STc].
Qed.
End S.
End CANSEC1.
