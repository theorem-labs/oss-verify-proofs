(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (31 recorded proofs replaced by written proofs (rpw_extP, rget_meta_rec_extP, rmeta_cells_extP and 28 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import PImg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import F_malloc_free MallocTree MallocKit_A MallocKit_AB.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Export MallocKit_A2.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require KStep.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B2 RMallocKit_B3 RMallocKit_A RMalloc_fp.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RMallocKit_A2 () := "C47Corelib4Init9Datatypes3fstC35stdpp4base6LookupC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I35stdpp9countable9Countable00C47Corelib4Init5Logic8eq_ind_rC35stdpp4base;RelDecisionC35stdpp4gmap;gmap_lookupC35stdpp4gmap:gmap_emptyC35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap9gmap_foldC35stdpp8fin_maps:map_eq_iffC35stdpp4gmap;gmap_finmapC35stdpp4base4fmapC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC35stdpp8fin_maps@lookup_insert_eqC35stdpp8fin_maps@lookup_insert_neI35stdpp8fin_maps6FinMap00C35stdpp8fin_maps7MapFoldC35stdpp8fin_maps:map_insertC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base6InsertC35stdpp4base<PartialAlterC35stdpp4base5MergeI35stdpp4gmap4gmap00C35stdpp8fin_maps@lookup_delete_eqC35stdpp8fin_maps@lookup_delete_neC35stdpp4gmapBgmap_partial_alterC59OSSVerify5KrLib6Malloc:MallocTree7optr_inC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C59OSSVerify5KrLib6Malloc9MallocRep2pwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep2wzC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes6option02I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1N00I47Corelib7Numbers7BinNums1Z00I47Corelib4Init5Logic4True00K47Corelib7Numbers7BinNums1Z01C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc7s_metasC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes2idC59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C35stdpp4base6lookupC35stdpp6option;from_optionI59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5meta0C1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC45stdpp7numbers1Z6eq_decC35stdpp9countable;N_countableC35stdpp9countable;Z_countableC59OSSVerify5KrLib4Spec6Malloc3ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_free_meta_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<c_avail_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_tailC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_brkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_prevC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00I47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6a_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6g_metaC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep9meta_wordC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01c59OSSVerify5KrLib5Plain=RMallocKit_A28rpw_extPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep:meta_cellsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc8brkstate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep9rmrep_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst6SECRETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;c_init_doneC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib4Spec6Malloc>c_mmap_counterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocGc_avail_meta_area_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_meta_alloc_shiftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep?rctx_head_cellsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib4Spec6Malloc8c_activeC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List7map_extC59OSSVerify5KrLib6Malloc9MallocRep7activesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7c_usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep6usagesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9unmap_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep2b8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;c_unmap_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep:unmap_seqsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7bouncesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9c_bouncesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep8bouncessC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_seqC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep5zerosC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib6Malloc9MallocRep>ctx_tail_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib3Lib3Arr6u64arrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr5u8arrC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4mctx00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain4PImg5psegsC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01C59OSSVerify5KrLib5Plain:RMallocRep4RCTXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep9rarea_repC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8a_nslotsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib4Spec6Malloc4aaddC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=RMallocKit_A2@rmeta_cells_extPC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=RMallocKit_A2Brget_meta_rec_extPC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C59OSSVerify5KrLib4Spec6Malloc8AREA_HDRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6NSLOTSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9META_SIZEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep:rgroup_repC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z4landC59OSSVerify5KrLib4Spec6Malloc<g_active_idxC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC47Corelib4Init5Peano2ltC59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3mrdC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC59OSSVerify5KrLib6Malloc;MallocKit_B8agree_onC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC47Corelib4Init5Logic3notC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<find_segmentC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<seg_writableC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType9seg_bytesC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8seg_baseC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith6BinInt1Z4to_NC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?segment_byte_atI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C59OSSVerify5KrLib3Lib5Cells8cells_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5CellsBcells_bytes_lengthC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=RMallocKit_A2?rbytes_at_agreeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=RMallocKit_A2<rwr_at_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr4u64sC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3mulC47Corelib4Init5Logic8iff_reflK46Stdlib9micromega7EnvRing5PExpr05C46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib3Lib3Arr;u64s_lengthC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappC56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulK46Stdlib9micromega=RingMicromega3Op201C59OSSVerify5KrLib5Plain:RMallocRep5rmrepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep;rregions_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep=rmrep_globalsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep;rmrep_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep<rmrep_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep<rmrep_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_seqC47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List:length_mapC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symK46Stdlib9micromega6VarMap1t01C59OSSVerify5KrLib6Malloc<MallocKit_A2<agree_on_subC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=RMallocKit_A2?rrw_cells_agreeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=RMallocKit_A2=ru64arr_agreeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=RMallocKit_A2<ru8arr_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst3CANC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03C59OSSVerify5KrLib4Spec6Malloc:get_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9cell_readC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc7cellval01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep;rshadow_repC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03C59OSSVerify5KrLib5Plain:RMallocRep6RMLOCKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep5RLIBCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep8RGOT_SSPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep:RSSP_GUARDC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep;RNEED_LOCKSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain4PImg:RPAGE_SIZEC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01I59OSSVerify5KrLib4Spec6Malloc7cellval00C1?~~~~~~~~~~~~~~~C35stdpp4base6insertc59OSSVerify5KrLib5Plain=RMallocKit_A2;rnr_regionsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic9False_indI47Corelib4Init5Logic5False00C56Stdlib6NArith6BinNat1N6eq_decI47Corelib4Init6Specif7sumbool00I47Corelib4Init5Logic2or00K59OSSVerify5KrLib4Spec6Malloc6region01C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01c59OSSVerify5KrLib5Plain=RMallocKit_A2>rnr_lookup_oldC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02c59OSSVerify5KrLib5Plain=RMallocKit_A2>rnr_lookup_newC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndI59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:new_regionC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_next_ridC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat3N2Z7inj_iffC56Stdlib6ZArith4Znat3N2Z9is_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib6Malloc9MallocRep5lr_loC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree>In_live_rangesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocAregion_live_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;live_rangesC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC59OSSVerify5KrLib6Malloc:MallocTree>ranges_free_InC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula06K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes:comparison00C59OSSVerify5KrLib5Plain:RMallocRep8rstaticsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_reservedC1?~~~~~~~~~~~~~~~C35stdpp8fin_maps;map_to_listC59OSSVerify5KrLib5Plain:RMallocRepArstatics_reservedC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9in_or_appC59OSSVerify5KrLib6Malloc:MallocTreeAranges_free_introC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=RMallocKit_A2>rnr_lookup_invC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=RMallocKit_A2@rnr_old_disjointC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses9not_morphC59OSSVerify5KrLib4Spec6Malloc;ranges_freeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;iv_disjointC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbK46Stdlib9micromega5Tauto8GFormula07C59OSSVerify5KrLib5Plain:RMallocRep<ref_reservedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=RMallocKit_A2=rnr_lr_lo_newC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep>round_up_pg_geC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib5Plain:RMallocRep:rarea_concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep;rarea_lr_loC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C59OSSVerify5KrLib5Plain:RMallocRep;rgroup_concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep;lr_lo_groupC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=RMallocKit_A2;rmrep_agreeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=RMallocKit_A28rnr_concC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=RMallocKit_A2>rmrep_ctx_extPC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=RMallocKit_A2>rarea_rep_extPC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=RMallocKit_A2?rgroup_rep_extPC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=RMallocKit_A2:rnr_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocKit_A2Acell_read_shadow0C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC59OSSVerify5KrLib5Plain:RMallocRep?rshadow_rep_extC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7shadow0C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z8inj_succc59OSSVerify5KrLib5Plain=RMallocKit_A2>rnr_regions_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep8ticks_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree7ptrs_inC1?~~~~~~~~~~~~~~~C35stdpp8fin_maps:map_deleteC35stdpp4base6deletec59OSSVerify5KrLib5Plain=RMallocKit_A2;rdr_regionsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=RMallocKit_A2>rdr_lookup_oldC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;set_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:set_shadowC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=RMallocKit_A28rdr_concC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=RMallocKit_A2>rdr_lookup_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep8lr_lo_geC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decC59OSSVerify5KrLib5Plain:RMalloc_fpCrreserved_disjoint2C1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphC47Corelib4Init5Logic5proj1c59OSSVerify5KrLib5Plain=RMallocKit_A2:rdr_shadowC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZC59OSSVerify5KrLib4Spec6Malloc5r_havC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_tickC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2leC59OSSVerify5KrLib4Spec6Malloc6r_havpC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N7compareK47Corelib4Init9Datatypes:comparison03C35stdpp4base:decide_relC35stdpp4base6decideC59OSSVerify5KrLib4Spec6Malloc9put_groupC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4ghdr01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem:length_le4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame:munch_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame6insideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;munch_writeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame:wmono_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;wmono_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep9s_staticsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells7cell_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells5csizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step>rw_cells_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells6cbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cell_updC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5s_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain<RMallocKit_B@rmrep_ctx_frameWC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@set_mmap_counterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7upd_ctxC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Section PEXT.
Variables (st st' : mstate) (P : N -> Prop).
Hypothesis HP : ptrs_in P st.
Hypothesis Hconc : forall q, P (fst q) -> conc st' q = conc st q.
Hypothesis Hctx : ctx st' = ctx st.
Hypothesis Hmetas : s_metas st' = s_metas st.

Lemma rpw_extP p : optr_in P p -> pw st' p = pw st p.
Proof. destruct p as [q|]; cbn; intros H; unfold pw, oconc; [rewrite Hconc by exact H|]; reflexivity. Qed.

Lemma rget_meta_rec_extP g : get_meta_rec st' g = get_meta_rec st g.
Proof. unfold get_meta_rec. rewrite Hmetas. reflexivity. Qed.

Lemma rmeta_cells_extP g : meta_cells st' (get_meta_rec st g) = meta_cells st (get_meta_rec st g).
Proof.
  destruct HP as (_ & _ & _ & _ & _ & _ & _ & H8 & _). destruct (H8 g) as (X1 & X2 & X3).
  unfold meta_cells. rewrite !rpw_extP by assumption. reflexivity.
Qed.

Lemma rmrep_ctx_extP m : rmrep_ctx st m -> rmrep_ctx st' m.
Proof.
  intros H. destruct HP as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & _).
  assert (E1 : rctx_head_cells st' = rctx_head_cells st).
  { unfold rctx_head_cells, rsecw. rewrite Hctx. rewrite !rpw_extP by assumption. reflexivity. }
  assert (E2 : actives st' = actives st).
  { unfold actives. apply map_ext. intros a. unfold active. rewrite Hctx. apply rpw_extP. apply (H6 (Z.of_nat a)). }
  assert (E3 : usages st' = usages st). { unfold usages. apply map_ext. intros. unfold usage. rewrite Hctx. reflexivity. }
  assert (E4 : unmap_seqs st' = unmap_seqs st). { unfold unmap_seqs. apply map_ext. intros. unfold unmap_seq. rewrite Hctx. reflexivity. }
  assert (E5 : bouncess st' = bouncess st). { unfold bouncess. apply map_ext. intros. unfold bounces. rewrite Hctx. reflexivity. }
  assert (E6 : ctx_tail_cells st' = ctx_tail_cells st).
  { unfold ctx_tail_cells, brk_word. rewrite Hctx. destruct (c_brk (ctx st)) as [| |rid off]; try reflexivity.
    rewrite (Hconc (rid, off)) by exact H7. reflexivity. }
  unfold rmrep_ctx in *. rewrite E1, E2, E3, E4, E5, E6. exact H.
Qed.

Lemma rarea_rep_extP m a ar : (s_areas st) !! a = Some ar -> rarea_rep st m a ar -> rarea_rep st' m a ar.
Proof.
  intros Ha (A1 & A2 & A3). destruct HP as (_ & _ & _ & _ & _ & _ & _ & H8 & H9 & _).
  destruct (H9 a ar Ha) as [Pa Pn].
  unfold rarea_rep. rewrite (Hconc a Pa). rewrite (rpw_extP _ Pn). split; [exact A1|]. split; [|exact A3].
  intros k Hk. rewrite rget_meta_rec_extP, rmeta_cells_extP. apply A2. exact Hk.
Qed.

Lemma rgroup_rep_extP m b gh : (s_groups st) !! b = Some gh -> rgroup_rep st m b gh -> rgroup_rep st' m b gh.
Proof.
  intros Hb (w8 & R & Hw8). destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H10).
  destruct (H10 b gh Hb) as [Pb Pg]. exists w8. rewrite (Hconc b Pb), (rpw_extP _ Pg). auto.
Qed.
End PEXT.

Lemma rbytes_at_agree m m' A bs : bytes_at psegs m A bs -> agree_on m m' A (Z.of_nat (length bs)) -> bytes_at psegs m' A bs.
Proof.
  intros (H0 & H1 & HB) AG. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  unfold mrd. rewrite (AG (A + Z.of_nat i)) by lia. apply HB. exact Hi.
Qed.

Lemma rwr_at_agree m m' A n : wr_at psegs m A n -> agree_on m m' A n -> wr_at psegs m' A n.
Proof.
  intros (H0 & H1 & HW) AG. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  unfold wview. rewrite (AG (A + i)) by lia. apply HW. exact Hi.
Qed.

Lemma rrw_cells_agree m m' A cs : rw_cells psegs m A cs -> agree_on m m' A (Z.of_nat (cells_size cs)) -> rw_cells psegs m' A cs.
Proof.
  intros [[Hwf HB] HW] AG. split; [split; [exact Hwf|]|].
  - eapply rbytes_at_agree; [exact HB|]. rewrite cells_bytes_length by assumption. exact AG.
  - eapply rwr_at_agree; eauto.
Qed.

Lemma ru64arr_agree m m' A ws : u64arr psegs m A ws -> agree_on m m' A (8 * Z.of_nat (length ws)) -> u64arr psegs m' A ws.
Proof.
  intros [HB HW] AG. split.
  - eapply rbytes_at_agree; [exact HB|]. rewrite u64s_length. replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws)) by lia. exact AG.
  - eapply rwr_at_agree; [exact HW|]. exact AG.
Qed.

Lemma ru8arr_agree m m' A bs : u8arr psegs m A bs -> agree_on m m' A (Z.of_nat (length bs)) -> u8arr psegs m' A bs.
Proof. intros [HB HW] AG. split; [eapply rbytes_at_agree; eauto| eapply rwr_at_agree; eauto]. Qed.

(* [comment removed for export] *)
Lemma rmrep_agree : forall st m m',
  rmrep st m ->
  agree_on m m' RMLOCK 4 -> agree_on m m' RLIBC 0x418 -> agree_on m m' RGOT_SSP 8 -> agree_on m m' RSSP_GUARD 8 ->
  (forall a ar, (s_areas st) !! a = Some ar -> agree_on m m' (conc st a) 4096) ->
  (forall b gh, (s_groups st) !! b = Some gh -> agree_on m m' (conc st b) 9) ->
  (forall rid r, (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> agree_on m m' (r_base r) (round_up_pg (r_len r))) ->
  rmrep st m'.
Proof.
  intros st m m' (WF & CX & GL & AR & GR & SH) AGL AGC AGS1 AGS2 AGA AGG AGR.
  split; [exact WF|]. split; [|split; [|split; [|split]]].
  - destruct CX as (C1 & C2 & C3 & C4 & C5 & C6). unfold rmrep_ctx.
    assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
    assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
    assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
    assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
    unfold RLIBC, RCTX in *.
    split; [|split; [|split; [|split; [|split]]]].
    + eapply rrw_cells_agree; [exact C1|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply ru64arr_agree; [exact C2|]. rewrite L1. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply ru64arr_agree; [exact C3|]. rewrite L2. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply ru8arr_agree; [exact C4|]. rewrite L3. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply ru8arr_agree; [exact C5|]. rewrite L4. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply rrw_cells_agree; [exact C6|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
  - destruct GL as (G1 & G2 & G3 & G4 & G5). unfold rmrep_globals, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RLIBC, RGOT_SSP, RSSP_GUARD in *.
    split; [|split; [|split; [|split]]].
    + eapply rrw_cells_agree; [exact G1|]. eapply agree_on_sub; [exact AGL| lia| cbn; lia].
    + eapply rrw_cells_agree; [exact G2|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply rrw_cells_agree; [exact G3|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply rrw_cells_agree; [exact G4|]. eapply agree_on_sub; [exact AGS1| lia| cbn; lia].
    + eapply rrw_cells_agree; [exact G5|]. eapply agree_on_sub; [exact AGS2| lia| cbn; lia].
  - intros a ar Ha. destruct (AR a ar Ha) as (A1 & A2 & A3). pose proof (AGA a ar Ha) as AG.
    split; [|split].
    + eapply rrw_cells_agree; [exact A1|]. eapply agree_on_sub; [exact AG| lia| cbn; lia].
    + intros k Hk. eapply rrw_cells_agree; [apply A2; exact Hk|]. unfold meta_cells. cbn [cells_size csize Nat.add length].
      unfold AREA_HDR, META_SIZE, NSLOTS in *. eapply agree_on_sub; [exact AG| lia| lia].
    + eapply rrw_cells_agree; [exact A3|]. eapply agree_on_sub; [exact AG| lia| cbn; lia].
  - intros b gh Hb. destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
    eapply rrw_cells_agree; [exact R|]. cbn. exact (AGG b gh Hb).
  - intros rid r Hr Hk. destruct (SH rid r Hr Hk) as [HWr HB]. pose proof (AGR rid r Hr Hk) as AG. split.
    + eapply rwr_at_agree; eauto.
    + intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
      eapply rbytes_at_agree; [exact Bt|]. cbn. eapply agree_on_sub; [exact AG| lia| lia].
Qed.

Section NEWREGION.
Variables (st : mstate) (m m' : mem) (x len : Z) (k : rkind).
Let rid := s_next_rid st.
Let L := round_up_pg len.
Let r0 := mkRegion k x len.
Let st' := fst (new_region k x len st).

Hypothesis MR : rmrep st m.
Hypothesis PT : ptrs_in (fun r => r <> rid) st.
Hypothesis FRr : (s_regions st) !! rid = None.
Hypothesis FRs : (s_shadow st) !! rid = None.
Hypothesis X0 : 0 < x.
Hypothesis XA : x mod 4096 = 0.
Hypothesis LEN : 0 <= len.
Hypothesis XC : x + L <= ATOP.
Hypothesis RF : ranges_free (live_ranges st) x L = true.
(* [comment removed for export] *)
Hypothesis AG : forall a, 0 <= a < 2^64 -> (a < x \/ x + L <= a) -> m' (wa a) = m (wa a).
Hypothesis ZF : k = RKGroup -> forall a, x <= a < x + L -> m' (wa a) = Some (b8 0).

Lemma rnr_regions : s_regions st' = <[rid := r0]> (s_regions st).
Proof. reflexivity. Qed.
Lemma rnr_lookup_new : (s_regions st') !! rid = Some r0.
Proof. rewrite rnr_regions. apply lookup_insert_eq. Qed.
Lemma rnr_lookup_old q : q <> rid -> (s_regions st') !! q = (s_regions st) !! q.
Proof. intros. rewrite rnr_regions. rewrite lookup_insert_ne by congruence. reflexivity. Qed.
Lemma rnr_lookup_inv q r : (s_regions st') !! q = Some r -> (q = rid /\ r = r0) \/ (q <> rid /\ (s_regions st) !! q = Some r).
Proof.
  intros H. destruct (N.eq_dec q rid) as [->|NE].
  - left. rewrite rnr_lookup_new in H. inversion H. auto.
  - right. rewrite rnr_lookup_old in H by exact NE. auto.
Qed.
Lemma rnr_conc q : fst q <> rid -> conc st' q = conc st q.
Proof. intros. unfold conc, get_region. rewrite rnr_lookup_old by assumption. reflexivity. Qed.
Lemma rnr_conc_new off : conc st' (rid, off) = x + off.
Proof. unfold conc, get_region. cbn [fst snd]. rewrite rnr_lookup_new. reflexivity. Qed.
Lemma rnr_shadow q : get_shadow st' q = get_shadow st q.
Proof. reflexivity. Qed.
Lemma rnr_lr_lo_new : x <= lr_lo r0.
Proof. unfold lr_lo, r0. cbn. destruct k; lia. Qed.

(* [comment removed for export] *)
Lemma rnr_old_disjoint q r : (s_regions st) !! q = Some r ->
  x + L <= lr_lo r \/ r_base r + round_up_pg (r_len r) <= x.
Proof.
  intros Hr. pose proof (In_live_ranges st q r Hr) as HI.
  unfold region_live_range in HI. unfold lr_lo. unfold PGSZ in HI.
  destruct (r_kind r); (pose proof (ranges_free_In _ _ _ _ _ RF HI); lia).
Qed.

Lemma rnr_regions_wf : rregions_wf st'.
Proof.
  pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
  assert (RFimg : ranges_free ref_reserved x L = true).
  { apply ranges_free_intro. intros b n HI. apply (ranges_free_In _ _ _ _ _ RF). unfold live_ranges. apply in_or_app. left. rewrite (rstatics_reserved _ RS). exact HI. }
  split; [exact RS|]. split; [|split; [|split]].
  - intros q r Hq. destruct (rnr_lookup_inv q r Hq) as [[-> ->]|[NE H]].
    + unfold r0. cbn. fold L. repeat split; try lia. exact RFimg.
    + exact (WR q r H).
  - intros q1 r1 q2 r2 H1 H2 NE.
    destruct (rnr_lookup_inv q1 r1 H1) as [[-> ->]|[NE1 H1']]; destruct (rnr_lookup_inv q2 r2 H2) as [[-> ->]|[NE2 H2']].
    + congruence.
    + cbn [r_base r_len r0]. fold L. pose proof (rnr_old_disjoint q2 r2 H2'). pose proof rnr_lr_lo_new. lia.
    + cbn [r_base r_len r0]. fold L. pose proof (rnr_old_disjoint q1 r1 H1'). pose proof rnr_lr_lo_new. lia.
    + exact (DJ q1 r1 q2 r2 H1' H2' NE).
  - intros a ar Ha. destruct (WA a ar Ha) as (r & Hr & REST).
    destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & P9 & _). destruct (P9 a ar Ha) as [Pa _].
    exists r. rewrite rnr_lookup_old by exact Pa. auto.
  - intros b gh Hb. destruct (WG b gh Hb) as (r & Hr & REST).
    destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10). destruct (P10 b gh Hb) as [Pb _].
    exists r. rewrite rnr_lookup_old by exact Pb. auto.
Qed.

Lemma rmrep_new_region : rmrep st' m'.
Proof.
  pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (RS & WR & DJ & WA & WG).
  assert (RI : forall b n, In (b, n) ref_reserved -> x + L <= b \/ b + n <= x).
  { intros b n HI. apply (ranges_free_In _ _ _ _ _ RF). unfold live_ranges. apply in_or_app. left. rewrite (rstatics_reserved _ RS). exact HI. }
  pose proof (RI _ _ ltac:(left; reflexivity)) as RI1. pose proof (RI _ _ ltac:(right; right; left; reflexivity)) as RI2.
  pose proof (RI _ _ ltac:(right; right; right; left; reflexivity)) as RI3.
  pose proof (round_up_pg_ge len) as LG. fold L in LG. atop_facts.
  assert (MR1 : rmrep st m').
  { eapply rmrep_agree; [exact MR| | | | | | |].
    - intros a Ha. apply AG; unfold RMLOCK in *; lia.
    - intros a Ha. apply AG; unfold RLIBC in *; lia.
    - intros a Ha. apply AG; unfold RGOT_SSP in *; lia.
    - intros a Ha. apply AG; unfold RSSP_GUARD in *; lia.
    - intros a ar Ha a0 Ha0.
      destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
      pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (rnr_old_disjoint _ _ Hra).
      atop_facts. apply AG; lia.
    - intros b gh Hb a0 Ha0.
      destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & SbA & RB0 & RBC).
      pose proof (lr_lo_group rb Kb). pose proof (rnr_old_disjoint _ _ Hrb). atop_facts. apply AG; lia.
    - intros q r Hq Hk a0 Ha0. destruct (WR q r Hq) as (B0 & _ & _ & BC & _). atop_facts.
      pose proof (lr_lo_group r Hk). pose proof (rnr_old_disjoint _ _ Hq). apply AG; lia. }
  pose proof MR1 as (_ & CX1 & GL1 & AR1 & GR1 & SH1).
  assert (Hconc : forall q, (fun r => r <> rid) (fst q) -> conc st' q = conc st q) by (intros q Hq; apply rnr_conc; exact Hq).
  split; [exact rnr_regions_wf|]. split; [|split; [exact GL1|split; [|split]]].
  - eapply (rmrep_ctx_extP st st' _ PT Hconc eq_refl). exact CX1.
  - intros a ar Ha. eapply (rarea_rep_extP st st' _ PT Hconc eq_refl); [exact Ha|]. exact (AR1 a ar Ha).
  - intros b gh Hb. eapply (rgroup_rep_extP st st' _ PT Hconc); [exact Hb|]. exact (GR1 b gh Hb).
  - intros q r Hq Hk. destruct (rnr_lookup_inv q r Hq) as [[-> ->]|[NE H]].
    +
      cbn [r_kind r0] in Hk. unfold rshadow_rep. cbn [r_base r_len r0]. fold L.
      split.
      * split; [lia|]. split; [lia|]. intros i Hi. unfold wview. rewrite (ZF Hk) by lia. discriminate.
      * intros o v Ho Hc. rewrite rnr_shadow in Hc. unfold get_shadow in Hc. fold rid in Hc. rewrite FRs in Hc. cbn [default from_option id] in Hc.
        rewrite cell_read_shadow0 in Hc. inversion Hc; subst v. split; [|lia].
        split; [lia|]. split; [cbn; lia|]. intros i Hi. destruct i; [|cbn in Hi; lia]. cbn [nth_error].
        unfold mrd. rewrite Z.add_0_r. rewrite (ZF Hk) by lia. reflexivity.
    + eapply rshadow_rep_ext; [apply rnr_shadow|]. exact (SH1 q r H Hk).
Qed.

Lemma rticks_ok_new_region : ticks_ok st -> ticks_ok st'.
Proof. intros H. exact H. Qed.

Lemma rptrs_in_new_region (P : N -> Prop) : ptrs_in P st -> ptrs_in P st'.
Proof. intros H. exact H. Qed.
End NEWREGION.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section DROPREGION.
Variables (st : mstate) (m m' : mem) (rid : N) (r : region).
Let st' := drop_region rid st.
Hypothesis MR : rmrep st m.
Hypothesis Hr : (s_regions st) !! rid = Some r.
Hypothesis PT : ptrs_in (fun q => q <> rid) st.
Hypothesis AG : forall a, 0 <= a < 2^64 -> (a < lr_lo r \/ r_base r + round_up_pg (r_len r) <= a) ->
  (RMLOCK <= a < RMLOCK + 4 \/ RLIBC <= a < RLIBC + 0x418 \/ RGOT_SSP <= a < RGOT_SSP + 8 \/ RSSP_GUARD <= a < RSSP_GUARD + 8
   \/ exists q rq, (s_regions st) !! q = Some rq /\ lr_lo rq <= a < r_base rq + round_up_pg (r_len rq)) ->
  m' (wa a) = m (wa a).

Lemma rdr_regions : s_regions st' = delete rid (s_regions st).
Proof. reflexivity. Qed.
Lemma rdr_lookup_inv q rq : (s_regions st') !! q = Some rq -> q <> rid /\ (s_regions st) !! q = Some rq.
Proof.
  intros H. rewrite rdr_regions in H. destruct (N.eq_dec q rid) as [->|NE].
  - rewrite lookup_delete_eq in H. discriminate.
  - rewrite lookup_delete_ne in H by congruence. auto.
Qed.
Lemma rdr_lookup_old q : q <> rid -> (s_regions st') !! q = (s_regions st) !! q.
Proof. intros. rewrite rdr_regions. rewrite lookup_delete_ne by congruence. reflexivity. Qed.
Lemma rdr_conc q : fst q <> rid -> conc st' q = conc st q.
Proof. intros. unfold conc, get_region. rewrite rdr_lookup_old by assumption. reflexivity. Qed.
Lemma rdr_shadow q : q <> rid -> get_shadow st' q = get_shadow st q.
Proof. intros. unfold get_shadow. unfold st', drop_region. cbn [s_shadow set_shadow set_regions]. rewrite lookup_delete_ne by congruence. reflexivity. Qed.

Lemma rmrep_drop_region : rmrep st' m'.
Proof.
ltac2:(KReplay.run1 (kr_t_RMallocKit_A2 ()) ["CANSEC1"; "DROPREGION"] "p'0p'1h04__x1h12L0h21Hh37__arithh44__ffh58__varmaph65__with74__x2h81rh94__x3h:4__x4h;4__p1h<1ah=4cstrh>5cstr0h?3Ha0h@5cstr1hA5cstr2hB2H0hC4__x5hD4__x6hE6__sat4hF2_HhG2HahH6__sat2hI6__sat3hJ1ni001nhK1qhL2rqhM1ohN4__x7hO2arhP1bhQ1ei011ehR2ghhS1khT2H2hU2NEhV3_H0hW3_H1hX6__sat1hY1vhZ1xi021xh[2H1h\2H3h]2Hqh^3_H2h_3_H3h`3_H4ha3_H5hb3_H6hc3_H7hd4__x8he4__x9hf2a0hg1ihh1phi2w8hj2H4hk3Ha1hl3NE0hm6__sat6hn6__sat9ho2r0hp2r1hq2r2hr1yhs2DDht3H10hu2H5hv2H6hw2H7hx2Hbhy3Hrahz3Hrbh{3P10h|2P9h}3RB0h~3RBCi034RESTi047__sat10i056__sat5i062rai072rbi083ridi094rid1i0:4rid2i0;1si0<2A1i0=2A2i0>2A3i0?3AGAi0@3AGCi0A3AGRi0B2ARi0C5ATOPRi0D2B0i0E2BCi0F3BCqi0G2Bqi0H2Bti0I2C1i0J2C2i0K2C3i0L2C4i0M2C5i0N2C6i0O2CXi0P2Cai0Q2Cbi0R2DJi0S2G1i0T2G2i0U2G3i0V2G4i0W2G5i0X2GLi0Y2GRi0Z3H1'i0[3H11i0\3H12i0]3H13i0^3H14i0_3H2'i0`2H8i0a2H9i0b2HBi0c3HWri0d2Hci0e5Hconci0f2Hki0g3Hk0i0h2Hoi0i2Hvi0j3Hw8i0k2Kbi0l2L1i0m2L2i0n2L3i0o2L4i0p2NKi0q5OTHERi0r2Pai0s2Pbi0t1Ri0u4RBALi0v3RFri0w3RL0i0x2RSi0y2SHi0z3Sa0i0{3Sa1i0|3SaLi0}3Sb0i0~3Sb1i103SbAi112WAi122WFi132WGi142WRi157__sat11i161gi172k0i181mi192q1i1:2q2i1;2sci1<3offp%0p%1p%2p%3p%4p&0p&1p&2p&3p;3p;2p;1p;4p;6p;9p;8p;5p;;p;:p;7p;<p;Bg02E7k31|Tg02F2k21{Tg00iak31QTg02G3k21aTg02H6k31}Tg02I7k21wTg02J9k21rTg00YoR0j20Tg03G2k21jTg00EPk11LTg00=1k416Tg003Ek41\Tg02K;k11^Tg02Llj13Tg00?gj16Tg01BSj1UTg02\Bj1`Tg02]8j1jTg034dk12aTg01FJR1j21Tg038jj1FTg00ZJk22=Tg00HMk42:Tg00Hkk628Tg00Zjk11]Tg00K]j6rTg00DLk20vTg001Vj38k11[Tg020Ij1GTg01NHj22Tg00\Yk11vTg03ofk22yTg00BEj2ETg033fk12tTg01Eej1NTg040gk313Tg00Ogk11lTg00P[k12`Tg00>ij2KTg00Q\k12]Tg00RYk12\Tg00SZk12ZTg00T[k12TTg00U^k21fTg00VUk12RTg00J`k20NTg00WKk11eTg00XBk11dTg00Y9k11cTg00[bk10<Tg00]Rj1wTg03lhk22FTg002Nk61ZTg01XSk409Tg01RIk40ITg00D2j2]Tg011>k22;Tg01Doj4tTg0153k129Tg017^k127Tg01;Hk126Tg01>:k125Tg01Ckk124Tg013\j1XTg014;k222Tg01Z<j2qTg02Mck221Tg00@Lk120Tg00@jk11~Tg012CR2j1YTg00AMk207Tg02NBk41@Tg02N^k41?Tg0160k236Tg00C:j1bTg018Zk235Tg019Tk10KTg01<Hk234Tg03T0k133Tg041nk11yTg042lk22~Tg02l`S00k22}Tg02m@j2kTg02O=k22|Tg02O`k31xTg01^jj4TTg01_Qk11;Tg03Xdk12{Tg03YBk22zTg03Yck31uTg02Uhk21tTg00cBk11YTg00^Ik12xTg01a2k12wTg01aPk12vTg01b^k21sTg01b;k21XTg00Dnk12uTg01e3k22sTg01eUk22rTg01fAk32nTg01f`k42mTg0304k30ETg02P=k12jTg03QDk62iTg043Lk41qTg02nSk30>Tg03U4k22hTg01C1k22gTg03U\k32fTg03DHk21TTg03V@k32dTg01NdR3j2:Tg01XmS01k21RTg01]1j4QTg02P[l9xTg02Q`j6iTg00lTk204Tg02@<k31oTg02Rhk61nTg02Snk61mTg03^Sk82bTg00`Vk10STg01?nk10`Tg02U3k12_Tg044Uk30pTg02?^k11kTg045;k42^Tg045^k60fTg00ILk12[Tg03Vck62YTg01LPj5nTg03Wck82STg046Gk31gTg037Yk30jk20xTg024eR4j1}Tg036Uk22QTg03NEk31CTg0376k10yTg038Jj2DTg03@4k21DTg03@Uk20ZTg03A2k21KTg03AYk21FTg03B@k21JTg03Bfk21GTg03CLk21HTg00j`k12PTg00^ik11PTg01MOk10|Tg01O@k20\Tg00dck20]Tg01@ck12OTg01A^k22NTg02Wfk22LTg00_^k12VTg00aKk12JTg00bCk12WTg03_Zm;2XTg03ZLk62ITg01UNj4{Tg03[Mk21bTg01VNk20{Tg01W8k214Tg01WVk10RTg03`am:2HTg02[Ak40kTg046bk22GTg01nZk40zTg02XRk215Tg02YMk210Tg02ZGk12ETg00ecj3ZTg02=Qk62DTg02<Ik62kTg03ePk72lTg03Nnk31`Tg0000k31UTg031Uk32CTg02L5k12BTg01GGk42oTg01H:k42pTg01gRm<1VTg02VQk30dTg02W:k20sTg01`6k22@Tg01cAj4mTg01h7k70HTg01h[k80eTg01`Tk40nTg01clk30uTg01dOk71=Tg02^4k62?Tg03ELk72>Tg028^k12<Tg02Bhm<30Tg02BBmB31Tg01YGk432Tg02bMR5f0R6+0vp>1Af5R7g00FWR8P5f4R9f3R:f2R;f1R<Er;86p=Og00GoR=/:6p=A%66#6p>0F%66#6#6#6p>17g00G5R>1D<6;8=p=;11;</26p=5g03QhR?@1`<6p>1>g01mZR@g01n:RA786,0<p>0}12=</06p>0[10<6,0;p=HA88<6#Gp=J%`6#jp=<12:;12<6'kp>0CB1U8>6p=\B2C8>6p=712=6p=4g02f:&2B6g02g238p=W10<6,0;,0:,09p=?21R56p==10<6,0;,0:p>1:1E;<=8>6p>0GB1`?<6=8@Ap>0D%N6#Np=y%N6#N#N#Np=p%66#6#6#6#6#6#6#6p>0c%66#6#6#Up=R12<6,0;p>0B%j6,1<p>1p%F6,2<p>0r12;</k6p>0q12;</06p>0Q1D;<=8>=/06,0:p=|P8P5P9P:P;P<Er20v56587p>0@P8P5P9P:B1U8>;P<Er=876p=h1D79=8>=11<6,2;,0:'0p>0211:;/2</06,09,07p=f11<6,2;p>0=12;</06,0:,09p>0oB1U8><=886#Gp=SA88<6p>0wP8P5P:P;P<P6Erp>1i20v5698;<p>1z%G</06p>0i1D;<=8>=/06p=_11:;/2</06p>0bP910:;P<P6H0Ip=of7R?f6RB119:/2;1D<6=8>='0,07'0'0p>0A11:;/2</06,09,07,0Bp>2A11:;/2</06,09p>1EPBP7P9P:P;P<P6H0IH0Ip>0h%66#Up>1_g01IcS02P;P<P6H2op>0Y%N6#6p=MQ02P;P<P6H2pp>0XQ02P;P<P6Ctp=a%X6#Xp>23%X6#X#X#Xp>0:g01JXRC?8<6p>0WPCP9P:P;P<P6J1Zp=vA8>6=p>06A8><6p=>1]>6p=CPCP>P6P2P<P;P:P9P7PBP?f8RDN<1Vp>1<21t>6p>0;B0d><6p=Lg01k`REg02gjRF-0s<;Z6p>0t22@>6p>08P;g01iaRGg01j@RHPHg01j`RIP>P<g02DPRJP6Cmg01k@RKK0Hp>1WP:PGPHPHPIP;P<P6L0ep=BA8@6Ap>2qP>P;P<P6H0np=z21s>6p=eP;PGPHPHPIP>P<g01lLRLP6CmPKK0Hp=@P>P<PLP6Cmp>0UP;PGPHPHPIP>P<g01m3RMP6CmPKK0Hp>0OP9PGPHPHPIP:PGPHPHPIP;PKK0HP<P6L0ep=PPBPGPHPHPIP7P9P:PGPHPHPIP;P<P6L0eL0ep>0P12:;1:<6'0p>0?%66#Np=V%N6#6#6#6p>2e21X>6p=I21X>6:0u><p>03P9PGPHPHPIP:PGPHPHPIP>P;PLP<CmPKK0HP6K1=p>0L1:<6,0;p=9B0d>;<:0d>:00sF=ZE6p>0V20s;F20s<F=ZE65ZEp>12P>P>P9P:P;H0nP<P6H0np=gP<PGPHPHPIP6J2?p>18B0u><6p=[P;PGPHPHPIP<P6K2>p>0aP;PGPHPHPIP<P6K1=p>2c12<6,k;p>1111<6,:;p>0T12;</06,0:p>1S&2<6#Yp=^P:PGPHPHPIP>B0u>;<PLP6CmPKK0Hp=dg00fCS03?Z<6p=lQ03&1P<;Z6p=cPCP>P>P>P2P2P7P9P:P;P<P6N<30p>19P>P>P>P>P>P>P1P6P<P;P1P:P9P7PBP?PDf9R1NB31p>0_P>P>P3P?P3PBP7P9P:P;P<P6N<1Vp>0gP:PGPHPHPIP>P;PMB0u><6CmPKK0Hp>0~B0E;<6:0E9:p>0J129:10<6,0;'0p>1h1D<6,2=p>00B0d><6:0d>;p>1BP>B0u>;<PLP6Cmp>1NP>P<PJP6Cmp>0lP7PGPHPHPIP9PGPHPHPIP:P;K1=P<P6L0ep>0mP?PGPHPHPIPBPGPHPHPIP7P9PGPHPHPIP>P:PMP;CmPKK0HK1=P<P6L0ep=sP8P>P6P4P<P;P:P9P7PBP?PDN<1Vp>1M12=;1:<6'0p=~P>P<PMP6Cmp>1IQ02P:P;Q03?Z<6Ctp>01g01RdS04,16p>0^Q02P:11;<P6Ctp=u207<6$1Pp>0MQ03Q03?Z<67Z;p>1OB0d><600sFp>2MAZE<6p>2KP>P9P:P>P;P<P6H0nH0np>2UQ02P;P<P6H32p>05p,2MRp,2rcRFp,2stRMp,1mR441|P021{FMS05B1QFM4S0621aF4S07B1}FM4S0821wM4S0921rM4S0:'0S0;'0S0<'0S0='0S0>p,3st'RKp,2m'RJ61|FRLP6Q05Q0>P0Q06Q0=PLP6Q06Q0=P0Q07Q0<PLP6Q07Q0<P0Q08Q0;PLP6Q08Q0;P0Q09Q0:PLP6Q09Q0:fAS0?Q05P021jFMS0@&1L5R3P8g00N9R2g00NkRNP5H16ROP8P2PNP5H1\RPP<&1^MRQ&1A6RREOS0A%3<RS#AS0Bg00F2RT#6RU#6S0C#6S0D#6RV#6S0E#6S0F$0FS0G$17S0H#URW,;SS0I%`<RX%jXRX&2aFRY55SS0J21>SX+0}+0[3HRZ[^85`088S0KP3POPPP:PQ&1A;R[EOS0LP3POPPP;PQ&1A<R\EOR]1J7:R^%37S0M%<7S0N'1S0O%F:%3:R_%`:R`#jRa'1Rb%F7RcH0C[Rd[[^q5`0:8^p5`098S0P22=8>Reg00h3Rf&1LfS0QPePfg000aS0RP8P2P>g00NRRgH2:S0SP8P2PNP>Pgg00OIJ28S0TPfH16S0UQ0RQ0SQ0TPfH1\S0VP<&1]MEr20vf6S0W38RgP3POPP%\:RNPQPREOS0X%7:R2#4S0Y%<6Rh952WS0Z1;2WS0[%W6Ri#GRj%F6Rk%36Rl/12S0\'2D?Rm'0X85#=Rn[]O]<S0]g00hjRo&1LoS0^PePoQ0RQ0SQ0TPoH16S0_Q0RQ0SQ0TPoH1\S0`P<&1vMEr20vo6S0a38RpQ0XPiQ0Y%UVRV=52hS0b1;2VS0cH1:R2'0X85#=S0d[]R^PeS0e'0S0f'0S0g'0S0hPLP6Q0@Q0hP0Q0KQ0gPLP6Q0KQ0gP0Q0PQ0fPLP6Q0PQ0fP0Q0]Q0ePLP6Q0]Q0e%\6Rqp,3ridRr'J22y<6W]XKe1J6rXK8RsPqO11EM<:0GK<[^Kef:RqPrp,1rRtp,2HrRuO3%3tRv#AS0i1;vWS0j%`tS0k#4S0lQ0k#jRw,1vS0m/2YS0n20DvwS0o'0S0p'0S0q'0S0r'0P0Q0iQ0rPLP6Q0iQ0rP0Q0jQ0qPLP6Q0jQ0qP0Q0lQ0pPLP6Q0lQ0pP0Q0nQ0oPLP6Q0nQ0o&2tF%NTS0s#NS0t#yS0u#yS0v#p#pRL#6#p#p$17$0c$0c#R/2YS0w%NL#p#p$17$0c$0c#RS0x80BYQ0A1J;rRLfLS0yP:P;PrPtP<PuP6O7WUW]XL5XK8Q0A%3;%`;+1p%FtS0zQ0m00r;40q\L[^L5^K821{FKB1QFKJS0{21aFJS0|B1}FKJS0}21wKJS0~21rKJS10'0S11'0S12'0S1321jFKP3POPPP<&1^KRuPREOS14PZ[^85`088RZP3POPPP:PuP[EOR[P3POPPP;PuP\EORxPd[[^q5`0:8^p5`098RdQ0QPePfQ0UQ0VP<&1]KS15ErQ0W38RyP3POPPPNPuPREORN/0mX85#=[^Of^<eRmQ0^PePoQ0_Q0`P<&1vKS16ErQ0a38S1710N2X85#=[^Ro^PeRN'0R2'0RzfQS18PZPzQ14B13;<610L]P01J:rS19Q0L%A_P_PW20D_a:0QbY-0[`C|P61J7rP3POPPPBPQP7J0@R`fUS1:P?PBP6O3W2WFP<P6O2n2001000000120000000b<W]XL5XK8PdP2B13B7;1JBrS1;/0`P01J?rP3POPPP?PQPBJ0@S1<%3?S1=%`?S1>#jS1?'1S1@Q0O00r?80qcP61J1rRcP3POPPPqPQP1J0@R`B131DBP3POPPP1PQPDJ0@,0cP01JqrP`f<R`#3S1A%``S1B#jS1C'1S1D%Fq%3qS1E%<q%F`3540qP61J`rP3POPPf=S1FPQP`J0@fZS1Gf@S1Hf?S1If>S1JQ1FP7P6PqO7Y0_WFP<P6O2n2001000000120000000b<Y0ZWFP<P6O2n2001000000120000000b<XU^XTxX[[Xq5Z1:8Xp5Z198PmPNfHS1KP;P<P6O3PnQ01P5P3POPPP9PQPREhS1L%79Rn#4S1MA5nWhS1N1;nWS1O11lnS1P:0BjkD?X85P3POPPP7PuPREhS1Q%77RN#4S1RPNPWPhPNPWPjPkPlPNJ02EfX85#=P6P3POPPPBPQPREhS1S%7BRm#4S1TA5mWhS1U1;mWS1V11lmS1W:0BjkD?P0P3POPPP?PQP\EhS1X%7?R\#4S1YA5\WXS1Z1;\WS1[%W<S1\#GS1]%F<11S\S1^'2D?P3POPP%\1RSPuPREOS1_%71R[#4S1`P[PWPhP[PWPjPkPlP[J02EfX85#=P6P3POPPPSPQ&1A:S1aEOS1b%7qRS#4S1c%<9S1d95SWS1e1;SWS1f%W9S1g#GS1h%F9%39S1i/1SS1j'2D?p,2PTS1k&1lMRx$2`,KsS1l&2]x,KsS1m&2\x,KsS1n&2Zx,KsS1o&2Tx,KsS1p21fM6,Ks`1;>S1qg00g8R^p-0Rc&2RxRxg00GSR2P2PsP<O1n01102000300002010811<Q0R20NM6Rd$1e,Ks&1dd,Ks&1cd,Ks3H_16S1rPs%\;RdO1Rb&0<<,KsRa'0\g^Of^<e%w<,KsR_,0b\p^Ro^Pe'0D?D?S1sP0Q1lQ1mQ1nQ1oQ1pQ1qP^PcPxP2P21J<rn01102000300002010811<S1tQ1r1JdrRd/0a\g^Of^<eS1u10d_\p^Ro^PeS1v'0S1w'0S1x'0S1y'0S1z'0S1{'0S1|'0S1}'0S1~P3POPPQ1JPuPREhS20Q1J#7Rp#4S2111pWS22Ph1;pWS23B0=klp7HjI0oX85#=P6Q1lQ1~P0Q1mQ1}P3POPPfBS24PuPREhS25Q24#7Rd#4S2611dWS27Ph1;dWS28B0=kld7HjI0oX85#=P6Q1mQ1}P0Q1nQ1|P3POPPfFS29PuPREhS2:Q29#7R_#4S2;P_PWPh1;_WS2<B0=kl_7HjEfX85#=P6Q1nQ1|P0Q1oQ1{P3POPPfJS2=PuPREhS2>Q2=#7Rg#4S2?PgPWPhPgPWPjPkPlPgJ02EfX85#=P6Q1oQ1{P0Q1pQ1zP3POPPfNRaPuPREhS2@%7aRx#4S2APxPWPhPxPWPjPkPlPxJ02EfX85#=P6Q1pQ1zP0Q1qQ1yP3POPPfRS2BPuPREhS2CQ2B#7R^#4S2DP^PWPhP^PWPjPkPlP^J02EfX85#=P6Q1qQ1yP0Q1tQ1xP3POPPfVS2EPuPREhS2FQ2E#7Rb#4S2GPbPWPhPbPWPjPkPlPbJ02EfX85#=P6Q1tQ1xP0Q1rQ1wP3POPPQ1G#\S2HPuPREOS2IQ1G#7RL#4S2JPLPWPhPLPWPjPkPlPLJ02EfX85#=P6Q1rQ1wP0Q1uQ1vP3POPPf^S2K#\S2LPuPREOS2MQ2K#7S2N#4S2OQ2NPWPhQ2NPWPjPkPlQ2NJ02EfX85#=P6Q1uQ1vP<f`R]f_RzQ2KO31S]rRZ&0<zS2P,Ks'0P0faS2Q/SrS2R&0<],KsP3POPPfcS2S#\S2TPuPREOS2UQ2S#7S2V#4S2WQ2VPWPhQ2VPWPjPkPlQ2VJ02EfX85#=P6Q2T00wrS2X#GS2YQ2S$0<,KsP5P3POPPffS2Z#\S2[PuPREOS2\Q2Z#7S2]#4R{Q2]/1WR|PhQ2]/;WR}Q2]:0=kl7HjI0oX85PzP3POPPfeS2^#\S2_PQH1iR~B1z36]S2`P{P|%<]R|%W]S2a#G%F]%3]S2bQ2]40=5H}I0oXM3B1z3~zS2cQ2^#7S2d#4S2eQ2dPW%<zS2fQ2d%WzS2g%FzS2h%3zS2iQ2d40=+0i7_WH0bf[S2jQ1GDoPOPPQ2_PuH1iRuQ2_02F<R}J1ZH09WFY0rP<P6O2n2001000000121000000bfWcW|P<P6O2n2001000000121000000W2WbP<P6O2n2001000000121000000W2WaP<P6O2n2001000000121000000W2W`P<P6O2n2001000000121000000W2W_P<P6O2n2001000000121000000W2W^P<P6O2n2001000000121000000W2WWP<P6O2n2011000000121000000W2WVP<P6O2n2011000000121000000W2WFP<P6O2n2011000000121000000bhY03WyP<P6O2n2001000000121000000W2Z065P<P6O2n2001000000121102000bQXGyXOfX<eQ17fGS2kP;P<P6O3Q0dQ01P5Q1LPiQ1MA5nVhS0d1;nVS2lD?X85Q1QPiQ1RPNPVPhPNPVL0AX85#=P6Q1SPiQ1TA5mVhS1R1;mVS1QD?P0Q1XQ1\Q1YA5\VXS2m1;\VS2nH1:Q1_PiQ1`P[PVPhP[PVL0AX85#=P6Q1bQ1gQ1cQ1d95SVS1`1;SVS1_H1:Q1kQ1sP0Q1lQ1~Q20PiQ2111pVS20/2h1;pVS2oD?X85#=P6Q1lQ1~P0Q1mQ1}Q25PiQ2611dVS25/2h1;dVS2pD?X85#=P6Q1mQ1}P0Q1nQ1|Q2:PiQ2;11_VS2;/2h1;_VS2:D?X85#=P6Q1nQ1|P0Q1oQ1{Q2>PiQ2?PgPVPh1;gVS2?K2AX85#=P6Q1oQ1{P0Q1pQ1zQ2@PiQ2APxPVPhPxPVL0AX85#=P6Q1pQ1zP0Q1qQ1yQ2CPiQ2DP^PVPhP^PVL0AX85#=P6Q1qQ1yP0Q1tQ1xQ2FPiQ2GPbPVPhPbPVL0AX85#=P6Q1tQ1xP0Q1rQ1wQ2IPiQ2JPLPVPhPLPVL0AX85#=P6Q1rQ1wP0Q1uQ1vQ2MPiQ2OQ2NPVPhQ2NPVL0AX85#=P6Q1uQ1vP6P]PzQ2KO3%wzS2O,Ks,0ZP0Q2R%w]S2M,KsQ2UPiQ2WQ2VPVPhQ2VPVL0AX85#=P6Q2YQ2S#w,KsP5Q2\PiP{Q2]/1VRZ/2hQ2]/;VRLD?X85PzP3P~Q2`Q2aP{12Z|PLD?XM3Q2cQ2gQ2eQ2dPVQ2fQ2d/;VI1EQ2jQ1GDoPuP}J1ZH09WFY0sP<P6O2n2001000000121000000b<W{WcP<P6O2n2001000000121000000W2WbP<P6O2n2001000000121000000W2WaP<P6O2n2001000000121000000W2W`P<P6O2n2001000000121000000W2W_P<P6O2n2001000000121000000W2W^P<P6O2n2001000000121000000W2WWP<P6O2n2011000000121000000W2WVP<P6O2n2011000000121000000W2WFP<P6O2n2011000000121000000bhY03WzP<P6O2n2001000000121000000W2Z075P<P6O2n2001000000121102000bQWxXRoXPeH0IK0hDoQ0{Q13PMPKPsQ1kfCS13g01Hl&1lK']PJP0Q02P4g01KVS0{22;FMS17CtS2eQ0{%NUS2g#6S2c$0FS2a$1_S2`'1S2\&29MS2W60Y4S2UQ0{Q0t#6Re#M#RS2J'1S2I&27MS2G60Y4S2FQ0{Q0s#6S2D#NS2C#6#M#RS2A'1S2@&26MS2>60X4S2qQ0{Q2C#N#M#RS2r'1S2s&25MS2t60X4S2uQ0{%6e#M#RS2v'1S2w&24MS2x5a4S2y'0S2z'0S2{'0S2|'0S2}B1QFMJS2~fbS30Q2eQ2}P0Q2UQ2|Q2~P6Q2UQ2|P0Q2FQ2{Q2~P6Q2FQ2{P0Q2qQ2zQ2~P6Q2qQ2zP0Q2uQ2yQ2~P6Q2uQ2yg01K7Re%XeS31#XS32#XS33#XS34#XS35#XS36#XS37#XS38#XS39#X$23$0:$0:$0:$0:$0:R}$0:$0:S3:$0:$0:Ru+22RL,qCRZ20W6uXJCR|PuP|1]CuPZ221ueDvR{Q0F$20S3;$1~R~PCP~%Y6S3<-1fM-07MXgCRbPLH1@'qPCP~PbPLH1?DvQ2W,q~S3=00WuS3>eQ3>PZP|P{PCP~Q3<-36M#bXgCR{PLH1@,q~PCP~P{PLH1?DvQ2G,q~S3?00WuS3@eQ3@222e}R~,qCRL20W6}XJCR{P}P{1]C}PL221}eDvR|Q0D$20S3A$1~RZPCPZQ3<-35M$0KXgCRbP~H1@'qPCPZPbP~H1?DvQ2>,qZS3B00W}S3CeQ3CPLP{P|PCPZQ3<-34M$0KXgCR|P~H1@,qZPCPZP|P~H1?DvQ2t,qZS3D00W}S3EeQ3EQ0k$33S3FQ0k/2wS3G&1ytS3HQ0z,2vS3I22~w=S3J&06wRt%GtS3K+2}S3LQ00PtQ3KQ0mQ0H#6#RQ0C#NS0H#N$0F$0c#RS3MPvH0CS3NQ0mQ3M%6T#y$0F#M$0c#RS3OPvH0C'0S3P/ktS3QP6Q3PQ3EQ3D#YR~Q0E#US3R'>R|&1[CR{&1[>S3S%Y<Q3<'>20W<622|<641xXrCXZCRLQ3DP~%C~P}Q3RQ3R#CRbN91<S3TP7CTS3UP|Q3CQ3B#YR^Q3R'>RxP{Q3SPLQ3BP^%C^P}Q3RPbN91<S3VP?CTS3WPxQ3@Q3?#YRbQ2D#6S3X#6S3Y$1_S3Z'>RgP{Q3SPLQ3?Pb%CbPuQ3ZQ3Z#CR_N91<S3[P1CTS3\PgQ3>Q3=#YRdQ3Z'>RpP{Q3SPLQ3=Pd%CdPuQ3ZP_N91<S3]f;R_CTS3^PpQ3?$1;RL%4bRbQ3D$1;R{%4~R~Q3=$1;RS%4dRdQ3B$1;R[%4^R^&2{T-2z>S3_Q31$0;S3`61u>21t>eS3a'LS3b&1YERe+0t&2xERE&08<S3c&2w>R\&2v>RX21s>TRm21X>=RN61WXS3d&2uHRnQ3dCB22sXIRyP6P;1]@A22r6;$2qdB2n>=<H2mRAb4b5b6X0>S3e&066S3f&06<[^0>S3gP6PwP1O2b3bAb@b>b=b1b1b1b180EtXQtP6O1Q3KQ3PPvPwfOS3hQ3UP|Q3WPxQ3\PgQ3^PpPSPdPLPbP[P^P{P~Q33$0;S33Q32$0;S32Q3`'LS3i'LS3j00tePE&2j>R@&08;S3k7z<P\PXPXPGPHPHPIQ3dJ2iPnPXQ0s#eRI=@XmPnPXPX20UNIPnB0OXNmDPK0PPyPAb4b5b6X0>X7>S0sQ3fg02kc[12;<S3f%4:S3d%A:S3l[[[^0>^7>S3mP6Q0kPwP1Q1Ff]S3nO5b3bAb@b>b=b1b1b1b1H1q80>tWJP6O1n200110;00021110111100c0;Q3Qg02_TS3oP6P6Q3oQ0E#y#RS0E'1S3pH0?p,2AGS3qP<Q3UP|Q3WPxQ3\PgQ3^PpPLPbP{P~PSPdP[P^%UURHQ0F#URG+2hS0F%AHS3r%4G22gHGS3s#A[S3t[S3u%4HS3vB2fHG<V2WGS3wQ3vQ3s#4\2]GS3vP<g03FLS3x21T=H']Q3reO1S3rQ3tPePEQ3cP\PXPXPX%6T#M#p#V#V$2e#RR2#IS3yPmQ3yQ0E+03S3z:0OXmI0LS3{PnPXPXPNPm%IHQ3;62d>:0OXmI0LS3;CBPyPAb4b5b6X0>P2P6P6Q0E,12RHH0?S3|%4<S3}Q3s79<S3~[^0>P6Q1FP`O2b3bmc05bmbAb@b>b=b1b1b1b1Q3UP|Q3WPxQ3\PgQ3^PpPSPdPLPbP[P^P{P~Q34$0;S40Q3j'LQ33Q32Q3`Q3a'LS3`'LS41'LQ35$0;S35Q33Q3aPeH0V412S42PE&089S43P;P@P<&08:S44DgS45P\PXQ3{PnPX218XBS46Q0C#eS47,[IS48Q3M#I5@XQ3O#I=@XI60aX62cXQ47>1WXN60aXPnPX%eURU9@XIS49PnB0OXmUQ48=@Xm60aXS4:K0PS4;CBPyPAb4b5b6X0>X7>X9>X:>X;cQ3|11:9S4<Q3MQ3OP:H0C,07&069'k129:1::9117B<11:S3O[[S3M[^0>^7>^9>^:>^;cP6Q3NPwPvQ0zPqP1P_P`O8b3bAb@b>b=b1b1b1b1g02^XS4=Q4=Q0C#US0C60T<80Q<S4>Q3oP<P<Q3pH0?S3pg02`OS4?Q4?Q0D#URG60T<80Q<S4@g02aMS4AQ4A>0T<G80Q<S4BQ0APkP:11lhS0A,::H1SXL5#=XK8S4C-1R8S4D'kS4E'kS4F'kS4GQ3pQ4FQ3UP|Q3WPxQ3\PgQ3^PpPLPbP{P~PSPdP[P^PePEQ3cP\PXQ3{PnQ3{CBPyPAb4b5b6X0>Q3|P2P<P<PHH0?S3^[^0>P6PqP1O2b3bAb@b>b=b1b1b1b1Q3pe40>40EO4WGX<>P4PJQ3oQ0ECQRhePh%6T#M#p#V#M#V#y#RRhQ175aJQ2`,1hS3oQ2W60YJS3|Q2J,1hS3\Q2G60YJS3WQ2A,1hS3UQ2>60XJS4HQ2r,1hS4IQ2t60XJS4JQ2v,1hS4KQ2x5aJS4L'0S4M'0S4N'0S4OP4PJPhQ17fIS4PP4PJP2Q0EPhQ17#^S4QP6Q3EP|Q3TP9CTS3TP|Q3CPxQ3VPBCTS3VPxQ3@PgQ3[PDCTS3[PgQ3>PpQ3]PqCTS3]PpPLPbP{P~PSPdP[P^PePEP@P\Q3y%IhS3>5@XPyPAb4b5b6122hP6b3bAb@b>b=b1b1b1b1Q3TP|Q3VPxQ3[PgQ3]PpPLPbP{P~PSPdP[P^PePEP@P\Q3>Q2`+03S2`Q3z5@XPyPAb4b5b6Q3o/2HP6b3bAb@b>b=b1b1b1b1Q4Q=5hHeM9xEiQ3|Q4OP4PJQ3oQ2WfERhPuP4PJQ3oQ3<-04GS4OCQXJCP4PJP2Q0EQ3o%Yu-04GS3|P6Q3TP|Q3VPxQ3[PgQ3]PpPLPbP{P~PSPdP[P^PePEP@P\Q3yQ2`5@XPyPAb4b5b6Q3o,22P6b3bAb@b>b=b1b1b1b1Q3TP|Q3VPxQ3[PgQ3]PpPLPbP{P~PSPdP[P^PePEP@P\PXQ2`%IGS2`Q3Z#I61o>S4QQ3zCdPyPAb4b5b6Q3oQ3Z-04GS3Z;5HP6b3bAb@b>b=b1b1b1b1Q3oQ3|;5HeM9xQ3=P?DvJ1nQ3WQ4NP4PJQ3\Q2GQ0?PuP4PJQ3\Q4OCQXJCP4PJP2Q0EQ3\Q3|P6Q3TP|Q3VPxQ3[PgQ3]PpPLPbP{P~PSPdP[P^PePEP@P\Q3yQ3>Q2J+03Ru5@XPyPAb4b5b6Q3\,22P6b3bAb@b>b=b1b1b1b1Q3TP|Q3VPxQ3[PgQ3]PpPLPbP{P~PSPdP[P^PePEP@P\PXPuQ4QQ3zCdPyPAb4b5b6Q3\Q3Z;5HP6b3bAb@b>b=b1b1b1b1Q3\Q3|;5HeM9xQ3?PBDvJ1nQ4HQ4MP4PJQ3UQ2>Q1FP}P4PJQ3UQ3<CQXJCP4PJP2Q0EQ3U%Y}RuP6Q3TP|Q3VPxQ3[PgQ3]PpPLPbP{P~PSPdP[P^PePEP@P\Q3yQ3>Q2A+03S2A5@XPyPAb4b5b6Q3U,22P6b3bAb@b>b=b1b1b1b1Q3TP|Q3VPxQ3[PgQ3]PpPLPbP{P~PSPdP[P^PePEP@P\PXQ2AQ3R#IS2AQ3zCdPyPAb4b5b6Q3UQ3R;5HP6b3bAb@b>b=b1b1b1b1Q3U?5uHeM9xQ3BP7DvJ1mQ4JQ4LP4PJQ4IQ2tP1P}P4PJQ4IQ3<CQXJCP4PJP2Q0EQ4IPuP6Q3TP|Q3VPxQ3[PgQ3]PpPLPbP{P~PSPdP[P^PePEP@P\Q3yQ3>Q2r+03S2r5@XPyPAb4b5b6Q4I,22P6b3bAb@b>b=b1b1b1b1Q3TP|Q3VPxQ3[PgQ3]PpPLPbP{P~PSPdP[P^PePEP@P\PXQ2rQ2AQ3zCdPyPAb4b5b6Q4IQ3R;5HP6b3bAb@b>b=b1b1b1b1Q4I?5uHeM9xQ3DP9DvJ1mP4PJQ4KQ2xPDP4PJP2Q0EQ4KQ2x#^RuP6Q3TP|Q3VPxQ3[PgQ3]PpPLPbP{P~PSPdP[P^PePEP@P\Q3yQ3>Q2v+03S3>5@XPyPAb4b5b6Q4K,22P6b3bAb@b>b=b1b1b1b1Q3TP|Q3VPxQ3[PgQ3]PpPLPbP{P~PSPdP[P^PePEP@P\PXQ3>%IVS3>Q3zCdPyPAb4b5b6Q4K?5VHP6b3bAb@b>b=b1b1b1b1Q4K?5uHeM9xEiK0hK0hDoQ02PJQ0{Q17CtQ2\Q2W60YJQ2IQ2G60YJQ2@Q2>60XJQ2sQ2t60XJQ2wQ2x5aJ'0D?ec0@bsbBb2c0oc0nc0mc0lQ2~eY0NY0MP<P6O2n2001000000121000000W2Y0LP<P6O2n2001000000121000000W2Y0KP<P6O2n2001000000121000000W2Y0JP<P6O2n2001000000121000000W2Y0IP<P6O2n2001000000121000000L2bQ0|Q12P0Q02P4Q4=%b=$0SQ03$1YRu'lRHCtS03Q02P4g02cF&0K=$0`/luR^CtS4=Q02P4g02dG%bW/cuS12CtS2eQ02P4Q4?Q4A#b/cuCtS4?Q02P4Q4A&2_F/cuS4ACtS2}'0S2U'0S2|'0S2FQ0|Q2KQ03Q2FP0Q4=Q2|Q0|P6Q4=Q2|P0Q2eQ2UQ0|P6Q2eQ2UP0Q4?Q2}Q0|P6Q4?Q2}Q3FQ3GQ3HQ3IQ3JQ3LQ00PtQ3KQ3QP6Q3PQ3eQ3gP6PwP<O2b380EtXQtP6O1Q3KQ3PPvPwQ2kQ0sQ3mP6Q0kPwP<P7fMR[O5b3H1q80>tWJP6O1n200110;00021110111100c0;Q3Q%6T#M#p#V#M#V#M#RRt=aJH%VT#V#y#M#M#y$17#y#URd=aJ^S3Q%6T#M#p#V#V#y#M#RRSQ125aJS3K&0FT#y$0F#M#V#V#M#RR~%6T#M#p#V#V#V$0F#RR{#b/cuS3P5aJS0kQ4A9aJ{S3m'0S0s'0S3gP4PJPtPHQ1H12t6Rb%^HS3e,1t796Q3qP<12t<RLQ34#YS00,1tS3L,:<Rp'0Q0C,1tRg99L<RxPLPpPLP6XZ>RpQ0CO1R|,1tR2,:<1]cLA8cLLe:0pLLPp1:<6$1kXr>XZ>S3JP<P<%C<S3GQ3LP2PpPpPpP>P>g047e11<6H2^#CZ18>XJ>S3LPtPt%CtQ00P|PpPpQ3<#CXZCS3<Q34Q0CQ0C#CJ19N:0_L0gJ0fP6CTS34PxQ0FQ3uQ3wQ3vQ3rQ3tPePEQ3cP\PXPXPX%ItRCPmQ0C-03C:0OXmI0LS0CPnQ3;CBPyPAb4b5b6X0>A9b6gS00Q3~[^0>P6PBP9O2S3Fb3bHbXbHb?Q34PxQ42PEQ45P\PXQ0CPnQ4;CBPyPAb4b5b6X0>X7>X9>X:>X;cQ00Q3M[^0>^7>^9>^:>^;cP6Q3NPwPvQ0zP:P<P9P7O8S3Nb3b?Q3^12~<Rg11~GS2{79<Rb12{<RC11{GS2q79<R|Q4D'kS2z'kR2'kRLQ34PxPePEQ3cP\PXQ0CPnQ0CCBPyPAb4b5b6X0>Q00Px[^0>P6P:P<O2S00b3b?60>xO4WGX<>P4PJPtQ3eCQeEiQ3QQ3gP4PJPdP^P`12d6S3g%^^S3Q,1d796Q3qP<12d<R^Q31#YS3e,1dS0C,:<S34'0%UTS2u,1dRT99^<RtP^Q34P^PpQ2uO1S34,1dS2y,:<1]c^A8c^^e:0p^^PpQ3JP<P<Q3GQ0CQ2yPpPpPpQ3LPdPd%CdQ3eQ34PpPpQ3<Q31Q2uQ2u#CJ19N:0_L0gJ0fP6CTS31PtQ0FQ3uQ3wQ3vQ3rQ3tPePEQ3cP\PXPXPX%IdR^PmPXPmP^Q2u#IS34H0~I0LR^PnQ3;CBPyPAb4b5b6X0>Q3g?96TRTQ3~[^0>Q3Fb3bHbXbHb?Q31PtQ42PEQ45P\PXP^PnQ4;CBPyPAb4b5b6X0>X7>X9>X:>X;cQ3M\T^0>^7>^9>^:>^;cQ3Nb3b?Q3^Q31PtPePEQ3cP\PXP^PnQ3{CBPyPAb4b5b6X0>Q3^\T^0>Q00b3b?80>2:0ExLO4WGX<>P4PJPdQ3QCQeEiQ3KQ0sP4PJPSQ12PD12S6S0sQ12#^S12,1S796Q3qP<12S<RdQ38#YRT,1SS3K,:<R^'011SGS3Q99d<RtPdP^PdPpPGO1R^,1SS31,:<1]cdA8cdde:0pddPpQ3JP<P<Q3GQ3KQ31PpPpPpQ3LPSPS%CSPTP^PpPpQ3<Q38PG%CGJ19S31N:0_L0gJ0fP6CTS3KPtQ0FQ3uQ3wQ3vQ3rQ3tPePEQ3cP\PXPXPX%ISRGPmPXPmPGQ2`H0~I0LRGPnQ3;CBPyPAb4b5b6X0>Q0sQ3Q796RdQ3~[^0>Q3Fb3bHbXbHb?Q3KPtQ42PEQ45P\PXPGPnQ4;CBPyPAb4b5b6X0>X7>X9>X:>X;cQ3M\d^0>^7>^9>^:>^;cQ3Nb3b?Q3^Q3KPtPePEQ3cP\PXPGPnQ3{CBPyPAb4b5b6X0>Q3^\d^0>Q00b3b?80>2:0ExLO4WGX<>P4PJPSQ12CQeEiQ0kQ3mP4PJP~Q3PP912~6RSQ3P#^Rd,1~796Q3qP<11~TRG,:<Rt,0gPbPgPtPg11~^Rt,:<1]cgA8cgge:0pggPpQ3JP<P<Q3GPGPtPpPpPpQ3LP~P~%C~PTP^Q31N:0_L0gJ0fP6CTRtPbQ0FQ3uQ3wQ3vQ3rQ3tPePEQ3cP\PXPXPX%I~RGPmPXPmPGQ2`H0~I0LRGPnQ3;CBPyPAb4b5b6X0>Q2{99S6RSQ3~[^0>Q3Fb3bHbXbHb?PtPbQ42PEQ45P\PXPGPnQ4;CBPyPAb4b5b6X0>X7>X9>X:>X;cQ3M\S^0>^7>^9>^:>^;cQ3Nb3b?PxPLQ3^P2Q2zPtPbPePEQ3cP\PXPGPnPGCBPyPAb4b5b6X0>Pb\S^0>Q00b3b?60>bI0JO4WGX<>P4PJP~PdCQeEiP4PJP{Q4AP:12{6RdQ4A#^R~,1{796Q3qP<11{TRS,:<RG,0CP|PCPGPC11{^RG,:<1]cCA8cCCe:0pCCPpQ3JP<P<Q3GPSPGPpPpPpQ3LP{P{%C{PTP^Q31N:0_L0gJ0fP6CTR^P|Q0FQ3uQ3wQ3vQ3rQ3tPePEQ3cP\PXPXPX%I{RTPmPXPmPTQ2`H0~I0LRTPnQ3;CBPyPAb4b5b6X0>Q2q99d6RdQ3~[^0>Q3Fb3bHbXbHb?P^P|Q42PEQ45P\PXPTPnQ4;CBPyPAb4b5b6X0>X7>X9>X:>X;cQ3M\d^0>^7>^9>^:>^;cQ3Nb3b?PxPLQ3^P2Q2zQ4DP^P|PePEQ3cP\PXPTPnPTCBPyPAb4b5b6X0>P|\d^0>Q00b3b?60>|60EbI0JO4WGX<>P4PJP{P~CQeEiH0IK0hDoQ0|ebsbBb2Y0WY0VP<P6O2n2001000000121000000W2Y0UP<P6O2n2001000000121000000W2Y0TP<P6O2n2001000000121000000W2Y0SP<P6O2n2001000000121000000Q0}Q11Q0RQ0QQ0RPfQ0UQ0VP<Q15ErQ0W38PMPKPsQ1kQ29Q0RQ0SQ0Tg00LLH16&2[K']PJP;P<P6PFPMP;P<fiR~P6J2YQ0XQ0\:0GM:S0\Q0YQ0ZQ0[%AlS0ZQ0A/2YS0T9_lW5HjRj'0D?X85#=Q01P5Q1LQ1P:0GM9S1PQ1MQ1NQ1O/0jD?X85PFPMPJP9P:DnP6Q1SQ1W:0GMBS1WQ1TQ1UQ1V/0jD?P0Q1XQ1^:0GM?S1^Q1YQ1ZQ1[Q1]Q0BQ0IQ0JH1:D?PFPMPJPDP?DnP6Q1bQ1j:0GMqS1jQ1cQ1eQ1fQ1hQ1i#AS1fQ1iQ1iQ1d;5YS1d7_W3HD?P0Q0M%7_S1h'1:0GM_S1iQ1h#4S1eQ1hPWQ0NQ1h%W7S0IQ0M#AS1]Q0MPWQ0O/2YS0OC|+0i7_WI1EPFPMPJP`P_DnP6Q1FQ1=Q1F#7'160GMS0MQ21Q22%`DS22#jS1[Q23%WDS23#G%3DS1Z#AS1VQ1Z/;WS1UQ1ZQ1[;5YS1OD?H1SP0Q1I#7S1N#4S0[Q1NPW%<1S0SQ1N%W1S0W%31Rj#AS0QPjPWQ0S=5jYS15C|+0i7_WH0bPFPMPJQ1HQ1IDnP6Q0?#7#4Q27Q1CQ28%W`#GQ1A#AS28Q1A/;WS27Q1D/2YS1D3HI1hP0Q13#7S0VQ1F#<S0U75WQ0VQ1F#WQ1F#3Rj#AS11PjPWQ0U=5jYS03C|+0i7_WPFPMPJfDRjQ13DnP6%7hS2FQ1I#`S4=#jS2|75WQ2<Q1H#W#GQ1H#3S2<#AS2eQ2</;WQ2<Q1H#`S2U#jS4?;5YS2}D?P0Q2k#7S0|/;WQ0?#WQ0?#3Rl#AS2zPlPWQ0?#<S00=5lYS3^C|+0iPFPMPJQ1KQ2kDnP6Q4P#7S3N/;W%Wj%3jS3M#AS4;Q3MPWQ3M%<jS42;5YS3FC|+0iP0%Wh#G%3hRl#AS3~PlPW%<h=5lYS2qC|PFPMPJQ0yfKS2`DnP6Q2k#W#GQ1K#3Rl#AS31PlPWQ1K#`-1plS4A/2YS2{C|P0Q4P#3Rl#AS3PQ4P#<=5lYS3m9_lWPFPMPJfPRlQ3hDnP6Q2`#3S0k#AS12Q0y#3S3{Q3{Q0y#<S3K'1S3Q/2YS0s7_WP0%3[S3g/;WQ3g%<[S2y'1S0C/2YPFPMPJfTS2~fSR{DnP6Q3h#3S2x/;W%3lS2w%<l;5YPFPMfWS2tQ2EQ18p+01OQ1:P[L2SQ18#FS2sQ18#3S2>Q2t#740=Q1kQ1sP0Q1lQ1~Q2H/JrP6Q1lQ1~P0Q1mQ1}Q2L00wrRb#GR|P6Q1mQ1}P0Q1nQ1|Q30#\S2H/JrP6Q1nQ1|P0Q1oQ1{Q2[/JrP6Q1oQ1{P0Q1pQ1zfjS2[/SrP6Q1pQ1zP0Q1qQ1yfnS2@/SrP6Q1qQ1yP0Q1tQ1xfrRd/SrP6Q1tQ1xP0Q1rQ1wfvS2G/SrP6Q1rQ1wP0Q1uQ1vfz/SrP6Q1uQ1vf}RT/Srf|R^$0<,KsP<PTP^f{O341gWcW|P<P6O2n2001000000120000000WBWbP<P6O2n2001000000121000000WBWaP<P6O2n2001000000121000000WBW`P<P6O2n2001000000121000000WBW_P<P6O2n2001000000121000000WBW^P<P6O2n2001000000121000000WBWWP<P6O2n2011000000121000000WBWVP<P6O2n2011000000121000000WBWFP<P6O2n2011000000121000000bhfXR^/SrQ1GfYS2I#\S2WP{Q3hP6O4%3{%<{S2\'1Q0zQ0m00r{40qQ3HQ3IQ1:$1yQ1:#3S17Q1:+0rQ3n,EMS0{Q0{>0T6W80Q6Q3qP<Q2NQ0y80jWS2N%4WRT%7z000W[S4KQ2I#3R200xWS3z%42Q2j#3S3]000W\T[S3[Q0FQ3uQ3wQ3vQ3rQ3tQ37$0;S37Q36$0;S36Q40Q41'LQ38$0;S38Q35Q33Q3_Q3261u>Q3a'LS3_41BS3V'L00teH0VS3TPE&087S3y?zB@S2vPBQ44P<&08BS0EP;P@PBQ43DgDgS3DP\PXPXQ2D#eS2D=@XmS4IPXPmQ2D%IWR2'[PnPXPXQ0t#eRLQ0H#eRxQ2g#eS2gCdS0tPnPXB0OXNLS2rPnPXPXQ0D#eRG@1N2xPnPXPX20UNGPnPXPXQ2D1[LGS0D+0lPnPXPX218XDQ2gQ0x#I5@XS4LPnQ3;J0mDPDPS4JDPK0PGsPyPAb4b5b6X0>X7>X9>X:>XC>XD>X;c12;6S3B11;WS3U796A59B;S4M%A7S4HA5?WD%4DS3?11D1S3|,>?Q0x:0B`?%4?S3\Q3s79?[[[S3Z[[[[^0>^7>^9>^:>^C>^D>^;cP6Q0wQ2K#<fdS4Q#7S2JQ2K#3RSQ4Q,EMS4OPYP?PBQ1FQ24PaQ2BQ2EQ2ZO>b3bEbIbEc05bmP|Q2L#}R|%}rRC'>Rt#GRg&1[8S4NQ3S%}<%}6'>20w<622Q<641xXr8XZ8S3WQ2LP|%C|PrPC%CCS3=N91M:1CbtP7CTPg%\zS3o$0yQ3o#}#4&0yrS3@%4CS3CQ2Q#7S3EQ3h80jWQ30#7000W\Tf\Rg#3S4R00xWQ4R#41DSWRt#4\T[Q3n#301DW&06WRb#GR|20ZSW-04W/1t,>S[21KSW%AWS4SQ2i/DWRS?~SW[Q2i01FW1:W=S4TQ2b/DWRS,:W@0BS=[Q2b01JWQ2Q#3S2b00ZW$06\bQ2b01GWQ30#3S4U/DWQ4U'>\bg03F0S4VQ4U01HWRSePS%7~S4W01DWQ2[#7RS20ZSW-04W1DSW'1'>\|21KSWQ4SfkS4X#7S4Y/DWR|?~|W[Q4Y01FWQ4TflR|#7S4Z/DWRt,:W@0Bt=[Q4Z01JWfmS4T#7S4[00ZW$06\bQ4[01GWQ2@#7Rt/DW/>t\bQ4V21HtWRtePtP9Q3x21T=W']Q4SeRtO1foS4S#7S2@/DWRb?~bWP_PtO1Q2[#3/DWRt?~tWQ37Q36Q3jQ38Q36Q35Q3_'LPeH0VH0VPEQ0E?z9@S3_P;&08D?z1@S3jP<&08?S4\P1&081S4]P:Q3yDgDgP\PXPXA@XLmS4^PXPm1[L2PnPXPXPGQ2c#eRtPUCdS2cQ48Q2C#eRb5@X60aXPnPX1[GxS2C9@XbPnPXPX21INGPnPXPX1[x2S4_00UtPnPXPXQ2C-0lLPnQ4:DPS2CDPDPK0PGsPyPAb4b5b6X0>X7>X9>X:>XC>XD>XN>Xd>Xe>1296S4`119WRb79611BDP;Q4<P1H0C11?DS4a,2q%ADA5qW_11q_,>11:B?Q3|<11B[S3|[[[[[^0>^7>^9>^:>^C>^D>^N>^d>^e>P6%F|%<|%7d%3|1EMdPwPvQ0zPhPjQ1KQ2=PlPgQ4QO?b3bjbtQ24Q0z':Q0mQ24411ec0^c0]c0\c0[btc0ac0`bwbvbubjb\bIbEb>b=blQ4>Q4GQ3pQ4FQ4@Q4EQ4BQ4DP8Q4CQ2LP5P3POPPQ3oPQPREOPkP;P;Q0AH0?S0A'0XL5P^P3POPPQ2LPQP^J0@%F^/2<%3^S2L%<^60T<Q2~Q2NQ4KQ3zQ3[Q35Q41'LQ36Q40Q3b41B<12ePEQ43P;Q0E?zB@P<Q2v?z:@DgS2vP\PXPXA@XxUS41PXPUQ4_PnPXPX1[ItRk-0UmPnPXPX21INIPnPXPXQ47:1Nt2PnPXPX20lxkPnPXPXPmPUQ48:0OXUS4_I0LS3[DPS3zDPDPDPGsPyPAb4b5b6X0>X7>X9>X:>XC>XD>129<S4K?9<bB0=<:B%A9S2NA5DWB11B1,>DP7PBPBQ4aH0?[S4a[[[[^0>^7>^9>^:>^C>^D>P6Q3EQ2Q,EMS3EQ2j#<S3oQ3]P9Q2j#FP:P1Q1IQ2`P{O;b3bIbEDoH09H09I0JI0JO4W?Xf>P4PJ1EMgS4bPWCQRbePbp+01IQ3nPgQ2jO3P4Q0{&2PF#b$1PS4c&0<g-07M&0|g#b$0S/lH'cH01g01S]9~66RbP41EMz$0^g01TT004<S4dQ04Q4d'1Rk-0\z-0NM-0]MCu[^S>P4Q0{Q0v$0F#RRd&2O}-2N}/luS0vCu3HP0P4Q2K,EMS0{Q4cQ3n$0<-07MQ3n$0|#b$0S/lH'cH01P41EM]S04$0^Q4d20\]k-0NM-0]MCu\b^S>P4Q0{PdQ0vCu'0PFPMPJPzQ2KDnP6P4Q04Q4cQ2P-07M&0|z#b$0S/lH'cH01P4Q2S,EM$0^Q4dQ2S00\k-0NM-0]MCu\b^S>P4Q3EPdQ0vCu'0P0P4Q4O$0^Q4dQ4Q00\k-0NM-0]MCu\b^S>P4Q30,EMR}PdQ0vCuPFPMPJQ2SQ30DnP6P4Q2Z,EMR|$0^Q4dQ2Z00\k-0NM-0]MCu\b^S>P4Q2^,EMS2ZPdQ0vCuQ4cQ2^$0<-0MMQ2^$0|#b$0S/lH41ORH9aJ|fhS4c,EMS4O$0^Q4d'1S4dQ4c00\k-0NMRk-0]MS2P5aJ\b^S>S4e11|dS4fQ0v5aJS4gP4PJP|PHP7P4PJP|PWP|%^HS4hP1Q2]Q2~80jWS4ifg#7S4j000W\TS4kQ2b00xWS4lQ2b#4Q2S#3S2S000W\T[S2bPePEQ3cP\A@XmmPyPAb4b5b6X0>1266^0>P61EM~O1S4mb3bIbEQ4iQ4kQ4lQ2bPePEQ3cP\Q3Y#URH-03mS3Y1[m2S4n5@XPyPAb4b5b6X0>116WS4o956H^0>Q4mb3bIbEQ4h11|WS4p55|eM9xEiQ4eQ4gP4PJQ4dQ2PP:P<P6O2P4PJQ4OPWQ4O/1HQ2a#US2a004<'1Q3:#YS3:P_Q4c#7R2Q2E80jWS4cQ4W000W\TS4gQ2S00xWS4eQ2S#4Q2^#3S2^000W\T[S2SQ3aQ3aQ33+2M+2L02KeS4hPEQ3kP<P@P:Q44I2US4qP\PXPXA@XNUS4r218X7S4sPnPXQ2rPnQ3YQ2a#IS4t>1o>U'[S3Y9@XmCBJ0mPyPAb4b5b6X0>X7>X9>X;cQ3}/0:Q3l11;HQ2a004:'1RH,2;[[^0>^7>^9>^;cP6Q3X#N#V#URT,:9Q2^P9Q4X,EMS4XP:Q4PO6b3bIbEQ4cQ4gQ4eQ2SQ4hPEQ4qP\PXPXQ4sPXPU%ITPnPXQ2rPnPXQ3YQ4tQ4nCdCBGsPyPAb4b5b6X0>X7>X9>X;cA9:<TQ3lQ2aQ3U55H[[^0>^7>^9>^;cP6%49RHQ2^P9Q4XP:Q4PO6b3bIbEM9xP4PJQ4dQ3:CQeP4PJQ4d&1ek-07M&1dk-07M&1ck-07M&2Vk#b$0S&2Jk#b$0S&2Wk#b/cu41O'c'c'c#^CQeP4PJQ4dQ2P#^CQeEiZ0gbZ17>P4PJQ4fQ0vP6P4PJP|PWQ4fQ0v#^R|P1Q4iQ4kQ4lQ2bPePEQ3cP\203mdRb9@XmPyPAb4b5b6X0>116dRd,26^0>Q4mb3bIbEQ4iQ4kQ4lQ2bPePEQ3cP\PXPbQ2AQ4nCdPyPAb4b5b6X0>Q3RQ4o55d^0>Q4mb3bIbEQ4fQ4p75|eM9xEiH0IDoY0>Y0=P<P6O2n2001000000121000000W\Y0<P<P6O2n2001000000121000000boc0?bTb[bBbUb2W~Y0uP<P6O2n2001000000121000000W2W}P<P6O2n2001000000121000000W2Y0pP<P6O2n2001000000121000000W2Y0|P<P6O2n2001000000121000000W2Y0{P<P6O2n2001000000121000000W2Y0zP<P6O2n2001000000121000000W2Y0PP<P6O2n2001000000121000000W2WyP<P6O2n2001000000121000000W2Z065P<P6O2n2001000000121102000bQN;2XWGXOfW<Q0}eQ0~Q10Q0RQ0^Q0RPoQ0_Q0`P<Q16ErQ0a38PMPKPsQ1kQ29PJP;P<P6PFPMP;P<P~P6J2IQ0XQ0\PiQ0YQ0bQ0cQ0ZQ0T'0RF3HD?X85#=Q01P5Q1LQ1PPiQ1MQ0dQ2l;HFD?X85PMPJP9P:C{P6Q1SQ1WPiQ1TQ1RQ1Q;HFD?P0Q1XQ1^Q1\Q1YQ2mQ2nQ0BQ0J3HD?PMPJPDP?C{P6Q1bQ1jQ1gQ1cQ1`Q1_Q1fQ1d3HD?P0Q1iQ0IQ1eQ1hPVQ0NQ1hQ1]Q0O'07_VEfPMPJP`P_C{P6Q0MQ23Q21Q20Q1[Q2oQ1VQ1O3HI0oP0Q0WQ0[Q1NPVQ0SQ1NQ0QQ15'07_VI1EPMPJQ1HQ1IC{P6%W_Q26Q25Q1CQ2pQ28Q1D3HH1SP0Q0V#4Q0VPVQ0UQ0VQ11Q03'07_VH0bPMPJPjQ13C{P6Q2F#4Q2;Q4?Q2:Q2eQ2}I1hP0Q0|Q0075VQ0|Q2zQ3^'07_VPMPJQ1KQ2kC{P6Q3NQ13#<RF75VQ2?Q4;Q3F3HP0Q2`#7/;VQ3~Q2q'0PMPJQ0yQ2`C{P6%7[/;VQ31Q2{'0P0Q3PQ3mPMPJPlQ3hC{P6Q12Q0sQ1kQ1sP0Q1lQ1~Q1:/SrP6Q1lQ1~P0Q1mQ1}Q2W/JrP6Q1mQ1}P0Q1nQ1|Q3n/SrP6Q1nQ1|P0Q1oQ1{Q2RP6Q1oQ1{P0Q1pQ1zQ2_/JrP6Q1pQ1zP0Q1qQ1y1S~rP6Q1qQ1yP0Q1tQ1xQ4T/SrP6Q1tQ1xP0Q1rQ1wfq/SrP6Q1rQ1wP0Q1uQ1vfu/SrP6Q1uQ1vfxRi/SrfwRf#w,KsP6PiPfQ2GO341gW{WcP<P6O2n2001000000120000000W2WbP<P6O2n2001000000121000000W2WaP<P6O2n2001000000121000000W2W`P<P6O2n2001000000121000000W2W_P<P6O2n2001000000121000000W2W^P<P6O2n2001000000121000000W2WWP<P6O2n2011000000121000000W2WVP<P6O2n2011000000121000000W2WFP<P6O2n2011000000121000000bh1S{rQ1:Q2~#\PaQ2=P6O4%3aR{%<aRf'1Q0zQ0m%FaRiH0CQ3HQ3I21blj%FlQ2w'>f~Q2tQ2EQ1:O3P41EM^Q2t#w-0MM&0`6/luRjH01Q3A00{6Q0u#URs+14R|Q2t$0R'>'0XiZ-1RZQ01PZP4Q2I,EM%w^-0MMPjH01&0R^,>|'0XiZPMPJQ2IP^C{P6P4Q2j,EMQ1G#w-0MMPjH01Q1G$0R,>|'0P0P4Q4bQ2j#w-0MM&0`</luH01Q3A00{<014sQ2j$0R'>PMPJQ3nPgC{P6P4Q0{Q3n#w-0MM&0`:/luH01Q3A00{9014sQ2K$0R'>PZPJQ3EQ2M-0MMRdPjH01&0R],>|'0XiZP7Q04Q2O-07M&0`7/lu'cR|5aJQ3A00{7014s&0Rz'>P4PJQ04P|P<Q3EQ3E&0`B>1Odu#^60T680Q6Q3qP<12}<RdQ39#YRu,1}Rz,:<Rs'0Q0H#UR],1}99d<RjPdPsPdPpP]O1Rs,1}Rb,:<&1kdPpQ3JP<P<Q3GPzPbPpPpPpQ3LP}P}%C}PuPsPpPpQ3<Q39P]%C]J19N:0_L0gJ0fP6CTRpPjQ2V@0jV[Rs%4VRuQ2J000V[R}Q0FQ3uQ3wQ3vQ3rQ3tQ3TPEQ3DP\PXPXQ4IPXPmQ2D%I]Rb'[PnPXQ0tPnPXQ2rPnPXPXQ3>>1NGxPnQ4JDPK0PGsPyPAb4b5b6X0>X7>X9>X:>XC>XD>X;cQ3B11;]796Q4MQ4H11?VRz/2DQ3Z[[[[^0>^7>^9>^:>^C>^D>^;cP6Q0wQ30#<P2Q4UQ4OPYP?P7PhQ29PaQ2BQ1GQ2[O>b3c04bnc04c15bkPpPjQ2YQ2T#}Rd/>CRk#GRTQ2XQ4NQ3SQ3WQ2TPd%CdPrPCQ3=N91M81CkQ1ICTPTQ4Q#\RT$0y%}T#4Q3@Q3CQ2]@0jVlQ4j000V\uQ4j01DV&06VRu#G20Z2V-04V1D2V'1,>2[21K2V%AVR2Q4W/DVRT?~TV[Q4W01FV1:V=1DSVRT,:V@0BT=[21JSVQ4Y00ZV$06\uQ4Y01GVQ4Z/DVQ4Z'>\uQ4VQ4Z01HVRuePuP9Q3x21T=V']P2eO1Q4[/DVR2?~2VQ38Q36Q3VQ37Q35Q40Q3i'LR2PeH0VH0VPEQ0EQ4]7z9P;Q3jP<Q4\P1P@P:Q3yDgDgP\PXPXQ4^PXPm1[LbPnPXPXQ3X#eR=00lGPnPXQ2cQ48=@X=60aXPnPXPXPxQ3>PtCdPnPXPX20UNxPnQ2CDPK0PDPGsPyPAb4b5b6X0>X7>X9>X:>XC>XD>XN>Xd>Xe>Q4`119]R]7961>1B11?1P:1197R=PqH0CA51Vq%4qQ3|[[[[[^0>^7>^9>^:>^C>^D>^N>^d>^e>P6%F~%<~Q2@%3~Q4S,EMPwPvQ0zQ1JP`Q1KQ2=Q1:Q2IQ2QO?b3b\Q0z,:`Q0m<11`ebwbvbubjb\bTbnb>b=blbkQ4>Q4GQ3pQ4FQ4@Q4EQ4BQ4DP8Q4CQ2HP5P3POPPQ2TPQPREOQ0A'0XL5PgP3POPPQ2HPQPgJ0@%Fg/2<Q4R%<g60T<P^PpPjPsP}Q35Q33Q3`'LR}'LQ36Q40Q32Q3b'L41B<12ePEQ2vP\PXPXQ41PXPU1[xbPnPXB1WXmIRbPnPXPXPtQ3>Q47CdPnPXPX20UNtPnQ3zDPK0PGsPyPAb4b5b6X0>X7>X9>X:>XC>XD>Q4K?9<]1><:R]12z7Q3?Q4a[[[[^0>^7>^9>^:>^C>^D>P6Q2dQ2ZQ2fQ2iP9Q2hP;Q1JQ2`Q3hQ2tO;b3bnbkDoH09H09I0JI0JO4W?Xf>P4PJQ04%^|CQeEiP6H0IH09Y0jY0tP<P6O2n2001000000121000000WTXiZP<P6O2n2001000000121102000bob[bBb2bUW~W}P<P6O2n2001000000121000000W2Y10P<P6O2n2001000000121000000W2Y0~P<P6O2n2001000000121000000W2Y0}P<P6O2n2001000000121000000W2Y0kP<P6O2n2001000000121000000W2Y0QP<P6O2n2001000000121000000W2WzP<P6O2n2001000000121000000W2Z075P<P6O2n2001000000121102000bQN:2HWxXRoWPQ0~eQ14Q1\B13:;<Q19Q0L'0P01J9rP3POPPP9PQQ1aEOPKPJP7P9H0kP6Q1;Q1<PMPKPJPDP?22GD<Q2EPDP?P6O3Q1=#AQ1=PWQ1>Q1@Q1=Q1?+0D80QY+0[C|P0Q1VQ1UQ22#4Q1OQ1ZQ1[+1>+0}3HPMPJPqP1H0kP6Q1E#A%3_RK%`_R_PK%j_R_PY20DK_H0b+0[7_WP0Q27Q1BQ1DQ1AQ1C+1>+0}+0[PMPJQ1JQ1FH0kP6Q1J#3/;WQ4=Q1I#3RWQ2|PYQ2|-0DWH0b+0[P0Q2U#4Q2}Q2<Q4?+1>+0}PMPJQ24Q0?H0kP6Q24#`#4Q13#3RWPFPY20DWFH0bP0Q3FQ3MQ42+0DPMPJQ29PhH0kP6Q29#3Q29#<;5YQ2k#3Q2k#<+0DQ2=Q4PQ1KQ0?Q24O4Q4AQ0zQ0mQ1K+0r40qQ3HQ3IQ2=Q1K+1bQ2=#FQ2=#3'>Q3{P6P6Q3QH0?Q3qP<Q0FQ3uQ3wQ3vQ3rQ3tQ35Q32Q3a'LRW'LQ40/L}<12ePEP@P9Q44P<Q3kQ437z9DgP\PXPXQ4IPXPmQ2D/[LRFPnPXPXQ2g-0UFPnPXPXQ2D-1INPnPXPXQ46Q4LPnQ3;J0mDPDPGsPyPAb4b5b6X0>X7>X9>X:>X;cQ3B11;:RN796Q4</2;Q2NQ0x:0B?9Q3s99H9[[[[^0>^7>^9>^:>^;cP6Q0wQ18#<RFQ2>PYP7P9PqQ29Q2~O9b3bEbIbE20warRq#G%}aRY/>CR_#GRKQ4NQ3SQ3WPaPY%CYPrPCQ3=N91M:1Cq_Q2kCTPKQ3@Q3C&0yl%}l#4Q35Q33PW20t2eH0VPEQ3_P;P@P<Q4\P?P@P:Q3yDgDgP\PXPXQ4^PXPmQ0DPnPXPX20lxLPnPXQ0D=@XUQ48=@Xx60aXPnQ4:CBDPGsPyPAb4b5b6X0>X7>X9>X:>XC>XD>XN>Q4`?96=1>?711B?P:P=PDH0CQ3O[[[^0>^7>^9>^:>^C>^D>^N>P6Q2sPFQ2>PwPvQ0zP7P9PBPDO:b3b>b=blQ4>Q4GQ3pQ4FQ4@Q4EQ4BQ4DP8Q4CPaP5P3POPPQ3hPQPREOQ0A'0XL5P[P3POPPPaPQP[J0@%F[/2<Q0C,:<Q2920t}ePEQ45P\PXPXQ49Q4_PnPXPbPnQ3[CBJ0mPyPAb4b5b6X0>X7>X9>X:>Q3f?9<NP;P:P:P=H0?\][^0>^7>^9>^:>P6PfP{P;PiP<P:O6b3DoH09H09I0JI0JO4W?Xf>P4PJQ0kQ2`#<CQRiePifsP[Q0yPhQ2=O4Q02P4Q3{Q3KH0zQ3}?9<fg02hVRf215Ml010;&2E<Rl38Q2w/1:&0K;&1YZRh5ZZR[6054Q0G#URi9~;;R{'0[[^Y>^M>'0P0Q02P4Q3gQ2yH0zQ3}Q3h#<R]79<Q18-15M010;=8flQ2>/1:>054[/0{[[^Y>^M>PMPJQ3hPaH0kP6Q02P4Q2xP]H0zQ3}Q2B#<79<Q2~-15M010;=8flQ2~#3/1:>054[/0{[[^Y>^M>Q02PJQ2>PFH0zQ3}Q2\79<R]Q1:-15M010;=8flRlQ17/1:Rf>05J[/0{[[^Y>^M>P4PJQ2>PFP<P7J2DP9P:P;P<P6O4B054f[/0{P0Q2E#3/19&0K:=ZZh6054Q3d?9:iQ2t#3/17&0K9=ZZh605J1:9i7HHP6Q2L/1B&0K7=ZZh6054A~BBiQ1G#3RB/1DRD&0K?=ZZhRh605JQ3\1:?iP4PJPDPhP<P4PJPBQ1G#<PDQ3eQ1JPePEQ3k?z<@P\PXPXQ4r218X9Pn1[mUR99@XmJ0mPyPAb4b5b6X0>X7>X;cQ3}/0;11<;R@,2<[^0>^7>^;cP6Q3o,:1P1Q3]P?O4b3PePEQ3kQ447z<P\PXPXQ4sPXPUPIPnPXP9Q341[mICdGsPyPAb4b5b6X0>X7>X9>X;cA9:<;Q2u11<:55@[^0>^7>^9>^;cP6%41Q3oP1Q3]P?O5b3M9xP4PJPD1qZh#YCQeJ2kP6DoY0iY0HP<P6O2n2001000000121000000b<Z0dlZ0h]XY>XM>H0IY0bY0cP<P6O2n2001000000121000000boc0AbTb[bBWWY0FP<P6O2n2001000000121000000WBWVP<P6O2n2001000000121000000WBWFP<P6O2n2001000000121000000WBY0GP<P6O2n2001000000121000000b<K2lW2WUP<P6O2n2001000000121000000b<Y0fW]XL5XK8Q10eK0hK0hDoc0qc0CY0vY0EP<P6O2n2001000000121000000W2Y0wP<P6O2n2001000000121000000W2WFP<P6O2n2001000000121000000W2Y0DP<P6O2n2001000000121000000b<c0eY13Y11P<P6O2n2001000000121000000W2Y0RP<P6O2n2011000000121000000W2Y14P<P6O2n2011000000121000000W2Y0xP<P6O2n2011000000121000000b2Y0yY0YP<P6O2n2001000000121000000W2Y0BP<P6O2n2001000000121000000W2Y0XP<P6O2n2001000000121000000W2Y0OP<P6O2n2001000000121000000W2Y12P<P6O2n2001000000121000000b2o"). Qed.

Lemma rticks_ok_drop_region : ticks_ok st -> ticks_ok st'.
Proof.
  intros [T1 T2]. split.
  - intros q sh u hl ch Hq Hu Hin. unfold st', drop_region in Hq. cbn [s_shadow set_shadow set_regions] in Hq.
    destruct (N.eq_dec q rid) as [->|NE]; [rewrite lookup_delete_eq in Hq; discriminate|].
    rewrite lookup_delete_ne in Hq by congruence. exact (T1 q sh u hl ch Hq Hu Hin).
  - intros q sh pg t Hq Hp. unfold st', drop_region in Hq. cbn [s_shadow set_shadow set_regions] in Hq.
    destruct (N.eq_dec q rid) as [->|NE]; [rewrite lookup_delete_eq in Hq; discriminate|].
    rewrite lookup_delete_ne in Hq by congruence. exact (T2 q sh pg t Hq Hp).
Qed.
End DROPREGION.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rmrep_put_group_new : forall st m b g ai r (w8 : byte),
  rmrep st m -> (s_groups st) !! b = None ->
  (s_regions st) !! (fst b) = Some r -> r_kind r = RKGroup -> 0 <= snd b -> snd b + 16 <= round_up_pg (r_len r) -> snd b mod 16 = 0 ->
  rw_cells psegs m (conc st b) [C8 (pw st (Some g)); C1 w8] -> Z.land (bv_unsigned w8) 31 = Z.land ai 31 ->
  rmrep (put_group b (Some g) ai st) m.
Proof.
  intros st m b g ai r w8 (WF & CX & GL & AR & GR & SH) Hb Hr Hk B0 B16 BA R Hw8.
  pose proof WF as (RS & WR & DJ & WA & WG).
  split; [|split; [exact CX|split; [exact GL|split; [exact AR|split; [|exact SH]]]]].
  - split; [exact RS|]. split; [exact WR|]. split; [exact DJ|]. split; [exact WA|].
    intros b' gh Hb'. unfold put_group in Hb'. cbn [s_groups set_groups] in Hb'.
    destruct (decide (b' = b)) as [->|NE].
    + rewrite lookup_insert_eq in Hb'. inversion Hb'; subst. exists r. auto.
    + rewrite lookup_insert_ne in Hb' by congruence. exact (WG b' gh Hb').
  - intros b' gh Hb'. unfold put_group in Hb'. cbn [s_groups set_groups] in Hb'.
    destruct (decide (b' = b)) as [->|NE].
    + rewrite lookup_insert_eq in Hb'. inversion Hb'; subst. exists w8. cbn [g_meta g_active_idx]. split; [exact R| exact Hw8].
    + rewrite lookup_insert_ne in Hb' by congruence. exact (GR b' gh Hb').
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rmrep_set_mmap_counter : forall st m v,
  rmrep st m -> 0 <= v < 2^32 ->
  rmrep (upd_ctx (set_mmap_counter v) st) (write_to_mem m (wa (RCTX + 12)) (le4 (wz v))).
Proof.
  intros st m v MR Hv. pose proof MR as (_ & (X1 & X2 & X3 & X4 & X5 & X6) & _).
  pose proof (length_le4 (wz v)) as L4.
  pose proof (munch_write [(RCTX + 12, RCTX + 16)] m m (RCTX + 12) (le4 (wz v)) (munch_refl _ m)
                ltac:(unfold RCTX; lia) ltac:(rewrite L4; unfold RCTX; lia) ltac:(rewrite L4; cbn [inside]; lia)) as MU.
  pose proof (wmono_write psegs m m (wa (RCTX + 12)) (le4 (wz v)) (wmono_refl psegs m)) as WM.
  eapply (rmrep_ctx_frameW st (upd_ctx (set_mmap_counter v) st) m _ _ MR MU WM); try reflexivity.
  - intros lo hi [E|[]]; inversion E; subst. unfold RCTX. lia.
  - left.
    pose proof (rw_cells_write psegs m RCTX (rctx_head_cells st) 12 (C4 (wz (c_mmap_counter (ctx st)))) (C4 (wz v)) X1 eq_refl eq_refl I) as W.
    replace (RCTX + Z.of_nat 12) with (RCTX + 12) in W by reflexivity.
    unfold rctx_head_cells, rsecw, ctx in *. cbn [s_ctx upd_ctx set_mmap_counter c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
      c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
    cbn [cell_upd csize Nat.eqb Nat.sub cbytes] in W. exact W.
  - right. split; [| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
    unfold actives, active, ctx. cbn [s_ctx upd_ctx set_mmap_counter c_active]. reflexivity.
  - right. split; [| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
    unfold usages, usage, ctx. cbn [s_ctx upd_ctx set_mmap_counter c_usage]. reflexivity.
  - right. split; [| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
    unfold unmap_seqs, unmap_seq, ctx. cbn [s_ctx upd_ctx set_mmap_counter c_unmap_seq]. reflexivity.
  - right. split; [| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
    unfold bouncess, bounces, ctx. cbn [s_ctx upd_ctx set_mmap_counter c_bounces]. reflexivity.
  - right. split; [| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
    unfold ctx_tail_cells, brk_word, ctx. cbn [s_ctx upd_ctx set_mmap_counter c_seq c_brk]. reflexivity.
Qed.

End CANSEC1.
