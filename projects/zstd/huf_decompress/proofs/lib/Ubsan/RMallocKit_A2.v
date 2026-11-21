(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (31 recorded proofs replaced by written proofs (rpw_extP, rget_meta_rec_extP, rmeta_cells_extP and 28 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import F_malloc_free MallocTree MallocKit_A MallocKit_AB.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Export MallocKit_A2.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require KStep.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B2 RMallocKit_B3 RMallocKit_A RMalloc_fp.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RMallocKit_A2 () := "C46Stdlib5Lists4List2hdC47Corelib4Init9Datatypes3fstC35stdpp4base6LookupC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I35stdpp9countable9Countable00C47Corelib4Init5Logic8eq_ind_rC35stdpp4base;RelDecisionC35stdpp4gmap;gmap_lookupC35stdpp4gmap:gmap_emptyC35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap9gmap_foldC35stdpp8fin_maps:map_eq_iffC35stdpp4gmap;gmap_finmapC35stdpp4base4fmapC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC35stdpp8fin_maps@lookup_insert_eqC35stdpp8fin_maps@lookup_insert_neI35stdpp8fin_maps6FinMap00C35stdpp8fin_maps7MapFoldC35stdpp8fin_maps:map_insertC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base6InsertC35stdpp4base<PartialAlterC35stdpp4base5MergeI35stdpp4gmap4gmap00C35stdpp8fin_maps@lookup_delete_eqC35stdpp8fin_maps@lookup_delete_neC35stdpp4gmapBgmap_partial_alterC59OSSVerify5KrLib6Malloc:MallocTree7optr_inC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C59OSSVerify5KrLib6Malloc9MallocRep2pwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep2wzC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes6option02I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1N00I47Corelib7Numbers7BinNums1Z00I47Corelib4Init5Logic4True00K47Corelib7Numbers7BinNums1Z01C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc7s_metasC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes2idC59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C35stdpp4base6lookupC35stdpp6option;from_optionI59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5meta0C1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC45stdpp7numbers1Z6eq_decC35stdpp9countable;N_countableC35stdpp9countable;Z_countableC59OSSVerify5KrLib4Spec6Malloc3ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_free_meta_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<c_avail_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_tailC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_brkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_prevC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00I47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6a_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6g_metaC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep9meta_wordC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01c59OSSVerify5KrLib5Ubsan=RMallocKit_A28rpw_extPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep:meta_cellsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc8brkstate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep9rmrep_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst6SECRETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;c_init_doneC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib4Spec6Malloc>c_mmap_counterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocGc_avail_meta_area_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_meta_alloc_shiftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep?rctx_head_cellsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib4Spec6Malloc8c_activeC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List7map_extC59OSSVerify5KrLib6Malloc9MallocRep7activesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7c_usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep6usagesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9unmap_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep2b8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;c_unmap_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep:unmap_seqsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7bouncesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9c_bouncesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep8bouncessC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_seqC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep5zerosC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib6Malloc9MallocRep>ctx_tail_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib3Lib3Arr6u64arrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr5u8arrC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4mctx00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan4UImg5usegsC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01C59OSSVerify5KrLib5Ubsan:RMallocRep4RCTXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep9rarea_repC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8a_nslotsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib4Spec6Malloc4aaddC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan=RMallocKit_A2@rmeta_cells_extPC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan=RMallocKit_A2Brget_meta_rec_extPC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C59OSSVerify5KrLib4Spec6Malloc8AREA_HDRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6NSLOTSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9META_SIZEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep:rgroup_repC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z4landC59OSSVerify5KrLib4Spec6Malloc<g_active_idxC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC47Corelib4Init5Peano2ltC59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3mrdC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC59OSSVerify5KrLib6Malloc;MallocKit_B8agree_onC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC47Corelib4Init5Logic3notC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<find_segmentC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<seg_writableC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType9seg_bytesC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8seg_baseC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith6BinInt1Z4to_NC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?segment_byte_atI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C59OSSVerify5KrLib3Lib5Cells8cells_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5CellsBcells_bytes_lengthC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan=RMallocKit_A2?rbytes_at_agreeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan=RMallocKit_A2<rwr_at_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr4u64sC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3mulC47Corelib4Init5Logic8iff_reflK46Stdlib9micromega7EnvRing5PExpr05C46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib3Lib3Arr;u64s_lengthC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappC56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulK46Stdlib9micromega=RingMicromega3Op201C59OSSVerify5KrLib5Ubsan:RMallocRep5rmrepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep;rregions_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep=rmrep_globalsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep;rmrep_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep<rmrep_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep<rmrep_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_seqC47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List:length_mapC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symK46Stdlib9micromega6VarMap1t01C59OSSVerify5KrLib6Malloc<MallocKit_A2<agree_on_subC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan=RMallocKit_A2?rrw_cells_agreeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan=RMallocKit_A2=ru64arr_agreeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan=RMallocKit_A2<ru8arr_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst3CANC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03C59OSSVerify5KrLib4Spec6Malloc:get_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9cell_readC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc7cellval01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep;rshadow_repC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03C59OSSVerify5KrLib5Ubsan:RMallocRep6RMLOCKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep5RLIBCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep8RGOT_SSPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep:RSSP_GUARDC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep;RNEED_LOCKSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan4UImg:RPAGE_SIZEC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01I59OSSVerify5KrLib4Spec6Malloc7cellval00C1?~~~~~~~~~~~~~~~C35stdpp4base6insertc59OSSVerify5KrLib5Ubsan=RMallocKit_A2;rnr_regionsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic9False_indI47Corelib4Init5Logic5False00C56Stdlib6NArith6BinNat1N6eq_decI47Corelib4Init6Specif7sumbool00I47Corelib4Init5Logic2or00K59OSSVerify5KrLib4Spec6Malloc6region01C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01c59OSSVerify5KrLib5Ubsan=RMallocKit_A2>rnr_lookup_oldC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02c59OSSVerify5KrLib5Ubsan=RMallocKit_A2>rnr_lookup_newC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndI59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:new_regionC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_next_ridC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat3N2Z7inj_iffC56Stdlib6ZArith4Znat3N2Z9is_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib6Malloc9MallocRep5lr_loC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree>In_live_rangesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocAregion_live_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;live_rangesC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC59OSSVerify5KrLib6Malloc:MallocTree>ranges_free_InC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula06K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes:comparison00C59OSSVerify5KrLib5Ubsan:RMallocRep8rstaticsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_reservedC1?~~~~~~~~~~~~~~~C35stdpp8fin_maps;map_to_listC59OSSVerify5KrLib5Ubsan:RMallocRepArstatics_reservedC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9in_or_appC59OSSVerify5KrLib6Malloc:MallocTreeAranges_free_introC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan=RMallocKit_A2>rnr_lookup_invC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan=RMallocKit_A2@rnr_old_disjointC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses9not_morphC59OSSVerify5KrLib4Spec6Malloc;ranges_freeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;iv_disjointC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbK46Stdlib9micromega5Tauto8GFormula07C59OSSVerify5KrLib5Ubsan:RMallocRep<ref_reservedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan=RMallocKit_A2=rnr_lr_lo_newC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep>round_up_pg_geC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib5Ubsan:RMallocRep:rarea_concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep;rarea_lr_loC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C59OSSVerify5KrLib5Ubsan:RMallocRep;rgroup_concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep;lr_lo_groupC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan=RMallocKit_A2;rmrep_agreeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan=RMallocKit_A28rnr_concC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan=RMallocKit_A2>rmrep_ctx_extPC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan=RMallocKit_A2>rarea_rep_extPC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan=RMallocKit_A2?rgroup_rep_extPC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan=RMallocKit_A2:rnr_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocKit_A2Acell_read_shadow0C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC59OSSVerify5KrLib5Ubsan:RMallocRep?rshadow_rep_extC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7shadow0C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z8inj_succc59OSSVerify5KrLib5Ubsan=RMallocKit_A2>rnr_regions_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep8ticks_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree7ptrs_inC1?~~~~~~~~~~~~~~~C35stdpp8fin_maps:map_deleteC35stdpp4base6deletec59OSSVerify5KrLib5Ubsan=RMallocKit_A2;rdr_regionsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan=RMallocKit_A2>rdr_lookup_oldC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;set_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:set_shadowC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan=RMallocKit_A28rdr_concC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan=RMallocKit_A2>rdr_lookup_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep8lr_lo_geC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decC59OSSVerify5KrLib5Ubsan:RMalloc_fpCrreserved_disjoint2C1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphC47Corelib4Init5Logic5proj1c59OSSVerify5KrLib5Ubsan=RMallocKit_A2:rdr_shadowC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZC59OSSVerify5KrLib4Spec6Malloc5r_havC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_tickC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2leC59OSSVerify5KrLib4Spec6Malloc6r_havpC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N7compareK47Corelib4Init9Datatypes:comparison03C35stdpp4base:decide_relC35stdpp4base6decideC59OSSVerify5KrLib4Spec6Malloc9put_groupC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4ghdr01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem:length_le4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3le4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame:munch_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame6insideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;munch_writeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame:wmono_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;wmono_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep9s_staticsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells7cell_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells5csizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step>rw_cells_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells6cbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cell_updC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5s_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan<RMallocKit_B@rmrep_ctx_frameWC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@set_mmap_counterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7upd_ctxC1?~~~~~~~~~~~~~~~".
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

Lemma rbytes_at_agree m m' A bs : bytes_at usegs m A bs -> agree_on m m' A (Z.of_nat (length bs)) -> bytes_at usegs m' A bs.
Proof.
  intros (H0 & H1 & HB) AG. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  unfold mrd. rewrite (AG (A + Z.of_nat i)) by lia. apply HB. exact Hi.
Qed.

Lemma rwr_at_agree m m' A n : wr_at usegs m A n -> agree_on m m' A n -> wr_at usegs m' A n.
Proof.
  intros (H0 & H1 & HW) AG. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  unfold wview. rewrite (AG (A + i)) by lia. apply HW. exact Hi.
Qed.

Lemma rrw_cells_agree m m' A cs : rw_cells usegs m A cs -> agree_on m m' A (Z.of_nat (cells_size cs)) -> rw_cells usegs m' A cs.
Proof.
  intros [[Hwf HB] HW] AG. split; [split; [exact Hwf|]|].
  - eapply rbytes_at_agree; [exact HB|]. rewrite cells_bytes_length by assumption. exact AG.
  - eapply rwr_at_agree; eauto.
Qed.

Lemma ru64arr_agree m m' A ws : u64arr usegs m A ws -> agree_on m m' A (8 * Z.of_nat (length ws)) -> u64arr usegs m' A ws.
Proof.
  intros [HB HW] AG. split.
  - eapply rbytes_at_agree; [exact HB|]. rewrite u64s_length. replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws)) by lia. exact AG.
  - eapply rwr_at_agree; [exact HW|]. exact AG.
Qed.

Lemma ru8arr_agree m m' A bs : u8arr usegs m A bs -> agree_on m m' A (Z.of_nat (length bs)) -> u8arr usegs m' A bs.
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
ltac2:(KReplay.run1 (kr_t_RMallocKit_A2 ()) ["CANSEC1"; "DROPREGION"] "p'0p'1h04__x1h12L0h21Hh37__arithh44__ffh58__varmaph65__with74__x2h81rh94__x3h:4__x4h;4__p1h<1ah=4cstrh>5cstr0h?3Ha0h@5cstr1hA5cstr2hB2H0hC4__x5hD4__x6hE6__sat4hF2_HhG2HahH6__sat2hI6__sat3hJ1ni001nhK1qhL2rqhM1ohN4__x7hO2arhP1bhQ1ei011ehR2ghhS1khT2H2hU2NEhV3_H0hW3_H1hX6__sat1hY1vhZ1xi021xh[2H1h\2H3h]2Hqh^3_H2h_3_H3h`3_H4ha3_H5hb3_H6hc3_H7hd4__x8he4__x9hf2a0hg1ihh1phi2w8hj2H4hk3Ha1hl3NE0hm6__sat6hn6__sat9ho2r0hp2r1hq2r2hr1yhs2DDht3H10hu2H5hv2H6hw2H7hx2Hbhy3Hrahz3Hrbh{3P10h|2P9h}3RB0h~3RBCi034RESTi047__sat10i056__sat5i062rai072rbi083ridi094rid1i0:4rid2i0;1si0<2A1i0=2A2i0>2A3i0?3AGAi0@3AGCi0A3AGRi0B2ARi0C5ATOPRi0D2B0i0E2BCi0F3BCqi0G2Bqi0H2Bti0I2C1i0J2C2i0K2C3i0L2C4i0M2C5i0N2C6i0O2CXi0P2Cai0Q2Cbi0R2DJi0S2G1i0T2G2i0U2G3i0V2G4i0W2G5i0X2GLi0Y2GRi0Z3H1'i0[3H11i0\3H12i0]3H13i0^3H14i0_3H2'i0`2H8i0a2H9i0b2HBi0c3HWri0d2Hci0e5Hconci0f2Hki0g3Hk0i0h2Hoi0i2Hvi0j3Hw8i0k2Kbi0l2L1i0m2L2i0n2L3i0o2L4i0p2NKi0q5OTHERi0r2Pai0s2Pbi0t1Ri0u4RBALi0v3RFri0w3RL0i0x2RSi0y2SHi0z3Sa0i0{3Sa1i0|3SaLi0}3Sb0i0~3Sb1i103SbAi112WAi122WFi132WGi142WRi157__sat11i161gi172k0i181mi192q1i1:2q2i1;2sci1<3offp%0p%1p%2p%3p%4p&0p&1p&2p&3p;3p;2p;1p;4p;6p;9p;8p;5p;;p;:p;7p;<p;Bg02ENk31}Tg02FIk21|Tg00j8k31RTg02GJk21bTg02HMk31~Tg02INk21xTg02JPk21tTg00ZFR0j20Tg03GIk21lTg00Egk11OTg00=Hk40|Tg003\k41DTg02KRk11_Tg02MCj13Tg00@>j16Tg01Bjj1STg02\Yj1]Tg02]Oj1jTg035;k12aTg01FaR1j21Tg039Aj1FTg00Zak22>Tg00Hdk42;Tg00IBk629Tg00[Ak11^Tg00L4j6sTg00Dck20wTg001mj38k11]Tg020`j1GTg01N_j22Tg00]0k11yTg040=k22yTg00B\j2DTg034=k12tTg01F<j1ITg041>k314Tg00P>k11nTg00Q2k12`Tg00?@j2KTg00R3k12\Tg00S0k12[Tg00T1k12ZTg00U2k12STg00V5k21gTg00Vlk12QTg00K7k20NTg00Wbk11fTg00XYk11eTg00YPk11dTg00\9k10=Tg00]ij1vTg03m?k22ETg002ek61YTg01Xjk406Tg01R`k40LTg00DIj2ZTg011Uk22<Tg01EFj4rTg015Jk12:Tg0185k128Tg01;_k127Tg01>Qk126Tg01DBk125Tg0143j1VTg014Rk223Tg01ZSj2pTg02N:k222Tg00@ck121Tg00AAk120Tg012ZR2j1WTg00Adk20:Tg02NYk41?Tg02O5k41>Tg016Gk237Tg00CQj1aTg0191k236Tg019kk10KTg01<_k235Tg03TGk134Tg042Ek11{Tg043Ck22~Tg02m7S00k22}Tg02mWj2gTg02OTk22|Tg02P7k31zTg01_Aj4QTg01_hk11:Tg03Y;k12{Tg03YYk22zTg03Z:k31wTg02V?k21vTg00cYk11\Tg00^`k12xTg01aIk12wTg01agk12vTg01c5k21uTg01bRk21[Tg00EEk12uTg01eJk22sTg01elk22rTg01fXk32mTg01g7k42lTg030Kk30JTg02PTk12jTg03Q[k62iTg043ck41sTg02njk30ATg03UKk22hTg01CHk22gTg03V3k32eTg03D_k21UTg03VWk32dTg01O;R3j2:Tg01YDS01k21STg01]Hj4RTg02Q2l9wTg02R7j6hTg00lkk201Tg02@Sk31qTg02S?k61pTg02TEk61oTg03^jk82bTg00`mk10QTg01@Ek10_Tg02UJk12_Tg044lk30sTg02@5k11mTg045Rk42]Tg0465k60gTg00Ick12YTg03W:k62XTg01Lgj5nTg03X:k82RTg046^k31hTg0380k30kk20xTg025<R4j1|Tg036lk22PTg03N\k31CTg037Mk10zTg038aj2HTg03@Kk21ETg03@lk20[Tg03AIk21NTg03B0k21MTg03BWk21GTg03C=k21HTg03Cck21LTg00k7k12OTg00_@k11KTg01Mfk10}Tg01OWk20]Tg00e:k20^Tg01A:k12NTg01B5k22MTg02X=k22KTg00`5k12JTg00abk12VTg00bZk12WTg03`1m;2ITg03Zck62HTg01Uej4uTg03[dk21cTg01Vek21@Tg01WOk211Tg01Wmk10RTg03a8m:2GTg02[Xk40cTg0479k22FTg01o1k40{Tg02Xik215Tg02Ydk216Tg02Z^k12fTg00f:j3XTg02=hk62DTg02<`k62kTg03egk72CTg03OEk31aTg000Gk31WTg031lk32BTg02LLk12oTg01G^k42pTg01HQk42qTg01gim<1XTg02Vhk30dTg02WQk20uTg01`Mk22@Tg01cXj4mTg01hNk70HTg01i2k80hTg01`kk40nTg01dCk30vTg01dfk71<Tg02^Kk62?Tg03Eck72=Tg0295k130Tg02C?m<31Tg02BYmB32Tg01Y^k433Tg02bdR5f0R6+0wp>1Af5R7g00FnR8P5f4R9f3R:f2R;f1R<Es;86p=Og00HFR=/:6p=@%66#6p>05%66#6#6#6p>1Vg00GLR>1H<6;8=p=<11;</26p=5g03R?R?@1a<6p>1=g01n1R@g01nQRA786,0<p>0y12=</06p>0Z10<6,0;p=EA88<6#Gp=M%]6#jp=;12:;12<6'gp>0EB1W8>6p=\B2B8>6p=712=6p=4g02fQ&2o6g02gI38p=U10<6,0;,0:,09p=?21S56p==10<6,0;,0:p>191D;<=8>6p>0FB1a?<6=8@Ap>0G%I6#Ip>04%I6#I#I#Ip>0b%66#6#6#6#6#6#6#6p>0a%66#6#6#Sp=T12<6,0;p>0B%j6,1<p>1r%F6,2<p>0r12;</g6p>0q12;</06p>0V1H;<=8>=/06,0:p={P8P5P9P:P;P<Es20w56587p>0DP8P5P9P:B1W8>;P<Es=876p=i1H79=8>=11<6,2;,0:'0p>0011:;/2</06,09,07p=k11<6,2;p>0>12;</06,0:,09p>0oB1W8><=886#Gp=PA88<6p>18P8P5P:P;P<P6Esp>1j20w5698;<p>1k%G</06p>0i1H;<=8>=/06p=_11:;/2</06p>0lP910:;P<P6H0Lp=ef7R?f6RB119:/2;1H<6=8>='0,07'0'0p>0I11:;/2</06,09,07,0Bp>2A11:;/2</06,09p>1FPBP7P9P:P;P<P6H0LH0Lp>0j%66#Sp>1`g01J:S02P;P<P6H2pp>0Y%I6#6p=[Q02P;P<P6H2qp>0XQ02P;P<P6Crp=^%V6#Vp>24%V6#V#V#Vp>0;g01JoRC?8<6p>0WPCP9P:P;P<P6J1Yp=zA8>6=p>09%66#Ip=xA8><6p=>1Z>6p=BPCP>P6P2P<P;P:P9P7PBP?f8RDN<1Xp>1;21v>6p>0<B0d><6p=Lg01l7REg02hARF-0u<;X6p>0t22@>6p>08P;g01j8RGg01jWRHPHg01k7RIP>P<g02DgRJP6Cmg01kWRKK0Hp>1ZP:PGPHPHPIP;P<P6L0hp=CA8@6Ap>2nP>P;P<P6H0np=t21u>6p=oP;PGPHPHPIP>P<g01lcRLP6CmPKK0Hp=AP>P<PLP6Cmp>0PP;PGPHPHPIP>P<g01mJRMP6CmPKK0Hp>0OP9PGPHPHPIP:PGPHPHPIP;PKK0HP<P6L0hp=NPBPGPHPHPIP7P9P:PGPHPHPIP;P<P6L0hL0hp>0U12:;1:<6'0p>0@%I6#I#6#Ip=c21[>6p=J21[>6:0v><p>02P9PGPHPHPIP:PGPHPHPIP>P;PLP<CmPKK0HP6K1<p>0C1:<6,0;p=9B0d>;<:0d>:00uF=XE6p>0T20u;F20u<F=XE65XEp>13P>P>P9P:P;H0nP<P6H0np=fP<PGPHPHPIP6J2?p>17B0v><6p=YP;PGPHPHPIP<P6K2=p>0`P;PGPHPHPIP<P6K1<p>2c12<6,g;p>1211<6,:;p>0S12;</06,0:p>1T&306#Wp=`P:PGPHPHPIP>B0v>;<PLP6CmPKK0Hp=bg00fZS03?X<6p=lQ03&1K<;X6p=d%I6#6#6#6p>2^PCP>P>P>P2P2P7P9P:P;P<P6N<31p>10P>P>P>P>P>P>P1P6P<P;P1P:P9P7PBP?PDf9R1NB32p>0fP>P>P3P?P3PBP7P9P:P;P<P6N<1Xp>0eP:PGPHPHPIP>P;PMB0v><6CmPKK0Hp>0~B0J;<6:0J9:p>0?129:10<6,0;'0p>1i1H<6,2=p=}B0d><6:0d>;p>1QP>B0v>;<PLP6Cmp>1BP>P<PJP6Cmp>0mP7PGPHPHPIP9PGPHPHPIP:P;K1<P<P6L0hp>0pP?PGPHPHPIPBPGPHPHPIP7P9PGPHPHPIP>P:PMP;CmPKK0HK1<P<P6L0hp=qP8P>P6P4P<P;P:P9P7PBP?PDN<1Xp>1P12=;1:<6'0p>03P>P<PMP6Cmp>1IQ02P:P;Q03?X<6Crp=~g01S;S04,16p>0\Q02P:11;<P6Crp=y20:<6$1Kp>0MQ03Q03?X<67X;p>1JB0d><600uFp>2LAXE<6p>2TP>P9P:P>P;P<P6H0nH0np>2UQ02P;P<P6H33p>07p,2MRp,2rcRFp,2stRMp,1mR441}P021|FMS05B1RFM4S0621bF4S07B1~FM4S0821xM4S0921tM4S0:'0S0;'0S0<'0S0='0S0>p,3st'RKp,2m'RJ61}FRLP6Q05Q0>P0Q06Q0=PLP6Q06Q0=P0Q07Q0<PLP6Q07Q0<P0Q08Q0;PLP6Q08Q0;P0Q09Q0:PLP6Q09Q0:fAS0?Q05P021lFMS0@&1O5R3P8g00NPR2g00OBRNP5H0|ROP8P2PNP5H1DRPP<&1_MRQ&1A6RREOS0A%3<RS#@S0Bg00FIRT#6RU#6S0C#6S0D#6RV#6S0E#6S0F$05S0G$1VS0H#SRW,<SS0I%]<RX%jXRX&2aFRY55SS0J21=SX+0y+0Z3ERZ[^85`088S0KP3POPPP:PQ&1A;R[EOS0LP3POPPP;PQ&1A<R\EOR]1M7:R^%37S0M%;7S0N'1S0O%F:%3:R_%]:R`#jRa'1Rb%F7RcH0E[Rd[[^q5`0:8^p5`098S0P22>8>Reg00hJRf&1OfS0QPePfg0018S0RP8P2P>g00NiRgH2;S0SP8P2PNP>Pgg00O`J29S0TPfH0|S0UQ0RQ0SQ0TPfH1DS0VP<&1^MEs20wf6S0W38RgP3POPP%\:RNPQPREOS0X%7:R2#4S0Y%;6Rh952WS0Z1<2WS0[%U6Ri#GRj%F6Rk%36Rl/12S0\'2D?Rm'0X85#=Rn[]O]<S0]g00iARo&1OoS0^PePoQ0RQ0SQ0TPoH0|S0_Q0RQ0SQ0TPoH1DS0`P<&1yMEs20wo6S0a38RpQ0XPiQ0Y%SVRV=52hS0b1<2VS0cH19R2'0X85#=S0d[]R^PeS0e'0S0f'0S0g'0S0hPLP6Q0@Q0hP0Q0KQ0gPLP6Q0KQ0gP0Q0PQ0fPLP6Q0PQ0fP0Q0]Q0ePLP6Q0]Q0e%\6Rqp,3ridRr'M22y<6W]XKe1M6rXK8RsPqO11DM<:0FK<[^Kef:RqPrp,1rRtp,2HrRuO3%3tRv#@S0i1<vWS0j%]tS0k#4S0lQ0k#jRw,1vS0m/2YS0n20GvwS0o'0S0p'0S0q'0S0r'0P0Q0iQ0rPLP6Q0iQ0rP0Q0jQ0qPLP6Q0jQ0qP0Q0lQ0pPLP6Q0lQ0pP0Q0nQ0oPLP6Q0nQ0o&2tF%ITS0s#IS0t$04S0u$04S0v$0b$0bRL#6$0b$0b$1V$0a$0a#T/2YS0w%IL$0b$0b$1V$0a$0a#TS0x80BYQ0A1M;rRLfLS0yP:P;PrPtP<PuP6O7WUW]XL5XK8Q0A%3;%];+1r%FtS0zQ0m00r;40q\L[^L5^K821|FKB1RFKJS0{21bFJS0|B1~FKJS0}21xKJS0~21tKJS10'0S11'0S12'0S1321lFKP3POPPP<&1_KRuPREOS14PZ[^85`088RZP3POPPP:PuP[EOR[P3POPPP;PuP\EORxPd[[^q5`0:8^p5`098RdQ0QPePfQ0UQ0VP<&1^KS15EsQ0W38RyP3POPPPNPuPREORN/0mX85#=[^Of^<eRmQ0^PePoQ0_Q0`P<&1yKS16EsQ0a38S1710N2X85#=[^Ro^PeRN'0R2'0RzfQS18PZPzQ14B14;<610L]P01M:rS19Q0L%@_P_PW20G_a:0VbY-0Z`C{P61M7rP3POPPPBPQP7J0DR`fUS1:P?PBP6O3W2WFP<P6O2n2001000000120000000b<W]XL5XK8PdP2B14B7;1MBrS1;/0`P01M?rP3POPPP?PQPBJ0DS1<%3?S1=%]?S1>#jS1?'1S1@Q0O00r?80qcP61M1rRcP3POPPPqPQP1J0DR`B141DBP3POPPP1PQPDJ0D,0cP01MqrP`f<R`#3S1A%]`S1B#jS1C'1S1D%Fq%3qS1E%;q%F`3540qP61M`rP3POPPf=S1FPQP`J0DfZS1Gf@S1Hf?S1If>S1JQ1FP7P6PqO7Y0_WFP<P6O2n2001000000120000000b<Y0ZWFP<P6O2n2001000000120000000b<XU^XTxX[[Xq5Z1:8Xp5Z198PmPNfHS1KP;P<P6O3PnQ01P5P3POPPP9PQPREiS1L%79Rn#4S1MA5nWhS1N1<nWS1O11lnS1P:0BjkD?X85P3POPPP7PuPREiS1Q%77RN#4S1RPNPWPhPNPWPjPkPlPNJ00EkX85#=P6P3POPPPBPQPREiS1S%7BRm#4S1TA5mWhS1U1<mWS1V11lmS1W:0BjkD?P0P3POPPP?PQP\EiS1X%7?R\#4S1YA5\WXS1Z1<\WS1[%U<S1\#GS1]%F<11S\S1^'2D?P3POPP%\1RSPuPREOS1_%71R[#4S1`P[PWPhP[PWPjPkPlP[J00EkX85#=P6P3POPPPSPQ&1A:S1aEOS1b%7qRS#4S1c%;9S1d95SWS1e1<SWS1f%U9S1g#GS1h%F9%39S1i/1SS1j'2D?p,2PTS1k&1nMRx$2`,KsS1l&2\x,KsS1m&2[x,KsS1n&2Zx,KsS1o&2Sx,KsS1p21gM6,Ks`1;>S1qg00gOR^p-0Rc&2QxRxg00GjR2P2PsP<O1n01102000300002010811<Q0R20NM6Rd$1f,Ks&1ed,Ks&1dd,Ks3E_16S1rPs%\;RdO1Rb&0=<,KsRa'0\g^Of^<e%v<,KsR_,0b\p^Ro^Pe'0D?D?S1sP0Q1lQ1mQ1nQ1oQ1pQ1qP^PcPxP2P21M<rn01102000300002010811<S1tQ1r1MdrRd/0a\g^Of^<eS1u10d_\p^Ro^PeS1v'0S1w'0S1x'0S1y'0S1z'0S1{'0S1|'0S1}'0S1~P3POPPQ1JPuPREiS20Q1J#7Rp#4S2111pWS22Ph1<pWS23B0>klp7EjI0oX85#=P6Q1lQ1~P0Q1mQ1}P3POPPfBS24PuPREiS25Q24#7Rd#4S2611dWS27Ph1<dWS28B0>kld7EjI0oX85#=P6Q1mQ1}P0Q1nQ1|P3POPPfFS29PuPREiS2:Q29#7R_#4S2;P_PWPh1<_WS2<B0>kl_7EjEkX85#=P6Q1nQ1|P0Q1oQ1{P3POPPfJS2=PuPREiS2>Q2=#7Rg#4S2?PgPWPhPgPWPjPkPlPgJ00EkX85#=P6Q1oQ1{P0Q1pQ1zP3POPPfNRaPuPREiS2@%7aRx#4S2APxPWPhPxPWPjPkPlPxJ00EkX85#=P6Q1pQ1zP0Q1qQ1yP3POPPfRS2BPuPREiS2CQ2B#7R^#4S2DP^PWPhP^PWPjPkPlP^J00EkX85#=P6Q1qQ1yP0Q1tQ1xP3POPPfVS2EPuPREiS2FQ2E#7Rb#4S2GPbPWPhPbPWPjPkPlPbJ00EkX85#=P6Q1tQ1xP0Q1rQ1wP3POPPQ1G#\S2HPuPREOS2IQ1G#7RL#4S2JPLPWPhPLPWPjPkPlPLJ00EkX85#=P6Q1rQ1wP0Q1uQ1vP3POPPf^S2K#\S2LPuPREOS2MQ2K#7S2N#4S2OQ2NPWPhQ2NPWPjPkPlQ2NJ00EkX85#=P6Q1uQ1vP<f`R]f_RzQ2KO31P]rRZ&0=zS2P,Ks'0P0faS2Q/PrS2R&0=],KsP3POPPfcS2S#\S2TPuPREOS2UQ2S#7S2V#4S2WQ2VPWPhQ2VPWPjPkPlQ2VJ00EkX85#=P6Q2T018rS2X#GS2YQ2S$0=,KsP5P3POPPffS2Z#\S2[PuPREOS2\Q2Z#7S2]#4R{Q2]/1WR|PhQ2]/<WR}Q2]:0>kl7EjI0oX85PzP3POPPfeS2^#\S2_PQH1jR~B1k36]S2`P{P|%;]R|%U]S2a#G%F]%3]S2bQ2]40>5E}I0oXM3B1k3~zS2cQ2^#7S2d#4S2eQ2dPW%;zS2fQ2d%UzS2g%FzS2h%3zS2iQ2d40>+0i7_WH0lf[S2jQ1GDePOPPQ2_PuH1jRuQ2_02E<R}J1YH06WFY0rP<P6O2n2001000000121000000bfWcW|P<P6O2n2001000000121000000W2WbP<P6O2n2001000000121000000W2WaP<P6O2n2001000000121000000W2W`P<P6O2n2001000000121000000W2W_P<P6O2n2001000000121000000W2W^P<P6O2n2001000000121000000W2WWP<P6O2n2011000000121000000W2WVP<P6O2n2011000000121000000W2WFP<P6O2n2011000000121000000bhY03WyP<P6O2n2001000000121000000W2Z065P<P6O2n2001000000121102000bQXGyXOfX<eQ17fGS2kP;P<P6O3Q0dQ01P5Q1LPiQ1MA5nVhS0d1<nVS2lD?X85Q1QPiQ1RPNPVPhPNPVL0IX85#=P6Q1SPiQ1TA5mVhS1R1<mVS1QD?P0Q1XQ1\Q1YA5\VXS2m1<\VS2nH19Q1_PiQ1`P[PVPhP[PVL0IX85#=P6Q1bQ1gQ1cQ1d95SVS1`1<SVS1_H19Q1kQ1sP0Q1lQ1~Q20PiQ2111pVS20/2h1<pVS2oD?X85#=P6Q1lQ1~P0Q1mQ1}Q25PiQ2611dVS25/2h1<dVS2pD?X85#=P6Q1mQ1}P0Q1nQ1|Q2:PiQ2;11_VS2;/2h1<_VS2:D?X85#=P6Q1nQ1|P0Q1oQ1{Q2>PiQ2?PgPVPh1<gVS2?K2AX85#=P6Q1oQ1{P0Q1pQ1zQ2@PiQ2APxPVPhPxPVL0IX85#=P6Q1pQ1zP0Q1qQ1yQ2CPiQ2DP^PVPhP^PVL0IX85#=P6Q1qQ1yP0Q1tQ1xQ2FPiQ2GPbPVPhPbPVL0IX85#=P6Q1tQ1xP0Q1rQ1wQ2IPiQ2JPLPVPhPLPVL0IX85#=P6Q1rQ1wP0Q1uQ1vQ2MPiQ2OQ2NPVPhQ2NPVL0IX85#=P6Q1uQ1vP6P]PzQ2KO3%vzS2O,Ks,0ZP0Q2R%v]S2M,KsQ2UPiQ2WQ2VPVPhQ2VPVL0IX85#=P6Q2YQ2S#v,KsP5Q2\PiP{Q2]/1VRZ/2hQ2]/<VRLD?X85PzP3P~Q2`Q2aP{12Z|PLD?XM3Q2cQ2gQ2eQ2dPVQ2fQ2d/<VI1FQ2jQ1GDePuP}J1YH06WFY0sP<P6O2n2001000000121000000b<W{WcP<P6O2n2001000000121000000W2WbP<P6O2n2001000000121000000W2WaP<P6O2n2001000000121000000W2W`P<P6O2n2001000000121000000W2W_P<P6O2n2001000000121000000W2W^P<P6O2n2001000000121000000W2WWP<P6O2n2011000000121000000W2WVP<P6O2n2011000000121000000W2WFP<P6O2n2011000000121000000bhY03WzP<P6O2n2001000000121000000W2Z075P<P6O2n2001000000121102000bQWxXRoXPeH0LK0jDeQ0{Q13PMPKPsQ1kfCS13g01IC&1nK'ZPJP0Q02P4g01KmS0{22<FMS17CrS2eQ0{%IUS2g#6S2c$05S2a$1`S2`'1S2\&2:MS2W60Y4S2UQ0{Q0t#6Re#[#TS2J'1S2I&28MS2G60Y4S2FQ0{Q0s#6S2D#IS2C#6#[#TS2A'1S2@&27MS2>60X4S2qQ0{Q2C#I#[#TS2r'1S2s&26MS2t60X4S2uQ0{%6e#[#TS2v'1S2w&25MS2x5^4S2y'0S2z'0S2{'0S2|'0S2}B1RFMJS2~fbS30Q2eQ2}P0Q2UQ2|Q2~P6Q2UQ2|P0Q2FQ2{Q2~P6Q2FQ2{P0Q2qQ2zQ2~P6Q2qQ2zP0Q2uQ2yQ2~P6Q2uQ2yg01KNRe%VeS31#VS32#VS33#VS34#VS35#VS36#VS37#VS38#VS39#V$24$0;$0;$0;$0;$0;R}$0;$0;S3:$0;$0;Ru+23RL,pCRZ20W6uXJCR|PuP|1ZCuPZ222ueDzR{Q0F$21S3;$20R~PCP~%W6S3<-1gM-0:MXgCRbPLH1?'pPCP~PbPLH1>DzQ2W,p~S3=00WuS3>eQ3>PZP|P{PCP~Q3<-37M#aXgCR{PLH1?,p~PCP~P{PLH1>DzQ2G,p~S3?00WuS3@eQ3@223e}R~,pCRL20W6}XJCR{P}P{1ZC}PL222}eDzR|Q0D$21S3A$20RZPCPZQ3<-36M$0KXgCRbP~H1?'pPCPZPbP~H1>DzQ2>,pZS3B00W}S3CeQ3CPLP{P|PCPZQ3<-35M$0KXgCR|P~H1?,pZPCPZP|P~H1>DzQ2t,pZS3D00W}S3EeQ3EQ0k$34S3FQ0k/2wS3G&1{tS3HQ0z,2vS3I22~w=S3J&09wRt%GtS3K+2}S3LQ00PtQ3KQ0mQ0H#6#T%xT#x$05$0a#TS0HPvH0ES3MQ0mQ0H%6T$04#[#[$0a#TS3NPvH0E'0S3O/gtS3PP6Q3OQ3EQ3D#WR~Q0E#SS3Q'>R|&1]CR{&1]>S3R%W<Q3<'>20W<622|<641zXrCXZCRLQ3DP~%B~P}Q3QQ3Q#BRbN91;S3SP7CQS3TP|Q3CQ3B#WR^Q3Q'>RxP{Q3RPLQ3BP^%B^P}Q3QPbN91;S3UP?CQS3VPxQ3@Q3?#WRbQ2D#6S3W#6S3X$1`S3Y'>RgP{Q3RPLQ3?Pb%BbPuQ3YQ3Y#BR_N91;S3ZP1CQS3[PgQ3>Q3=#WRdQ3Y'>RpP{Q3RPLQ3=Pd%BdPuQ3YP_N91;S3\f;R_CQS3]PpQ3?$1:RL%4bRbQ3D$1:R{%4~R~Q3=$1:RS%4dRdQ3B$1:R[%4^R^&2{T-2z>S3^Q31$0<S3_61w>21v>eS3`'LS3a&1\ERe+0t&2xERE&08<S3b&2w>R\&2v>RX21u>TRm21[>=RN61ZXS3c&2uHRnQ3cCC22sXIRyP6P;1Z@A22r6;$2ndB2m>=<H2lRAb4b5b6X0>S3d&096S3e&09<[^0>S3fP6PwP1O2b3bAb@b>b=b1b1b1b180JtXQtP6O1Q3KQ3OPvPwfOS3gQ3TP|Q3VPxQ3[PgQ3]PpPSPdPLPbP[P^P{P~Q33$0<S33Q32$0<S32Q3_'LS3h'LS3i00tePE&2j>R@&08;S3j7t<P\PXPXPGPHPHPIQ3cJ2iPnPXQ0s#oRI=AXmPnPXPX20PNIPnB0OXNmDNK0UPyPAb4b5b6X0>X7>S0sQ3eg02l:[12;<S3e%4:S3c%@:S3k[[[^0>^7>S3lP6Q0kPwP1Q1Ff]S3mO5b3bAb@b>b=b1b1b1b1H1s80AtWJP6O1n200110;00021110111100c0;Q3Pg02_kS3nP6P6Q3nQ0E$04#TS0E'1S3oH0@p,2AGS3pP<Q3TP|Q3VPxQ3[PgQ3]PpPLPbP{P~PSPdP[P^%SURHQ0F#SRG+2hS0F%@HS3q%4G22gHGS3r#@[S3s[S3t%4HS3uB2eHG<V2WGS3vQ3uQ3r#4\2]GS3uP<g03FcS3w21U=H'ZQ3qeO1S3qQ3sPePEQ3bP\PXPXPX%6T#c#c#[#x#[#TR2#JS3xPmQ3xQ0E+02S3y:0OXmI0CS3zPnPXPXPNPm%JHQ3;62d>:0OXmI0CS3;CCPyPAb4b5b6X0>P2P6P6Q0E,12RHH0@S3{%4<S3|Q3r79<S3}[^0>P6Q1FP`O2b3bmc05bmbAb@b>b=b1b1b1b1Q3TP|Q3VPxQ3[PgQ3]PpPSPdPLPbP[P^P{P~Q34$0<S3~Q3i'LQ33Q32Q3_Q3`'LS3_'LS40'LQ35$0<S35Q33Q3`PeH0T413S41PE&089S42P;P@P<&08:S43DfS44P\PXQ3zPnPX217XBS45Q0C#oS46,YIS47Q0H#J5AXQ3N#J=AXI60`X62cXQ46>1ZXN60`XPnPX%oURU9AXIS48PnB0OXmUQ47=AXm60`XS49K0US4:CCPyPAb4b5b6X0>X7>X9>X:>X;cQ3{11:9S4;Q0HQ3NP:H0E,07&099'g129:1::9117B<12:S3N[[S0H[^0>^7>^9>^:>^;cP6Q3MPwPvQ0zPqP1P_P`O8b3bAb@b>b=b1b1b1b1g02^oS4<Q4<Q0C#SS4=60S<80V<S4>Q3nP<P<Q3oH0@S3og02`fS4?Q4?Q0D#SRG60S<80V<S4@g02adS4AQ4A>0S<G80V<S4BQ0APkP:11lhS0A,::H1TXL5#=XK8S4C-1S8S4D'gS4E'gS4F'gS4GQ3oQ4FQ3TP|Q3VPxQ3[PgQ3]PpPLPbP{P~PSPdP[P^PePEQ3bP\PXQ3zPnQ3zCCPyPAb4b5b6X0>Q3{P2P<P<PHH0@S3][^0>P6PqP1O2b3bAb@b>b=b1b1b1b1Q3oe40A40JO4WGX<>P4PJQ3nQ0ECRRhePh%6T#c#c#c#x#TRhQ175^JQ2`,1hS3nQ2W60YJS3{Q2J,1hS3[Q2G60YJS3VQ2A,1hS3TQ2>60XJS4HQ2r,1hS4IQ2t60XJS4JQ2v,1hS4KQ2x5^JS4L'0S4M'0S4N'0S4OP4PJPhQ17fIS4PP4PJP2Q0EPhQ17#`S4QP6Q3EP|Q3SP9CQS3SP|Q3CPxQ3UPBCQS3UPxQ3@PgQ3ZPDCQS3ZPgQ3>PpQ3\PqCQS3\PpPLPbP{P~PSPdP[P^PePEP@P\Q3x%JhS3>5AXPyPAb4b5b6122hP6b3bAb@b>b=b1b1b1b1Q3SP|Q3UPxQ3ZPgQ3\PpPLPbP{P~PSPdP[P^PePEP@P\Q3>Q2`+02S2`Q3y5AXPyPAb4b5b6Q3n/2HP6b3bAb@b>b=b1b1b1b1Q4Q=5hHeM9wEhQ3{Q4OP4PJQ3nQ2WfERhPuP4PJQ3nQ3<-01GS4OCRXJCP4PJP2Q0EQ3n%Wu-01GS3{P6Q3SP|Q3UPxQ3ZPgQ3\PpPLPbP{P~PSPdP[P^PePEP@P\Q3xQ2`5AXPyPAb4b5b6Q3n,22P6b3bAb@b>b=b1b1b1b1Q3SP|Q3UPxQ3ZPgQ3\PpPLPbP{P~PSPdP[P^PePEP@P\PXQ2`%JGS2`Q3Y#J61q>S4QQ3yCbPyPAb4b5b6Q3nQ3Y-01GS3Y;5HP6b3bAb@b>b=b1b1b1b1Q3nQ3{;5HeM9wQ3=P?DzJ1pQ3VQ4NP4PJQ3[Q2GQ0?PuP4PJQ3[Q4OCRXJCP4PJP2Q0EQ3[Q3{P6Q3SP|Q3UPxQ3ZPgQ3\PpPLPbP{P~PSPdP[P^PePEP@P\Q3xQ3>Q2J+02Ru5AXPyPAb4b5b6Q3[,22P6b3bAb@b>b=b1b1b1b1Q3SP|Q3UPxQ3ZPgQ3\PpPLPbP{P~PSPdP[P^PePEP@P\PXPuQ4QQ3yCbPyPAb4b5b6Q3[Q3Y;5HP6b3bAb@b>b=b1b1b1b1Q3[Q3{;5HeM9wQ3?PBDzJ1pQ4HQ4MP4PJQ3TQ2>Q1FP}P4PJQ3TQ3<CRXJCP4PJP2Q0EQ3T%W}RuP6Q3SP|Q3UPxQ3ZPgQ3\PpPLPbP{P~PSPdP[P^PePEP@P\Q3xQ3>Q2A+02S2A5AXPyPAb4b5b6Q3T,22P6b3bAb@b>b=b1b1b1b1Q3SP|Q3UPxQ3ZPgQ3\PpPLPbP{P~PSPdP[P^PePEP@P\PXQ2AQ3Q#JS2AQ3yCbPyPAb4b5b6Q3TQ3Q;5HP6b3bAb@b>b=b1b1b1b1Q3T?5uHeM9wQ3BP7DzJ1oQ4JQ4LP4PJQ4IQ2tP1P}P4PJQ4IQ3<CRXJCP4PJP2Q0EQ4IPuP6Q3SP|Q3UPxQ3ZPgQ3\PpPLPbP{P~PSPdP[P^PePEP@P\Q3xQ3>Q2r+02S2r5AXPyPAb4b5b6Q4I,22P6b3bAb@b>b=b1b1b1b1Q3SP|Q3UPxQ3ZPgQ3\PpPLPbP{P~PSPdP[P^PePEP@P\PXQ2rQ2AQ3yCbPyPAb4b5b6Q4IQ3Q;5HP6b3bAb@b>b=b1b1b1b1Q4I?5uHeM9wQ3DP9DzJ1oP4PJQ4KQ2xPDP4PJP2Q0EQ4KQ2x#`RuP6Q3SP|Q3UPxQ3ZPgQ3\PpPLPbP{P~PSPdP[P^PePEP@P\Q3xQ3>Q2v+02S3>5AXPyPAb4b5b6Q4K,22P6b3bAb@b>b=b1b1b1b1Q3SP|Q3UPxQ3ZPgQ3\PpPLPbP{P~PSPdP[P^PePEP@P\PXQ3>%JVS3>Q3yCbPyPAb4b5b6Q4K?5VHP6b3bAb@b>b=b1b1b1b1Q4K?5uHeM9wEhK0jK0jDeQ02PJQ0{Q17CrQ2\Q2W60YJQ2IQ2G60YJQ2@Q2>60XJQ2sQ2t60XJQ2wQ2x5^J'0D?ec0@bsbBb2c0oc0nc0mc0lQ2~eY0NY0MP<P6O2n2001000000121000000W2Y0LP<P6O2n2001000000121000000W2Y0KP<P6O2n2001000000121000000W2Y0JP<P6O2n2001000000121000000W2Y0IP<P6O2n2001000000121000000L2bQ0|Q12P0Q02P4Q4<%a=$0QQ03$1\Ru'lRHCrS03Q02P4g02c]&0K=$0_/luR^CrS4<Q02P4g02d^%aW/duS12CrS2eQ02P4Q4?Q4A#a/duCrS4?Q02P4Q4A&2_F/duS4ACrS2}'0S2U'0S2|'0S2FQ0|Q2KQ03Q2FP0Q4<Q2|Q0|P6Q4<Q2|P0Q2eQ2UQ0|P6Q2eQ2UP0Q4?Q2}Q0|P6Q4?Q2}Q3FQ3GQ3HQ3IQ3JQ3LQ00PtQ3KQ3PP6Q3OQ3dQ3fP6PwP<O2b380JtXQtP6O1Q3KQ3OPvPwQ2kQ0sQ3lP6Q0kPwP<P7fMR[O5b3H1s80AtWJP6O1n200110;00021110111100c0;Q3P%6T#c#c#c$05#TRt=^JH%xT#[$04#[$04$05$04$05$04#SRd=^J^S3P%6T#c#c#[$04$05#TRSQ125^JS3K%xT#x$05#[#[#x#x#TR~%6T#c#c$2^#[#TR{#a/duS3O5^JS0kQ4A9^J{S3l'0S0s'0S3fP4PJPtPHQ1H12t6Rb%`HS3d,1t796Q3pP<12t<RLQ34#WS00,1tS3L,:<Rp'0Q4=,1tRg99L<RxPLPpPLP6XZ>RpQ4=O1R|,1tR2,:<1ZcLA8cLLe:0sLLPp1:<6$1mXr>XZ>S3JP<P<%B<S3GQ3LP2PpPpPpP>P>g048<11<6H2]#BZ18>XJ>S3LPtPt%BtQ00P|PpPpQ3<#BXZCS3<Q34Q4=Q4=#BJ10N:0fL0eJ0gP6CQS34PxQ0FQ3tQ3vQ3uQ3qQ3sPePEQ3bP\PXPXPX%JtRCPmQ4=-02C:0OXmI0CS4=PnQ3;CCPyPAb4b5b6X0>A9b6gS00Q3}[^0>P6PBP9O2S3Fb3bHbXbHb?Q34PxQ41PEQ44P\PXQ4=PnQ4:CCPyPAb4b5b6X0>X7>X9>X:>X;cQ00Q0H[^0>^7>^9>^:>^;cP6Q3MPwPvQ0zP:P<P9P7O8S3Mb3b?Q3]12~<Rg11~GS2{79<Rb12{<RC11{GS2q79<R|Q4D'gS2z'gR2'gRLQ34PxPePEQ3bP\PXQ4=PnQ4=CCPyPAb4b5b6X0>Q00Px[^0>P6P:P<O2S00b3b?60AxO4WGX<>P4PJPtQ3dCReEhQ3PQ3fP4PJPdP^P`12d6S3f%`^S3P,1d796Q3pP<12d<R^Q31#WS3d,1dS4=,:<S34'0%STS2u,1dRT99^<RtP^Q34P^PpQ2uO1S34,1dS2y,:<1Zc^A8c^^e:0s^^PpQ3JP<P<Q3GQ4=Q2yPpPpPpQ3LPdPd%BdQ3dQ34PpPpQ3<Q31Q2uQ2u#BJ10N:0fL0eJ0gP6CQS31PtQ0FQ3tQ3vQ3uQ3qQ3sPePEQ3bP\PXPXPX%JdR^PmPXPmP^Q2u#JS34H0~I0CR^PnQ3;CCPyPAb4b5b6X0>Q3f?96TRTQ3}[^0>Q3Fb3bHbXbHb?Q31PtQ41PEQ44P\PXP^PnQ4:CCPyPAb4b5b6X0>X7>X9>X:>X;cQ0H\T^0>^7>^9>^:>^;cQ3Mb3b?Q3]Q31PtPePEQ3bP\PXP^PnQ3zCCPyPAb4b5b6X0>Q3]\T^0>Q00b3b?80A2:0JxLO4WGX<>P4PJPdQ3PCReEhQ3KQ0sP4PJPSQ12PD12S6S0sQ12#`S12,1S796Q3pP<12S<RdQ38#WRT,1SS3K,:<R^'011SGS3P99d<RtPdP^PdPpPGO1R^,1SS31,:<1ZcdA8cdde:0sddPpQ3JP<P<Q3GQ3KQ31PpPpPpQ3LPSPS%BSPTP^PpPpQ3<Q38PG%BGJ10S31N:0fL0eJ0gP6CQS3KPtQ0FQ3tQ3vQ3uQ3qQ3sPePEQ3bP\PXPXPX%JSRGPmPXPmPGQ2`H0~I0CRGPnQ3;CCPyPAb4b5b6X0>Q0sQ3P796RdQ3}[^0>Q3Fb3bHbXbHb?Q3KPtQ41PEQ44P\PXPGPnQ4:CCPyPAb4b5b6X0>X7>X9>X:>X;cQ0H\d^0>^7>^9>^:>^;cQ3Mb3b?Q3]Q3KPtPePEQ3bP\PXPGPnQ3zCCPyPAb4b5b6X0>Q3]\d^0>Q00b3b?80A2:0JxLO4WGX<>P4PJPSQ12CReEhQ0kQ3lP4PJP~Q3OP912~6RSQ3O#`Rd,1~796Q3pP<11~TRG,:<Rt,0gPbPgPtPg11~^Rt,:<1ZcgA8cgge:0sggPpQ3JP<P<Q3GPGPtPpPpPpQ3LP~P~%B~PTP^Q31N:0fL0eJ0gP6CQRtPbQ0FQ3tQ3vQ3uQ3qQ3sPePEQ3bP\PXPXPX%J~RGPmPXPmPGQ2`H0~I0CRGPnQ3;CCPyPAb4b5b6X0>Q2{99S6RSQ3}[^0>Q3Fb3bHbXbHb?PtPbQ41PEQ44P\PXPGPnQ4:CCPyPAb4b5b6X0>X7>X9>X:>X;cQ0H\S^0>^7>^9>^:>^;cQ3Mb3b?PxPLQ3]P2Q2zPtPbPePEQ3bP\PXPGPnPGCCPyPAb4b5b6X0>Pb\S^0>Q00b3b?60AbI0?O4WGX<>P4PJP~PdCReEhP4PJP{Q4AP:12{6RdQ4A#`R~,1{796Q3pP<11{TRS,:<RG,0CP|PCPGPC11{^RG,:<1ZcCA8cCCe:0sCCPpQ3JP<P<Q3GPSPGPpPpPpQ3LP{P{%B{PTP^Q31N:0fL0eJ0gP6CQR^P|Q0FQ3tQ3vQ3uQ3qQ3sPePEQ3bP\PXPXPX%J{RTPmPXPmPTQ2`H0~I0CRTPnQ3;CCPyPAb4b5b6X0>Q2q99d6RdQ3}[^0>Q3Fb3bHbXbHb?P^P|Q41PEQ44P\PXPTPnQ4:CCPyPAb4b5b6X0>X7>X9>X:>X;cQ0H\d^0>^7>^9>^:>^;cQ3Mb3b?PxPLQ3]P2Q2zQ4DP^P|PePEQ3bP\PXPTPnPTCCPyPAb4b5b6X0>P|\d^0>Q00b3b?60A|60JbI0?O4WGX<>P4PJP{P~CReEhH0LK0jDeQ0|ebsbBb2Y0WY0VP<P6O2n2001000000121000000W2Y0UP<P6O2n2001000000121000000W2Y0TP<P6O2n2001000000121000000W2Y0SP<P6O2n2001000000121000000Q0}Q11Q0RQ0QQ0RPfQ0UQ0VP<Q15EsQ0W38PMPKPsQ1kQ29Q0RQ0SQ0Tg00LcH0|&2YK'ZPJP;P<P6PFPMP;P<fiR~P6J2XQ0XQ0\:0FM:S0\Q0YQ0ZQ0[%@lS0ZQ0A/2YS0T9_lW5EjRj'0D?X85#=Q01P5Q1LQ1P:0FM9S1PQ1MQ1NQ1O/0jD?X85PFPMPJP9P:DnP6Q1SQ1W:0FMBS1WQ1TQ1UQ1V/0jD?P0Q1XQ1^:0FM?S1^Q1YQ1ZQ1[Q1]Q0BQ0IQ0JH19D?PFPMPJPDP?DnP6Q1bQ1j:0FMqS1jQ1cQ1eQ1fQ1hQ1i#@S1fQ1iQ1iQ1d;5YS1d7_W3ED?P0Q0M%7_S1h'1:0FM_S1iQ1h#4S1eQ1hPWQ0NQ1h%U7S0IQ0M#@S1]Q0MPWQ0O/2YS0OC{+0i7_WI1FPFPMPJP`P_DnP6Q1FQ1=Q1F#7'160FMS0MQ21Q22%]DS22#jS1[Q23%UDS23#G%3DS1Z#@S1VQ1Z/<WS1UQ1ZQ1[;5YS1OD?H1TP0Q1I#7S1N#4S0[Q1NPW%;1S0SQ1N%U1S0W%31Rj#@S0QPjPWQ0S=5jYS15C{+0i7_WH0lPFPMPJQ1HQ1IDnP6Q0?#7#4Q27Q1CQ28%U`#GQ1A#@S28Q1A/<WS27Q1D/2YS1D3EI1iP0Q13#7S0VQ1F#;S0U75WQ0VQ1F#UQ1F#3Rj#@S11PjPWQ0U=5jYS03C{+0i7_WPFPMPJfDRjQ13DnP6%7hS2FQ1I#]S4<#jS2|75WQ2<Q1H#U#GQ1H#3S2<#@S2eQ2</<WQ2<Q1H#]S2U#jS4?;5YS2}D?P0Q2k#7S0|/<WQ0?#UQ0?#3Rl#@S2zPlPWQ0?#;S00=5lYS3]C{+0iPFPMPJQ1KQ2kDnP6Q4P#7S3M/<W%Uj%3jS0H#@S4:Q0HPWQ0H%;jS41;5YS3FC{+0iP0%Uh#G%3hRl#@S3}PlPW%;h=5lYS2qC{PFPMPJQ0yfKS2`DnP6Q2k#U#GQ1K#3Rl#@S31PlPWQ1K#]-1rlS4A/2YS2{C{P0Q4P#3Rl#@S3OQ4P#;=5lYS3l9_lWPFPMPJfPRlQ3gDnP6Q2`#3S0k#@S12Q0y#3S3zQ3zQ0y#;S3K'1S3P/2YS0s7_WP0%3[S3f/<WQ3f%;[S2y'1S4=/2YPFPMPJfTS2~fSR{DnP6Q3g#3S2x/<W%3lS2w%;l;5YPFPMfWS2tQ2EQ18p+01OQ1:P[L2RQ18#FS2sQ18#3S2>Q2t#740>Q1kQ1sP0Q1lQ1~Q2H/MrP6Q1lQ1~P0Q1mQ1}Q2L018rRb#GR|P6Q1mQ1}P0Q1nQ1|Q30#\S2H/MrP6Q1nQ1|P0Q1oQ1{Q2[/MrP6Q1oQ1{P0Q1pQ1zfjS2[/PrP6Q1pQ1zP0Q1qQ1yfnS2@/PrP6Q1qQ1yP0Q1tQ1xfrRd/PrP6Q1tQ1xP0Q1rQ1wfvS2G/PrP6Q1rQ1wP0Q1uQ1vfz/PrP6Q1uQ1vf}RT/Prf|R^$0=,KsP<PTP^f{O341hWcW|P<P6O2n2001000000120000000WBWbP<P6O2n2001000000121000000WBWaP<P6O2n2001000000121000000WBW`P<P6O2n2001000000121000000WBW_P<P6O2n2001000000121000000WBW^P<P6O2n2001000000121000000WBWWP<P6O2n2011000000121000000WBWVP<P6O2n2011000000121000000WBWFP<P6O2n2011000000121000000bhfXR^/PrQ1GfYS2I#\S2WP{Q3gP6O4%3{%;{S2\'1Q0zQ0m00r{40qQ3HQ3IQ1:$1{Q1:#3S17Q1:+0rQ3m,DMS0{Q0{>0S6W80V6Q3pP<Q2NQ0y80kWS2N%4WRT%7z/}W[S4KQ2I#3R200xWS3y%42Q2j#3S3\/}W\T[S3ZQ0FQ3tQ3vQ3uQ3qQ3sQ37$0<S37Q36$0<S36Q3~Q40'LQ38$0<S38Q35Q33Q3^Q3261w>Q3`'LS3^41QS3U'L00teH0TS3SPE&087S3x?tB@S2vPBQ43P<&08BS0EP;P@PBQ42DfDfS3DP\PXPXQ2D#oS2D=AXmS4IPXPmQ2D%JWR2'YPnPXPXQ0t#oRLQ0C#IS0C#oRxQ2g#oS2gCbS0tPnPXB0OXNLS2rPnPXPXQ0D#oRG@1B2xPnPXPX20PNGPnPXPXQ2D1YLGS0D+0mPnPXPX217XDQ2gQ0x#J5AXS4LPnQ3;J0pDNDNS4JDNK0UGqPyPAb4b5b6X0>X7>X9>X:>XC>XD>X;c12;6S3B11;WS3T796A59B;S4M%@7S4HA5?WD%4DS3?11D1S3{,>?Q0x:0B`?%4?S3[Q3r79?[[[S3Y[[[[^0>^7>^9>^:>^C>^D>^;cP6Q0wQ2K#;fdS4Q#7S2JQ2K#3RSQ4Q,DMS4OPYP?PBQ1FQ24PaQ2BQ2EQ2ZO>b3bEbIbEc05bmP|Q2L#|R|%|rRC'>Rt#GRg&1]8S4NQ3R%|<%|6'>218<622P<641zXr8XZ8S3VQ2LP|%B|PrPC%BCS3=N91P:1CbtP7CQPg%\zS3n$0zQ3n#|#4&0zrS3@%4CS3CQ2Q#7S3EQ3g80kWQ30#7/}W\Tf\Rg#3S4R00xWQ4R#41HSWRt#4\T[Q3m#301EW&09WRb#GR|20[SW-01W/1t,>S[21NSW%@WS4SQ2i/HWRS@03SW[Q2i01MW1:W=S4TQ2b/HWRS,:W@0BS=[Q2b01GWQ2Q#3S2b00[W$09\bQ2b01HWQ30#3S4U/HWQ4U'>\bg03FGS4VQ4U01LWRSePS%7~S4W01EWQ2[#7RS20[SW-01W1HSW'1'>\|21NSWQ4SfkS4X#7S4Y/HWR|@03|W[Q4Y01MWQ4TflR|#7S4Z/HWRt,:W@0Bt=[Q4Z01GWfmS4T#7S4[00[W$09\bQ4[01HWQ2@#7Rt/HW/>t\bQ4V21LtWRtePtP9Q3w21U=W'ZQ4SeRtO1foS4S#7S2@/HWRb@03bWP_PtO1Q2[#3/HWRt@03tWQ37Q36Q3iQ38Q36Q35Q3^'LPeH0TH0TPEQ0E?t9@S3^P;&08D?t1@S3iP<&08?S4\P1&081S4]P:Q3xDfDfP\PXPXAAXLmS4^PXPm1YL2PnPXPXPGQ2c#oRtPUCbS2cQ47Q2C#oRb5AX60`XPnPX1YGxS2C9AXbPnPXPX21INGPnPXPX1Yx2S4_00PtPnPXPXQ2C-0mLPnQ49DNS2CDNDNK0UGqPyPAb4b5b6X0>X7>X9>X:>XC>XD>XN>Xd>Xe>1296S4`119WRb79611BDP;Q4;P1H0E11?DS4a,2q%@DA5qW_11q_,>11:B?Q3{<12B[S3{[[[[[^0>^7>^9>^:>^C>^D>^N>^d>^e>P6%F|%;|%7d%3|1DMdPwPvQ0zPhPjQ1KQ2=PlPgQ4QO?b3bjbtQ24Q0z':Q0mQ24412ec0^c0]c0\c0[btc0ac0`bwbvbubjb\bIbEb>b=blQ4>Q4GQ3oQ4FQ4@Q4EQ4BQ4DP8Q4CQ2LP5P3POPPQ3nPQPREOPkP;P;Q0AH0@S0A'0XL5P^P3POPPQ2LPQP^J0D%F^/2<%3^S2L%;^60S<Q2~Q2NQ4KQ3yQ3ZQ35Q40'LQ36Q3~Q3a41Q<13ePEQ42P;Q0E?tB@P<Q2v?t:@DfS2vP\PXPXAAXxUS40PXPUQ4_PnPXPX1YItRk-0PmPnPXPX21INIPnPXPXQ46:1Bt2PnPXPX20mxkPnPXPXPmPUQ47:0OXUS4_I0CS3ZDNS3yDNDNDNGqPyPAb4b5b6X0>X7>X9>X:>XC>XD>129<S4K?9<bB0><:B%@9S2NA5DWB11B1,>DP7PBPBQ4aH0@[S4a[[[[^0>^7>^9>^:>^C>^D>P6Q3EQ2Q,DMS3EQ2j#;S3nQ3\P9Q2j#FP:P1Q1IQ2`P{O;b3bIbEDeH06H06I0?I0?O4W?Xf>P4PJ1DMgS4bPWCRRbePbp+01IQ3mPgQ2jO3P4Q0{&2OF#a$1KS4c&0=g-0:M&0}g#a$0Q/lH'dC~g01T4:0366RbP41DMz$0\g01Tk001<S4dQ04Q4d'1Rk-0]z-0NM-0^MCy[^S>P4Q0{Q0v$05#TRd&2N}-2M}/luS0vCy3EP0P4Q2K,DMS0{Q4cQ3m$0=-0:MQ3m$0}#a$0Q/lH'dC~P41DM]S04$0\Q4d20]]k-0NM-0^MCy\b^S>P4Q0{PdQ0vCy'0PFPMPJPzQ2KDnP6P4Q04Q4cQ2P-0:M&0}z#a$0Q/lH'dC~P4Q2S,DM$0\Q4dQ2S00]k-0NM-0^MCy\b^S>P4Q3EPdQ0vCy'0P0P4Q4O$0\Q4dQ4Q00]k-0NM-0^MCy\b^S>P4Q30,DMR}PdQ0vCyPFPMPJQ2SQ30DnP6P4Q2Z,DMR|$0\Q4dQ2Z00]k-0NM-0^MCy\b^S>P4Q2^,DMS2ZPdQ0vCyQ4cQ2^$0=-0MMQ2^$0}#a$0Q/lH41JRH9^J|fhS4c,DMS4O$0\Q4d'1S4dQ4c00]k-0NMRk-0^MS2P5^J\b^S>S4e11|dS4fQ0v5^JS4gP4PJP|PHP7P4PJP|PWP|%`HS4hP1Q2]Q2~80kWS4ifg#7S4j/}W\TS4kQ2b00xWS4lQ2b#4Q2S#3S2S/}W\T[S2bPePEQ3bP\AAXmmPyPAb4b5b6X0>1266^0>P61DM~O1S4mb3bIbEQ4iQ4kQ4lQ2bPePEQ3bP\Q3X#SRH-02mS3X1Ym2S4n5AXPyPAb4b5b6X0>116WS4o956H^0>Q4mb3bIbEQ4h11|WS4p55|eM9wEhQ4eQ4gP4PJQ4dQ2PP:P<P6O2P4PJQ4OPWQ4O/1HQ2a#SS2a001<'1Q3:#WS3:P_Q4c#7R2Q2E80kWS4cQ4W/}W\TS4gQ2S00xWS4eQ2S#4Q2^#3S2^/}W\T[S2SQ3`Q3`Q33+2L+2K02TeS4hPEQ3jP<P@P:Q43I2US4qP\PXPXAAXNUS4r217X7S4sPnPXQ2rPnQ3XQ2a#JS4t>1q>U'YS3X9AXmCCJ0pPyPAb4b5b6X0>X7>X9>X;cQ3|/0:Q3k11;HQ2a001:'1RH,2;[[^0>^7>^9>^;cP6Q3W#I#x#SRT,:9Q2^P9Q4X,DMS4XP:Q4PO6b3bIbEQ4cQ4gQ4eQ2SQ4hPEQ4qP\PXPXQ4sPXPU%JTPnPXQ2rPnPXQ3XQ4tQ4nCbCCGqPyPAb4b5b6X0>X7>X9>X;cA9:<TQ3kQ2aQ3T55H[[^0>^7>^9>^;cP6%49RHQ2^P9Q4XP:Q4PO6b3bIbEM9wP4PJQ4dQ3:CReP4PJQ4d&1fk-0:M&1ek-0:M&1dk-0:M&2Jk#a$0Q&2Vk#a$0Q&2Wk#a/du41J'd'd'd#`CReP4PJQ4dQ2P#`CReEhZ0gbZ17>P4PJQ4fQ0vP6P4PJP|PWQ4fQ0v#`R|P1Q4iQ4kQ4lQ2bPePEQ3bP\202mdRb9AXmPyPAb4b5b6X0>116dRd,26^0>Q4mb3bIbEQ4iQ4kQ4lQ2bPePEQ3bP\PXPbQ2AQ4nCbPyPAb4b5b6X0>Q3QQ4o55d^0>Q4mb3bIbEQ4fQ4p75|eM9wEhH0LDeY0>Y0=P<P6O2n2001000000121000000W\Y0<P<P6O2n2001000000121000000boc0?bTb[bBbUb2W~Y0uP<P6O2n2001000000121000000W2W}P<P6O2n2001000000121000000W2Y0pP<P6O2n2001000000121000000W2Y0|P<P6O2n2001000000121000000W2Y0{P<P6O2n2001000000121000000W2Y0zP<P6O2n2001000000121000000W2Y0PP<P6O2n2001000000121000000W2WyP<P6O2n2001000000121000000W2Z065P<P6O2n2001000000121102000bQN;2IWGXOfW<Q0}eQ0~Q10Q0RQ0^Q0RPoQ0_Q0`P<Q16EsQ0a38PMPKPsQ1kQ29PJP;P<P6PFPMP;P<P~P6J2HQ0XQ0\PiQ0YQ0bQ0cQ0ZQ0T'0RF3ED?X85#=Q01P5Q1LQ1PPiQ1MQ0dQ2l;EFD?X85PMPJP9P:CuP6Q1SQ1WPiQ1TQ1RQ1Q;EFD?P0Q1XQ1^Q1\Q1YQ2mQ2nQ0BQ0J3ED?PMPJPDP?CuP6Q1bQ1jQ1gQ1cQ1`Q1_Q1fQ1d3ED?P0Q1iQ0IQ1eQ1hPVQ0NQ1hQ1]Q0O'07_VEkPMPJP`P_CuP6Q0MQ23Q21Q20Q1[Q2oQ1VQ1O3EI0oP0Q0WQ0[Q1NPVQ0SQ1NQ0QQ15'07_VI1FPMPJQ1HQ1ICuP6%U_Q26Q25Q1CQ2pQ28Q1D3EH1TP0Q0V#4Q0VPVQ0UQ0VQ11Q03'07_VH0lPMPJPjQ13CuP6Q2F#4Q2;Q4?Q2:Q2eQ2}I1iP0Q0|Q0075VQ0|Q2zQ3]'07_VPMPJQ1KQ2kCuP6Q3MQ13#;RF75VQ2?Q4:Q3F3EP0Q2`#7/<VQ3}Q2q'0PMPJQ0yQ2`CuP6%7[/<VQ31Q2{'0P0Q3OQ3lPMPJPlQ3gCuP6Q12Q0sQ1kQ1sP0Q1lQ1~Q1:/PrP6Q1lQ1~P0Q1mQ1}Q2W/MrP6Q1mQ1}P0Q1nQ1|Q3m/PrP6Q1nQ1|P0Q1oQ1{Q2RP6Q1oQ1{P0Q1pQ1zQ2_/MrP6Q1pQ1zP0Q1qQ1y1P~rP6Q1qQ1yP0Q1tQ1xQ4T/PrP6Q1tQ1xP0Q1rQ1wfq/PrP6Q1rQ1wP0Q1uQ1vfu/PrP6Q1uQ1vfxRi/PrfwRf#v,KsP6PiPfQ2GO341hW{WcP<P6O2n2001000000120000000W2WbP<P6O2n2001000000121000000W2WaP<P6O2n2001000000121000000W2W`P<P6O2n2001000000121000000W2W_P<P6O2n2001000000121000000W2W^P<P6O2n2001000000121000000W2WWP<P6O2n2011000000121000000W2WVP<P6O2n2011000000121000000W2WFP<P6O2n2011000000121000000bh1P{rQ1:Q2~#\PaQ2=P6O4%3aR{%;aRf'1Q0zQ0m%FaRiH0EQ3HQ3I21clj%FlQ2w'>f~Q2tQ2EQ1:O3P41DM^Q2t#v-0MM&0_6/luRjC~Q3A01@6Q0u#SRs+11R|Q2t$0R'>'0XiZ-1SZQ01PZP4Q2I,DM%v^-0MMPjC~&0R^,>|'0XiZPMPJQ2IP^CuP6P4Q2j,DMQ1G#v-0MMPjC~Q1G$0R,>|'0P0P4Q4bQ2j#v-0MM&0_</luC~Q3A01@<011sQ2j$0R'>PMPJQ3mPgCuP6P4Q0{Q3m#v-0MM&0_:/luC~Q3A01@9011sQ2K$0R'>PZPJQ3EQ2M-0MMRdPjC~&0R],>|'0XiZP7Q04Q2O-0:M&0_7/lu'dR|5^JQ3A01@7011s&0Rz'>P4PJQ04P|P<Q3EQ3E&0_B>1Jdu#`60S680V6Q3pP<12}<RdQ39#WRu,1}Rz,:<Rs'0Q0C#SR],1}99d<RjPdPsPdPpP]O1Rs,1}Rb,:<&1mdPpQ3JP<P<Q3GPzPbPpPpPpQ3LP}P}%B}PuPsPpPpQ3<Q39P]%B]J10N:0fL0eJ0gP6CQRpPjQ2V@0kV[Rs%4VRuQ2J/}V[R}Q0FQ3tQ3vQ3uQ3qQ3sQ3SPEQ3DP\PXPXQ4IPXPmQ2D%J]Rb'YPnPXQ0tPnPXQ2rPnPXPXQ3>>1BGxPnQ4JDNK0UGqPyPAb4b5b6X0>X7>X9>X:>XC>XD>X;cQ3B11;]796Q4MQ4H11?VRz/2DQ3Y[[[[^0>^7>^9>^:>^C>^D>^;cP6Q0wQ30#;P2Q4UQ4OPYP?P7PhQ29PaQ2BQ1GQ2[O>b3c04bnc04c15bkPpPjQ2YQ2T#|Rd/>CRk#GRTQ2XQ4NQ3RQ3VQ2TPd%BdPrPCQ3=N91P81CkQ1ICQPTQ4Q#\RT$0z%|T#4Q3@Q3CQ2]@0kVlQ4j/}V\uQ4j01EV&09VRu#G20[2V-01V1H2V'1,>2[21N2V%@VR2Q4W/HVRT@03TV[Q4W01MV1:V=1HSVRT,:V@0BT=[21GSVQ4Y00[V$09\uQ4Y01HVQ4Z/HVQ4Z'>\uQ4VQ4Z01LVRuePuP9Q3w21U=V'ZP2eO1Q4[/HVR2@032VQ38Q36Q3UQ37Q35Q3~Q3h'LR2PeH0TH0TPEQ0EQ4]7t9P;Q3iP<Q4\P1P@P:Q3xDfDfP\PXPXQ4^PXPm1YLbPnPXPXQ3W#oR=00mGPnPXQ2cQ47=AX=60`XPnPXPXPxQ3>PtCbPnPXPX20PNxPnQ2CDNK0UDNGqPyPAb4b5b6X0>X7>X9>X:>XC>XD>XN>Xd>Xe>Q4`119]R]7961>1B11?1P:1197R=PqH0EA51Vq%4qQ3{[[[[[^0>^7>^9>^:>^C>^D>^N>^d>^e>P6%F~%;~Q2@%3~Q4S,DMPwPvQ0zQ1JP`Q1KQ2=Q1:Q2IQ2QO?b3b\Q0z,:`Q0m<12`ebwbvbubjb\bTbnb>b=blbkQ4>Q4GQ3oQ4FQ4@Q4EQ4BQ4DP8Q4CQ2HP5P3POPPQ2TPQPREOQ0A'0XL5PgP3POPPQ2HPQPgJ0D%Fg/2<Q4R%;g60S<P^PpPjPsP}Q35Q33Q3_'LR}'LQ36Q3~Q32Q3a'L41Q<13ePEQ2vP\PXPXQ40PXPU1YxbPnPXB1ZXmIRbPnPXPXPtQ3>Q46CbPnPXPX20PNtPnQ3yDNK0UGqPyPAb4b5b6X0>X7>X9>X:>XC>XD>Q4K?9<]1><:R]12z7Q3?Q4a[[[[^0>^7>^9>^:>^C>^D>P6Q2dQ2ZQ2fQ2iP9Q2hP;Q1JQ2`Q3gQ2tO;b3bnbkDeH06H06I0?I0?O4W?Xf>P4PJQ04%`|CReEhP6H0LH06Y0jY0tP<P6O2n2001000000121000000WTXiZP<P6O2n2001000000121102000bob[bBb2bUW~W}P<P6O2n2001000000121000000W2Y10P<P6O2n2001000000121000000W2Y0~P<P6O2n2001000000121000000W2Y0}P<P6O2n2001000000121000000W2Y0kP<P6O2n2001000000121000000W2Y0QP<P6O2n2001000000121000000W2WzP<P6O2n2001000000121000000W2Z075P<P6O2n2001000000121102000bQN:2GWxXRoWPQ0~eQ14Q1\B14:;<Q19Q0L'0P01M9rP3POPPP9PQQ1aEOPKPJP7P9H0cP6Q1;Q1<PMPKPJPDP?22FD<Q2EPDP?P6O3Q1=#@Q1=PWQ1>Q1@Q1=Q1?+0G80VY+0ZC{P0Q1VQ1UQ22#4Q1OQ1ZQ1[+1=+0y3EPMPJPqP1H0cP6Q1E#@%3_RK%]_R_PK%j_R_PY20GK_H0l+0Z7_WP0Q27Q1BQ1DQ1AQ1C+1=+0y+0ZPMPJQ1JQ1FH0cP6Q1J#3/<WQ4<Q1I#3RWQ2|PYQ2|-0GWH0l+0ZP0Q2U#4Q2}Q2<Q4?+1=+0yPMPJQ24Q0?H0cP6Q24#]#4Q13#3RWPFPY20GWFH0lP0Q3FQ0HQ41+0GPMPJQ29PhH0cP6Q29#3Q29#;;5YQ2k#3Q2k#;+0GQ2=Q4PQ1KQ0?Q24O4Q4AQ0zQ0mQ1K+0r40qQ3HQ3IQ2=Q1K+1cQ2=#FQ2=#3'>Q3zP6P6Q3PH0@Q3pP<Q0FQ3tQ3vQ3uQ3qQ3sQ35Q32Q3`'LRW'LQ3~/L}<13ePEP@P9Q43P<Q3jQ427t9DfP\PXPXQ4IPXPmQ2D/YLRFPnPXPXQ2g-0PFPnPXPXQ2D-1INPnPXPXQ45Q4LPnQ3;J0pDNDNGqPyPAb4b5b6X0>X7>X9>X:>X;cQ3B11;:RN796Q4;/2;Q2NQ0x:0B?9Q3r99H9[[[[^0>^7>^9>^:>^;cP6Q0wQ18#;RFQ2>PYP7P9PqQ29Q2~O9b3bEbIbE218arRq#G%|aRY/>CR_#GRKQ4NQ3RQ3VPaPY%BYPrPCQ3=N91P:1Cq_Q2kCQPKQ3@Q3C&0zl%|l#4Q35Q33PW20t2eH0TPEQ3^P;P@P<Q4\P?P@P:Q3xDfDfP\PXPXQ4^PXPmQ0DPnPXPX20mxLPnPXQ0D=AXUQ47=AXx60`XPnQ49CCDNGqPyPAb4b5b6X0>X7>X9>X:>XC>XD>XN>Q4`?96=1>?711B?P:P=PDH0EQ3N[[[^0>^7>^9>^:>^C>^D>^N>P6Q2sPFQ2>PwPvQ0zP7P9PBPDO:b3b>b=blQ4>Q4GQ3oQ4FQ4@Q4EQ4BQ4DP8Q4CPaP5P3POPPQ3gPQPREOQ0A'0XL5P[P3POPPPaPQP[J0D%F[/2<Q4=,:<Q2920t}ePEQ44P\PXPXQ48Q4_PnPXPbPnQ3ZCCJ0pPyPAb4b5b6X0>X7>X9>X:>Q3e?9<NP;P:P:P=H0@\][^0>^7>^9>^:>P6PfP{P;PiP<P:O6b3DeH06H06I0?I0?O4W?Xf>P4PJQ0kQ2`#;CRRiePifsP[Q0yPhQ2=O4Q02P4Q3zQ3KH0{Q3|?9<fg02hmRf215Ml016;&2f<Rl38Q2w/1:&0K;&1\ZRh5XZR[6074Q0G#SRi:03;;R{'0[[^Y>^M>'0P0Q02P4Q3fQ2yH0{Q3|Q3g#;R]79<Q18-15M016;=8flQ2>/1:>074[/0{[[^Y>^M>PMPJQ3gPaH0cP6Q02P4Q2xP]H0{Q3|Q2B#;79<Q2~-15M016;=8flQ2~#3/1:>074[/0{[[^Y>^M>Q02PJQ2>PFH0{Q3|Q2\79<R]Q1:-15M016;=8flRlQ17/1:Rf>07J[/0{[[^Y>^M>P4PJQ2>PFP<P7J2DP9P:P;P<P6O4B074f[/0{P0Q2E#3/19&0K:=XZh6074Q3c?9:iQ2t#3/17&0K9=XZh607J1:9i7EHP6Q2L/1B&0K7=XZh6074B03BBiQ1G#3RB/1DRD&0K?=XZhRh607JQ3[1:?iP4PJPDPhP<P4PJPBQ1G#;PDQ3dQ1JPePEQ3j?t<@P\PXPXQ4r217X9Pn1YmUR99AXmJ0pPyPAb4b5b6X0>X7>X;cQ3|/0;11<;R@,2<[^0>^7>^;cP6Q3n,:1P1Q3\P?O4b3PePEQ3jQ437t<P\PXPXQ4sPXPUPIPnPXP9Q341YmICbGqPyPAb4b5b6X0>X7>X9>X;cA9:<;Q2u11<:55@[^0>^7>^9>^;cP6%41Q3nP1Q3\P?O5b3M9wP4PJPD1pZh#WCReJ2kP6DeY0iY0HP<P6O2n2001000000121000000b<Z0dlZ0h]XY>XM>H0LY0bY0cP<P6O2n2001000000121000000boc0AbTb[bBWWY0FP<P6O2n2001000000121000000WBWVP<P6O2n2001000000121000000WBWFP<P6O2n2001000000121000000WBY0GP<P6O2n2001000000121000000b<K2CW2WUP<P6O2n2001000000121000000b<Y0fW]XL5XK8Q10eK0jK0jDec0qc0CY0vY0EP<P6O2n2001000000121000000W2Y0wP<P6O2n2001000000121000000W2WFP<P6O2n2001000000121000000W2Y0DP<P6O2n2001000000121000000b<c0eY13Y11P<P6O2n2001000000121000000W2Y0RP<P6O2n2011000000121000000W2Y14P<P6O2n2011000000121000000W2Y0xP<P6O2n2011000000121000000b2Y0yY0YP<P6O2n2001000000121000000W2Y0BP<P6O2n2001000000121000000W2Y0XP<P6O2n2001000000121000000W2Y0OP<P6O2n2001000000121000000W2Y12P<P6O2n2001000000121000000b2o"). Qed.

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
  rw_cells usegs m (conc st b) [C8 (pw st (Some g)); C1 w8] -> Z.land (bv_unsigned w8) 31 = Z.land ai 31 ->
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
  pose proof (wmono_write usegs m m (wa (RCTX + 12)) (le4 (wz v)) (wmono_refl usegs m)) as WM.
  eapply (rmrep_ctx_frameW st (upd_ctx (set_mmap_counter v) st) m _ _ MR MU WM); try reflexivity.
  - intros lo hi [E|[]]; inversion E; subst. unfold RCTX. lia.
  - left.
    pose proof (rw_cells_write usegs m RCTX (rctx_head_cells st) 12 (C4 (wz (c_mmap_counter (ctx st)))) (C4 (wz v)) X1 eq_refl eq_refl I) as W.
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
