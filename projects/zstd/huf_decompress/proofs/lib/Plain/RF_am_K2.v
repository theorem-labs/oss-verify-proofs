(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (14 recorded proofs replaced by written proofs (rmrep_agree_but_ctx, rmrep_ctx_mid_agree, rarea_in_live and 11 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk Arr ITree Nodes.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import PImg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocKit_A2.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import F_malloc_free MallocTree MallocModel_B F_ntf_B F_am_K F_am_K2.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B2 RMallocKit_B3 RMallocKit_A2 RF_am_K.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_am_K2 () := "C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC35stdpp4base6lookupC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I35stdpp9countable9Countable00C35stdpp4base;RelDecisionC35stdpp4gmap;gmap_lookupC35stdpp4base4fmapC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~I35stdpp8fin_maps6FinMap00C35stdpp8fin_maps7MapFoldC35stdpp8fin_maps:map_insertC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base6InsertC35stdpp4base<PartialAlterC35stdpp4base5MergeI35stdpp4gmap4gmap00C35stdpp8fin_maps:map_eq_iffC35stdpp8fin_maps@lookup_insert_eqC35stdpp8fin_maps@lookup_insert_neC35stdpp4gmap:gmap_emptyC35stdpp4gmapBgmap_partial_alterC35stdpp4gmap9gmap_foldK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib5Plain:RMallocRep5rmrepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep;rregions_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep9rmrep_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep=rmrep_globalsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep;rmrep_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep<rmrep_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep<rmrep_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc7s_metasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_shadowC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib5Plain:RMallocRep9s_staticsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib5Plain8RF_am_K22A28agree_onC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init5Logic2eq01C59OSSVerify5KrLib4Spec6Malloc4concC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C59OSSVerify5KrLib5Plain:RMallocRepErregions_wf_restaticsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep2wzC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep2b8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst3CANC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2lec69OSSVerify5KrLib5Plain8RF_am_K22A2<agree_on_subC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib5Plain8RF_am_K23RA2?rrw_cells_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst6SECRETC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6a_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8a_nslotsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib4Spec6Malloc4aaddC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep:meta_cellsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C59OSSVerify5KrLib6Malloc9MallocRep5zerosC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep9rarea_repC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep2pwC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib4Spec6Malloc6m_prevC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep9meta_wordC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes2idK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02C56Stdlib6ZArith6BinInt1Z6of_natK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z2ltK46Stdlib9micromega=RingMicromega7Formula01C59OSSVerify5KrLib6Malloc;MallocKit_B8agree_onC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6g_metaC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z4landC59OSSVerify5KrLib4Spec6Malloc<g_active_idxC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib5Plain:RMallocRep:rgroup_repC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9cell_readC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc7cellval01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep;rshadow_repC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib5Plain8RF_am_K23RA2<rwr_at_agreeC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthc69OSSVerify5KrLib5Plain8RF_am_K23RA2?rbytes_at_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega7EnvRing5PExpr03C35stdpp6option;from_optionK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep6RMLOCKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep5RLIBCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep8RGOT_SSPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep:RSSP_GUARDC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain4PImg5psegsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep;RNEED_LOCKSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain4PImg:RPAGE_SIZEC1?~~~~~~~~~~~~~~~C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums1Z01C59OSSVerify5KrLib4Spec6Malloc8AREA_HDRC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5meta0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7shadow0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib6Malloc:MallocTree3memC1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableC45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableI59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib4Spec6Malloc6NSLOTSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9META_SIZEC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205I59OSSVerify5KrLib4Spec6Malloc7cellval00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep7activesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep6usagesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep:unmap_seqsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep?rctx_head_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep8bouncessC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep>ctx_tail_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9unmap_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7bouncesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8c_activeC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List7map_extC59OSSVerify5KrLib4Spec6Malloc7c_usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;c_unmap_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9c_bouncesC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_seqC47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List:length_mapC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegc69OSSVerify5KrLib5Plain8RF_am_K23RA2=ru64arr_agreeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib5Plain8RF_am_K23RA2<ru8arr_agreeC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C59OSSVerify5KrLib3Lib3Arr5u8arrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr6u64arrC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelI59OSSVerify5KrLib4Spec6Malloc4mctx00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C59OSSVerify5KrLib5Plain:RMallocRep4RCTXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep:rarea_concC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep5lr_loC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic7f_equalC59OSSVerify5KrLib5Plain:RMallocRep;rarea_lr_loC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C47Corelib4Init5Logic3notK46Stdlib9micromega=RingMicromega3Op201C59OSSVerify5KrLib5Plain:RMallocRep;rgroup_concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep;lr_lo_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_reservedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;live_rangesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;ranges_freeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocAregion_live_rangeC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC46Stdlib5Lists4List2InC46Stdlib5Lists4List9in_or_appC59OSSVerify5KrLib6Malloc:MallocTree>ranges_free_InC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02C35stdpp8fin_maps;map_to_listK47Corelib4Init9Datatypes4prod01K47Corelib4Init5Logic2or01K46Stdlib9micromega5Tauto8GFormula06C59OSSVerify5KrLib5Plain:RMallocRep<ref_reservedC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00K59OSSVerify5KrLib4Spec6Malloc6region01C1?~~~~~~~~~~~~~~~C35stdpp4base6insertC59OSSVerify5KrLib4Spec6Malloc;set_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:upd_regionC1?~~~~~~~~~~~~~~~C35stdpp4base:decide_relC35stdpp4base6decideI47Corelib4Init6Specif7sumbool00C35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap;gmap_finmapC47Corelib4Init5Logic9False_indc59OSSVerify5KrLib5Plain8RF_am_K2;rgr_regionsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain8RF_am_K2>rgr_lookup_oldC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain8RF_am_K2>rgr_lookup_newC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC59OSSVerify5KrLib6Malloc7F_am_K2Cround_up_pg_alignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula07C59OSSVerify5KrLib5Plain:RMallocRep8rstaticsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain8RF_am_K2>rgr_lookup_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRepArstatics_reservedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTreeAranges_free_introC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree>In_live_rangesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep>round_up_pg_geC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith4Znat3N2Z7inj_iffC46Stdlib9micromega;ZifyClasses9not_morphC56Stdlib6ZArith4Znat3N2Z9is_nonnegc59OSSVerify5KrLib5Plain8RF_am_K26rgr_ruC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind01C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01K59OSSVerify5KrLib4Spec6Malloc5rkind02C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain8RF_am_K28rgr_concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_free_meta_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;c_init_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>c_mmap_counterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<c_avail_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocGc_avail_meta_area_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_meta_alloc_shiftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_tailC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_brkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_seqC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powc59OSSVerify5KrLib5Plain8RF_am_K2>rgr_regions_wfC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc8brkstate00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree7ptrs_inC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain;RMallocTree@rimpl_vis_unfoldC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4implC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5epostC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5enodeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes7at_nodeC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4nretC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec3evtC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib3Lib5ITree3Exc3exc02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec8evt_monoC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib3Lib5ITree3Exc3exc01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec8evt_doneC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5ITree5itree00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4respC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00".
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Module A2 := MallocKit_A2.
Module RA2 := RMallocKit_A2.


(* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
Lemma rmrep_agree_but_ctx : forall st st' m m',
  rmrep st m ->
  s_regions st' = s_regions st -> s_metas st' = s_metas st -> s_areas st' = s_areas st ->
  s_groups st' = s_groups st -> s_shadow st' = s_shadow st -> s_statics st' = s_statics st ->
  A2.agree_on m m' RMLOCK 4 -> A2.agree_on m m' RLIBC 0x68 -> A2.agree_on m m' RGOT_SSP 8 -> A2.agree_on m m' RSSP_GUARD 8 ->
  (forall a ar, (s_areas st) !! a = Some ar -> A2.agree_on m m' (conc st a) 4096) ->
  (forall b gh, (s_groups st) !! b = Some gh -> A2.agree_on m m' (conc st b) 9) ->
  (forall rid r, (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> A2.agree_on m m' (r_base r) (round_up_pg (r_len r))) ->
  rmrep_ctx st' m' ->
  rmrep st' m'.
Proof.
  intros st st' m m' (WF & CX & GL & AR & GR & SH) ER EM EA EG ES ERs AGL AGC AGS1 AGS2 AGA AGG AGR CX'.
  assert (Hconc : forall q, conc st' q = conc st q) by (intros; unfold conc, get_region; rewrite ER; reflexivity).
  split; [|split; [exact CX'|split; [|split; [|split]]]].
  - exact (rregions_wf_restatics _ _ ER EA EG ERs WF).
  - destruct GL as (G1 & G2 & G3 & G4 & G5). unfold rmrep_globals, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RLIBC, RGOT_SSP, RSSP_GUARD in *.
    split; [|split; [|split; [|split]]].
    + eapply RA2.rrw_cells_agree; [exact G1|]. eapply A2.agree_on_sub; [exact AGL| lia| cbn; lia].
    + eapply RA2.rrw_cells_agree; [exact G2|]. eapply A2.agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply RA2.rrw_cells_agree; [exact G3|]. eapply A2.agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply RA2.rrw_cells_agree; [exact G4|]. eapply A2.agree_on_sub; [exact AGS1| lia| cbn; lia].
    + eapply RA2.rrw_cells_agree; [exact G5|]. eapply A2.agree_on_sub; [exact AGS2| lia| cbn; lia].
  - intros a ar Ha. rewrite EA in Ha. destruct (AR a ar Ha) as (A1 & A3 & A4). pose proof (AGA a ar Ha) as AG.
    unfold rarea_rep. rewrite !Hconc.
    assert (PW : forall p, pw st' p = pw st p) by (intros [q|]; unfold pw, oconc; [rewrite Hconc|]; reflexivity).
    assert (MC : forall r, meta_cells st' r = meta_cells st r) by (intros; unfold meta_cells; rewrite !PW; reflexivity).
    assert (GM : forall g, get_meta_rec st' g = get_meta_rec st g) by (intros; unfold get_meta_rec; rewrite EM; reflexivity).
    rewrite PW. split; [|split].
    + eapply RA2.rrw_cells_agree; [exact A1|]. eapply A2.agree_on_sub; [exact AG| lia| cbn; lia].
    + intros k Hk. rewrite MC, GM. eapply RA2.rrw_cells_agree; [apply A3; exact Hk|]. unfold meta_cells. cbn [cells_size csize Nat.add length].
      unfold AREA_HDR, META_SIZE, NSLOTS in *. eapply A2.agree_on_sub; [exact AG| lia| lia].
    + eapply RA2.rrw_cells_agree; [exact A4|]. eapply A2.agree_on_sub; [exact AG| lia| cbn; lia].
  - intros b gh Hb. rewrite EG in Hb. destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
    rewrite Hconc. replace (pw st' (g_meta gh)) with (pw st (g_meta gh)) by (destruct (g_meta gh); unfold pw, oconc; [rewrite Hconc|]; reflexivity).
    eapply RA2.rrw_cells_agree; [exact R|]. cbn. exact (AGG b gh Hb).
  - intros rid r Hr Hk. rewrite ER in Hr. destruct (SH rid r Hr Hk) as [HWr HB]. pose proof (AGR rid r Hr Hk) as AG.
    unfold rshadow_rep. replace (get_shadow st' rid) with (get_shadow st rid) by (unfold get_shadow; rewrite ES; reflexivity). split.
    + eapply RA2.rwr_at_agree; eauto.
    + intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
      eapply RA2.rbytes_at_agree; [exact Bt|]. cbn. eapply A2.agree_on_sub; [exact AG| lia| lia].
Qed.

(* [comment removed for export] *)
Lemma rmrep_ctx_mid_agree : forall st st' m m',
  rmrep st m -> ctx st' = ctx st \/ (forall sc, active st' sc = active st sc) /\ (forall sc, usage st' sc = usage st sc)
                               /\ (forall i, unmap_seq st' i = unmap_seq st i) /\ (forall i, bounces st' i = bounces st i) ->
  s_regions st' = s_regions st ->
  A2.agree_on m m' (RCTX + 80) 832 ->
  u64arr psegs m' (RCTX + 80) (actives st') /\ u64arr psegs m' (RCTX + 464) (usages st')
  /\ u8arr psegs m' (RCTX + 848) (unmap_seqs st') /\ u8arr psegs m' (RCTX + 880) (bouncess st').
Proof.
  intros st st' m m' (WF & (C1 & C2 & C3 & C4 & C5 & C6) & _) HX ER AG.
  assert (Hconc : forall q, conc st' q = conc st q) by (intros; unfold conc, get_region; rewrite ER; reflexivity).
  assert (PW : forall p, pw st' p = pw st p) by (intros [q|]; unfold pw, oconc; [rewrite Hconc|]; reflexivity).
  assert (E2 : actives st' = actives st).
  { unfold actives. apply map_ext. intros i. rewrite PW. destruct HX as [E|(E & _)]; [unfold active; rewrite E| rewrite E]; reflexivity. }
  assert (E3 : usages st' = usages st).
  { unfold usages. apply map_ext. intros i. destruct HX as [E|(_ & E & _)]; [unfold usage; rewrite E| rewrite E]; reflexivity. }
  assert (E4 : unmap_seqs st' = unmap_seqs st).
  { unfold unmap_seqs. apply map_ext. intros i. destruct HX as [E|(_ & _ & E & _)]; [unfold unmap_seq; rewrite E| rewrite E]; reflexivity. }
  assert (E5 : bouncess st' = bouncess st).
  { unfold bouncess. apply map_ext. intros i. destruct HX as [E|(_ & _ & _ & E)]; [unfold bounces; rewrite E| rewrite E]; reflexivity. }
  rewrite E2, E3, E4, E5.
  assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
  assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
  assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
  assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
  unfold RCTX in *.
  split; [|split; [|split]].
  - eapply RA2.ru64arr_agree; [exact C2|]. rewrite L1. eapply A2.agree_on_sub; [exact AG| lia| cbn; lia].
  - eapply RA2.ru64arr_agree; [exact C3|]. rewrite L2. eapply A2.agree_on_sub; [exact AG| lia| cbn; lia].
  - eapply RA2.ru8arr_agree; [exact C4|]. rewrite L3. eapply A2.agree_on_sub; [exact AG| lia| cbn; lia].
  - eapply RA2.ru8arr_agree; [exact C5|]. rewrite L4. eapply A2.agree_on_sub; [exact AG| lia| cbn; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rarea_in_live : forall st a ar r x, rregions_wf st -> (s_areas st) !! a = Some ar -> (s_regions st) !! (fst a) = Some r ->
  conc st a <= x < conc st a + 4096 -> lr_lo r <= x < r_base r + round_up_pg (r_len r).
Proof.
  intros st a ar r x WF Ha Hr Hx. destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & _).
  rewrite Hr in Hra. assert (ra = r) by congruence. subst ra.
  pose proof (rarea_lr_lo st a ar r WF Ha Hr). lia.
Qed.

Lemma rgroup_in_live : forall st b gh r x, rregions_wf st -> (s_groups st) !! b = Some gh -> (s_regions st) !! (fst b) = Some r ->
  conc st b <= x < conc st b + 9 -> lr_lo r <= x < r_base r + round_up_pg (r_len r).
Proof.
  intros st b gh r x WF Hb Hr Hx. destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & _).
  rewrite Hr in Hrb. assert (rb = r) by congruence. subst rb. rewrite (lr_lo_group r Krb). lia.
Qed.

(* [comment removed for export] *)
Lemma rimage_clear_of_ranges_free st lo n x : s_reserved st = ref_reserved -> ranges_free (live_ranges st) lo n = true ->
  0x10000 <= x < 0x59000 -> ~ (lo <= x < lo + n).
Proof.
  intros RS RF Hx Hin. unfold live_ranges in RF. rewrite RS in RF.
  pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; left; reflexivity)).
  pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; right; left; reflexivity)).
  pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; right; right; left; reflexivity)).
  pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; right; right; right; left; reflexivity)). cbn in *. lia.
Qed.

Section GROW.
Variables (st : mstate) (m : mem) (rid : N) (r : region) (off : Z).
Hypothesis MR : rmrep st m.
Hypothesis Hr : (s_regions st) !! rid = Some r.
Hypothesis NK : r_kind r <> RKGroup.
Hypothesis LEN : r_len r = off.
Hypothesis OFF : 0 <= off.
Hypothesis OAL : off mod 4096 = 0.
Hypothesis RF : ranges_free (live_ranges st) (r_base r + off) 4096 = true.
Hypothesis CEIL : r_base r + off + 4096 <= ATOP.
Hypothesis RPOS : forall q rq, (s_regions st) !! q = Some rq -> 0 < r_len rq.
Hypothesis UNIQ : forall q rq, (s_regions st) !! q = Some rq -> q <> rid -> r_kind rq <> RKBrk.

Let r' := mkRegion (r_kind r) (r_base r) (off + 4096).
Let st' := set_regions (<[rid := r']> (s_regions st)) st.

Lemma rgr_eq : upd_region rid (fun rg => mkRegion (r_kind rg) (r_base rg) (off + 4096)) st = st'.
Proof. unfold st', upd_region, get_region. rewrite Hr. reflexivity. Qed.
Lemma rgr_regions : s_regions st' = <[rid := r']> (s_regions st).
Proof. reflexivity. Qed.
Lemma rgr_lookup_inv q rq : (s_regions st') !! q = Some rq -> (q = rid /\ rq = r') \/ (q <> rid /\ (s_regions st) !! q = Some rq).
Proof.
  rewrite rgr_regions. intros H. destruct (decide (q = rid)) as [->|NE].
  - rewrite lookup_insert_eq in H. left. split; congruence.
  - rewrite lookup_insert_ne in H by congruence. right. auto.
Qed.
Lemma rgr_lookup_old q : q <> rid -> (s_regions st') !! q = (s_regions st) !! q.
Proof. intros. rewrite rgr_regions, lookup_insert_ne by congruence. reflexivity. Qed.
Lemma rgr_lookup_new : (s_regions st') !! rid = Some r'.
Proof. rewrite rgr_regions, lookup_insert_eq. reflexivity. Qed.
Lemma rgr_conc q : conc st' q = conc st q.
Proof.
  unfold conc, get_region. destruct (decide (fst q = rid)) as [E|NE].
  - rewrite E, rgr_lookup_new, Hr. reflexivity.
  - rewrite rgr_lookup_old by exact NE. reflexivity.
Qed.
Lemma rgr_ru : round_up_pg (off + 4096) = round_up_pg off + 4096.
Proof. rewrite !round_up_pg_aligned; [lia| exact OAL|]. Z.div_mod_to_equations. lia. Qed.

Lemma rgr_regions_wf : rregions_wf st'.
Proof.
  pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
  destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RFr).
  assert (RU : round_up_pg off = off) by (apply round_up_pg_aligned; exact OAL).
  split; [exact RS|]. split; [|split; [|split]].
  - intros q rq Hq. destruct (rgr_lookup_inv q rq Hq) as [[-> ->]|[NE H]]; [| exact (WR q rq H)].
    cbn [r_base r_len r_kind r']. rewrite rgr_ru, RU. split; [exact RB0|]. split; [exact RBAL|]. split; [lia|]. split; [lia|].
    apply ranges_free_intro. intros b n HI.
    pose proof (ranges_free_In _ _ _ _ _ RFr HI) as D1. rewrite LEN, RU in D1.
    assert (D2 := ranges_free_In _ _ _ _ _ RF ltac:(unfold live_ranges; apply in_or_app; left; rewrite (rstatics_reserved _ RS); exact HI)).
    destruct HI as [E|[E|[E|[E|[]]]]]; inversion E; subst; lia.
  - intros q1 r1 q2 r2 H1 H2 NE.
    assert (OLD : forall q rq, (s_regions st) !! q = Some rq -> q <> rid ->
              r_base r' + round_up_pg (r_len r') <= lr_lo rq \/ r_base rq + round_up_pg (r_len rq) <= lr_lo r').
    { intros q rq Hq NEq. cbn [r_base r_len r']. rewrite rgr_ru, RU.
      replace (lr_lo r') with (lr_lo r) by (unfold lr_lo, r'; cbn; reflexivity).
      destruct (DJ _ _ _ _ Hr Hq ltac:(congruence)) as [D|D]; rewrite ?LEN, ?RU in D.
      - left. pose proof (In_live_ranges st q rq Hq) as HI. unfold region_live_range in HI. unfold lr_lo in *. unfold PGSZ in HI.
        pose proof (RPOS q rq Hq) as RLq. pose proof (round_up_pg_ge (r_len rq)). pose proof (UNIQ q rq Hq NEq) as NB.
        destruct (r_kind rq); [exfalso; apply NB; reflexivity | |]; (pose proof (ranges_free_In _ _ _ _ _ RF HI) as D2; lia).
      - right. exact D. }
    destruct (rgr_lookup_inv q1 r1 H1) as [[-> ->]|[NE1 H1']]; destruct (rgr_lookup_inv q2 r2 H2) as [[-> ->]|[NE2 H2']].
    + congruence.
    + exact (OLD q2 r2 H2' NE2).
    + destruct (OLD q1 r1 H1' NE1); [right| left]; assumption.
    + exact (DJ q1 r1 q2 r2 H1' H2' NE).
  - intros a ar Ha. destruct (WA a ar Ha) as (ra & Hra & A0 & A1 & AAL & NKa & LO).
    destruct (decide (fst a = rid)) as [E|NE].
    + exists r'. rewrite E in Hra |- *. rewrite rgr_lookup_new. rewrite Hr in Hra. assert (ra = r) by congruence. subst ra.
      cbn [r_base r_len r_kind r']. rewrite rgr_ru. replace (lr_lo r') with (lr_lo r) by (unfold lr_lo, r'; cbn; reflexivity).
      rewrite LEN in A1. repeat split; try assumption; lia.
    + exists ra. rewrite rgr_lookup_old by exact NE. repeat split; assumption.
  - intros b gh Hb. destruct (WG b gh Hb) as (rb & Hrb & Kb & REST).
    assert (NE : fst b <> rid) by (intros E; rewrite E, Hr in Hrb; assert (rb = r) by congruence; subst; exact (NK Kb)).
    exists rb. rewrite rgr_lookup_old by exact NE. auto.
Qed.

Lemma rmrep_grow_region : rmrep st' m.
Proof.
  pose proof MR as (WF & CX & GL & AR & GR & SH).
  assert (PW : forall p, pw st' p = pw st p) by (intros [q|]; unfold pw, oconc; [rewrite rgr_conc|]; reflexivity).
  assert (MC : forall mr, meta_cells st' mr = meta_cells st mr) by (intros; unfold meta_cells; rewrite !PW; reflexivity).
  split; [exact rgr_regions_wf|]. split; [|split; [exact GL|split; [|split]]].
  - destruct CX as (C1 & C2 & C3 & C4 & C5 & C6). unfold rmrep_ctx.
    replace (rctx_head_cells st') with (rctx_head_cells st) by (unfold rctx_head_cells, rsecw; change (ctx st') with (ctx st); rewrite !PW; reflexivity).
    replace (actives st') with (actives st) by (unfold actives; apply map_ext; intros; rewrite PW; reflexivity).
    replace (ctx_tail_cells st') with (ctx_tail_cells st).
    2:{ unfold ctx_tail_cells, brk_word. change (ctx st') with (ctx st). destruct (c_brk (ctx st)); rewrite ?rgr_conc; reflexivity. }
    change (usages st') with (usages st). change (unmap_seqs st') with (unmap_seqs st). change (bouncess st') with (bouncess st).
    split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [exact C4|]. split; [exact C5| exact C6].
  - intros a ar Ha. change (s_areas st') with (s_areas st) in Ha. destruct (AR a ar Ha) as (A1 & A3 & A4).
    unfold rarea_rep. rewrite !rgr_conc, PW. change (get_meta_rec st') with (get_meta_rec st).
    split; [exact A1|]. split; [| exact A4]. intros k Hk. rewrite MC. apply A3. exact Hk.
  - intros b gh Hb. change (s_groups st') with (s_groups st) in Hb. destruct (GR b gh Hb) as (w8 & R & Hw8).
    exists w8. rewrite rgr_conc, PW. split; assumption.
  - intros q rq Hq Hk. change (get_shadow st' q) with (get_shadow st q).
    destruct (rgr_lookup_inv q rq Hq) as [[-> ->]|[NE H]].
    + exfalso. apply NK. exact Hk.
    + exact (SH q rq H Hk).
Qed.

Lemma rptrs_in_grow P : ptrs_in P st -> ptrs_in P st'.
Proof. intros H. exact H. Qed.
End GROW.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rimpl_enode_dec_weaken {A} n (dec dec' : resp -> option A) (G : A -> Prop) (P : A -> machine_state -> Prop) ms :
  impl psegs (at_node psegs) (enode n dec) (epost P) ms ->
  (forall rsp a, dec' rsp = Some a -> dec rsp = Some a /\ G a) ->
  impl psegs (at_node psegs) (enode n dec') (epost (fun a ms' => P a ms' /\ G a)) ms.
Proof.
  intros H HD. unfold enode in *. rewrite rimpl_vis_unfold in H. rewrite rimpl_vis_unfold.
  eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. specialize (Hk rsp).
  destruct (dec' rsp) as [a|] eqn:E.
  - destruct (HD rsp a E) as [E1 HG]. rewrite E1 in Hk. cbn in Hk |- *. eapply evt_mono; [exact Hk|]. intros ms' HP; cbn in *. auto.
  - cbn. apply evt_done. exact I.
Qed.

End CANSEC1.
