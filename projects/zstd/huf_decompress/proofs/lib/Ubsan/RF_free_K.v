(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (10 recorded proofs replaced by written proofs (rfree_fp_hdr_st, rconc_drop, rpw_drop and 7 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk Arr ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import F_malloc_free MallocBlocks MallocFacts_B MallocKit_B MallocModel_B MallocKit_B3 MallocFacts_Bpres.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Export F_free_K.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_free_K () := "C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I35stdpp9countable9Countable00C47Corelib4Init5Logic8eq_ind_rC35stdpp4base;RelDecisionC35stdpp4gmap;gmap_lookupC35stdpp4base4fmapC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C35stdpp4base6lookupI35stdpp8fin_maps6FinMap00C35stdpp8fin_maps7MapFoldC35stdpp8fin_maps:map_insertC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base6InsertC35stdpp4base<PartialAlterC35stdpp4base5MergeI35stdpp4gmap4gmap00C35stdpp8fin_maps:map_eq_iffC35stdpp8fin_maps@lookup_delete_neC35stdpp4gmap:gmap_emptyC35stdpp4gmapBgmap_partial_alterC35stdpp4gmap9gmap_foldI47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib6Malloc9MallocRep8ticks_okC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z2leC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndK59OSSVerify5KrLib4Spec6Malloc7cellval01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8F_free_K6hdr_stC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan<RMallocKit_B8rfree_fpC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02C56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init9Datatypes6option00C47Corelib4Init5Logic3notC59OSSVerify5KrLib6Malloc9MallocRep5lr_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic2or00C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib4Spec6Malloc4concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_shadowC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C59OSSVerify5KrLib6Malloc8F_free_KAhdr_st_known_backC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib4Spec6Malloc9cell_readC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I59OSSVerify5KrLib4Spec6Malloc7cellval00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00C59OSSVerify5KrLib5Ubsan:RMallocRep4RCTXC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableC45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableI46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01C35stdpp8fin_maps:map_deleteC35stdpp4base6deleteC59OSSVerify5KrLib4Spec6Malloc8s_shadowC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~C35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap;gmap_finmapC47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic9False_indI47Corelib4Init5Logic5False00C59OSSVerify5KrLib6Malloc:MallocTree7optr_inC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C59OSSVerify5KrLib6Malloc9MallocRep2pwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep2wzC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan9RF_free_K:rconc_dropC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5oconcC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00C47Corelib4Init9Datatypes2idC59OSSVerify5KrLib6Malloc9MallocRepAget_shadow_unfoldC1?~~~~~~~~~~~~~~~C35stdpp6option;from_optionC59OSSVerify5KrLib4Spec6Malloc7shadow0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_free_meta_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<c_avail_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_tailC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_brkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_prevC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6a_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6g_metaC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep9meta_wordC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan9RF_free_K8rpw_dropC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep:meta_cellsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc8brkstate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep?rctx_head_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst6SECRETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;c_init_doneC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib4Spec6Malloc>c_mmap_counterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocGc_avail_meta_area_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_meta_alloc_shiftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep7activesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List7map_extI47Corelib4Init9Datatypes3nat00C59OSSVerify5KrLib6Malloc9MallocRep>ctx_tail_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep2b8C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep5zerosC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powK47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib5Ubsan:RMallocRep5rmrepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep;rregions_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep9rmrep_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep=rmrep_globalsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep;rmrep_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep<rmrep_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep<rmrep_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep8rstaticsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;ranges_freeC1?~~~~~~~~~~~~~~~C35stdpp8fin_mapsBlookup_delete_SomeC47Corelib4Init5Logic7and_indC59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr6u64arrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep6usagesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep:unmap_seqsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr5u8arrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep8bouncessC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep9rarea_repC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8a_nslotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4aaddC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan9RF_free_K@rmeta_cells_dropC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan9RF_free_K9rrec_dropC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep:rgroup_repC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z4landC59OSSVerify5KrLib4Spec6Malloc<g_active_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep;rshadow_repC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan9RF_free_K@rget_shadow_dropC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib5Ubsan4UImg5usegsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8AREA_HDRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan:RMallocRep<ref_reservedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan9RF_free_KDrctx_tail_cells_dropC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan9RF_free_K=ractives_dropC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Ubsan9RF_free_KDrctx_head_cells_dropC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6NSLOTSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9META_SIZEC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6MallocAMallocFacts_Bpres4KINV00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6MallocAMallocFacts_Bpres4ZINVC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_B8ci_mptrsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_B6ng_ptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree7ptrs_inC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep9meta_slotC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic7f_equalC59OSSVerify5KrLib6MallocAMallocFacts_Bpres8ki_linksC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Malloc=MallocFacts_B:ci_links_t00C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffC59OSSVerify5KrLib6Malloc=MallocFacts_B5is_gmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6MallocAMallocFacts_Bpres>kinv_free_headC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C59OSSVerify5KrLib4Spec6Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6MallocAMallocFacts_Bpres;kinv_activeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2K59OSSVerify5KrLib4Spec6Malloc8brkstate03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6MallocAMallocFacts_Bpres5ki_bkC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transC59OSSVerify5KrLib6Malloc=MallocFacts_B5hostsC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC59OSSVerify5KrLib6Malloc=MallocFacts_B:areas_initC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4ghdr01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6MallocAMallocFacts_Bpres7ki_grpsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6MallocAMallocFacts_Bpres9ki_gmetasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_B7go_slotC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocBlocks5blockC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01K59OSSVerify5KrLib4Spec6Malloc8brkstate01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc8brkstate02C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Lemma rfree_fp_hdr_st st pf lo (sp sp' : Z) a : ticks_ok st ->
  (forall k, 1 <= k <= 3 -> exists w, cell_read (get_shadow st (fst pf)) (snd pf - k) = Known w) ->
  sp' <= sp -> rfree_fp (hdr_st st pf) lo sp' a -> rfree_fp st lo sp a.
Proof.
  intros TK HK HS H. destruct H as [H|[H|H]].
  - left. destruct H as [H|[H|H]]; [left; lia| right; left; exact H| right; right; exact H].
  - right; left. exact H.
  - right; right. destruct H as (rid & r & v & H1 & H2 & H3 & H4). destruct (hdr_st_known_back st pf rid _ v TK HK H4) as [w Hw].
    exists rid, r, w. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section DROP.
Variables (st : mstate) (rid : N).
Let st' := drop_region rid st.
Hypothesis PTR : ptrs_in (fun x => x <> rid) st.

Lemma rdrop_regions : s_regions st' = delete rid (s_regions st).
Proof.
ltac2:(KReplay.run1 (kr_t_RF_free_K ()) ["CANSEC1"; "DROP"] "p;4p;1p;5p;2g0075j45Tg008_j44Tg00n\j40Tg00Hlj11Tg00o8j53Tg00T0j22Tg00cYR0g00hKR1g00hdR2g00a0R3C5R4P0P4P0P3P4P0P1P2P3C4C0p,3ridp,2st#1D3'2o"). Qed.
Lemma rdrop_shadow : s_shadow st' = delete rid (s_shadow st).
Proof.
ltac2:(KReplay.run1 (kr_t_RF_free_K ()) ["CANSEC1"; "DROP"] "p;4p;1p;5p;2g0075j45Tg008_j44Tg00n\j40Tg00oLj11Tg00o8j53Tg00T0j22Tg00cYR0g00hKR1g00hdR2g010ER3C5R4P0P4P0P3P4P0P1P2P3C4C0p,3ridp,2st#1D3'2o"). Qed.
Lemma rconc_drop q : fst q <> rid -> conc st' q = conc st q.
Proof. intros NE. unfold conc, get_region. cbn [st' drop_region s_regions set_shadow set_regions]. rewrite lookup_delete_ne by congruence. reflexivity. Qed.
Lemma rpw_drop p : optr_in (fun x => x <> rid) p -> pw st' p = pw st p.
Proof. destruct p as [q|]; cbn; intros H; [| reflexivity]. unfold pw. cbn [oconc]. rewrite rconc_drop by exact H. reflexivity. Qed.
Lemma rget_shadow_drop rid' : rid' <> rid -> get_shadow st' rid' = get_shadow st rid'.
Proof. intros NE. rewrite !get_shadow_unfold. cbn [st' drop_region s_shadow set_shadow set_regions]. rewrite lookup_delete_ne by congruence. reflexivity. Qed.
Lemma rrec_drop q : get_meta_rec st' q = get_meta_rec st q.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_free_K ()) ["CANSEC1"; "DROP"] "h01qp;2g01<kj21Tg00T0j20Tg0000R0g01=hp,2stf0R1'1'0X00P1O1X00P1O1W0o"). Qed.

Lemma rmeta_cells_drop q : meta_cells st' (get_meta_rec st q) = meta_cells st (get_meta_rec st q).
Proof.
  destruct PTR as (_ & _ & _ & _ & _ & _ & _ & PM & _). destruct (PM q) as (P1 & P2 & P3).
  unfold meta_cells. rewrite !rpw_drop by assumption. reflexivity.
Qed.

Lemma rctx_head_cells_drop : rctx_head_cells st' = rctx_head_cells st.
Proof.
  destruct PTR as (P1 & P2 & P3 & P4 & P5 & _). unfold rctx_head_cells, rsecw. change (ctx st') with (ctx st).
  rewrite !rpw_drop by assumption. reflexivity.
Qed.
Lemma ractives_drop : actives st' = actives st.
Proof.
  destruct PTR as (_ & _ & _ & _ & _ & PA & _). unfold actives. apply map_ext. intros i.
  change (active st' (Z.of_nat i)) with (active st (Z.of_nat i)). apply rpw_drop. apply PA.
Qed.
Lemma rctx_tail_cells_drop : ctx_tail_cells st' = ctx_tail_cells st.
Proof.
  destruct PTR as (_ & _ & _ & _ & _ & _ & PB & _). unfold ctx_tail_cells, brk_word. change (ctx st') with (ctx st).
  destruct (c_brk (ctx st)) as [| |brid boff]; try reflexivity. rewrite (rconc_drop (brid, boff)) by exact PB. reflexivity.
Qed.

Lemma rmrep_drop_region m : rmrep st m -> rmrep st' m.
Proof.
  intros MR. pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DJ & WA & WG).
  destruct PTR as (P1 & P2 & P3 & P4 & P5 & PA & PB & PM & PAR & PG).
  split; [|split; [|split; [|split; [|split]]]].
  - split; [exact Hres|]. split; [|split; [|split]].
    + intros k r Hk. cbn [st' drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. apply (WR k r). tauto.
    + intros k1 r1 k2 r2 H1 H2 NE. cbn [st' drop_region s_regions set_shadow set_regions] in H1, H2.
      apply lookup_delete_Some in H1. apply lookup_delete_Some in H2. apply (DJ k1 r1 k2 r2); tauto.
    + intros a ar Ha. destruct (PAR a ar Ha) as [Pa _]. destruct (WA a ar Ha) as (r & Hr & REST). exists r.
      cbn [st' drop_region s_regions set_shadow set_regions s_areas]. rewrite lookup_delete_ne by congruence. auto.
    + intros b gh Hb. destruct (PG b gh Hb) as [Pb _]. destruct (WG b gh Hb) as (r & Hr & REST). exists r.
      cbn [st' drop_region s_regions set_shadow set_regions s_groups]. rewrite lookup_delete_ne by congruence. auto.
  - unfold rmrep_ctx. rewrite rctx_head_cells_drop, ractives_drop, rctx_tail_cells_drop.
    change (usages st') with (usages st). change (unmap_seqs st') with (unmap_seqs st). change (bouncess st') with (bouncess st). exact CX.
  - exact GL.
  - intros a ar Ha. destruct (PAR a ar Ha) as [Pa Pn]. destruct (AR a ar Ha) as (A1 & A2 & A3).
    unfold rarea_rep. rewrite (rconc_drop a) by exact Pa. rewrite rpw_drop by exact Pn. split; [exact A1|]. split; [| exact A3].
    intros k Hk. rewrite rrec_drop, rmeta_cells_drop. apply A2. exact Hk.
  - intros b gh Hb. destruct (PG b gh Hb) as [Pb Pm]. destruct (GR b gh Hb) as (w8 & R & Hw). exists w8.
    rewrite (rconc_drop b) by exact Pb. rewrite rpw_drop by exact Pm. auto.
  - intros k r Hk Kr. cbn [st' drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. destruct Hk as [NE Hk].
    unfold rshadow_rep. rewrite rget_shadow_drop by congruence. exact (SH k r Hk Kr).
Qed.
End DROP.

Lemma rptrs_in_norid st2 LB c rid r m :
  KINV st2 LB c -> ZINV st2 [] -> rmrep st2 m ->
  (s_regions st2) !! rid = Some r -> r_kind r = RKGroup ->
  (forall b gh, (s_groups st2) !! b = Some gh -> fst b <> rid) ->
  ci_mptrs st2 ->
  ptrs_in (fun x => x <> rid) st2.
Proof.
  intros K ZI MR Hr Kr NOG (M1 & M2 & M3 & M4 & M5).
  pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG).
  assert (MSr : forall q, meta_slot st2 q -> fst q <> rid).
  { intros q (a & ar & k & Ha & Hk & ->) E. cbn in E. destruct (WA a ar Ha) as (ra & Hra & _ & _ & _ & NK & _).
    rewrite E, Hr in Hra. assert (ra = r) by congruence. subst ra. exact (NK Kr). }
  assert (NGr : forall p, ng_ptr st2 p -> optr_in (fun x => x <> rid) p).
  { intros [q|]; cbn; [| exact (fun _ => I)]. intros (r' & Hr' & NK) E. rewrite E, Hr in Hr'. assert (r' = r) by congruence. subst r'. exact (NK Kr). }
  assert (OM : forall p, (forall q, p = Some q -> meta_slot st2 q) -> optr_in (fun x => x <> rid) p).
  { intros [q|] H; cbn; [apply MSr; apply H; reflexivity| exact I]. }
  pose proof (ki_links _ _ _ K) as [LN LP LNN LS].
  unfold ptrs_in. cbv zeta. split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
  - apply OM. intros h Hh. exact (proj1 (kinv_free_head st2 LB c h K Hh)).
  - apply NGr. exact M1.
  - apply NGr. exact M2.
  - apply NGr. exact M3.
  - apply NGr. exact M4.
  - intros sc. apply OM. intros a Ha. exact (proj1 (proj2 (kinv_active st2 LB c sc a K Ha))).
  - destruct (c_brk (ctx st2)) as [| |brid boff] eqn:HB; try exact I.
    intros E. destruct (ki_bk _ _ _ K brid boff HB) as (r' & Hr' & K'). rewrite E, Hr in Hr'. assert (r' = r) by congruence. subst r'. rewrite Kr in K'. discriminate.
  - intros g. split; [| split].
    + apply OM. intros pv Hp. exact (proj2 (LP g pv Hp)).
    + apply OM. intros nx Hn. exact (proj2 (LN g nx Hn)).
    + destruct (m_mem (get_meta_rec st2 g)) as [b|] eqn:MB; cbn; [| exact I].
      destruct (proj1 ZI g b MB) as [[ai Hb]|[]]. exact (NOG b _ Hb).
  - intros a ar Ha. split; [| apply NGr; exact (M5 a ar Ha)].
    intros E. destruct (WA a ar Ha) as (ra & Hra & _ & _ & _ & NK & _). rewrite E, Hr in Hra. assert (ra = r) by congruence. subst ra. exact (NK Kr).
  - intros b gh Hb. split; [exact (NOG b gh Hb)|].
    destruct (ki_grps _ _ _ K b gh Hb) as (g & Hg & _). rewrite Hg. cbn. apply MSr.
    assert (HB : hosts st2 b g) by (exists (g_active_idx gh); rewrite Hb; destruct gh; cbn in Hg |- *; subst; reflexivity).
    exact (go_slot _ _ _ (ki_gmetas _ _ _ K b g HB)).
Qed.

End CANSEC1.
