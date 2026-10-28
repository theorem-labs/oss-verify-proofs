(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwEqH GwApply GwApply2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QDXD.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKNz.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qfw3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq1.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Export Qy5Y.Mq6.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UQXM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UQXM. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uv2Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uv2Y.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0.
Import ListNotations. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply GwApply2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module GwI.
Definition segs := rsegs.
Definition RATP := UKNz.RATP.
Definition RDEBRUIJN := UKNz.RDEBRUIJN.
Definition RGOT_SSP := UKNz.RGOT_SSP.
Definition RIMG_HI := UKNz.RIMG_HI.
Definition RDATA_LO := UKNz.RDATA_LO.
Definition gw_RTEXT_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 1 UKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition gw_RDATA2_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 3 UKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition ref_reserved := UKNz.ref_reserved.
Definition ref_find_segment_none := @UKNz.ref_find_segment_none.
Definition ref_ro_addr_false := @UKNz.ref_ro_addr_false.
Definition ref_memory_read_none := @UKNz.ref_memory_read_none.
Definition ref_wview_overlay := @UKNz.ref_wview_overlay.
Definition ref_seg_rom_none := @UKNz.ref_seg_rom_none.
Definition ref_mrd_overlay := @UKNz.ref_mrd_overlay.
Lemma ROM_reservedZ : ltac2:(GwEq.gw_fact_ty 'segs '(@QDXD.Mq2.gw_all) @ROM_reservedZ). Proof. first [ apply QWxq.Mq0.ro_bytes_b_sound; vm_compute; reflexivity | GwApply.gw_side ]. Qed.
End GwI.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition rrepfoot (st : mstate) (a : Z) : Prop :=
(RCTX <= a < RCTX + 928) \/ (RMLOCK <= a < RMLOCK + 4) \/ (RNEED_LOCKS <= a < RNEED_LOCKS + 1) \/ (RPAGE_SIZE <= a < RPAGE_SIZE + 8)
\/ (exists ak ar, (s_areas st) !! ak = Some ar /\ conc st ak <= a < conc st ak + 4096)
\/ (exists b gh, (s_groups st) !! b = Some gh /\ conc st b <= a < conc st b + 9)
\/ (exists rid r v, (s_regions st) !! rid = Some r /\ r_kind r = RKGroup
/\ r_base r <= a < r_base r + round_up_pg (r_len r) /\ cell_read (get_shadow st rid) (a - r_base r) = Known v)
\/ (RGOT_SSP <= a < RGOT_SSP + 8) \/ (RSSP_GUARD <= a < RSSP_GUARD + 8).
Lemma gw_eq_rrepfoot : @rrepfoot = ltac:(GwInst.gw_term (@QDXD.Mq2.rrepfoot UKNz.RATP UKNz.RGOT_SSP) (@rrepfoot)). Proof. unfold rrepfoot, QDXD.Mq2.rrepfoot; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rrepfoot : gw_eqs.

#[using="Type"] Lemma rrepfoot_ctx st a : RCTX <= a < RCTX + 928 -> rrepfoot st a. Proof. rewrite ?gw_eq_rrepfoot; first [GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rrepfoot_ctx) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rrepfoot_ctx)]. Qed.
#[using="Type"] Lemma rrepfoot_mlock st a : RMLOCK <= a < RMLOCK + 4 -> rrepfoot st a. Proof. rewrite ?gw_eq_rrepfoot; first [GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rrepfoot_mlock) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rrepfoot_mlock)]. Qed.
#[using="Type"] Lemma rrepfoot_nl st a : RNEED_LOCKS <= a < RNEED_LOCKS + 1 -> rrepfoot st a. Proof. rewrite ?gw_eq_rrepfoot; first [GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rrepfoot_nl) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rrepfoot_nl)]. Qed.
#[using="Type"] Lemma rrepfoot_pgsz st a : RPAGE_SIZE <= a < RPAGE_SIZE + 8 -> rrepfoot st a. Proof. rewrite ?gw_eq_rrepfoot; first [GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rrepfoot_pgsz) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rrepfoot_pgsz)]. Qed.
#[using="Type"] Lemma rrepfoot_area st a ak ar : (s_areas st) !! ak = Some ar -> conc st ak <= a < conc st ak + 4096 -> rrepfoot st a.
Proof. rewrite ?gw_eq_rrepfoot; first [GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rrepfoot_area) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rrepfoot_area)]. Qed.
#[using="Type"] Lemma rrepfoot_group st a b gh : (s_groups st) !! b = Some gh -> conc st b <= a < conc st b + 9 -> rrepfoot st a.
Proof. rewrite ?gw_eq_rrepfoot; first [GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rrepfoot_group) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rrepfoot_group)]. Qed.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@Q8QT.Mq4.rshadow_rep) (@UQXM.rshadow_rep) (Q6nq.gwt_def (@QDXD.Mq2.rshadow_rep) (@UQXM.rshadow_rep) (Q6nq.gwt_def (@Q8QT.Mq4.rregions_wf) (@UQXM.rregions_wf) (Q6nq.gwt_def (@QDXD.Mq2.rregions_wf) (@UQXM.rregions_wf) (Q6nq.gwt_def (@QCa8.Mq5.rpres_except) (@Uv2Y.rpres_except) (Q6nq.gwt_def (@QDXD.Mq2.rpres_except) (@Uv2Y.rpres_except) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_shadow) (@UQXM.rmrep_shadow) (Q6nq.gwt_def (@QDXD.Mq2.rmrep_shadow) (@UQXM.rmrep_shadow) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_groups) (@UQXM.rmrep_groups) (Q6nq.gwt_def (@QDXD.Mq2.rmrep_groups) (@UQXM.rmrep_groups) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_globals) (@UQXM.rmrep_globals) (Q6nq.gwt_def (@QDXD.Mq2.rmrep_globals) (@UQXM.rmrep_globals) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_ctx) (@UQXM.rmrep_ctx) (Q6nq.gwt_def (@QDXD.Mq2.rmrep_ctx) (@UQXM.rmrep_ctx) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_areas) (@UQXM.rmrep_areas) (Q6nq.gwt_def (@QDXD.Mq2.rmrep_areas) (@UQXM.rmrep_areas) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@UQXM.rmrep) (Q6nq.gwt_def (@QDXD.Mq2.rmrep) (@UQXM.rmrep) (Q6nq.gwt_def (@Q8QT.Mq4.rgroup_rep) (@UQXM.rgroup_rep) (Q6nq.gwt_def (@QDXD.Mq2.rgroup_rep) (@UQXM.rgroup_rep) (Q6nq.gwt_def (@Q8QT.Mq4.rarea_rep) (@UQXM.rarea_rep) (Q6nq.gwt_def (@QDXD.Mq2.rarea_rep) (@UQXM.rarea_rep) Q6nq.gwt_nil)))))))))))))))))))))).
#[using="Type"] Lemma rrepfoot_known : ltac2:(Q6nq.ty2 'GwI.segs '(@QDXD.Mq2.rrepfoot_known) [[@gw_eq_rrepfoot]] '(@nil Z) 'gwt_X).
Proof. rewrite ?gw_eq_rrepfoot; first [GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rrepfoot_known) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rrepfoot_known)]. Qed.
#[using="Type"] Lemma rrepfoot_got st a : RGOT_SSP <= a < RGOT_SSP + 8 -> rrepfoot st a. Proof. rewrite ?gw_eq_rrepfoot; first [GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rrepfoot_got) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rrepfoot_got)]. Qed.
#[using="Type"] Lemma rrepfoot_guard st a : RSSP_GUARD <= a < RSSP_GUARD + 8 -> rrepfoot st a. Proof. rewrite ?gw_eq_rrepfoot; first [GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rrepfoot_guard) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rrepfoot_guard)]. Qed.

#[using="Type"] Lemma rbytes_at_agree : ltac2:(Q6nq.ty2 'GwI.segs '(@QDXD.Mq2.rbytes_at_agree) [[@gw_eq_rrepfoot__3; @gw_eq_rrepfoot__2; @gw_eq_rrepfoot]] '(@nil Z) 'gwt_X).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rbytes_at_agree) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rbytes_at_agree)]. Qed.

#[using="Type"] Lemma rrw_cells_agree : ltac2:(Q6nq.ty2 'GwI.segs '(@QDXD.Mq2.rrw_cells_agree) [[@gw_eq_rrepfoot__3; @gw_eq_rrepfoot__2; @gw_eq_rrepfoot]] '(@nil Z) 'gwt_X).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rrw_cells_agree) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rrw_cells_agree)]. Qed.

#[using="Type"] Lemma ru64arr_agree : ltac2:(Q6nq.ty2 'GwI.segs '(@QDXD.Mq2.ru64arr_agree) [[@gw_eq_rrepfoot__3; @gw_eq_rrepfoot__2; @gw_eq_rrepfoot]] '(@nil Z) 'gwt_X).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.ru64arr_agree) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.ru64arr_agree)]. Qed.

#[using="Type"] Lemma ru8arr_agree : ltac2:(Q6nq.ty2 'GwI.segs '(@QDXD.Mq2.ru8arr_agree) [[@gw_eq_rrepfoot__3; @gw_eq_rrepfoot__2; @gw_eq_rrepfoot]] '(@nil Z) 'gwt_X).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.ru8arr_agree) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.ru8arr_agree)]. Qed.

#[using="Type"] Lemma rmrep_transport_unowned : ltac2:(Q6nq.ty2 'GwI.segs '(@QDXD.Mq2.rmrep_transport_unowned) [[@gw_eq_W__3; @gw_eq_W__2; @gw_eq_W]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_rrepfoot]] '(@nil Z) 'gwt_X).
Proof. rewrite ?gw_eq_rrepfoot; ltac2:(GwEq.gw_rw [[@gw_eq_W__3; @gw_eq_W__2; @gw_eq_W]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rmrep_transport_unowned) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rmrep_transport_unowned)]. Qed.

#[using="Type"] Lemma rmrep_put_meta_frame : ltac2:(Q6nq.ty2 'GwI.segs '(@QDXD.Mq2.rmrep_put_meta_frame) [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_rrepfoot__3; @gw_eq_rrepfoot__2; @gw_eq_rrepfoot]] '(@nil Z) '(Q6nq.gwt_zc META_SIZE gwt_X)).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rmrep_put_meta_frame) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rmrep_put_meta_frame)]. Qed.

#[using="Type"] Lemma rmrep_ctx_frame' : forall st st' m m',
rmrep st m -> munch [(RCTX, RCTX + 928)] m m' -> wmono rsegs m m' ->
s_regions st' = s_regions st -> s_metas st' = s_metas st -> s_areas st' = s_areas st ->
s_groups st' = s_groups st -> s_shadow st' = s_shadow st -> s_reserved st' = s_reserved st ->
rmrep_ctx st' m' -> rmrep st' m'.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_rmrep_ctx__3; @gw_eq_rmrep_ctx__2; @gw_eq_rmrep_ctx]]); first [GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rmrep_ctx_frame') | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rmrep_ctx_frame')]. Qed.

#[using="Type"] Lemma rmrep_del_group : forall st m p, rmrep st m -> rmrep (del_group p st) m.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rmrep_del_group) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rmrep_del_group)]. Qed.

#[using="Type"] Lemma rmrep_set_slots : forall st m v, rmrep st m -> rmrep (set_slots v st) m.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rmrep_set_slots) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rmrep_set_slots)]. Qed.

#[using="Type"] Lemma rmrep_del_slots : forall st m p s c, rmrep st m -> rmrep (del_slots p s c st) m.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rmrep_del_slots) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rmrep_del_slots)]. Qed.

#[using="Type"] Lemma rmrep_active_read : forall st m sc a, rmrep st m -> 0 <= sc < 48 -> a = wa (RCTX + 80 + 8 * sc) ->
ov_read_bytes rsegs m a 8 = Some (le8 (pw st (active st sc))).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rmrep_active_read) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rmrep_active_read)]. Qed.

#[using="Type"] Lemma rmrep_usage_read : forall st m sc a, rmrep st m -> 0 <= sc < 48 -> a = wa (RCTX + 464 + 8 * sc) ->
ov_read_bytes rsegs m a 8 = Some (le8 (wz (usage st sc))).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rmrep_usage_read) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rmrep_usage_read)]. Qed.

#[using="Type"] Lemma rmrep_bounces_read : forall st m i a, rmrep st m -> 0 <= i < 32 -> a = wa (RCTX + 880 + i) ->
ov_read_bytes rsegs m a 1 = Some [b8 (bounces st i)].
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rmrep_bounces_read) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rmrep_bounces_read)]. Qed.

#[using="Type"] Lemma rmrep_seq_read : forall st m a, rmrep st m -> a = wa (RCTX + 912) ->
ov_read_bytes rsegs m a 1 = Some [b8 (c_seq (ctx st))].
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rmrep_seq_read) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rmrep_seq_read)]. Qed.

#[using="Type"] Lemma rmrep_fmh_read : forall st m a, rmrep st m -> a = wa (RCTX + 16) ->
ov_read_bytes rsegs m a 8 = Some (le8 (pw st (c_free_meta_head (ctx st)))).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rmrep_fmh_read) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rmrep_fmh_read)]. Qed.

#[using="Type"] Lemma rbytes_at_cons : forall m a b bs, bytes_at rsegs m a (b :: bs) <-> bytes_at rsegs m a [b] /\ bytes_at rsegs m (a + 1) bs.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rbytes_at_cons) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rbytes_at_cons)]. Qed.

#[using="Type"] Lemma rmrep_group_word8 : ltac2:(Q6nq.ty2 'GwI.segs '(@QDXD.Mq2.rmrep_group_word8) [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_rrepfoot__3; @gw_eq_rrepfoot__2; @gw_eq_rrepfoot]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rmrep_group_word8) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rmrep_group_word8)]. Qed.

#[using="Type"] Lemma rmeta_slot_bounds : ltac2:(Q6nq.ty2 'GwI.segs '(@QDXD.Mq2.rmeta_slot_bounds) [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_rrepfoot__3; @gw_eq_rrepfoot__2; @gw_eq_rrepfoot]] '([4096; 65536; 626688]%Z : list Z) '(Q6nq.gwt_unf (@RIMG_LO) (Q6nq.gwt_unf (@RIMG_HI) (Q6nq.gwt_unf (@PGSZ) (Q6nq.gwt_pat (@RIMG_HI) (@RIMG_HI) (Q6nq.gwt_hdr GwI.RIMG_HI (@RIMG_HI) gwt_X)))))).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rmeta_slot_bounds) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rmeta_slot_bounds)]. Qed.

#[using="Type"] Lemma rgroup_bounds : ltac2:(Q6nq.ty2 'GwI.segs '(@QDXD.Mq2.rgroup_bounds) [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_rrepfoot__3; @gw_eq_rrepfoot__2; @gw_eq_rrepfoot]] '([65536; 626688]%Z : list Z) '(Q6nq.gwt_unf (@RIMG_LO) (Q6nq.gwt_unf (@RIMG_HI) (Q6nq.gwt_pat (@RIMG_HI) (@RIMG_HI) (Q6nq.gwt_hdr GwI.RIMG_HI (@RIMG_HI) gwt_X))))).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rgroup_bounds) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rgroup_bounds)]. Qed.

Definition rfree_fp (st : mstate) (lo sp : Z) (a : Z) : Prop :=
(lo <= a < sp
\/ RCTX <= a < RCTX + 928
\/ exists rid r, (s_regions st) !! rid = Some r /\ r_kind r <> RKGroup /\ lr_lo r <= a < r_base r + round_up_pg (r_len r))
\/ (exists b gh, (s_groups st) !! b = Some gh /\ conc st b <= a < conc st b + 8)
\/ (exists rid r v, (s_regions st) !! rid = Some r /\ r_kind r = RKGroup
/\ r_base r <= a < r_base r + round_up_pg (r_len r) /\ cell_read (get_shadow st rid) (a - r_base r) = Known v).
Lemma gw_eq_rfree_fp : @rfree_fp = ltac:(GwInst.gw_term (@QDXD.Mq2.rfree_fp UKNz.RATP) (@rfree_fp)). Proof. unfold rfree_fp, QDXD.Mq2.rfree_fp; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rfree_fp : gw_eqs.

#[using="Type"] Lemma rfree_fp_stack st lo sp a : lo <= a < sp -> rfree_fp st lo sp a.
Proof. rewrite ?gw_eq_rfree_fp; first [GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rfree_fp_stack) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rfree_fp_stack)]. Qed.
#[using="Type"] Lemma rfree_fp_ctx st lo sp a : RCTX <= a < RCTX + 928 -> rfree_fp st lo sp a.
Proof. rewrite ?gw_eq_rfree_fp; first [GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rfree_fp_ctx) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rfree_fp_ctx)]. Qed.
#[using="Type"] Lemma rfree_fp_region : ltac2:(Q6nq.ty2 'GwI.segs '(@QDXD.Mq2.rfree_fp_region) [[@gw_eq_rfree_fp]; [@gw_eq_rrepfoot__3; @gw_eq_rrepfoot__2; @gw_eq_rrepfoot]] '(@nil Z) 'gwt_X).
Proof. rewrite ?gw_eq_rfree_fp; first [GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rfree_fp_region) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rfree_fp_region)]. Qed.
#[using="Type"] Lemma rfree_fp_group st lo sp a b gh : (s_groups st) !! b = Some gh -> conc st b <= a < conc st b + 8 -> rfree_fp st lo sp a.
Proof. rewrite ?gw_eq_rfree_fp; first [GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rfree_fp_group) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rfree_fp_group)]. Qed.

#[using="Type"] Lemma rfree_fp_meta : ltac2:(Q6nq.ty2 'GwI.segs '(@QDXD.Mq2.rfree_fp_meta) [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_rfree_fp]; [@gw_eq_rrepfoot__3; @gw_eq_rrepfoot__2; @gw_eq_rrepfoot]] '(@nil Z) 'gwt_X).
Proof. rewrite ?gw_eq_rfree_fp; ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rfree_fp_meta) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rfree_fp_meta)]. Qed.

#[using="Type"] Lemma rfree_fp_mono : ltac2:(Q6nq.ty2 'GwI.segs '(@QDXD.Mq2.rfree_fp_mono) [[@gw_eq_rfree_fp]; [@gw_eq_rrepfoot__3; @gw_eq_rrepfoot__2; @gw_eq_rrepfoot]] '(@nil Z) 'gwt_X).
Proof. rewrite ?gw_eq_rfree_fp; first [GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rfree_fp_mono) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rfree_fp_mono)]. Qed.

#[using="Type"] Lemma rpres_except_of_munch' : ltac2:(Q6nq.ty2 'GwI.segs '(@QDXD.Mq2.rpres_except_of_munch') [[@gw_eq_W__3; @gw_eq_W__2; @gw_eq_W]; [@gw_eq_rpres_except__3; @gw_eq_rpres_except__2; @gw_eq_rpres_except]; [@gw_eq_rrepfoot__3; @gw_eq_rrepfoot__2; @gw_eq_rrepfoot]; [@gw_eq_rfree_fp__3; @gw_eq_rfree_fp__2; @gw_eq_rfree_fp]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_W__3; @gw_eq_W__2; @gw_eq_W]; [@gw_eq_rpres_except__3; @gw_eq_rpres_except__2; @gw_eq_rpres_except]]); first [GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rpres_except_of_munch') | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rpres_except_of_munch')]. Qed.

#[using="Type"] Lemma rpres_except_of_munch_cov : forall C W m m',
munch W m m' -> wmono rsegs m m' -> ivs_covered C W -> rpres_except C m m'.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_W__3; @gw_eq_W__2; @gw_eq_W]; [@gw_eq_rpres_except__3; @gw_eq_rpres_except__2; @gw_eq_rpres_except]]); first [GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rpres_except_of_munch_cov) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rpres_except_of_munch_cov)]. Qed.

Section CTXFRAME.
Variables (st st' : mstate) (m m' : word -> option byte) (W : list (Z * Z)).
Hypothesis MR : rmrep st m.
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono rsegs m m'.
Hypothesis ER : s_regions st' = s_regions st.
Hypothesis EM : s_metas st' = s_metas st.
Hypothesis EA : s_areas st' = s_areas st.
Hypothesis EG : s_groups st' = s_groups st.
Hypothesis ES : s_shadow st' = s_shadow st.
Hypothesis ERs : s_reserved st' = s_reserved st.

Hypothesis WIN : forall lo hi, In (lo, hi) W -> RCTX <= lo /\ hi <= RCTX + 928.

#[using="MU WIN"] Lemma rctxW_avoid : ltac2:(Q6nq.ty2 'GwI.segs '(@QDXD.Mq2.rctxW_avoid) [[@gw_eq_W__3; @gw_eq_W__2; @gw_eq_W]; [@gw_eq_W__3; @gw_eq_W__2; @gw_eq_W]; [@gw_eq_W__3; @gw_eq_W__2; @gw_eq_W]; [@gw_eq_rrepfoot__3; @gw_eq_rrepfoot__2; @gw_eq_rrepfoot]; [@gw_eq_rfree_fp__3; @gw_eq_rfree_fp__2; @gw_eq_rfree_fp]] '([928]%Z : list Z) '(Q6nq.gwt_zc RCTX (Q6nq.gwt_pat (@RATP) (@RATP) (Q6nq.gwt_hdr GwI.RATP (@RATP) gwt_X)))).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_W__3; @gw_eq_W__2; @gw_eq_W]]); first [ (pose proof MU as gw_h_; clear MU; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_W__3; @gw_eq_W__2; @gw_eq_W]]); rename gw_h_ into MU) | idtac ]; first [ (pose proof WIN as gw_h_; clear WIN; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_W__3; @gw_eq_W__2; @gw_eq_W]]); rename gw_h_ into WIN) | idtac ]; first [GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rctxW_avoid) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rctxW_avoid)]. Qed.

#[using="m MR MU WM ER EM EA EG ES ERs WIN"] Lemma rmrep_ctx_frameW :
(rw_cells rsegs m' RCTX (ctx_head_cells st') \/ (ctx_head_cells st' = ctx_head_cells st /\ forall lo hi, In (lo, hi) W -> RCTX + 80 <= lo \/ hi <= RCTX)) ->
(u64arr rsegs m' (RCTX + 80) (actives st') \/ (actives st' = actives st /\ forall lo hi, In (lo, hi) W -> RCTX + 464 <= lo \/ hi <= RCTX + 80)) ->
(u64arr rsegs m' (RCTX + 464) (usages st') \/ (usages st' = usages st /\ forall lo hi, In (lo, hi) W -> RCTX + 848 <= lo \/ hi <= RCTX + 464)) ->
(u8arr rsegs m' (RCTX + 848) (unmap_seqs st') \/ (unmap_seqs st' = unmap_seqs st /\ forall lo hi, In (lo, hi) W -> RCTX + 880 <= lo \/ hi <= RCTX + 848)) ->
(u8arr rsegs m' (RCTX + 880) (bouncess st') \/ (bouncess st' = bouncess st /\ forall lo hi, In (lo, hi) W -> RCTX + 912 <= lo \/ hi <= RCTX + 880)) ->
(rw_cells rsegs m' (RCTX + 912) (ctx_tail_cells st') \/ (ctx_tail_cells st' = ctx_tail_cells st /\ forall lo hi, In (lo, hi) W -> RCTX + 928 <= lo \/ hi <= RCTX + 912)) ->
rmrep st' m'.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_W__3; @gw_eq_W__2; @gw_eq_W]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [ (pose proof MU as gw_h_; clear MU; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_W__3; @gw_eq_W__2; @gw_eq_W]]); rename gw_h_ into MU) | idtac ]; first [ (pose proof WIN as gw_h_; clear WIN; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_W__3; @gw_eq_W__2; @gw_eq_W]]); rename gw_h_ into WIN) | idtac ]; first [GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rmrep_ctx_frameW) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QDXD.Mq2.rmrep_ctx_frameW)]. Qed.
End CTXFRAME.

Definition rntf_ret_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (st : mstate) (m : word -> option byte) (st' : mstate) (a0v a1v : word) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0v a1v a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp)
/\ rmrep st' m'.

End RC__1.
Lemma gw_eq_rrepfoot__2 : @rrepfoot = ltac:(GwInst.gw_term (@QDXD.Mq2.rrepfoot UKNz.RATP UKNz.RGOT_SSP) (@rrepfoot)). Proof. unfold rrepfoot, QDXD.Mq2.rrepfoot; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_rrepfoot__2 : gw_eqs.
Lemma gw_eq_rfree_fp__2 : @rfree_fp = ltac:(GwInst.gw_term (@QDXD.Mq2.rfree_fp UKNz.RATP) (@rfree_fp)). Proof. unfold rfree_fp, QDXD.Mq2.rfree_fp; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_rfree_fp__2 : gw_eqs.
