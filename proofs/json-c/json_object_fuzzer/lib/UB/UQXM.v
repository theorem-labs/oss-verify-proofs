(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwApply GwApply2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q8QT.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QnDM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Export QnDM.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UZ24.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Export UZ24. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKNz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Export UKNz.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV.
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
Lemma LAY_lo_RATP : ltac2:(GwEq.gw_fact_ty 'segs '(@Q8QT.Mq4.gw_all) @LAY_lo_RATP). Proof. GwApply.gw_side. Qed.
Lemma LAY_hi_RATP : ltac2:(GwEq.gw_fact_ty 'segs '(@Q8QT.Mq4.gw_all) @LAY_hi_RATP). Proof. GwApply.gw_side. Qed.
Lemma LAY_hi_RGOT_SSP : ltac2:(GwEq.gw_fact_ty 'segs '(@Q8QT.Mq4.gw_all) @LAY_hi_RGOT_SSP). Proof. GwApply.gw_side. Qed.
Lemma LAY_win_0 : ltac2:(GwEq.gw_fact_ty 'segs '(@Q8QT.Mq4.gw_all) @LAY_win_0). Proof. GwApply.gw_side. Qed.
Lemma LAY_win_1 : ltac2:(GwEq.gw_fact_ty 'segs '(@Q8QT.Mq4.gw_all) @LAY_win_1). Proof. GwApply.gw_side. Qed.
Lemma LAY_win_2 : ltac2:(GwEq.gw_fact_ty 'segs '(@Q8QT.Mq4.gw_all) @LAY_win_2). Proof. GwApply.gw_side. Qed.
Lemma LAY_win_3 : ltac2:(GwEq.gw_fact_ty 'segs '(@Q8QT.Mq4.gw_all) @LAY_win_3). Proof. GwApply.gw_side. Qed.
Lemma LAY_win_4 : ltac2:(GwEq.gw_fact_ty 'segs '(@Q8QT.Mq4.gw_all) @LAY_win_4). Proof. GwApply.gw_side. Qed.
Lemma ROM_RSIZE_CLASSES : ltac2:(GwEq.gw_fact_ty 'segs '(@Q8QT.Mq4.gw_all) @ROM_RSIZE_CLASSES). Proof. first [ apply QWxq.Mq0.ro_bytes_b_sound; vm_compute; reflexivity | GwApply.gw_side ]. Qed.
Lemma ROM_reservedZ : ltac2:(GwEq.gw_fact_ty 'segs '(@Q8QT.Mq4.gw_all) @ROM_reservedZ). Proof. first [ apply QWxq.Mq0.ro_bytes_b_sound; vm_compute; reflexivity | GwApply.gw_side ]. Qed.
Lemma LAY_ref_reserved : ltac2:(GwEq.gw_fact_ty 'segs '(@Q8QT.Mq4.gw_all) @LAY_ref_reserved). Proof. GwApply.gw_side. Qed.
End GwI.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma reservedZ_ref : reservedZ rsegs = ref_reserved.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.reservedZ_ref) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.reservedZ_ref)]. Qed.

Section MREP.
Variable st : mstate.
Variable m : word -> option byte.

Definition rmrep_ctx : Prop :=
rw_cells rsegs m RCTX (ctx_head_cells st)
/\ u64arr rsegs m (RCTX + 80) (actives st)
/\ u64arr rsegs m (RCTX + 464) (usages st)
/\ u8arr rsegs m (RCTX + 848) (unmap_seqs st)
/\ u8arr rsegs m (RCTX + 880) (bouncess st)
/\ rw_cells rsegs m (RCTX + 912) (ctx_tail_cells st).
Lemma gw_eq_rmrep_ctx : @rmrep_ctx = ltac:(GwInst.gw_term (@Q8QT.Mq4.rmrep_ctx rsegs UKNz.RATP) (@rmrep_ctx)). Proof. unfold rmrep_ctx, Q8QT.Mq4.rmrep_ctx; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rmrep_ctx : gw_eqs.

Definition rmrep_globals : Prop :=
rw_cells rsegs m RMLOCK [C4 (wz 0)]
/\ rw_cells rsegs m RNEED_LOCKS [C1 (b8 0)]
/\ rw_cells rsegs m RPAGE_SIZE [C8 (wz 4096)]
/\ rw_cells rsegs m RGOT_SSP [C8 (wz RSSP_GUARD)]
/\ rw_cells rsegs m RSSP_GUARD [C8 rc_canary].

Definition rarea_rep (a : aptr) (ar : area) : Prop :=
rw_cells rsegs m (conc st a) [C8 (wz (a_check ar)); C8 (pw st (a_next ar)); C4 (wz (a_nslots ar)); C4 (wz 0)]
/\ (forall k, 0 <= k < NSLOTS ->
rw_cells rsegs m (conc st a + AREA_HDR + META_SIZE * k)
(meta_cells st (get_meta_rec st (aadd a (AREA_HDR + META_SIZE * k)))))
/\ rw_cells rsegs m (conc st a + 4064) [CB 32 (zeros 32)].
Lemma gw_eq_rarea_rep : @rarea_rep = ltac:(GwInst.gw_term (@Q8QT.Mq4.rarea_rep rsegs) (@rarea_rep)). Proof. unfold rarea_rep, Q8QT.Mq4.rarea_rep; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rarea_rep : gw_eqs.
Definition rmrep_areas : Prop :=
forall a ar, (s_areas st) !! a = Some ar -> rarea_rep a ar.
Lemma gw_eq_rmrep_areas : @rmrep_areas = ltac:(GwInst.gw_term (@Q8QT.Mq4.rmrep_areas rsegs) (@rmrep_areas)). Proof. unfold rmrep_areas, Q8QT.Mq4.rmrep_areas; rewrite ?gw_eq_rarea_rep; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rmrep_areas : gw_eqs.

Definition rgroup_rep (b : aptr) (gh : ghdr) : Prop :=
exists w8 : byte,
rw_cells rsegs m (conc st b) [C8 (pw st (g_meta gh)); C1 w8]
/\ Z.land (bv_unsigned w8) 31 = g_active_idx gh.
Lemma gw_eq_rgroup_rep : @rgroup_rep = ltac:(GwInst.gw_term (@Q8QT.Mq4.rgroup_rep rsegs) (@rgroup_rep)). Proof. unfold rgroup_rep, Q8QT.Mq4.rgroup_rep; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rgroup_rep : gw_eqs.
Definition rmrep_groups : Prop :=
forall b gh, (s_groups st) !! b = Some gh -> rgroup_rep b gh.
Lemma gw_eq_rmrep_groups : @rmrep_groups = ltac:(GwInst.gw_term (@Q8QT.Mq4.rmrep_groups rsegs) (@rmrep_groups)). Proof. unfold rmrep_groups, Q8QT.Mq4.rmrep_groups; rewrite ?gw_eq_rgroup_rep; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rmrep_groups : gw_eqs.

Definition rshadow_rep (rid : N) (r : region) : Prop :=
wr_at rsegs m (r_base r) (round_up_pg (r_len r))
/\ forall o v, 0 <= o < round_up_pg (r_len r) ->
cell_read (get_shadow st rid) o = Known v ->
bytes_at rsegs m (r_base r + o) [b8 v] /\ 0 <= v < 256.
Lemma gw_eq_rshadow_rep : @rshadow_rep = ltac:(GwInst.gw_term (@Q8QT.Mq4.rshadow_rep rsegs) (@rshadow_rep)). Proof. unfold rshadow_rep, Q8QT.Mq4.rshadow_rep; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rshadow_rep : gw_eqs.
Definition rmrep_shadow : Prop :=
forall rid r, (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> rshadow_rep rid r.
Lemma gw_eq_rmrep_shadow : @rmrep_shadow = ltac:(GwInst.gw_term (@Q8QT.Mq4.rmrep_shadow rsegs) (@rmrep_shadow)). Proof. unfold rmrep_shadow, Q8QT.Mq4.rmrep_shadow; rewrite ?gw_eq_rshadow_rep; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rmrep_shadow : gw_eqs.

Definition rregions_wf : Prop :=
s_reserved st = ref_reserved
/\ (forall rid r, (s_regions st) !! rid = Some r ->
0 < r_base r /\ r_base r mod 4096 = 0 /\ 0 <= r_len r
/\ r_base r + round_up_pg (r_len r) <= alloc_ceiling
/\ ranges_free ref_reserved (r_base r) (round_up_pg (r_len r)) = true)
/\ (forall rid1 r1 rid2 r2, (s_regions st) !! rid1 = Some r1 -> (s_regions st) !! rid2 = Some r2 -> rid1 <> rid2 ->
r_base r1 + round_up_pg (r_len r1) <= lr_lo r2 \/ r_base r2 + round_up_pg (r_len r2) <= lr_lo r1)

/\ (forall a ar, (s_areas st) !! a = Some ar ->
exists r, (s_regions st) !! (fst a) = Some r /\ 0 <= snd a /\ snd a + 4096 <= round_up_pg (r_len r) /\ snd a mod 4096 = 0
/\ r_kind r <> RKGroup /\ lr_lo r <= r_base r + snd a)
/\ (forall b gh, (s_groups st) !! b = Some gh ->
exists r, (s_regions st) !! (fst b) = Some r /\ r_kind r = RKGroup /\ 0 <= snd b /\ snd b + 16 <= round_up_pg (r_len r) /\ snd b mod 16 = 0).

Definition rmrep : Prop :=
rregions_wf /\ rmrep_ctx /\ rmrep_globals /\ rmrep_areas /\ rmrep_groups /\ rmrep_shadow.

End MREP.
Lemma gw_eq_rmrep_ctx__2 : @rmrep_ctx = ltac:(GwInst.gw_term (@Q8QT.Mq4.rmrep_ctx rsegs UKNz.RATP) (@rmrep_ctx)). Proof. unfold rmrep_ctx, Q8QT.Mq4.rmrep_ctx; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rmrep_ctx__2 : gw_eqs.
Lemma gw_eq_rarea_rep__2 : @rarea_rep = ltac:(GwInst.gw_term (@Q8QT.Mq4.rarea_rep rsegs) (@rarea_rep)). Proof. unfold rarea_rep, Q8QT.Mq4.rarea_rep; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rarea_rep__2 : gw_eqs.
Lemma gw_eq_rmrep_areas__2 : @rmrep_areas = ltac:(GwInst.gw_term (@Q8QT.Mq4.rmrep_areas rsegs) (@rmrep_areas)). Proof. unfold rmrep_areas, Q8QT.Mq4.rmrep_areas; rewrite ?gw_eq_rarea_rep__2; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rmrep_areas__2 : gw_eqs.
Lemma gw_eq_rgroup_rep__2 : @rgroup_rep = ltac:(GwInst.gw_term (@Q8QT.Mq4.rgroup_rep rsegs) (@rgroup_rep)). Proof. unfold rgroup_rep, Q8QT.Mq4.rgroup_rep; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rgroup_rep__2 : gw_eqs.
Lemma gw_eq_rmrep_groups__2 : @rmrep_groups = ltac:(GwInst.gw_term (@Q8QT.Mq4.rmrep_groups rsegs) (@rmrep_groups)). Proof. unfold rmrep_groups, Q8QT.Mq4.rmrep_groups; rewrite ?gw_eq_rgroup_rep__2; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rmrep_groups__2 : gw_eqs.
Lemma gw_eq_rshadow_rep__2 : @rshadow_rep = ltac:(GwInst.gw_term (@Q8QT.Mq4.rshadow_rep rsegs) (@rshadow_rep)). Proof. unfold rshadow_rep, Q8QT.Mq4.rshadow_rep; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rshadow_rep__2 : gw_eqs.
Lemma gw_eq_rmrep_shadow__2 : @rmrep_shadow = ltac:(GwInst.gw_term (@Q8QT.Mq4.rmrep_shadow rsegs) (@rmrep_shadow)). Proof. unfold rmrep_shadow, Q8QT.Mq4.rmrep_shadow; rewrite ?gw_eq_rshadow_rep__2; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rmrep_shadow__2 : gw_eqs.

Definition rmrep_W (st : mstate) : list (Z * Z) :=
(RCTX, RCTX + 928)
:: map (fun kr : N * region => (r_base (snd kr), r_base (snd kr) + round_up_pg (r_len (snd kr)))) (map_to_list (s_regions st)).
Lemma gw_eq_rmrep_W : @rmrep_W = ltac:(GwInst.gw_term (@Q8QT.Mq4.rmrep_W UKNz.RATP) (@rmrep_W)). Proof. unfold rmrep_W, Q8QT.Mq4.rmrep_W; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rmrep_W : gw_eqs.

#[using="Type"] Lemma rmrep_shadow_read : ltac2:(Q6nq.ty2 'GwI.segs '(@Q8QT.Mq4.rmrep_shadow_read) [[@gw_eq_rmrep_ctx__3; @gw_eq_rmrep_ctx__2; @gw_eq_rmrep_ctx]; [@gw_eq_rarea_rep__3; @gw_eq_rarea_rep__2; @gw_eq_rarea_rep]; [@gw_eq_rmrep_areas__3; @gw_eq_rmrep_areas__2; @gw_eq_rmrep_areas]; [@gw_eq_rgroup_rep__3; @gw_eq_rgroup_rep__2; @gw_eq_rgroup_rep]; [@gw_eq_rmrep_groups__3; @gw_eq_rmrep_groups__2; @gw_eq_rmrep_groups]; [@gw_eq_rshadow_rep__3; @gw_eq_rshadow_rep__2; @gw_eq_rshadow_rep]; [@gw_eq_rmrep_shadow__3; @gw_eq_rmrep_shadow__2; @gw_eq_rmrep_shadow]; [@gw_eq_rmrep_W__3; @gw_eq_rmrep_W__2; @gw_eq_rmrep_W]] '(@nil Z) '(Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@rmrep) (Q6nq.gwt_def (@Q8QT.Mq4.rregions_wf) (@rregions_wf) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_globals) (@rmrep_globals) Q6nq.gwt_nil)))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rmrep_shadow_read) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rmrep_shadow_read)]. Qed.

#[using="Type"] Lemma rmrep_shadow_read2 : ltac2:(Q6nq.ty2 'GwI.segs '(@Q8QT.Mq4.rmrep_shadow_read2) [[@gw_eq_rmrep_ctx__3; @gw_eq_rmrep_ctx__2; @gw_eq_rmrep_ctx]; [@gw_eq_rarea_rep__3; @gw_eq_rarea_rep__2; @gw_eq_rarea_rep]; [@gw_eq_rmrep_areas__3; @gw_eq_rmrep_areas__2; @gw_eq_rmrep_areas]; [@gw_eq_rgroup_rep__3; @gw_eq_rgroup_rep__2; @gw_eq_rgroup_rep]; [@gw_eq_rmrep_groups__3; @gw_eq_rmrep_groups__2; @gw_eq_rmrep_groups]; [@gw_eq_rshadow_rep__3; @gw_eq_rshadow_rep__2; @gw_eq_rshadow_rep]; [@gw_eq_rmrep_shadow__3; @gw_eq_rmrep_shadow__2; @gw_eq_rmrep_shadow]; [@gw_eq_rmrep_W__3; @gw_eq_rmrep_W__2; @gw_eq_rmrep_W]] '([256]%Z : list Z) '(Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@rmrep) (Q6nq.gwt_def (@Q8QT.Mq4.rregions_wf) (@rregions_wf) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_globals) (@rmrep_globals) Q6nq.gwt_nil)))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rmrep_shadow_read2) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rmrep_shadow_read2)]. Qed.

Definition rsize_classes_bytes : list byte :=
Eval vm_compute in (match image_bytes rsegs RSIZE_CLASSES 96 with Some bs => bs | None => [] end).
Lemma gw_eq_rsize_classes_bytes : @rsize_classes_bytes = ltac:(GwInst.gw_term (@Q8QT.Mq4.rsize_classes_bytes) (@rsize_classes_bytes)). Proof. unfold rsize_classes_bytes, Q8QT.Mq4.rsize_classes_bytes; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rsize_classes_bytes : gw_eqs.

#[using="Type"] Lemma rsize_classes_ro : forall m, mem_inv rsegs m -> ro_cells rsegs m RSIZE_CLASSES [CB 96 rsize_classes_bytes].
Proof. rewrite ?gw_eq_rsize_classes_bytes; first [GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rsize_classes_ro) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rsize_classes_ro)]. Qed.

#[using="Type"] Lemma rsize_classes_read : ltac2:(Q6nq.ty2 'GwI.segs '(@Q8QT.Mq4.rsize_classes_read) [[@gw_eq_rmrep_ctx__3; @gw_eq_rmrep_ctx__2; @gw_eq_rmrep_ctx]; [@gw_eq_rarea_rep__3; @gw_eq_rarea_rep__2; @gw_eq_rarea_rep]; [@gw_eq_rmrep_areas__3; @gw_eq_rmrep_areas__2; @gw_eq_rmrep_areas]; [@gw_eq_rgroup_rep__3; @gw_eq_rgroup_rep__2; @gw_eq_rgroup_rep]; [@gw_eq_rmrep_groups__3; @gw_eq_rmrep_groups__2; @gw_eq_rmrep_groups]; [@gw_eq_rshadow_rep__3; @gw_eq_rshadow_rep__2; @gw_eq_rshadow_rep]; [@gw_eq_rmrep_shadow__3; @gw_eq_rmrep_shadow__2; @gw_eq_rmrep_shadow]; [@gw_eq_rmrep_W__3; @gw_eq_rmrep_W__2; @gw_eq_rmrep_W]; [@gw_eq_rsize_classes_bytes__3; @gw_eq_rsize_classes_bytes__2; @gw_eq_rsize_classes_bytes]] '(@nil Z) '(Q6nq.gwt_zc RSIZE_CLASSES (Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@rmrep) (Q6nq.gwt_def (@Q8QT.Mq4.rregions_wf) (@rregions_wf) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_globals) (@rmrep_globals) (Q6nq.gwt_pat (@RDEBRUIJN) (@RDEBRUIJN) (Q6nq.gwt_hdr GwI.RDEBRUIJN (@RDEBRUIJN) Q6nq.gwt_nil))))))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rsize_classes_read) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rsize_classes_read)]. Qed.

#[using="Type"] Lemma rmrep_meta_chunk : ltac2:(Q6nq.ty2 'GwI.segs '(@Q8QT.Mq4.rmrep_meta_chunk) [[@gw_eq_rmrep_ctx__3; @gw_eq_rmrep_ctx__2; @gw_eq_rmrep_ctx]; [@gw_eq_rarea_rep__3; @gw_eq_rarea_rep__2; @gw_eq_rarea_rep]; [@gw_eq_rmrep_areas__3; @gw_eq_rmrep_areas__2; @gw_eq_rmrep_areas]; [@gw_eq_rgroup_rep__3; @gw_eq_rgroup_rep__2; @gw_eq_rgroup_rep]; [@gw_eq_rmrep_groups__3; @gw_eq_rmrep_groups__2; @gw_eq_rmrep_groups]; [@gw_eq_rshadow_rep__3; @gw_eq_rshadow_rep__2; @gw_eq_rshadow_rep]; [@gw_eq_rmrep_shadow__3; @gw_eq_rmrep_shadow__2; @gw_eq_rmrep_shadow]; [@gw_eq_rmrep_W__3; @gw_eq_rmrep_W__2; @gw_eq_rmrep_W]; [@gw_eq_rsize_classes_bytes__3; @gw_eq_rsize_classes_bytes__2; @gw_eq_rsize_classes_bytes]] '(@nil Z) '(Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@rmrep) (Q6nq.gwt_def (@Q8QT.Mq4.rregions_wf) (@rregions_wf) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_globals) (@rmrep_globals) Q6nq.gwt_nil)))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rmrep_meta_chunk) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rmrep_meta_chunk)]. Qed.

#[using="Type"] Lemma rmrep_group_read : ltac2:(Q6nq.ty2 'GwI.segs '(@Q8QT.Mq4.rmrep_group_read) [[@gw_eq_rmrep_ctx__3; @gw_eq_rmrep_ctx__2; @gw_eq_rmrep_ctx]; [@gw_eq_rarea_rep__3; @gw_eq_rarea_rep__2; @gw_eq_rarea_rep]; [@gw_eq_rmrep_areas__3; @gw_eq_rmrep_areas__2; @gw_eq_rmrep_areas]; [@gw_eq_rgroup_rep__3; @gw_eq_rgroup_rep__2; @gw_eq_rgroup_rep]; [@gw_eq_rmrep_groups__3; @gw_eq_rmrep_groups__2; @gw_eq_rmrep_groups]; [@gw_eq_rshadow_rep__3; @gw_eq_rshadow_rep__2; @gw_eq_rshadow_rep]; [@gw_eq_rmrep_shadow__3; @gw_eq_rmrep_shadow__2; @gw_eq_rmrep_shadow]; [@gw_eq_rmrep_W__3; @gw_eq_rmrep_W__2; @gw_eq_rmrep_W]; [@gw_eq_rsize_classes_bytes__3; @gw_eq_rsize_classes_bytes__2; @gw_eq_rsize_classes_bytes]] '(@nil Z) '(Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@rmrep) (Q6nq.gwt_def (@Q8QT.Mq4.rregions_wf) (@rregions_wf) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_globals) (@rmrep_globals) Q6nq.gwt_nil)))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rmrep_group_read) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rmrep_group_read)]. Qed.

#[using="Type"] Lemma rmrep_area_check_read : ltac2:(Q6nq.ty2 'GwI.segs '(@Q8QT.Mq4.rmrep_area_check_read) [[@gw_eq_rmrep_ctx__3; @gw_eq_rmrep_ctx__2; @gw_eq_rmrep_ctx]; [@gw_eq_rarea_rep__3; @gw_eq_rarea_rep__2; @gw_eq_rarea_rep]; [@gw_eq_rmrep_areas__3; @gw_eq_rmrep_areas__2; @gw_eq_rmrep_areas]; [@gw_eq_rgroup_rep__3; @gw_eq_rgroup_rep__2; @gw_eq_rgroup_rep]; [@gw_eq_rmrep_groups__3; @gw_eq_rmrep_groups__2; @gw_eq_rmrep_groups]; [@gw_eq_rshadow_rep__3; @gw_eq_rshadow_rep__2; @gw_eq_rshadow_rep]; [@gw_eq_rmrep_shadow__3; @gw_eq_rmrep_shadow__2; @gw_eq_rmrep_shadow]; [@gw_eq_rmrep_W__3; @gw_eq_rmrep_W__2; @gw_eq_rmrep_W]; [@gw_eq_rsize_classes_bytes__3; @gw_eq_rsize_classes_bytes__2; @gw_eq_rsize_classes_bytes]] '(@nil Z) '(Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@rmrep) (Q6nq.gwt_def (@Q8QT.Mq4.rregions_wf) (@rregions_wf) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_globals) (@rmrep_globals) Q6nq.gwt_nil)))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rmrep_area_check_read) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rmrep_area_check_read)]. Qed.

#[using="Type"] Lemma rmrep_ctx_secret_read : forall st m,
rmrep st m -> ov_read_bytes rsegs m (wa RCTX) 8 = Some (le8 (wz (c_secret (ctx st)))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rmrep_ctx_secret_read) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rmrep_ctx_secret_read)]. Qed.

#[using="Type"] Lemma rreserved_disjoint : ltac2:(Q6nq.ty2 'GwI.segs '(@Q8QT.Mq4.rreserved_disjoint) [[@gw_eq_rmrep_ctx__3; @gw_eq_rmrep_ctx__2; @gw_eq_rmrep_ctx]; [@gw_eq_rarea_rep__3; @gw_eq_rarea_rep__2; @gw_eq_rarea_rep]; [@gw_eq_rmrep_areas__3; @gw_eq_rmrep_areas__2; @gw_eq_rmrep_areas]; [@gw_eq_rgroup_rep__3; @gw_eq_rgroup_rep__2; @gw_eq_rgroup_rep]; [@gw_eq_rmrep_groups__3; @gw_eq_rmrep_groups__2; @gw_eq_rmrep_groups]; [@gw_eq_rshadow_rep__3; @gw_eq_rshadow_rep__2; @gw_eq_rshadow_rep]; [@gw_eq_rmrep_shadow__3; @gw_eq_rmrep_shadow__2; @gw_eq_rmrep_shadow]; [@gw_eq_rmrep_W__3; @gw_eq_rmrep_W__2; @gw_eq_rmrep_W]; [@gw_eq_rsize_classes_bytes__3; @gw_eq_rsize_classes_bytes__2; @gw_eq_rsize_classes_bytes]] '([65536; 131072; 401408; 417792; 626688]%Z : list Z) '(Q6nq.gwt_unf (@RIMG_LO) (Q6nq.gwt_unf (@RIMG_HI) (Q6nq.gwt_unf (@RDATA_LO) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@rmrep) (Q6nq.gwt_def (@Q8QT.Mq4.rregions_wf) (@rregions_wf) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_globals) (@rmrep_globals) (Q6nq.gwt_pat (@ref_reserved) (@ref_reserved) (Q6nq.gwt_hdr GwI.ref_reserved (@ref_reserved) (Q6nq.gwt_pat (@RIMG_HI) (@RIMG_HI) (Q6nq.gwt_hdr GwI.RIMG_HI (@RIMG_HI) (Q6nq.gwt_pat (@RDATA_LO) (@RDATA_LO) (Q6nq.gwt_hdr GwI.RDATA_LO (@RDATA_LO) Q6nq.gwt_nil))))))))))))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rreserved_disjoint) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rreserved_disjoint)]. Qed.

#[using="Type"] Lemma rreserved_disjoint1 : forall b n, ranges_free ref_reserved b n = true -> 0 < n ->
b + n <= 0x10000 \/ 0x99000 <= b.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rreserved_disjoint1) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rreserved_disjoint1)]. Qed.

#[using="Type"] Lemma rwr_in_image : ltac2:(Q6nq.ty2 'GwI.segs '(@Q8QT.Mq4.rwr_in_image) [[@gw_eq_rmrep_ctx__3; @gw_eq_rmrep_ctx__2; @gw_eq_rmrep_ctx]; [@gw_eq_rarea_rep__3; @gw_eq_rarea_rep__2; @gw_eq_rarea_rep]; [@gw_eq_rmrep_areas__3; @gw_eq_rmrep_areas__2; @gw_eq_rmrep_areas]; [@gw_eq_rgroup_rep__3; @gw_eq_rgroup_rep__2; @gw_eq_rgroup_rep]; [@gw_eq_rmrep_groups__3; @gw_eq_rmrep_groups__2; @gw_eq_rmrep_groups]; [@gw_eq_rshadow_rep__3; @gw_eq_rshadow_rep__2; @gw_eq_rshadow_rep]; [@gw_eq_rmrep_shadow__3; @gw_eq_rmrep_shadow__2; @gw_eq_rmrep_shadow]; [@gw_eq_rmrep_W__3; @gw_eq_rmrep_W__2; @gw_eq_rmrep_W]; [@gw_eq_rsize_classes_bytes__3; @gw_eq_rsize_classes_bytes__2; @gw_eq_rsize_classes_bytes]] '([401408; 417792; 626688]%Z : list Z) '(Q6nq.gwt_unf (@RIMG_HI) (Q6nq.gwt_unf (@RDATA_LO) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@rmrep) (Q6nq.gwt_def (@Q8QT.Mq4.rregions_wf) (@rregions_wf) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_globals) (@rmrep_globals) (Q6nq.gwt_pat (@RIMG_HI) (@RIMG_HI) (Q6nq.gwt_hdr GwI.RIMG_HI (@RIMG_HI) (Q6nq.gwt_pat (@RDATA_LO) (@RDATA_LO) (Q6nq.gwt_hdr GwI.RDATA_LO (@RDATA_LO) Q6nq.gwt_nil)))))))))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rwr_in_image) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rwr_in_image)]. Qed.

#[using="Type"] Lemma rwr_in_other : ltac2:(Q6nq.ty2 'GwI.segs '(@Q8QT.Mq4.rwr_in_other) [[@gw_eq_rmrep_ctx__3; @gw_eq_rmrep_ctx__2; @gw_eq_rmrep_ctx]; [@gw_eq_rarea_rep__3; @gw_eq_rarea_rep__2; @gw_eq_rarea_rep]; [@gw_eq_rmrep_areas__3; @gw_eq_rmrep_areas__2; @gw_eq_rmrep_areas]; [@gw_eq_rgroup_rep__3; @gw_eq_rgroup_rep__2; @gw_eq_rgroup_rep]; [@gw_eq_rmrep_groups__3; @gw_eq_rmrep_groups__2; @gw_eq_rmrep_groups]; [@gw_eq_rshadow_rep__3; @gw_eq_rshadow_rep__2; @gw_eq_rshadow_rep]; [@gw_eq_rmrep_shadow__3; @gw_eq_rmrep_shadow__2; @gw_eq_rmrep_shadow]; [@gw_eq_rmrep_W__3; @gw_eq_rmrep_W__2; @gw_eq_rmrep_W]; [@gw_eq_rsize_classes_bytes__3; @gw_eq_rsize_classes_bytes__2; @gw_eq_rsize_classes_bytes]] '(@nil Z) '(Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@rmrep) (Q6nq.gwt_def (@Q8QT.Mq4.rregions_wf) (@rregions_wf) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_globals) (@rmrep_globals) Q6nq.gwt_nil)))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rwr_in_other) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rwr_in_other)]. Qed.

#[using="Type"] Lemma rarea_lr_lo : ltac2:(Q6nq.ty2 'GwI.segs '(@Q8QT.Mq4.rarea_lr_lo) [[@gw_eq_rmrep_ctx__3; @gw_eq_rmrep_ctx__2; @gw_eq_rmrep_ctx]; [@gw_eq_rarea_rep__3; @gw_eq_rarea_rep__2; @gw_eq_rarea_rep]; [@gw_eq_rmrep_areas__3; @gw_eq_rmrep_areas__2; @gw_eq_rmrep_areas]; [@gw_eq_rgroup_rep__3; @gw_eq_rgroup_rep__2; @gw_eq_rgroup_rep]; [@gw_eq_rmrep_groups__3; @gw_eq_rmrep_groups__2; @gw_eq_rmrep_groups]; [@gw_eq_rshadow_rep__3; @gw_eq_rshadow_rep__2; @gw_eq_rshadow_rep]; [@gw_eq_rmrep_shadow__3; @gw_eq_rmrep_shadow__2; @gw_eq_rmrep_shadow]; [@gw_eq_rmrep_W__3; @gw_eq_rmrep_W__2; @gw_eq_rmrep_W]; [@gw_eq_rsize_classes_bytes__3; @gw_eq_rsize_classes_bytes__2; @gw_eq_rsize_classes_bytes]] '(@nil Z) '(Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@rmrep) (Q6nq.gwt_def (@Q8QT.Mq4.rregions_wf) (@rregions_wf) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_globals) (@rmrep_globals) Q6nq.gwt_nil)))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rarea_lr_lo) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rarea_lr_lo)]. Qed.

#[using="Type"] Lemma rregions_disjoint_full : ltac2:(Q6nq.ty2 'GwI.segs '(@Q8QT.Mq4.rregions_disjoint_full) [[@gw_eq_rmrep_ctx__3; @gw_eq_rmrep_ctx__2; @gw_eq_rmrep_ctx]; [@gw_eq_rarea_rep__3; @gw_eq_rarea_rep__2; @gw_eq_rarea_rep]; [@gw_eq_rmrep_areas__3; @gw_eq_rmrep_areas__2; @gw_eq_rmrep_areas]; [@gw_eq_rgroup_rep__3; @gw_eq_rgroup_rep__2; @gw_eq_rgroup_rep]; [@gw_eq_rmrep_groups__3; @gw_eq_rmrep_groups__2; @gw_eq_rmrep_groups]; [@gw_eq_rshadow_rep__3; @gw_eq_rshadow_rep__2; @gw_eq_rshadow_rep]; [@gw_eq_rmrep_shadow__3; @gw_eq_rmrep_shadow__2; @gw_eq_rmrep_shadow]; [@gw_eq_rmrep_W__3; @gw_eq_rmrep_W__2; @gw_eq_rmrep_W]; [@gw_eq_rsize_classes_bytes__3; @gw_eq_rsize_classes_bytes__2; @gw_eq_rsize_classes_bytes]] '(@nil Z) '(Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@rmrep) (Q6nq.gwt_def (@Q8QT.Mq4.rregions_wf) (@rregions_wf) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_globals) (@rmrep_globals) Q6nq.gwt_nil)))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rregions_disjoint_full) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rregions_disjoint_full)]. Qed.

#[using="Type"] Lemma rregions_disjoint_grp : ltac2:(Q6nq.ty2 'GwI.segs '(@Q8QT.Mq4.rregions_disjoint_grp) [[@gw_eq_rmrep_ctx__3; @gw_eq_rmrep_ctx__2; @gw_eq_rmrep_ctx]; [@gw_eq_rarea_rep__3; @gw_eq_rarea_rep__2; @gw_eq_rarea_rep]; [@gw_eq_rmrep_areas__3; @gw_eq_rmrep_areas__2; @gw_eq_rmrep_areas]; [@gw_eq_rgroup_rep__3; @gw_eq_rgroup_rep__2; @gw_eq_rgroup_rep]; [@gw_eq_rmrep_groups__3; @gw_eq_rmrep_groups__2; @gw_eq_rmrep_groups]; [@gw_eq_rshadow_rep__3; @gw_eq_rshadow_rep__2; @gw_eq_rshadow_rep]; [@gw_eq_rmrep_shadow__3; @gw_eq_rmrep_shadow__2; @gw_eq_rmrep_shadow]; [@gw_eq_rmrep_W__3; @gw_eq_rmrep_W__2; @gw_eq_rmrep_W]; [@gw_eq_rsize_classes_bytes__3; @gw_eq_rsize_classes_bytes__2; @gw_eq_rsize_classes_bytes]] '(@nil Z) '(Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@rmrep) (Q6nq.gwt_def (@Q8QT.Mq4.rregions_wf) (@rregions_wf) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_globals) (@rmrep_globals) Q6nq.gwt_nil)))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rregions_disjoint_grp) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rregions_disjoint_grp)]. Qed.

#[using="Type"] Lemma rmrep_ctx_ext : ltac2:(Q6nq.ty2 'GwI.segs '(@Q8QT.Mq4.rmrep_ctx_ext) [[@gw_eq_rmrep_ctx__2]; [@gw_eq_rarea_rep__3; @gw_eq_rarea_rep__2; @gw_eq_rarea_rep]; [@gw_eq_rmrep_areas__3; @gw_eq_rmrep_areas__2; @gw_eq_rmrep_areas]; [@gw_eq_rgroup_rep__3; @gw_eq_rgroup_rep__2; @gw_eq_rgroup_rep]; [@gw_eq_rmrep_groups__3; @gw_eq_rmrep_groups__2; @gw_eq_rmrep_groups]; [@gw_eq_rshadow_rep__3; @gw_eq_rshadow_rep__2; @gw_eq_rshadow_rep]; [@gw_eq_rmrep_shadow__3; @gw_eq_rmrep_shadow__2; @gw_eq_rmrep_shadow]; [@gw_eq_rmrep_W__3; @gw_eq_rmrep_W__2; @gw_eq_rmrep_W]; [@gw_eq_rsize_classes_bytes__3; @gw_eq_rsize_classes_bytes__2; @gw_eq_rsize_classes_bytes]] '(@nil Z) '(Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@rmrep) (Q6nq.gwt_def (@Q8QT.Mq4.rregions_wf) (@rregions_wf) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_globals) (@rmrep_globals) Q6nq.gwt_nil)))).
Proof. rewrite ?gw_eq_rmrep_ctx__2; first [GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rmrep_ctx_ext) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rmrep_ctx_ext)]. Qed.

#[using="Type"] Lemma rarea_rep_ext : ltac2:(Q6nq.ty2 'GwI.segs '(@Q8QT.Mq4.rarea_rep_ext) [[@gw_eq_rarea_rep__2]; [@gw_eq_rmrep_ctx__3; @gw_eq_rmrep_ctx__2; @gw_eq_rmrep_ctx]; [@gw_eq_rmrep_areas__3; @gw_eq_rmrep_areas__2; @gw_eq_rmrep_areas]; [@gw_eq_rgroup_rep__3; @gw_eq_rgroup_rep__2; @gw_eq_rgroup_rep]; [@gw_eq_rmrep_groups__3; @gw_eq_rmrep_groups__2; @gw_eq_rmrep_groups]; [@gw_eq_rshadow_rep__3; @gw_eq_rshadow_rep__2; @gw_eq_rshadow_rep]; [@gw_eq_rmrep_shadow__3; @gw_eq_rmrep_shadow__2; @gw_eq_rmrep_shadow]; [@gw_eq_rmrep_W__3; @gw_eq_rmrep_W__2; @gw_eq_rmrep_W]; [@gw_eq_rsize_classes_bytes__3; @gw_eq_rsize_classes_bytes__2; @gw_eq_rsize_classes_bytes]] '(@nil Z) '(Q6nq.gwt_zc NSLOTS (Q6nq.gwt_zc META_SIZE (Q6nq.gwt_zc AREA_HDR (Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@rmrep) (Q6nq.gwt_def (@Q8QT.Mq4.rregions_wf) (@rregions_wf) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_globals) (@rmrep_globals) Q6nq.gwt_nil))))))).
Proof. rewrite ?gw_eq_rarea_rep__2; first [GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rarea_rep_ext) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rarea_rep_ext)]. Qed.

#[using="Type"] Lemma rgroup_rep_ext : ltac2:(Q6nq.ty2 'GwI.segs '(@Q8QT.Mq4.rgroup_rep_ext) [[@gw_eq_rgroup_rep__2]; [@gw_eq_rmrep_ctx__3; @gw_eq_rmrep_ctx__2; @gw_eq_rmrep_ctx]; [@gw_eq_rarea_rep__3; @gw_eq_rarea_rep__2; @gw_eq_rarea_rep]; [@gw_eq_rmrep_areas__3; @gw_eq_rmrep_areas__2; @gw_eq_rmrep_areas]; [@gw_eq_rmrep_groups__3; @gw_eq_rmrep_groups__2; @gw_eq_rmrep_groups]; [@gw_eq_rshadow_rep__3; @gw_eq_rshadow_rep__2; @gw_eq_rshadow_rep]; [@gw_eq_rmrep_shadow__3; @gw_eq_rmrep_shadow__2; @gw_eq_rmrep_shadow]; [@gw_eq_rmrep_W__3; @gw_eq_rmrep_W__2; @gw_eq_rmrep_W]; [@gw_eq_rsize_classes_bytes__3; @gw_eq_rsize_classes_bytes__2; @gw_eq_rsize_classes_bytes]] '(@nil Z) '(Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@rmrep) (Q6nq.gwt_def (@Q8QT.Mq4.rregions_wf) (@rregions_wf) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_globals) (@rmrep_globals) Q6nq.gwt_nil)))).
Proof. rewrite ?gw_eq_rgroup_rep__2; first [GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rgroup_rep_ext) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rgroup_rep_ext)]. Qed.

#[using="Type"] Lemma rshadow_rep_ext : ltac2:(Q6nq.ty2 'GwI.segs '(@Q8QT.Mq4.rshadow_rep_ext) [[@gw_eq_rshadow_rep__2]; [@gw_eq_rmrep_ctx__3; @gw_eq_rmrep_ctx__2; @gw_eq_rmrep_ctx]; [@gw_eq_rarea_rep__3; @gw_eq_rarea_rep__2; @gw_eq_rarea_rep]; [@gw_eq_rmrep_areas__3; @gw_eq_rmrep_areas__2; @gw_eq_rmrep_areas]; [@gw_eq_rgroup_rep__3; @gw_eq_rgroup_rep__2; @gw_eq_rgroup_rep]; [@gw_eq_rmrep_groups__3; @gw_eq_rmrep_groups__2; @gw_eq_rmrep_groups]; [@gw_eq_rmrep_shadow__3; @gw_eq_rmrep_shadow__2; @gw_eq_rmrep_shadow]; [@gw_eq_rmrep_W__3; @gw_eq_rmrep_W__2; @gw_eq_rmrep_W]; [@gw_eq_rsize_classes_bytes__3; @gw_eq_rsize_classes_bytes__2; @gw_eq_rsize_classes_bytes]] '(@nil Z) '(Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@rmrep) (Q6nq.gwt_def (@Q8QT.Mq4.rregions_wf) (@rregions_wf) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_globals) (@rmrep_globals) Q6nq.gwt_nil)))).
Proof. rewrite ?gw_eq_rshadow_rep__2; first [GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rshadow_rep_ext) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rshadow_rep_ext)]. Qed.

#[using="Type"] Lemma rmrep_ctx_frame : ltac2:(Q6nq.ty2 'GwI.segs '(@Q8QT.Mq4.rmrep_ctx_frame) [[@gw_eq_rmrep_ctx__2]; [@gw_eq_rarea_rep__3; @gw_eq_rarea_rep__2; @gw_eq_rarea_rep]; [@gw_eq_rmrep_areas__3; @gw_eq_rmrep_areas__2; @gw_eq_rmrep_areas]; [@gw_eq_rgroup_rep__3; @gw_eq_rgroup_rep__2; @gw_eq_rgroup_rep]; [@gw_eq_rmrep_groups__3; @gw_eq_rmrep_groups__2; @gw_eq_rmrep_groups]; [@gw_eq_rshadow_rep__3; @gw_eq_rshadow_rep__2; @gw_eq_rshadow_rep]; [@gw_eq_rmrep_shadow__3; @gw_eq_rmrep_shadow__2; @gw_eq_rmrep_shadow]; [@gw_eq_rmrep_W__3; @gw_eq_rmrep_W__2; @gw_eq_rmrep_W]; [@gw_eq_rsize_classes_bytes__3; @gw_eq_rsize_classes_bytes__2; @gw_eq_rsize_classes_bytes]] '(@nil Z) '(Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@rmrep) (Q6nq.gwt_def (@Q8QT.Mq4.rregions_wf) (@rregions_wf) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_globals) (@rmrep_globals) Q6nq.gwt_nil)))).
Proof. rewrite ?gw_eq_rmrep_ctx__2; first [GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rmrep_ctx_frame) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rmrep_ctx_frame)]. Qed.

#[using="Type"] Lemma rmrep_globals_frame : ltac2:(Q6nq.ty2 'GwI.segs '(@Q8QT.Mq4.rmrep_globals_frame) [[@gw_eq_rmrep_ctx__3; @gw_eq_rmrep_ctx__2; @gw_eq_rmrep_ctx]; [@gw_eq_rarea_rep__3; @gw_eq_rarea_rep__2; @gw_eq_rarea_rep]; [@gw_eq_rmrep_areas__3; @gw_eq_rmrep_areas__2; @gw_eq_rmrep_areas]; [@gw_eq_rgroup_rep__3; @gw_eq_rgroup_rep__2; @gw_eq_rgroup_rep]; [@gw_eq_rmrep_groups__3; @gw_eq_rmrep_groups__2; @gw_eq_rmrep_groups]; [@gw_eq_rshadow_rep__3; @gw_eq_rshadow_rep__2; @gw_eq_rshadow_rep]; [@gw_eq_rmrep_shadow__3; @gw_eq_rmrep_shadow__2; @gw_eq_rmrep_shadow]; [@gw_eq_rmrep_W__3; @gw_eq_rmrep_W__2; @gw_eq_rmrep_W]; [@gw_eq_rsize_classes_bytes__3; @gw_eq_rsize_classes_bytes__2; @gw_eq_rsize_classes_bytes]] '(@nil Z) '(Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@rmrep) (Q6nq.gwt_def (@Q8QT.Mq4.rregions_wf) (@rregions_wf) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_globals) (@rmrep_globals) Q6nq.gwt_nil)))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rmrep_globals_frame) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rmrep_globals_frame)]. Qed.

#[using="Type"] Lemma rarea_rep_frame : ltac2:(Q6nq.ty2 'GwI.segs '(@Q8QT.Mq4.rarea_rep_frame) [[@gw_eq_rarea_rep__2]; [@gw_eq_rmrep_ctx__3; @gw_eq_rmrep_ctx__2; @gw_eq_rmrep_ctx]; [@gw_eq_rmrep_areas__3; @gw_eq_rmrep_areas__2; @gw_eq_rmrep_areas]; [@gw_eq_rgroup_rep__3; @gw_eq_rgroup_rep__2; @gw_eq_rgroup_rep]; [@gw_eq_rmrep_groups__3; @gw_eq_rmrep_groups__2; @gw_eq_rmrep_groups]; [@gw_eq_rshadow_rep__3; @gw_eq_rshadow_rep__2; @gw_eq_rshadow_rep]; [@gw_eq_rmrep_shadow__3; @gw_eq_rmrep_shadow__2; @gw_eq_rmrep_shadow]; [@gw_eq_rmrep_W__3; @gw_eq_rmrep_W__2; @gw_eq_rmrep_W]; [@gw_eq_rsize_classes_bytes__3; @gw_eq_rsize_classes_bytes__2; @gw_eq_rsize_classes_bytes]] '([4096]%Z : list Z) '(Q6nq.gwt_unf (@PGSZ) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@rmrep) (Q6nq.gwt_def (@Q8QT.Mq4.rregions_wf) (@rregions_wf) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_globals) (@rmrep_globals) Q6nq.gwt_nil))))).
Proof. rewrite ?gw_eq_rarea_rep__2; first [GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rarea_rep_frame) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rarea_rep_frame)]. Qed.

#[using="Type"] Lemma rgroup_rep_frame : ltac2:(Q6nq.ty2 'GwI.segs '(@Q8QT.Mq4.rgroup_rep_frame) [[@gw_eq_rgroup_rep__2]; [@gw_eq_rmrep_ctx__3; @gw_eq_rmrep_ctx__2; @gw_eq_rmrep_ctx]; [@gw_eq_rarea_rep__3; @gw_eq_rarea_rep__2; @gw_eq_rarea_rep]; [@gw_eq_rmrep_areas__3; @gw_eq_rmrep_areas__2; @gw_eq_rmrep_areas]; [@gw_eq_rmrep_groups__3; @gw_eq_rmrep_groups__2; @gw_eq_rmrep_groups]; [@gw_eq_rshadow_rep__3; @gw_eq_rshadow_rep__2; @gw_eq_rshadow_rep]; [@gw_eq_rmrep_shadow__3; @gw_eq_rmrep_shadow__2; @gw_eq_rmrep_shadow]; [@gw_eq_rmrep_W__3; @gw_eq_rmrep_W__2; @gw_eq_rmrep_W]; [@gw_eq_rsize_classes_bytes__3; @gw_eq_rsize_classes_bytes__2; @gw_eq_rsize_classes_bytes]] '(@nil Z) '(Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@rmrep) (Q6nq.gwt_def (@Q8QT.Mq4.rregions_wf) (@rregions_wf) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_globals) (@rmrep_globals) Q6nq.gwt_nil)))).
Proof. rewrite ?gw_eq_rgroup_rep__2; first [GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rgroup_rep_frame) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rgroup_rep_frame)]. Qed.

#[using="Type"] Lemma rshadow_rep_frame : ltac2:(Q6nq.ty2 'GwI.segs '(@Q8QT.Mq4.rshadow_rep_frame) [[@gw_eq_rshadow_rep__2]; [@gw_eq_rmrep_ctx__3; @gw_eq_rmrep_ctx__2; @gw_eq_rmrep_ctx]; [@gw_eq_rarea_rep__3; @gw_eq_rarea_rep__2; @gw_eq_rarea_rep]; [@gw_eq_rmrep_areas__3; @gw_eq_rmrep_areas__2; @gw_eq_rmrep_areas]; [@gw_eq_rgroup_rep__3; @gw_eq_rgroup_rep__2; @gw_eq_rgroup_rep]; [@gw_eq_rmrep_groups__3; @gw_eq_rmrep_groups__2; @gw_eq_rmrep_groups]; [@gw_eq_rmrep_shadow__3; @gw_eq_rmrep_shadow__2; @gw_eq_rmrep_shadow]; [@gw_eq_rmrep_W__3; @gw_eq_rmrep_W__2; @gw_eq_rmrep_W]; [@gw_eq_rsize_classes_bytes__3; @gw_eq_rsize_classes_bytes__2; @gw_eq_rsize_classes_bytes]] '(@nil Z) '(Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@rmrep) (Q6nq.gwt_def (@Q8QT.Mq4.rregions_wf) (@rregions_wf) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_globals) (@rmrep_globals) Q6nq.gwt_nil)))).
Proof. rewrite ?gw_eq_rshadow_rep__2; first [GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rshadow_rep_frame) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rshadow_rep_frame)]. Qed.

#[using="Type"] Lemma rarea_conc : ltac2:(Q6nq.ty2 'GwI.segs '(@Q8QT.Mq4.rarea_conc) [[@gw_eq_rmrep_ctx__3; @gw_eq_rmrep_ctx__2; @gw_eq_rmrep_ctx]; [@gw_eq_rarea_rep__3; @gw_eq_rarea_rep__2; @gw_eq_rarea_rep]; [@gw_eq_rmrep_areas__3; @gw_eq_rmrep_areas__2; @gw_eq_rmrep_areas]; [@gw_eq_rgroup_rep__3; @gw_eq_rgroup_rep__2; @gw_eq_rgroup_rep]; [@gw_eq_rmrep_groups__3; @gw_eq_rmrep_groups__2; @gw_eq_rmrep_groups]; [@gw_eq_rshadow_rep__3; @gw_eq_rshadow_rep__2; @gw_eq_rshadow_rep]; [@gw_eq_rmrep_shadow__3; @gw_eq_rmrep_shadow__2; @gw_eq_rmrep_shadow]; [@gw_eq_rmrep_W__3; @gw_eq_rmrep_W__2; @gw_eq_rmrep_W]; [@gw_eq_rsize_classes_bytes__3; @gw_eq_rsize_classes_bytes__2; @gw_eq_rsize_classes_bytes]] '([4096]%Z : list Z) '(Q6nq.gwt_unf (@PGSZ) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@rmrep) (Q6nq.gwt_def (@Q8QT.Mq4.rregions_wf) (@rregions_wf) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_globals) (@rmrep_globals) Q6nq.gwt_nil))))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rarea_conc) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rarea_conc)]. Qed.

#[using="Type"] Lemma rgroup_conc : ltac2:(Q6nq.ty2 'GwI.segs '(@Q8QT.Mq4.rgroup_conc) [[@gw_eq_rmrep_ctx__3; @gw_eq_rmrep_ctx__2; @gw_eq_rmrep_ctx]; [@gw_eq_rarea_rep__3; @gw_eq_rarea_rep__2; @gw_eq_rarea_rep]; [@gw_eq_rmrep_areas__3; @gw_eq_rmrep_areas__2; @gw_eq_rmrep_areas]; [@gw_eq_rgroup_rep__3; @gw_eq_rgroup_rep__2; @gw_eq_rgroup_rep]; [@gw_eq_rmrep_groups__3; @gw_eq_rmrep_groups__2; @gw_eq_rmrep_groups]; [@gw_eq_rshadow_rep__3; @gw_eq_rshadow_rep__2; @gw_eq_rshadow_rep]; [@gw_eq_rmrep_shadow__3; @gw_eq_rmrep_shadow__2; @gw_eq_rmrep_shadow]; [@gw_eq_rmrep_W__3; @gw_eq_rmrep_W__2; @gw_eq_rmrep_W]; [@gw_eq_rsize_classes_bytes__3; @gw_eq_rsize_classes_bytes__2; @gw_eq_rsize_classes_bytes]] '(@nil Z) '(Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@rmrep) (Q6nq.gwt_def (@Q8QT.Mq4.rregions_wf) (@rregions_wf) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_globals) (@rmrep_globals) Q6nq.gwt_nil)))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rgroup_conc) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rgroup_conc)]. Qed.

#[using="Type"] Lemma rmrep_wr8 : ltac2:(Q6nq.ty2 'GwI.segs '(@Q8QT.Mq4.rmrep_wr8) [[@gw_eq_rmrep_ctx__3; @gw_eq_rmrep_ctx__2; @gw_eq_rmrep_ctx]; [@gw_eq_rarea_rep__3; @gw_eq_rarea_rep__2; @gw_eq_rarea_rep]; [@gw_eq_rmrep_areas__3; @gw_eq_rmrep_areas__2; @gw_eq_rmrep_areas]; [@gw_eq_rgroup_rep__3; @gw_eq_rgroup_rep__2; @gw_eq_rgroup_rep]; [@gw_eq_rmrep_groups__3; @gw_eq_rmrep_groups__2; @gw_eq_rmrep_groups]; [@gw_eq_rshadow_rep__3; @gw_eq_rshadow_rep__2; @gw_eq_rshadow_rep]; [@gw_eq_rmrep_shadow__3; @gw_eq_rmrep_shadow__2; @gw_eq_rmrep_shadow]; [@gw_eq_rmrep_W__3; @gw_eq_rmrep_W__2; @gw_eq_rmrep_W]; [@gw_eq_rsize_classes_bytes__3; @gw_eq_rsize_classes_bytes__2; @gw_eq_rsize_classes_bytes]] '([256]%Z : list Z) '(Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@rmrep) (Q6nq.gwt_def (@Q8QT.Mq4.rregions_wf) (@rregions_wf) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_globals) (@rmrep_globals) Q6nq.gwt_nil)))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rmrep_wr8) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rmrep_wr8)]. Qed.

#[using="Type"] Lemma rmrep_wr16 : ltac2:(Q6nq.ty2 'GwI.segs '(@Q8QT.Mq4.rmrep_wr16) [[@gw_eq_rmrep_ctx__3; @gw_eq_rmrep_ctx__2; @gw_eq_rmrep_ctx]; [@gw_eq_rarea_rep__3; @gw_eq_rarea_rep__2; @gw_eq_rarea_rep]; [@gw_eq_rmrep_areas__3; @gw_eq_rmrep_areas__2; @gw_eq_rmrep_areas]; [@gw_eq_rgroup_rep__3; @gw_eq_rgroup_rep__2; @gw_eq_rgroup_rep]; [@gw_eq_rmrep_groups__3; @gw_eq_rmrep_groups__2; @gw_eq_rmrep_groups]; [@gw_eq_rshadow_rep__3; @gw_eq_rshadow_rep__2; @gw_eq_rshadow_rep]; [@gw_eq_rmrep_shadow__3; @gw_eq_rmrep_shadow__2; @gw_eq_rmrep_shadow]; [@gw_eq_rmrep_W__3; @gw_eq_rmrep_W__2; @gw_eq_rmrep_W]; [@gw_eq_rsize_classes_bytes__3; @gw_eq_rsize_classes_bytes__2; @gw_eq_rsize_classes_bytes]] '([65536]%Z : list Z) '(Q6nq.gwt_unf (@RIMG_LO) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@rmrep) (Q6nq.gwt_def (@Q8QT.Mq4.rregions_wf) (@rregions_wf) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_globals) (@rmrep_globals) Q6nq.gwt_nil))))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rmrep_wr16) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rmrep_wr16)]. Qed.

#[using="Type"] Lemma rmrep_meta_store4 : ltac2:(Q6nq.ty2 'GwI.segs '(@Q8QT.Mq4.rmrep_meta_store4) [[@gw_eq_rmrep_ctx__3; @gw_eq_rmrep_ctx__2; @gw_eq_rmrep_ctx]; [@gw_eq_rarea_rep__3; @gw_eq_rarea_rep__2; @gw_eq_rarea_rep]; [@gw_eq_rmrep_areas__3; @gw_eq_rmrep_areas__2; @gw_eq_rmrep_areas]; [@gw_eq_rgroup_rep__3; @gw_eq_rgroup_rep__2; @gw_eq_rgroup_rep]; [@gw_eq_rmrep_groups__3; @gw_eq_rmrep_groups__2; @gw_eq_rmrep_groups]; [@gw_eq_rshadow_rep__3; @gw_eq_rshadow_rep__2; @gw_eq_rshadow_rep]; [@gw_eq_rmrep_shadow__3; @gw_eq_rmrep_shadow__2; @gw_eq_rmrep_shadow]; [@gw_eq_rmrep_W__3; @gw_eq_rmrep_W__2; @gw_eq_rmrep_W]; [@gw_eq_rsize_classes_bytes__3; @gw_eq_rsize_classes_bytes__2; @gw_eq_rsize_classes_bytes]] '(@nil Z) '(Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@rmrep) (Q6nq.gwt_def (@Q8QT.Mq4.rregions_wf) (@rregions_wf) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_globals) (@rmrep_globals) Q6nq.gwt_nil)))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rmrep_meta_store4) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rmrep_meta_store4)]. Qed.

#[using="Type"] Lemma rmrep_meta_set_avail : ltac2:(Q6nq.ty2 'GwI.segs '(@Q8QT.Mq4.rmrep_meta_set_avail) [[@gw_eq_rmrep_ctx__3; @gw_eq_rmrep_ctx__2; @gw_eq_rmrep_ctx]; [@gw_eq_rarea_rep__3; @gw_eq_rarea_rep__2; @gw_eq_rarea_rep]; [@gw_eq_rmrep_areas__3; @gw_eq_rmrep_areas__2; @gw_eq_rmrep_areas]; [@gw_eq_rgroup_rep__3; @gw_eq_rgroup_rep__2; @gw_eq_rgroup_rep]; [@gw_eq_rmrep_groups__3; @gw_eq_rmrep_groups__2; @gw_eq_rmrep_groups]; [@gw_eq_rshadow_rep__3; @gw_eq_rshadow_rep__2; @gw_eq_rshadow_rep]; [@gw_eq_rmrep_shadow__3; @gw_eq_rmrep_shadow__2; @gw_eq_rmrep_shadow]; [@gw_eq_rmrep_W__3; @gw_eq_rmrep_W__2; @gw_eq_rmrep_W]; [@gw_eq_rsize_classes_bytes__3; @gw_eq_rsize_classes_bytes__2; @gw_eq_rsize_classes_bytes]] '(@nil Z) '(Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@rmrep) (Q6nq.gwt_def (@Q8QT.Mq4.rregions_wf) (@rregions_wf) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_globals) (@rmrep_globals) Q6nq.gwt_nil)))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rmrep_meta_set_avail) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rmrep_meta_set_avail)]. Qed.

#[using="Type"] Lemma rmrep_meta_set_freed : ltac2:(Q6nq.ty2 'GwI.segs '(@Q8QT.Mq4.rmrep_meta_set_freed) [[@gw_eq_rmrep_ctx__3; @gw_eq_rmrep_ctx__2; @gw_eq_rmrep_ctx]; [@gw_eq_rarea_rep__3; @gw_eq_rarea_rep__2; @gw_eq_rarea_rep]; [@gw_eq_rmrep_areas__3; @gw_eq_rmrep_areas__2; @gw_eq_rmrep_areas]; [@gw_eq_rgroup_rep__3; @gw_eq_rgroup_rep__2; @gw_eq_rgroup_rep]; [@gw_eq_rmrep_groups__3; @gw_eq_rmrep_groups__2; @gw_eq_rmrep_groups]; [@gw_eq_rshadow_rep__3; @gw_eq_rshadow_rep__2; @gw_eq_rshadow_rep]; [@gw_eq_rmrep_shadow__3; @gw_eq_rmrep_shadow__2; @gw_eq_rmrep_shadow]; [@gw_eq_rmrep_W__3; @gw_eq_rmrep_W__2; @gw_eq_rmrep_W]; [@gw_eq_rsize_classes_bytes__3; @gw_eq_rsize_classes_bytes__2; @gw_eq_rsize_classes_bytes]] '(@nil Z) '(Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@rmrep) (Q6nq.gwt_def (@Q8QT.Mq4.rregions_wf) (@rregions_wf) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_globals) (@rmrep_globals) Q6nq.gwt_nil)))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rmrep_meta_set_freed) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rmrep_meta_set_freed)]. Qed.

#[using="Type"] Lemma rmrep_set_active : forall st m sc v,
rmrep st m -> 0 <= sc < 48 ->
rmrep (set_active sc v st) (write_to_mem m (wa (RCTX + 80 + 8 * sc)) (le8 (pw st v))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rmrep_set_active) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rmrep_set_active)]. Qed.

#[using="Type"] Lemma rshadow_rep_le : ltac2:(Q6nq.ty2 'GwI.segs '(@Q8QT.Mq4.rshadow_rep_le) [[@gw_eq_rshadow_rep__2]; [@gw_eq_rmrep_ctx__3; @gw_eq_rmrep_ctx__2; @gw_eq_rmrep_ctx]; [@gw_eq_rarea_rep__3; @gw_eq_rarea_rep__2; @gw_eq_rarea_rep]; [@gw_eq_rmrep_areas__3; @gw_eq_rmrep_areas__2; @gw_eq_rmrep_areas]; [@gw_eq_rgroup_rep__3; @gw_eq_rgroup_rep__2; @gw_eq_rgroup_rep]; [@gw_eq_rmrep_groups__3; @gw_eq_rmrep_groups__2; @gw_eq_rmrep_groups]; [@gw_eq_rmrep_shadow__3; @gw_eq_rmrep_shadow__2; @gw_eq_rmrep_shadow]; [@gw_eq_rmrep_W__3; @gw_eq_rmrep_W__2; @gw_eq_rmrep_W]; [@gw_eq_rsize_classes_bytes__3; @gw_eq_rsize_classes_bytes__2; @gw_eq_rsize_classes_bytes]] '(@nil Z) '(Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@rmrep) (Q6nq.gwt_def (@Q8QT.Mq4.rregions_wf) (@rregions_wf) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_globals) (@rmrep_globals) Q6nq.gwt_nil)))).
Proof. rewrite ?gw_eq_rshadow_rep__2; first [GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rshadow_rep_le) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rshadow_rep_le)]. Qed.

#[using="Type"] Lemma rmrep_upd_shadow : ltac2:(Q6nq.ty2 'GwI.segs '(@Q8QT.Mq4.rmrep_upd_shadow) [[@gw_eq_rmrep_ctx__3; @gw_eq_rmrep_ctx__2; @gw_eq_rmrep_ctx]; [@gw_eq_rarea_rep__3; @gw_eq_rarea_rep__2; @gw_eq_rarea_rep]; [@gw_eq_rmrep_areas__3; @gw_eq_rmrep_areas__2; @gw_eq_rmrep_areas]; [@gw_eq_rgroup_rep__3; @gw_eq_rgroup_rep__2; @gw_eq_rgroup_rep]; [@gw_eq_rmrep_groups__3; @gw_eq_rmrep_groups__2; @gw_eq_rmrep_groups]; [@gw_eq_rshadow_rep__3; @gw_eq_rshadow_rep__2; @gw_eq_rshadow_rep]; [@gw_eq_rmrep_shadow__3; @gw_eq_rmrep_shadow__2; @gw_eq_rmrep_shadow]; [@gw_eq_rmrep_W__3; @gw_eq_rmrep_W__2; @gw_eq_rmrep_W]; [@gw_eq_rsize_classes_bytes__3; @gw_eq_rsize_classes_bytes__2; @gw_eq_rsize_classes_bytes]] '(@nil Z) '(Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@rmrep) (Q6nq.gwt_def (@Q8QT.Mq4.rregions_wf) (@rregions_wf) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_globals) (@rmrep_globals) Q6nq.gwt_nil)))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rmrep_upd_shadow) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rmrep_upd_shadow)]. Qed.

#[using="Type"] Lemma rmrep_havoc : forall st m p n, rmrep st m -> ticks_ok st -> rmrep (havoc p n st) m /\ ticks_ok (havoc p n st).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rmrep_havoc) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rmrep_havoc)]. Qed.

#[using="Type"] Lemma rmrep_hdr_havoc : forall st m b, rmrep st m -> ticks_ok st -> rmrep (hdr_havoc b st) m /\ ticks_ok (hdr_havoc b st).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rmrep_hdr_havoc) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rmrep_hdr_havoc)]. Qed.

#[using="Type"] Lemma rmrep_transport_high : forall st m m' W,
rmrep st m -> munch W m m' -> wmono rsegs m m' -> W_high W -> rmrep st m'.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_W__3; @gw_eq_W__2; @gw_eq_W]]); first [GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rmrep_transport_high) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rmrep_transport_high)]. Qed.

#[using="Type"] Lemma rmrep_set_tick : forall st m t, rmrep st m -> rmrep (set_tick t st) m.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rmrep_set_tick) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rmrep_set_tick)]. Qed.

#[using="Type"] Lemma rwr_at_bytes_exist : ltac2:(Q6nq.ty2 'GwI.segs '(@Q8QT.Mq4.rwr_at_bytes_exist) [[@gw_eq_rmrep_ctx__3; @gw_eq_rmrep_ctx__2; @gw_eq_rmrep_ctx]; [@gw_eq_rarea_rep__3; @gw_eq_rarea_rep__2; @gw_eq_rarea_rep]; [@gw_eq_rmrep_areas__3; @gw_eq_rmrep_areas__2; @gw_eq_rmrep_areas]; [@gw_eq_rgroup_rep__3; @gw_eq_rgroup_rep__2; @gw_eq_rgroup_rep]; [@gw_eq_rmrep_groups__3; @gw_eq_rmrep_groups__2; @gw_eq_rmrep_groups]; [@gw_eq_rshadow_rep__3; @gw_eq_rshadow_rep__2; @gw_eq_rshadow_rep]; [@gw_eq_rmrep_shadow__3; @gw_eq_rmrep_shadow__2; @gw_eq_rmrep_shadow]; [@gw_eq_rmrep_W__3; @gw_eq_rmrep_W__2; @gw_eq_rmrep_W]; [@gw_eq_rsize_classes_bytes__3; @gw_eq_rsize_classes_bytes__2; @gw_eq_rsize_classes_bytes]] '([65536; 626688]%Z : list Z) '(Q6nq.gwt_unf (@RIMG_LO) (Q6nq.gwt_unf (@RIMG_HI) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@rmrep) (Q6nq.gwt_def (@Q8QT.Mq4.rregions_wf) (@rregions_wf) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_globals) (@rmrep_globals) (Q6nq.gwt_pat (@RIMG_HI) (@RIMG_HI) (Q6nq.gwt_hdr GwI.RIMG_HI (@RIMG_HI) Q6nq.gwt_nil)))))))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rwr_at_bytes_exist) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q8QT.Mq4.rwr_at_bytes_exist)]. Qed.

End RC__1.
Lemma gw_eq_rmrep_ctx__3 : @rmrep_ctx = ltac:(GwInst.gw_term (@Q8QT.Mq4.rmrep_ctx rsegs UKNz.RATP) (@rmrep_ctx)). Proof. unfold rmrep_ctx, Q8QT.Mq4.rmrep_ctx; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_rmrep_ctx__3 : gw_eqs.
Lemma gw_eq_rarea_rep__3 : @rarea_rep = ltac:(GwInst.gw_term (@Q8QT.Mq4.rarea_rep rsegs) (@rarea_rep)). Proof. unfold rarea_rep, Q8QT.Mq4.rarea_rep; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_rarea_rep__3 : gw_eqs.
Lemma gw_eq_rmrep_areas__3 : @rmrep_areas = ltac:(GwInst.gw_term (@Q8QT.Mq4.rmrep_areas rsegs) (@rmrep_areas)). Proof. unfold rmrep_areas, Q8QT.Mq4.rmrep_areas; rewrite ?gw_eq_rarea_rep__3; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_rmrep_areas__3 : gw_eqs.
Lemma gw_eq_rgroup_rep__3 : @rgroup_rep = ltac:(GwInst.gw_term (@Q8QT.Mq4.rgroup_rep rsegs) (@rgroup_rep)). Proof. unfold rgroup_rep, Q8QT.Mq4.rgroup_rep; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_rgroup_rep__3 : gw_eqs.
Lemma gw_eq_rmrep_groups__3 : @rmrep_groups = ltac:(GwInst.gw_term (@Q8QT.Mq4.rmrep_groups rsegs) (@rmrep_groups)). Proof. unfold rmrep_groups, Q8QT.Mq4.rmrep_groups; rewrite ?gw_eq_rgroup_rep__3; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_rmrep_groups__3 : gw_eqs.
Lemma gw_eq_rshadow_rep__3 : @rshadow_rep = ltac:(GwInst.gw_term (@Q8QT.Mq4.rshadow_rep rsegs) (@rshadow_rep)). Proof. unfold rshadow_rep, Q8QT.Mq4.rshadow_rep; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_rshadow_rep__3 : gw_eqs.
Lemma gw_eq_rmrep_shadow__3 : @rmrep_shadow = ltac:(GwInst.gw_term (@Q8QT.Mq4.rmrep_shadow rsegs) (@rmrep_shadow)). Proof. unfold rmrep_shadow, Q8QT.Mq4.rmrep_shadow; rewrite ?gw_eq_rshadow_rep__3; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_rmrep_shadow__3 : gw_eqs.
Lemma gw_eq_rmrep_W__2 : @rmrep_W = ltac:(GwInst.gw_term (@Q8QT.Mq4.rmrep_W UKNz.RATP) (@rmrep_W)). Proof. unfold rmrep_W, Q8QT.Mq4.rmrep_W; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_rmrep_W__2 : gw_eqs.
Lemma gw_eq_rsize_classes_bytes__2 : @rsize_classes_bytes = ltac:(GwInst.gw_term (@Q8QT.Mq4.rsize_classes_bytes) (@rsize_classes_bytes)). Proof. unfold rsize_classes_bytes, Q8QT.Mq4.rsize_classes_bytes; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_rsize_classes_bytes__2 : gw_eqs.
