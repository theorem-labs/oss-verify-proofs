(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwApply GwApply2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QkTt.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QlEo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QytA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QytA. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qnxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnxq. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.Mq4.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QLsg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Export QLsg.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UQXM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UQXM. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uv2Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uv2Y. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UiOj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UiOj. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U8FW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U8FW.
Import ListNotations. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

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
Lemma LAY_win_0 : ltac2:(GwEq.gw_fact_ty 'segs '(@QkTt.Mq5.gw_all) @LAY_win_0). Proof. GwApply.gw_side. Qed.
Lemma LAY_win_1 : ltac2:(GwEq.gw_fact_ty 'segs '(@QkTt.Mq5.gw_all) @LAY_win_1). Proof. GwApply.gw_side. Qed.
Lemma LAY_win_2 : ltac2:(GwEq.gw_fact_ty 'segs '(@QkTt.Mq5.gw_all) @LAY_win_2). Proof. GwApply.gw_side. Qed.
Lemma LAY_win_3 : ltac2:(GwEq.gw_fact_ty 'segs '(@QkTt.Mq5.gw_all) @LAY_win_3). Proof. GwApply.gw_side. Qed.
Lemma ROM_reservedZ : ltac2:(GwEq.gw_fact_ty 'segs '(@QkTt.Mq5.gw_all) @ROM_reservedZ). Proof. first [ apply QWxq.Mq0.ro_bytes_b_sound; vm_compute; reflexivity | GwApply.gw_side ]. Qed.
Lemma LAY_ref_reserved : ltac2:(GwEq.gw_fact_ty 'segs '(@QkTt.Mq5.gw_all) @LAY_ref_reserved). Proof. GwApply.gw_side. Qed.
End GwI.

Notation RMFACTS := (@MFACTS_g ref_reserved).
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@QkTt.Mq5.rshadow_rep) (@UQXM.rshadow_rep) (Q6nq.gwt_def (@Q8QT.Mq4.rshadow_rep) (@UQXM.rshadow_rep) (Q6nq.gwt_def (@QkTt.Mq5.rregions_wf) (@UQXM.rregions_wf) (Q6nq.gwt_def (@Q8QT.Mq4.rregions_wf) (@UQXM.rregions_wf) (Q6nq.gwt_def (@QkTt.Mq5.rpres_except) (@Uv2Y.rpres_except) (Q6nq.gwt_def (@QCa8.Mq5.rpres_except) (@Uv2Y.rpres_except) (Q6nq.gwt_def (@QkTt.Mq5.rmrep_shadow) (@UQXM.rmrep_shadow) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_shadow) (@UQXM.rmrep_shadow) (Q6nq.gwt_def (@QkTt.Mq5.rmrep_groups) (@UQXM.rmrep_groups) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_groups) (@UQXM.rmrep_groups) (Q6nq.gwt_def (@QkTt.Mq5.rmrep_globals) (@UQXM.rmrep_globals) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_globals) (@UQXM.rmrep_globals) (Q6nq.gwt_def (@QkTt.Mq5.rmrep_ctx) (@UQXM.rmrep_ctx) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_ctx) (@UQXM.rmrep_ctx) (Q6nq.gwt_def (@QkTt.Mq5.rmrep_areas) (@UQXM.rmrep_areas) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_areas) (@UQXM.rmrep_areas) (Q6nq.gwt_def (@QkTt.Mq5.rmrep) (@UQXM.rmrep) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@UQXM.rmrep) (Q6nq.gwt_def (@QkTt.Mq5.rgroup_rep) (@UQXM.rgroup_rep) (Q6nq.gwt_def (@Q8QT.Mq4.rgroup_rep) (@UQXM.rgroup_rep) (Q6nq.gwt_def (@QCa8.Mq3.renframe_tail_mem) (@UiOj.renframe_tail_mem) (Q6nq.gwt_def (@QCa8.Mq3.renframe_off_mem) (@UiOj.renframe_off_mem) (Q6nq.gwt_def (@QkTt.Mq5.rarea_rep) (@UQXM.rarea_rep) (Q6nq.gwt_def (@Q8QT.Mq4.rarea_rep) (@UQXM.rarea_rep) (Q6nq.gwt_def (@QkTt.Mq5.ralloc_fp) (@Uv2Y.ralloc_fp) (Q6nq.gwt_def (@QCa8.Mq5.ralloc_fp) (@Uv2Y.ralloc_fp) Q6nq.gwt_nil)))))))))))))))))))))))))).
#[using="Type"] Lemma rreserved_disjoint2 : ltac2:(Q6nq.ty2 'UDxd.GwI.segs '(@QkTt.Mq5.rreserved_disjoint2) [] '([65536; 401408; 626688]%Z : list Z) '(Q6nq.gwt_unf (@RIMG_LO) (Q6nq.gwt_unf (@RIMG_HI) (Q6nq.gwt_unf (@RDATA_LO) (Q6nq.gwt_pat (@ref_reserved) (@ref_reserved) (Q6nq.gwt_hdr GwI.ref_reserved (@ref_reserved) gwt_X)))))).
Proof. first [GwApply2.gw_by_name2 UDxd.GwI.segs (@QkTt.Mq5.rreserved_disjoint2) | autorewrite with gw_eqs; GwApply2.gw_by_name2 UDxd.GwI.segs (@QkTt.Mq5.rreserved_disjoint2)]. Qed.

#[using="Type"] Lemma wr8_comm p q v w st : fst p = fst q -> snd p <> snd q -> wr8 p v (wr8 q w st) = wr8 q w (wr8 p v st).
Proof. first [GwApply2.gw_by_name2 UDxd.GwI.segs (@QkTt.Mq5.wr8_comm) | autorewrite with gw_eqs; GwApply2.gw_by_name2 UDxd.GwI.segs (@QkTt.Mq5.wr8_comm)]. Qed.

Section ENFRAME.
Variables (st2 : mstate) (m4 : mem) (g b : aptr) (r : region) (k n off : Z).
Let mr := get_meta_rec st2 g.
Let stride := get_stride mr.
Let B := conc st2 b.
Let P0 := B + 16 + stride * k.

Hypothesis MR : rmrep st2 m4.
Hypothesis TK : ticks_ok st2.
Hypothesis Hmem : m_mem mr = Some b.
Hypothesis Hr : (s_regions st2) !! (fst b) = Some r.
Hypothesis Hk : r_kind r = RKGroup.
Hypothesis B0 : 0 <= snd b.
Hypothesis K0 : 0 <= k < 32.
Hypothesis SPAN : snd b + 16 + stride * (k + 1) <= round_up_pg (r_len r).
Hypothesis S16 : 16 <= stride.
Hypothesis S31 : stride - 4 - n < 2^31.
Hypothesis NOGRP : forall b' gh, (s_groups st2) !! b' = Some gh -> fst b' = fst b ->
snd b' + 9 <= snd b + 16 + stride * k - 4 \/ snd b + 16 + stride * k + stride - 4 <= snd b'.
Hypothesis OFF0 : 0 <= off.
Hypothesis N0 : 0 <= n.
Hypothesis FIT : 16 * off + n + 4 <= stride.
Hypothesis Q16 : (stride * k + 16 * off) / 16 < 65536.

#[using="Hr"] Lemma rconc_b : B = r_base r + snd b.
Proof. first [GwApply2.gw_by_name2 UDxd.GwI.segs (@QkTt.Mq5.rconc_b) | autorewrite with gw_eqs; GwApply2.gw_by_name2 UDxd.GwI.segs (@QkTt.Mq5.rconc_b)]. Qed.

#[using="b off B P0 K0 S16"] Lemma rsk_nonneg : 0 <= stride * k.
Proof. first [GwApply2.gw_by_name2 UDxd.GwI.segs (@QkTt.Mq5.rsk_nonneg) | autorewrite with gw_eqs; GwApply2.gw_by_name2 UDxd.GwI.segs (@QkTt.Mq5.rsk_nonneg)]. Qed.

#[using="off B P0 Hr Hk B0 K0 SPAN S16 NOGRP"] Lemma rwr8_rep : ltac2:(Q6nq.ty2 'UDxd.GwI.segs '(@QkTt.Mq5.rwr8_rep) [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]] '([256]%Z : list Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 UDxd.GwI.segs (@QkTt.Mq5.rwr8_rep) | autorewrite with gw_eqs; GwApply2.gw_by_name2 UDxd.GwI.segs (@QkTt.Mq5.rwr8_rep)]. Qed.

#[using="off B P0 Hr Hk B0 K0 SPAN S16 NOGRP"] Lemma rwr16_rep : ltac2:(Q6nq.ty2 'UDxd.GwI.segs '(@QkTt.Mq5.rwr16_rep) [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]] '([65536]%Z : list Z) '(Q6nq.gwt_unf (@RIMG_LO) gwt_X)).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 UDxd.GwI.segs (@QkTt.Mq5.rwr16_rep) | autorewrite with gw_eqs; GwApply2.gw_by_name2 UDxd.GwI.segs (@QkTt.Mq5.rwr16_rep)]. Qed.

#[using="off B P0 Hr Hk B0 K0 SPAN S16 NOGRP"] Lemma rwr32_rep : ltac2:(Q6nq.ty2 'UDxd.GwI.segs '(@QkTt.Mq5.rwr32_rep) [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 UDxd.GwI.segs (@QkTt.Mq5.rwr32_rep) | autorewrite with gw_eqs; GwApply2.gw_by_name2 UDxd.GwI.segs (@QkTt.Mq5.rwr32_rep)]. Qed.

#[using="st2 g b k off mr stride B P0 K0"] Lemma wr16_wr8_comm : ltac2:(Q6nq.ty2 'UDxd.GwI.segs '(@QkTt.Mq5.wr16_wr8_comm) [] '(@nil Z) 'gwt_X).
Proof. first [GwApply2.gw_by_name2 UDxd.GwI.segs (@QkTt.Mq5.wr16_wr8_comm) | autorewrite with gw_eqs; GwApply2.gw_by_name2 UDxd.GwI.segs (@QkTt.Mq5.wr16_wr8_comm)]. Qed.

#[using="st2 g b k off mr stride B P0 K0"] Lemma wr32_wr8_comm p q v w st : fst p = fst q -> snd q + 1 = snd p ->
wr8 q w (wr32 p v st) = wr32 p v (wr8 q w st).
Proof. first [GwApply2.gw_by_name2 UDxd.GwI.segs (@QkTt.Mq5.wr32_wr8_comm) | autorewrite with gw_eqs; GwApply2.gw_by_name2 UDxd.GwI.segs (@QkTt.Mq5.wr32_wr8_comm)]. Qed.

#[using="r MR TK Hmem Hr Hk B0 K0 SPAN S16 S31 NOGRP OFF0 N0 FIT Q16"] Lemma renframe_mrep : ltac2:(Q6nq.ty2 'UDxd.GwI.segs '(@QkTt.Mq5.renframe_mrep) [[@gw_eq_renframe_off_mem__3; @gw_eq_renframe_off_mem__2; @gw_eq_renframe_off_mem]; [@gw_eq_renframe_tail_mem__3; @gw_eq_renframe_tail_mem__2; @gw_eq_renframe_tail_mem]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_renframe_off_mem__3; @gw_eq_renframe_off_mem__2; @gw_eq_renframe_off_mem]; [@gw_eq_renframe_tail_mem__3; @gw_eq_renframe_tail_mem__2; @gw_eq_renframe_tail_mem]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 UDxd.GwI.segs (@QkTt.Mq5.renframe_mrep) | autorewrite with gw_eqs; GwApply2.gw_by_name2 UDxd.GwI.segs (@QkTt.Mq5.renframe_mrep)]. Qed.
End ENFRAME.

#[using="Type"] Lemma rpres_enframe : ltac2:(Q6nq.ty2 'UDxd.GwI.segs '(@QkTt.Mq5.rpres_enframe) [[@gw_eq_renframe_off_mem__3; @gw_eq_renframe_off_mem__2; @gw_eq_renframe_off_mem]; [@gw_eq_renframe_tail_mem__3; @gw_eq_renframe_tail_mem__2; @gw_eq_renframe_tail_mem]; [@gw_eq_rpres_except__3; @gw_eq_rpres_except__2; @gw_eq_rpres_except]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_renframe_off_mem__3; @gw_eq_renframe_off_mem__2; @gw_eq_renframe_off_mem]; [@gw_eq_renframe_tail_mem__3; @gw_eq_renframe_tail_mem__2; @gw_eq_renframe_tail_mem]; [@gw_eq_rpres_except__3; @gw_eq_rpres_except__2; @gw_eq_rpres_except]]); first [GwApply2.gw_by_name2 UDxd.GwI.segs (@QkTt.Mq5.rpres_enframe) | autorewrite with gw_eqs; GwApply2.gw_by_name2 UDxd.GwI.segs (@QkTt.Mq5.rpres_enframe)]. Qed.

#[using="Type"] Lemma rrdv_agree : ltac2:(Q6nq.ty2 'UDxd.GwI.segs '(@QkTt.Mq5.rrdv_agree) [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 UDxd.GwI.segs (@QkTt.Mq5.rrdv_agree) | autorewrite with gw_eqs; GwApply2.gw_by_name2 UDxd.GwI.segs (@QkTt.Mq5.rrdv_agree)]. Qed.

#[using="Type"] Lemma rmeta_chunk_facts : forall st m g,
rmrep st m -> meta_slot st g ->
let G := conc st g in
rw_cells rsegs m G (meta_cells st (get_meta_rec st g))
/\ 0 < G /\ G + 40 <= alloc_ceiling
/\ (G + 40 <= 0x10000 \/ 0x62000 <= G) /\ (G + 40 <= 0x62000 \/ 0x99000 <= G)
/\ (forall rid' r', (s_regions st) !! rid' = Some r' -> r_kind r' = RKGroup ->
G + 40 <= r_base r' \/ r_base r' + round_up_pg (r_len r') <= G)
/\ (exists rid0 r0, (s_regions st) !! rid0 = Some r0 /\ r_kind r0 <> RKGroup
/\ lr_lo r0 <= G /\ G + 40 <= r_base r0 + round_up_pg (r_len r0)).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 UDxd.GwI.segs (@QkTt.Mq5.rmeta_chunk_facts) | autorewrite with gw_eqs; GwApply2.gw_by_name2 UDxd.GwI.segs (@QkTt.Mq5.rmeta_chunk_facts)]. Qed.

#[using="Type"] Lemma rregion_facts : ltac2:(Q6nq.ty2 'UDxd.GwI.segs '(@QkTt.Mq5.rregion_facts) [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]] '([4096; 65536; 401408; 626688]%Z : list Z) '(Q6nq.gwt_unf (@RIMG_LO) (Q6nq.gwt_unf (@RIMG_HI) (Q6nq.gwt_unf (@RDATA_LO) (Q6nq.gwt_unf (@PGSZ) (Q6nq.gwt_pat (@RIMG_HI) (@RIMG_HI) (Q6nq.gwt_hdr GwI.RIMG_HI (@RIMG_HI) (Q6nq.gwt_pat (@RDATA_LO) (@RDATA_LO) (Q6nq.gwt_hdr GwI.RDATA_LO (@RDATA_LO) gwt_X))))))))).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 UDxd.GwI.segs (@QkTt.Mq5.rregion_facts) | autorewrite with gw_eqs; GwApply2.gw_by_name2 UDxd.GwI.segs (@QkTt.Mq5.rregion_facts)]. Qed.

Section SLOT.
Variables (st : mstate) (m1 o : mem) (g b : aptr) (r : region) (idx n : Z).
Let mr := get_meta_rec st g.
Let stride := get_stride mr.
Let B := conc st b.
Let P0 := B + 16 + stride * idx.

Hypothesis MR : rmrep st m1.
Hypothesis UA : unk_agree st o m1.
Hypothesis Hmem : m_mem mr = Some b.
Hypothesis Hr : (s_regions st) !! (fst b) = Some r.
Hypothesis Hk : r_kind r = RKGroup.
Hypothesis B0 : 0 <= snd b.
Hypothesis IDX : 0 <= idx.
Hypothesis SPAN : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r).
Hypothesis S16 : 16 <= stride.
Hypothesis B16 : snd b mod 16 = 0.
Hypothesis SMOD : stride mod 16 = 0.
Hypothesis NOGRP : forall b' gh, (s_groups st) !! b' = Some gh -> fst b' = fst b ->
snd b' + 9 <= snd b + 16 + stride * idx - 4 \/ snd b + 16 + stride * idx + stride - 4 <= snd b'.
Hypothesis HDR0 : cell_read (get_shadow st (fst b)) (snd b + 16 + stride * idx - 4) = Known 0.

#[using="MR UA Hr Hk B0 IDX SPAN S16 B16 SMOD HDR0"] Lemma rslot_facts : ltac2:(Q6nq.ty2 'UDxd.GwI.segs '(@QkTt.Mq5.rslot_facts) [] '([4096; 65536; 401408]%Z : list Z) '(Q6nq.gwt_unf (@RIMG_LO) (Q6nq.gwt_unf (@RDATA_LO) (Q6nq.gwt_unf (@PGSZ) (Q6nq.gwt_pat (@RDATA_LO) (@RDATA_LO) (Q6nq.gwt_hdr GwI.RDATA_LO (@RDATA_LO) gwt_X)))))).
Proof. first [GwApply2.gw_by_name2 UDxd.GwI.segs (@QkTt.Mq5.rslot_facts) | autorewrite with gw_eqs; GwApply2.gw_by_name2 UDxd.GwI.segs (@QkTt.Mq5.rslot_facts)]. Qed.
End SLOT.

Definition rmalloc_fp (st st' : mstate) (lo sp : Z) (a : Z) : Prop :=
ralloc_fp (fun k => k <> RKGroup) st' lo sp a \/ new_reg_addr st st' a \/ free_slot_addr st a \/ grp_hdr_addr st a
\/ fresh_addr st a.

#[using="Type"] Lemma rmalloc_fp_mono : ltac2:(Q6nq.ty2 'UDxd.GwI.segs '(@QkTt.Mq5.rmalloc_fp_mono) [] '(@nil Z) '(Q6nq.gwt_def (@QkTt.Mq5.rmalloc_fp) (@rmalloc_fp) gwt_X)).
Proof. first [GwApply2.gw_by_name2 UDxd.GwI.segs (@QkTt.Mq5.rmalloc_fp_mono) | autorewrite with gw_eqs; GwApply2.gw_by_name2 UDxd.GwI.segs (@QkTt.Mq5.rmalloc_fp_mono)]. Qed.

Section FASTFACTS.
Variables (st : mstate) (LB : list block) (sc n : Z) (g : aptr) (k : Z) (t : N).
Let st1 := set_tick t st.
Let mr := get_meta_rec st g.
Let st2 := upd_meta g (m_set_avail (m_avail mr - 2 ^ k)) st1.
Hypothesis MF : RMFACTS st LB.
Hypothesis ACT : active st sc = Some g.
Hypothesis AV : 0 < m_avail mr.
Hypothesis K0 : 0 <= k.
Hypothesis LBK : lowbit (m_avail mr) = 2 ^ k.
Hypothesis N0 : 0 <= n.
Hypothesis NFIT : n + 4 <= 16 * size_class sc.

#[using="Type"] Lemma rget_meta_rec_st2 : get_meta_rec st2 g = m_set_avail (m_avail mr - 2 ^ k) mr.
Proof. first [GwApply2.gw_by_name2 UDxd.GwI.segs (@QkTt.Mq5.rget_meta_rec_st2) | autorewrite with gw_eqs; GwApply2.gw_by_name2 UDxd.GwI.segs (@QkTt.Mq5.rget_meta_rec_st2)]. Qed.

#[using="LB sc MF ACT AV K0 LBK N0 NFIT"] Lemma rfast_slot_ok : ltac2:(Q6nq.ty2 'UDxd.GwI.segs '(@QkTt.Mq5.rfast_slot_ok) [] '(@nil Z) '(Q6nq.gwt_def (@QkTt.Mq5.rmalloc_fp) (@rmalloc_fp) gwt_X)).
Proof. first [GwApply2.gw_by_name2 UDxd.GwI.segs (@QkTt.Mq5.rfast_slot_ok) | autorewrite with gw_eqs; GwApply2.gw_by_name2 UDxd.GwI.segs (@QkTt.Mq5.rfast_slot_ok)]. Qed.
End FASTFACTS.

End RC__1.
