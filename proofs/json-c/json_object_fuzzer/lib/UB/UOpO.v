(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwApply GwApply2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qe1A.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKNz.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qnxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnxq. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBpc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBpc. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QNAo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNAo.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QULt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QULt.Mq2.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UQXM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UQXM. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uv2Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uv2Y. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UIMz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UIMz. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UXT6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UXT6.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QTyG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
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
Lemma ROM_reservedZ : ltac2:(GwEq.gw_fact_ty 'segs '(@Qe1A.gw_all) @ROM_reservedZ). Proof. first [ apply QWxq.Mq0.ro_bytes_b_sound; vm_compute; reflexivity | GwApply.gw_side ]. Qed.
End GwI.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@Qe1A.rshadow_rep) (@UQXM.rshadow_rep) (Q6nq.gwt_def (@Q8QT.Mq4.rshadow_rep) (@UQXM.rshadow_rep) (Q6nq.gwt_def (@Qe1A.rrepfoot) (@UIMz.rrepfoot) (Q6nq.gwt_def (@QDXD.Mq2.rrepfoot) (@UIMz.rrepfoot) (Q6nq.gwt_def (@Qe1A.rregions_wf) (@UQXM.rregions_wf) (Q6nq.gwt_def (@Q8QT.Mq4.rregions_wf) (@UQXM.rregions_wf) (Q6nq.gwt_def (@Qe1A.rmrep_shadow) (@UQXM.rmrep_shadow) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_shadow) (@UQXM.rmrep_shadow) (Q6nq.gwt_def (@Qe1A.rmrep_groups) (@UQXM.rmrep_groups) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_groups) (@UQXM.rmrep_groups) (Q6nq.gwt_def (@Qe1A.rmrep_globals) (@UQXM.rmrep_globals) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_globals) (@UQXM.rmrep_globals) (Q6nq.gwt_def (@Qe1A.rmrep_ctx) (@UQXM.rmrep_ctx) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_ctx) (@UQXM.rmrep_ctx) (Q6nq.gwt_def (@Qe1A.rmrep_areas) (@UQXM.rmrep_areas) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_areas) (@UQXM.rmrep_areas) (Q6nq.gwt_def (@Qe1A.rmrep) (@UQXM.rmrep) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@UQXM.rmrep) (Q6nq.gwt_def (@Qe1A.rgroup_rep) (@UQXM.rgroup_rep) (Q6nq.gwt_def (@Q8QT.Mq4.rgroup_rep) (@UQXM.rgroup_rep) (Q6nq.gwt_def (@Qe1A.rclient_write_ok) (@UXT6.rclient_write_ok) (Q6nq.gwt_def (@QDXD.Mq3.rclient_write_ok) (@UXT6.rclient_write_ok) (Q6nq.gwt_def (@Qe1A.rblock_range) (@UXT6.rblock_range) (Q6nq.gwt_def (@QDXD.Mq3.rblock_range) (@UXT6.rblock_range) (Q6nq.gwt_def (@Qe1A.rarea_rep) (@UQXM.rarea_rep) (Q6nq.gwt_def (@Q8QT.Mq4.rarea_rep) (@UQXM.rarea_rep) (Q6nq.gwt_def (@Qe1A.RHEAP) (@UXT6.RHEAP) (Q6nq.gwt_def (@QDXD.Mq3.RHEAP) (@UXT6.RHEAP) Q6nq.gwt_nil)))))))))))))))))))))))))))).
#[using="Type"] Lemma rregion_addr_facts : ltac2:(Q6nq.ty2 'GwI.segs '(@Qe1A.rregion_addr_facts) [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]] '([4096; 65536; 626688]%Z : list Z) '(Q6nq.gwt_unf (@RIMG_LO) (Q6nq.gwt_unf (@RIMG_HI) (Q6nq.gwt_unf (@PGSZ) gwt_X)))).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.rregion_addr_facts) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.rregion_addr_facts)]. Qed.

#[using="Type"] Lemma rblock_inside : ltac2:(Q6nq.ty2 'GwI.segs '(@Qe1A.rblock_inside) [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]] '([4096; 65536; 626688]%Z : list Z) '(Q6nq.gwt_unf (@RIMG_LO) (Q6nq.gwt_unf (@RIMG_HI) (Q6nq.gwt_unf (@PGSZ) (Q6nq.gwt_pat (@ref_reserved) (@ref_reserved) (Q6nq.gwt_hdr GwI.ref_reserved (@ref_reserved) (Q6nq.gwt_pat (@RIMG_HI) (@RIMG_HI) (Q6nq.gwt_hdr GwI.RIMG_HI (@RIMG_HI) gwt_X)))))))).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.rblock_inside) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.rblock_inside)]. Qed.

#[using="Type"] Lemma RHEAP_blocks_nodup_proof : forall s LB m, RHEAP s LB m -> List.NoDup (map blk_id LB).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_RHEAP__3; @gw_eq_RHEAP__2; @gw_eq_RHEAP]]); first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.RHEAP_blocks_nodup_proof) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.RHEAP_blocks_nodup_proof)]. Qed.

#[using="Type"] Lemma RHEAP_block_range_proof : forall s LB m b, RHEAP s LB m -> In b LB -> rblock_range (blk_addr b) (blk_size b).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_RHEAP__3; @gw_eq_RHEAP__2; @gw_eq_RHEAP]; [@gw_eq_rblock_range__3; @gw_eq_rblock_range__2; @gw_eq_rblock_range]]); first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.RHEAP_block_range_proof) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.RHEAP_block_range_proof)]. Qed.

#[using="Type"] Lemma RHEAP_blocks_disjoint_proof : ltac2:(Q6nq.ty2 'GwI.segs '(@Qe1A.RHEAP_blocks_disjoint_proof) [[@gw_eq_RHEAP__3; @gw_eq_RHEAP__2; @gw_eq_RHEAP]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_RHEAP__3; @gw_eq_RHEAP__2; @gw_eq_RHEAP]]); first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.RHEAP_blocks_disjoint_proof) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.RHEAP_blocks_disjoint_proof)]. Qed.

#[using="Type"] Lemma rrepfoot_where st m a : rmrep st m -> rrepfoot st a ->
a < alloc_ceiling /\ (RCTX <= a < RCTX + 928 \/ RMLOCK <= a < RMLOCK + 4 \/ RLIBC <= a < RLIBC + 0x38
\/ RGOT_SSP <= a < RGOT_SSP + 8 \/ RSSP_GUARD <= a < RSSP_GUARD + 8 \/ a < 0x10000 \/ 0x99000 <= a).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_rrepfoot__3; @gw_eq_rrepfoot__2; @gw_eq_rrepfoot]]); first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.rrepfoot_where) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.rrepfoot_where)]. Qed.

#[using="Type"] Lemma RHEAP_frame_proof : ltac2:(Q6nq.ty2 'GwI.segs '(@Qe1A.RHEAP_frame_proof) [[@gw_eq_RHEAP__3; @gw_eq_RHEAP__2; @gw_eq_RHEAP]; [@gw_eq_W__3; @gw_eq_W__2; @gw_eq_W]; [@gw_eq_rclient_write_ok__3; @gw_eq_rclient_write_ok__2; @gw_eq_rclient_write_ok]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_RHEAP__3; @gw_eq_RHEAP__2; @gw_eq_RHEAP]; [@gw_eq_W__3; @gw_eq_W__2; @gw_eq_W]; [@gw_eq_rclient_write_ok__3; @gw_eq_rclient_write_ok__2; @gw_eq_rclient_write_ok]]); first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.RHEAP_frame_proof) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.RHEAP_frame_proof)]. Qed.

#[using="Type"] Lemma reservedZ_ref : reservedZ rsegs = ref_reserved.
Proof. vm_compute. reflexivity. Qed.

#[using="Type"] Lemma u64arr_of_rw_cells' : ltac2:(Q6nq.ty2 'GwI.segs '(@Qe1A.u64arr_of_rw_cells') [] '(@nil Z) 'gwt_X).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.u64arr_of_rw_cells') | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.u64arr_of_rw_cells')]. Qed.
End RC__1.

Ltac rimg_chunk NONE m A cs H :=
let bs := eval vm_compute in (cells_bytes cs) in
assert (H : rw_cells rsegs m A cs);
[ apply (rw_cells_recast rsegs m A [CB (length bs) bs] cs);
[ apply (rw_cells_image0 rsegs m A bs);
[ intros a Ha; apply NONE; cbn [length] in Ha; lia | vm_compute; reflexivity | lia | cbn [length]; lia ]
| cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
| ].
Section RC__2. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma RHEAP_init_proof : forall (m : mem) (auxv : word),
(forall a : word, 0x97f78 <= bv_unsigned a < 0x98320 -> m a = None) ->
rw_cells rsegs m 0x97e90 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 (Z_to_bv 64 0)] ->
rw_cells rsegs m 0x97e98 [C8 auxv; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 224); C8 (Z_to_bv 64 8); C8 (Z_to_bv 64 0);
C8 (Z_to_bv 64 4096); CB 48 (repeat (Z_to_bv 8 0) 48)] ->
rw_cells rsegs m 0x659d0 [C8 (Z_to_bv 64 0x97e70)] ->
rw_cells rsegs m 0x97e70 [C8 rc_canary] ->
mem_inv rsegs m ->
RHEAP (ps_init_s rc_secret (reservedZ rsegs)) [] m
/\ rw_cells rsegs m RAUXV_CELL [C8 auxv].
Proof.
intros m auxv NONE LC LC2 GOT GUARD MI.
set (st0 := minit rc_secret ref_reserved).
rimg_chunk NONE m 0x97f80%Z (ctx_head_cells st0) CXH.
rimg_chunk NONE m (0x97f80 + 80)%Z [CB 384 (u64s (repeat (wz 0) 48))] CXA.
rimg_chunk NONE m (0x97f80 + 464)%Z [CB 384 (u64s (repeat (wz 0) 48))] CXU.
rimg_chunk NONE m (0x97f80 + 848)%Z [CB 32 (zeros 32)] CXS.
rimg_chunk NONE m (0x97f80 + 880)%Z [CB 32 (zeros 32)] CXB.
rimg_chunk NONE m (0x97f80 + 912)%Z (ctx_tail_cells st0) CXT.
rimg_chunk NONE m 0x97f78%Z [C4 (wz 0)] ML.

pose proof (proj1 (rw_cells_app rsegs m 0x97e90 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] _) LC) as [_ LC3]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in LC3.
pose proof (proj1 (rw_cells_app rsegs m (0x97e90 + 3) [C1 (Z_to_bv 8 0)] _) LC3) as [NL _].
pose proof (proj1 (rw_cells_app rsegs m 0x97e98 [C8 auxv] _) LC2) as [AUXC LC16]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in LC16.
pose proof (proj1 (rw_cells_app rsegs m (0x97e98 + 8) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 224); C8 (Z_to_bv 64 8); C8 (Z_to_bv 64 0)] _) LC16) as [_ LC48].
cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in LC48.
pose proof (proj1 (rw_cells_app rsegs m _ [C8 (Z_to_bv 64 4096)] _) LC48) as [PS _].
split.
2:{ unfold RAUXV_CELL. exact AUXC. }
exists st0, []. split; [apply Permutation_refl|]. split; [unfold ps_init_s; cbn [ps_m]; rewrite reservedZ_ref; reflexivity|].
split.
2:{ unfold ps_init_s; cbn [ps_brk]. apply HINV_from_init. exact rc_secret_range. }
split; [|split; [|split; [|split; [|split]]]].
-  split; [reflexivity|]. split; [intros rid r H; rewrite lookup_empty in H; discriminate|].
split; [intros ? ? ? ? H; rewrite lookup_empty in H; discriminate|].
split; [intros ? ? H; cbn in H; rewrite lookup_empty in H; discriminate|].
intros ? ? H; cbn in H; rewrite lookup_empty in H; discriminate.
- unfold rmrep_ctx, RCTX. split; [exact CXH|]. split; [|split; [|split; [|split]]].
+ replace (actives st0) with (repeat (wz 0) 48) by reflexivity. eapply u64arr_of_rw_cells'; [exact CXA| reflexivity| reflexivity].
+ replace (usages st0) with (repeat (wz 0) 48) by reflexivity. eapply u64arr_of_rw_cells'; [exact CXU| reflexivity| reflexivity].
+ replace (unmap_seqs st0) with (zeros 32) by reflexivity. apply (u8arr_of_rw_cells rsegs m _ 32). exact CXS.
+ replace (bouncess st0) with (zeros 32) by reflexivity. apply (u8arr_of_rw_cells rsegs m _ 32). exact CXB.
+ exact CXT.
- unfold rmrep_globals, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD. split; [exact ML|]. split; [|split; [|split]].
+ match goal with |- rw_cells _ _ ?G _ => match type of NL with rw_cells _ _ ?A _ => replace G with A by reflexivity end end.
change (b8 0) with (Z_to_bv 8 0). exact NL.
+ match goal with |- rw_cells _ _ ?G _ => match type of PS with rw_cells _ _ ?A _ => replace G with A by reflexivity end end.
change (wz 4096) with (Z_to_bv 64 4096). exact PS.
+ change (wz 622192) with (Z_to_bv 64 0x97e70). exact GOT.
+ exact GUARD.
- intros a ar H. cbn in H. rewrite lookup_empty in H. discriminate.
- intros b gh H. cbn in H. rewrite lookup_empty in H. discriminate.
- intros rid r H. cbn in H. rewrite lookup_empty in H. discriminate.
Qed.

End RC__2.
