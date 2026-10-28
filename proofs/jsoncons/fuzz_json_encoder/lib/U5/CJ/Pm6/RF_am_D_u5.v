(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.Agent Require Import F_malloc_free_u5 MallocTree_u5 MallocModel_B_u5 F_ntf_A_u5 F_ntf_B_u5 F_ntf_C_u5 MallocKit_B_u5 MallocKit_B3_u5 F_am_A_u5 F_am_D_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.Pm6 Require Import RMallocRep_u5 RMallocTree_u5 RMallocKit_B_u5 RMallocKit_B3_u5 RF_ntf_A_u5 RF_ntf_C_u5 RF_am_A_u5.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac ctx_cells_cbn :=
  cbn [ctx set_head upd_ctx s_ctx set_free_meta_head set_avail_meta set_avail_meta_count c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
       c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ram_deq : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
    (m : word -> option byte) (junk : list byte) (lo : Z) (st : mstate) (h nx pv : aptr),
  rmrep st m -> mem_inv rsegs m ->
  c_free_meta_head (ctx st) = Some h -> meta_slot st h ->
  m_next (get_meta_rec st h) = Some nx -> m_prev (get_meta_rec st h) = Some pv ->
  meta_slot st nx -> meta_slot st pv -> (nx = h <-> pv = h) ->
  rw_cells rsegs m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
  stk rsegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
  evt rsegs (ram_ret_post raw sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc lo st m (dequeue LFree h st) (Z_to_bv 64 (conc st h)))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb0344) fc None m (seg_rom rsegs)).
Proof.
  intros until pv. intros MR MI FMH MSh HN HP MSn MSp SELF FR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (rmeta_slot_bounds st m h MR MSh) as (HB0 & HB1 & HB2 & _). pose_ceil.
  pose proof (rmeta_slot_bounds st m nx MR MSn) as (NB0 & NB1 & NB2 & _). pose_ceil.
  pose proof (rmeta_slot_bounds st m pv MR MSp) as (PB0 & PB1 & PB2 & _). pose_ceil.
  pose proof MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1. rewrite FMH in C1.
  (pose_ceil; unfold RCTX, RMLOCK, RSSP_GUARD in *).
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (conc st h, conc st h + 40); (conc st pv, conc st pv + 40); (conc st nx, conc st nx + 40); (1037344, 1037344 + 928)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (* [comment removed for export] *)
  unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
  st1. st1.
  assert (CF : bv_eqb (Z_to_bv 64 (conc st h)) (Z_to_bv 64 0) = false) by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
  rewrite CF; clear CF.
  (* [comment removed for export] *)
  rmeta_chunk MR MSh CH. rewrite HN, HP in CH. cbn [oconc] in CH.
  st1. clear CH.
  (* [comment removed for export] *)
  st1. if_cases K; zify_cond K.
  - (* [comment removed for export] *)
    assert (Enx : nx = h).
    { rewrite ?unsigned_lit in K by lia. exact (rconc_meta_inj st m h nx MR MSh MSn ltac:(first [exact K | symmetry; exact K])). }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      pose proof (munch_refl [(RCTX + 16, RCTX + 24)]%Z mX) as MUc; pose proof (wmono_refl rsegs mX) as WMc end.
    unfold RCTX in MUc.
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR1 : rmrep (set_head LFree None st) mX) end.
    { eapply (rmrep_ctx_frameW st _ _ _ _ MR MUc WMc); try reflexivity.
      - intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - left. unfold ctx_head_cells, RCTX. ctx_cells_cbn. unfold pw at 1. cbn [oconc]. unfold pw. unfold wz at 4.
        lazymatch goal with H : rw_cells rsegs ?mX 1037344 _ |- _ => exact H end.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia. }
    clear MUc WMc C1.
    st1.
    assert (EQ : dequeue LFree h st = upd_meta h clr_links (set_head LFree None st)).
    { rewrite dequeue_mid. unfold deq_mid. rewrite HN, <- Enx, optr_eqb_refl. reflexivity. }
    rewrite EQ.
    change (conc st h) with (conc (set_head LFree None st) h). change (Z_to_bv 64 1036928) with (Z_to_bv 64 RSSP_GUARD).
    eapply evt_mono.
    { eapply (ram_tail sp gp tp _ _ _ s0 s1 _ _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc _ junk lo (set_head LFree None st) h);
        [exact MR1 | | apply meta_slot_same_areas with st; [reflexivity| exact MSh] | | | pose_ceil; lia | lia].
      - lazymatch goal with H : mem_inv rsegs ?mX |- _ => exact H end.
      - lazymatch goal with H : rw_cells rsegs ?mX (bv_unsigned sp + -64) _ |- _ => exact H end.
      - lazymatch goal with H : stk rsegs ?mX lo _ |- _ => exact H end. }
    intros ms' RP. unfold ram_ret_post in RP |- *.
    destruct RP as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m' & -> & PE' & WM' & MI' & ST' & MR').
    do 15 eexists. split; [reflexivity|].
    split.
    { apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [|exact WM|].
      - eapply rpres_except_trans; [exact MU|]. eapply rpres_except_mono; [exact PE'|]. intros a Ha. apply (proj1 (ram_fp_same st _ lo _ a eq_refl)). exact Ha.
      - cbn [ivs_covered]. repeat split; intros x Hx.
        + apply ram_fp_stack. lia.
        + eapply ram_fp_meta; [exact MR | exact MSh | lia].
        + eapply ram_fp_meta; [exact MR | exact MSp | lia].
        + eapply ram_fp_meta; [exact MR | exact MSn | lia].
        + apply ram_fp_ctx. unfold RCTX. lia. }
    split; [eapply wmono_trans; [exact WM| exact WM']|]. split; [exact MI'|]. split; [exact ST'|]. exact MR'.
  - (* [comment removed for export] *)
    assert (NEn : nx <> h) by (intros ->; apply K; reflexivity).
    assert (NEp : pv <> h) by (intros E; apply NEn; apply (proj2 SELF); exact E).
    (* [comment removed for export] *)
    rmeta_chunk MR MSh CH. rewrite HN, HP in CH. cbn [oconc] in CH.
    st1. clear CH.
    (* [comment removed for export] *)
    rmeta_open (conc st pv) MUp WMp.
    rmeta_chunk MR MSp CH.
    st1.
    rmeta_close2 MR MSp MUp WMp CH (put_meta pv (m_set_next (Some nx) (get_meta_rec st pv)) st) MR1 HP HN.
    set (st1 := put_meta pv (m_set_next (Some nx) (get_meta_rec st pv)) st) in MR1.
    assert (MSh1 : meta_slot st1 h) by (apply meta_slot_put_meta; exact MSh).
    assert (MSn1 : meta_slot st1 nx) by (apply meta_slot_put_meta; exact MSn).
    (* [comment removed for export] *)
    rmeta_chunk MR1 MSh1 CH. unfold st1 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
    rewrite HN, HP in CH. cbn [oconc] in CH.
    st1. st1. clear CH.
    (* [comment removed for export] *)
    rmeta_open (conc st nx) MUn WMn.
    rmeta_chunk MR1 MSn1 CH.
    st1.
    rmeta_close2 MR1 MSn1 MUn WMn CH (put_meta nx (m_set_prev (Some pv) (get_meta_rec st1 nx)) st1) MR2 HP HN.
    set (st2 := put_meta nx (m_set_prev (Some pv) (get_meta_rec st1 nx)) st1) in MR2.
    assert (MSh2 : meta_slot st2 h) by (apply meta_slot_put_meta; exact MSh1).
    (* [comment removed for export] *)
    st1. st1.
    rewrite bv_eqb_refl. cbn [negb]. cbv iota.
    (* [comment removed for export] *)
    rmeta_chunk MR2 MSh2 CH. unfold st2 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEn; symmetry; exact E).
    unfold st1 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
    rewrite HN, HP in CH. cbn [oconc] in CH.
    st1. clear CH.
    (* [comment removed for export] *)
    clear C1. pose proof MR2 as (_ & (C1 & _) & _). unfold ctx_head_cells, RCTX in C1.
    replace (c_free_meta_head (ctx st2)) with (Some h) in C1 by (symmetry; exact FMH).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      pose proof (munch_refl [(RCTX + 16, RCTX + 24)]%Z mX) as MUc; pose proof (wmono_refl rsegs mX) as WMc end.
    unfold RCTX in MUc.
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR3 : rmrep (set_head LFree (Some nx) st2) mX) end.
    { eapply (rmrep_ctx_frameW st2 _ _ _ _ MR2 MUc WMc); try reflexivity.
      - intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - left. unfold ctx_head_cells, RCTX. ctx_cells_cbn. unfold pw at 1. cbn [oconc]. change (conc (set_head LFree (Some nx) st2) nx) with (conc st nx).
        unfold pw. unfold wz at 4.
        lazymatch goal with H : rw_cells rsegs ?mX 1037344 _ |- _ => exact H end.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia. }
    clear MUc WMc C1.
    (* [comment removed for export] *)
    st1.
    assert (EQ : dequeue LFree h st = upd_meta h clr_links (set_head LFree (Some nx) st2)).
    { rewrite dequeue_mid. unfold deq_mid. rewrite HN, HP. cbn [optr_eqb negb]. rewrite (aptr_eqb_neq nx h NEn). cbn [negb get_head].
      rewrite !upd_meta_put. fold st1. fold st2. rewrite ctx_put_meta. unfold st1. rewrite ctx_put_meta. rewrite FMH, optr_eqb_refl. reflexivity. }
    rewrite EQ.
    change (conc st h) with (conc (set_head LFree (Some nx) st2) h). change (Z_to_bv 64 1036928) with (Z_to_bv 64 RSSP_GUARD).
    eapply evt_mono.
    { eapply (ram_tail sp gp tp _ _ _ s0 s1 _ _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc _ junk lo (set_head LFree (Some nx) st2) h);
        [exact MR3 | | apply meta_slot_same_areas with st; [reflexivity| exact MSh] | | | pose_ceil; lia | lia].
      - lazymatch goal with H : mem_inv rsegs ?mX |- _ => exact H end.
      - lazymatch goal with H : rw_cells rsegs ?mX (bv_unsigned sp + -64) _ |- _ => exact H end.
      - lazymatch goal with H : stk rsegs ?mX lo _ |- _ => exact H end. }
    intros ms' RP. unfold ram_ret_post in RP |- *.
    destruct RP as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m' & -> & PE' & WM' & MI' & ST' & MR').
    do 15 eexists. split; [reflexivity|].
    split.
    { apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [|exact WM|].
      - eapply rpres_except_trans; [exact MU|]. eapply rpres_except_mono; [exact PE'|]. intros a Ha. apply (proj1 (ram_fp_same st _ lo _ a eq_refl)). exact Ha.
      - cbn [ivs_covered]. repeat split; intros x Hx.
        + apply ram_fp_stack. lia.
        + eapply ram_fp_meta; [exact MR | exact MSh | lia].
        + eapply ram_fp_meta; [exact MR | exact MSp | lia].
        + eapply ram_fp_meta; [exact MR | exact MSn | lia].
        + apply ram_fp_ctx. unfold RCTX. lia. }
    split; [eapply wmono_trans; [exact WM| exact WM']|]. split; [exact MI'|]. split; [exact ST'|]. exact MR'.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ram_take_walk : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
    (m : word -> option byte) (junk : list byte) (lo : Z) (st : mstate) (q : aptr),
  rmrep st m -> mem_inv rsegs m ->
  c_free_meta_head (ctx st) = None -> c_avail_meta_count (ctx st) <> 0 -> 0 <= c_avail_meta_count (ctx st) < 2^64 ->
  c_avail_meta (ctx st) = Some q -> meta_slot st q ->
  rw_cells rsegs m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
  stk rsegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
  evt rsegs (ram_ret_post raw sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc lo st m
               (am_took st q (c_avail_meta_count (ctx st) - 1)) (Z_to_bv 64 (conc st q)))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb0344) fc None m (seg_rom rsegs)).
Proof.
  intros until q. intros MR MI FMH CNT CR AVM MSq FR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (rmeta_slot_bounds st m q MR MSq) as (QB0 & QB1 & QB2 & _). pose_ceil.
  pose proof MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1. rewrite FMH, AVM in C1.
  unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
  (pose_ceil; unfold RCTX, RMLOCK, RSSP_GUARD in *).
  (* [comment removed for export] *)
  st1. st1.
  rewrite bv_eqb_refl. cbv iota.
  st1. st1.
  assert (CF : bv_eqb (Z_to_bv 64 (c_avail_meta_count (ctx st))) (Z_to_bv 64 0) = false)
    by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; exact CNT).
  rewrite CF; clear CF.
  st1. st1. st1. rewrite ?(unsigned_lit (c_avail_meta_count (ctx st))) by lia.
  replace (c_avail_meta_count (ctx st) + -1) with (c_avail_meta_count (ctx st) - 1) by lia.
  change (Z_to_bv 64 1036928) with (Z_to_bv 64 RSSP_GUARD). change (Z_to_bv 64 1037336) with (Z_to_bv 64 RMLOCK).
  eapply (ram_b0 sp gp tp _ _ _ s0 s1 _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc m junk lo _ st q);
    [exact MR | exact MI | exact MSq | lia | exact FR | exact ST | pose_ceil; lia | lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ram_disp0 : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
    (m : word -> option byte) (st : mstate),
  rmrep st m -> c_free_meta_head (ctx st) = None -> c_avail_meta_count (ctx st) = 0 ->
  evt rsegs (fun ms' => ms' = MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7
                                   s2 (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb0398) fc None m (seg_rom rsegs))
      (MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb0344) fc None m (seg_rom rsegs)).
Proof.
  intros until st. intros MR FMH CNT.
  pose proof MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1. rewrite FMH, CNT in C1.
  unfold pw in C1. cbn [oconc] in C1. unfold wz in C1. unfold RCTX, RMLOCK in *.
  st1. st1. rewrite bv_eqb_refl. cbv iota.
  st1. st1. rewrite bv_eqb_refl. cbv iota.
  apply evt_done. reflexivity.
Qed.
End CEIL_WRAP_1.

