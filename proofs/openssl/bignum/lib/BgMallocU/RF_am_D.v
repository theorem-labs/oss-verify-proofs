(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OssFuzzTheorems.openssl.bignum.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import F_malloc_free MallocTree MallocModel_B F_ntf_B F_ntf_C MallocKit_B MallocKit_B3 F_am_A F_am_D.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import STree Malloc MallocCtrl.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3 RF_ntf_A RF_ntf_C RF_am_A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac ctx_cells_cbn :=
  cbn [ctx set_head upd_ctx s_ctx set_free_meta_head set_avail_meta set_avail_meta_count c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
       c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].

From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib.ZBridge.flia ::= first [ assumption | OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib.ZBridge.slim; lia | lia ].
Local Ltac OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Lemma ram_deq : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
    (m : word -> option byte) (junk : list byte) (lo : Z) (st : mstate) (h nx pv : aptr),
  rmrep st m -> mem_inv bgusegs m ->
  c_free_meta_head (ctx st) = Some h -> meta_slot st h ->
  m_next (get_meta_rec st h) = Some nx -> m_prev (get_meta_rec st h) = Some pv ->
  meta_slot st nx -> meta_slot st pv -> (nx = h <-> pv = h) ->
  rw_cells bgusegs m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
  stk bgusegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
  evt bgusegs (ram_ret_post raw sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc lo st m (dequeue LFree h st) (Z_to_bv 64 (conc st h)))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x2b1794) fc None m (seg_rom bgusegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until pv. intros MR MI FMH MSh HN HP MSn MSp SELF FR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (rmeta_slot_bounds st m h MR MSh) as (HB0 & HB1 & HB2 & _).
  pose proof (rmeta_slot_bounds st m nx MR MSn) as (NB0 & NB1 & NB2 & _).
  pose proof (rmeta_slot_bounds st m pv MR MSp) as (PB0 & PB1 & PB2 & _).
  pose proof MR as (WF & (C1 & _) & _). unfold rctx_head_cells in C1. rewrite FMH in C1.
  unfold RCTX, RMLOCK, RSSP_GUARD, OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec.Malloc.MCEIL in *; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (conc st h, conc st h + 40); (conc st pv, conc st pv + 40); (conc st nx, conc st nx + 40); (3478176, 3478176 + 928)]%Z m) as MU.
  pose proof (wmono_refl bgusegs m) as WM.

  unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
  st1. st1.
  assert (CF : bv_eqb (Z_to_bv 64 (conc st h)) (Z_to_bv 64 0) = false) by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
  rewrite CF; clear CF.

  rmeta_chunk MR MSh CH. rewrite HN, HP in CH. cbn [oconc] in CH.
  st1. clear CH.

  st1. if_cases K; zify_cond K.
  -
    assert (Enx : nx = h).
    { rewrite ?unsigned_lit in K by lia. exact (rconc_meta_inj st m h nx MR MSh MSn ltac:(first [exact K | symmetry; exact K])). }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      pose proof (munch_refl [(RCTX + 16, RCTX + 24)]%Z mX) as MUc; pose proof (wmono_refl bgusegs mX) as WMc end.
    unfold RCTX in MUc.
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR1 : rmrep (set_head LFree None st) mX) end.
    { eapply (rmrep_ctx_frameW st _ _ _ _ MR MUc WMc); try reflexivity.
      - intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - left. unfold rctx_head_cells, RCTX. ctx_cells_cbn. unfold pw at 1. cbn [oconc]. unfold pw. unfold wz at 4.
        lazymatch goal with H : rw_cells bgusegs ?mX 3478176 _ |- _ => exact H end.
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
    change (conc st h) with (conc (set_head LFree None st) h). change (Z_to_bv 64 3477464) with (Z_to_bv 64 RSSP_GUARD).
    eapply evt_mono.
    { eapply (ram_tail sp gp tp _ _ _ s0 s1 _ _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc _ junk lo (set_head LFree None st) h);
        [exact MR1 | | apply meta_slot_same_areas with st; [reflexivity| exact MSh] | | | unfold OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec.Malloc.MCEIL; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; lia | lia].
      - lazymatch goal with H : mem_inv bgusegs ?mX |- _ => exact H end.
      - lazymatch goal with H : rw_cells bgusegs ?mX (bv_unsigned sp + -64) _ |- _ => exact H end.
      - lazymatch goal with H : stk bgusegs ?mX lo _ |- _ => exact H end. }
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
  -
    assert (NEn : nx <> h) by (intros ->; apply K; reflexivity).
    assert (NEp : pv <> h) by (intros E; apply NEn; apply (proj2 SELF); exact E).

    rmeta_chunk MR MSh CH. rewrite HN, HP in CH. cbn [oconc] in CH.
    st1. clear CH.

    rmeta_open (conc st pv) MUp WMp.
    rmeta_chunk MR MSp CH.
    st1.
    rmeta_close2 MR MSp MUp WMp CH (put_meta pv (m_set_next (Some nx) (get_meta_rec st pv)) st) MR1 HP HN.
    set (st1 := put_meta pv (m_set_next (Some nx) (get_meta_rec st pv)) st) in MR1.
    assert (MSh1 : meta_slot st1 h) by (apply meta_slot_put_meta; exact MSh).
    assert (MSn1 : meta_slot st1 nx) by (apply meta_slot_put_meta; exact MSn).

    rmeta_chunk MR1 MSh1 CH. unfold st1 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
    rewrite HN, HP in CH. cbn [oconc] in CH.
    st1. st1. clear CH.

    rmeta_open (conc st nx) MUn WMn.
    rmeta_chunk MR1 MSn1 CH.
    st1.
    rmeta_close2 MR1 MSn1 MUn WMn CH (put_meta nx (m_set_prev (Some pv) (get_meta_rec st1 nx)) st1) MR2 HP HN.
    set (st2 := put_meta nx (m_set_prev (Some pv) (get_meta_rec st1 nx)) st1) in MR2.
    assert (MSh2 : meta_slot st2 h) by (apply meta_slot_put_meta; exact MSh1).

    st1. st1.
    rewrite bv_eqb_refl. cbn [negb]. cbv iota.

    rmeta_chunk MR2 MSh2 CH. unfold st2 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEn; symmetry; exact E).
    unfold st1 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
    rewrite HN, HP in CH. cbn [oconc] in CH.
    st1. clear CH.

    clear C1. pose proof MR2 as (_ & (C1 & _) & _). unfold rctx_head_cells, RCTX in C1.
    replace (c_free_meta_head (ctx st2)) with (Some h) in C1 by (symmetry; exact FMH).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      pose proof (munch_refl [(RCTX + 16, RCTX + 24)]%Z mX) as MUc; pose proof (wmono_refl bgusegs mX) as WMc end.
    unfold RCTX in MUc.
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR3 : rmrep (set_head LFree (Some nx) st2) mX) end.
    { eapply (rmrep_ctx_frameW st2 _ _ _ _ MR2 MUc WMc); try reflexivity.
      - intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - left. unfold rctx_head_cells, RCTX. ctx_cells_cbn. unfold pw at 1. cbn [oconc]. change (conc (set_head LFree (Some nx) st2) nx) with (conc st nx).
        unfold pw. unfold wz at 4.
        lazymatch goal with H : rw_cells bgusegs ?mX 3478176 _ |- _ => exact H end.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia. }
    clear MUc WMc C1.

    st1.
    assert (EQ : dequeue LFree h st = upd_meta h clr_links (set_head LFree (Some nx) st2)).
    { rewrite dequeue_mid. unfold deq_mid. rewrite HN, HP. cbn [optr_eqb negb]. rewrite (aptr_eqb_neq nx h NEn). cbn [negb get_head].
      rewrite !upd_meta_put. fold st1. fold st2. rewrite ctx_put_meta. unfold st1. rewrite ctx_put_meta. rewrite FMH, optr_eqb_refl. reflexivity. }
    rewrite EQ.
    change (conc st h) with (conc (set_head LFree (Some nx) st2) h). change (Z_to_bv 64 3477464) with (Z_to_bv 64 RSSP_GUARD).
    eapply evt_mono.
    { eapply (ram_tail sp gp tp _ _ _ s0 s1 _ _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc _ junk lo (set_head LFree (Some nx) st2) h);
        [exact MR3 | | apply meta_slot_same_areas with st; [reflexivity| exact MSh] | | | unfold OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec.Malloc.MCEIL; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; lia | lia].
      - lazymatch goal with H : mem_inv bgusegs ?mX |- _ => exact H end.
      - lazymatch goal with H : rw_cells bgusegs ?mX (bv_unsigned sp + -64) _ |- _ => exact H end.
      - lazymatch goal with H : stk bgusegs ?mX lo _ |- _ => exact H end. }
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

Lemma ram_take_walk : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
    (m : word -> option byte) (junk : list byte) (lo : Z) (st : mstate) (q : aptr),
  rmrep st m -> mem_inv bgusegs m ->
  c_free_meta_head (ctx st) = None -> c_avail_meta_count (ctx st) <> 0 -> 0 <= c_avail_meta_count (ctx st) < 2^64 ->
  c_avail_meta (ctx st) = Some q -> meta_slot st q ->
  rw_cells bgusegs m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
  stk bgusegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
  evt bgusegs (ram_ret_post raw sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc lo st m
               (am_took st q (c_avail_meta_count (ctx st) - 1)) (Z_to_bv 64 (conc st q)))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x2b1794) fc None m (seg_rom bgusegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until q. intros MR MI FMH CNT CR AVM MSq FR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (rmeta_slot_bounds st m q MR MSq) as (QB0 & QB1 & QB2 & _).
  pose proof MR as (WF & (C1 & _) & _). unfold rctx_head_cells in C1. rewrite FMH, AVM in C1.
  unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
  unfold RCTX, RMLOCK, RSSP_GUARD, OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec.Malloc.MCEIL in *; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.

  st1. st1.
  rewrite bv_eqb_refl. cbv iota.
  st1. st1.
  assert (CF : bv_eqb (Z_to_bv 64 (c_avail_meta_count (ctx st))) (Z_to_bv 64 0) = false)
    by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; exact CNT).
  rewrite CF; clear CF.
  st1. st1. st1. rewrite ?(unsigned_lit (c_avail_meta_count (ctx st))) by lia.
  replace (c_avail_meta_count (ctx st) + -1) with (c_avail_meta_count (ctx st) - 1) by lia.
  change (Z_to_bv 64 3477464) with (Z_to_bv 64 RSSP_GUARD). change (Z_to_bv 64 3478168) with (Z_to_bv 64 RMLOCK).
  eapply (ram_b0 sp gp tp _ _ _ s0 s1 _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc m junk lo _ st q);
    [exact MR | exact MI | exact MSq | lia | exact FR | exact ST | unfold OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec.Malloc.MCEIL; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; lia | lia].
Qed.

Lemma ram_disp0 : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
    (m : word -> option byte) (st : mstate),
  rmrep st m -> c_free_meta_head (ctx st) = None -> c_avail_meta_count (ctx st) = 0 ->
  evt bgusegs (fun ms' => ms' = MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7
                                   s2 (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x2b17e8) fc None m (seg_rom bgusegs))
      (MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x2b1794) fc None m (seg_rom bgusegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until st. intros MR FMH CNT.
  pose proof MR as (WF & (C1 & _) & _). unfold rctx_head_cells in C1. rewrite FMH, CNT in C1.
  unfold pw in C1. cbn [oconc] in C1. unfold wz in C1. unfold RCTX, RMLOCK in *.
  st1. st1. rewrite bv_eqb_refl. cbv iota.
  st1. st1. rewrite bv_eqb_refl. cbv iota.
  apply evt_done. reflexivity.
Qed.
End WithCeiling0.
