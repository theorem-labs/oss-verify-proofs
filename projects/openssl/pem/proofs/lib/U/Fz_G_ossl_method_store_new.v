(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OSSVerify.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn.
From OSSVerify.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OSSVerify.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OSSVerify.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit. From OSSVerify.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit. From OSSVerify.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit. From OSSVerify.Proofs.openssl.pem.lib.P Require Import Fz_G_pkit. From OSSVerify.Proofs.openssl.pem.lib.U Require Import Fz_M_malloc Fz_M_zalloc F_memset Fz_M_calloc Fz_T_sa_new Th_mutex Fz_T_lock_new.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.openssl.pem.lib.P Require Import Rnd.
From OSSVerify.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac tslia ::= wp_tslia.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition FZ_G_ossl_method_store_new : Z := 0xec964.
Definition ossl_method_store_new_STACK : Z := 80 + LOCK_NEW_STACK.

Definition ossl_method_store_new_res (a0 : word) (LBall : list block) (L : @clist bptr)
  : word -> list block -> @clist bptr -> mem -> Prop :=
  fun v LBall' L' m' =>
    exists (qs : bptr) (As : Z) (qh : bptr) (Ah : Z)
           (qa0 : bptr) (Aa0 : Z) (qx0 : bptr) (Ax0 : Z) (qy0 : bptr) (Ay0 : Z)
           (qa1 : bptr) (Aa1 : Z) (qx1 : bptr) (Ax1 : Z) (qy1 : bptr) (Ay1 : Z)
           (qa2 : bptr) (Aa2 : Z) (qx2 : bptr) (Ax2 : Z) (qy2 : bptr) (Ay2 : Z)
           (qa3 : bptr) (Aa3 : Z) (qx3 : bptr) (Ax3 : Z) (qy3 : bptr) (Ay3 : Z)
           (qb : bptr) (Ab : Z),
      v = Z_to_bv 64 As /\
      LBall' = (qb, Ab, 40) :: (qy3, Ay3, 40) :: (qx3, Ax3, 40) :: (qa3, Aa3, 32)
               :: (qy2, Ay2, 40) :: (qx2, Ax2, 40) :: (qa2, Aa2, 32)
               :: (qy1, Ay1, 40) :: (qx1, Ax1, 40) :: (qa1, Aa1, 32)
               :: (qy0, Ay0, 40) :: (qx0, Ax0, 40) :: (qa0, Aa0, 32)
               :: (qh, Ah, 384) :: (qs, As, 24) :: LBall /\
      L' = (qb, 40) :: (qy3, 40) :: (qx3, 40) :: (qa3, 32)
           :: (qy2, 40) :: (qx2, 40) :: (qa2, 32)
           :: (qy1, 40) :: (qx1, 40) :: (qa1, 32)
           :: (qy0, 40) :: (qx0, 40) :: (qa0, 32)
           :: (qh, 384) :: (qs, 24) :: L /\
      rblock_range As 24 /\ rblock_range Ah 384 /\
      rblock_range Aa0 32 /\ rblock_range Ax0 40 /\ rblock_range Ay0 40 /\
      rblock_range Aa1 32 /\ rblock_range Ax1 40 /\ rblock_range Ay1 40 /\
      rblock_range Aa2 32 /\ rblock_range Ax2 40 /\ rblock_range Ay2 40 /\
      rblock_range Aa3 32 /\ rblock_range Ax3 40 /\ rblock_range Ay3 40 /\
      rblock_range Ab 40 /\
      rw_cells usegs m' As [C8 a0; C8 (Z_to_bv 64 Ah); C8 (Z_to_bv 64 Ab)] /\
      rw_cells usegs m' Ay3 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) /\
      rw_cells usegs m' Ax3 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) /\
      rw_cells usegs m' Aa3 [CB (Z.to_nat 32) (repeat (Z_to_bv 8 0) (Z.to_nat 32))] /\
      rw_cells usegs m' Ay2 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) /\
      rw_cells usegs m' Ax2 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) /\
      rw_cells usegs m' Aa2 [CB (Z.to_nat 32) (repeat (Z_to_bv 8 0) (Z.to_nat 32))] /\
      rw_cells usegs m' Ay1 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) /\
      rw_cells usegs m' Ax1 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) /\
      rw_cells usegs m' Aa1 [CB (Z.to_nat 32) (repeat (Z_to_bv 8 0) (Z.to_nat 32))] /\
      rw_cells usegs m' Ay0 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) /\
      rw_cells usegs m' Ax0 (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)) /\
      rw_cells usegs m' Aa0 [CB (Z.to_nat 32) (repeat (Z_to_bv 8 0) (Z.to_nat 32))] /\
      rw_cells usegs m' Ah
        [C8 (Z_to_bv 64 Aa0); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 Ax0); C8 (Z_to_bv 64 Ay0);
         C8 (Z_to_bv 64 Aa1); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 Ax1); C8 (Z_to_bv 64 Ay1);
         C8 (Z_to_bv 64 Aa2); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 Ax2); C8 (Z_to_bv 64 Ay2);
         C8 (Z_to_bv 64 Aa3); CB 72 (repeat (Z_to_bv 8 0) 72); C8 (Z_to_bv 64 Ax3); C8 (Z_to_bv 64 Ay3)] /\
      rw_cells usegs m' Ab (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)).

Definition ossl_method_store_new_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : PState) (LBall LB : list block) (L : @clist bptr)
         (f : nat) (lo B : Z),
    (15 <= f)%nat ->
    croom L 14 1 8576 ->
    cstate st LBall LB L m sp tp lo B ->
    lo <= bv_unsigned sp - ossl_method_store_new_STACK ->
    climpl f L st
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FZ_G_ossl_method_store_new) fc None m (seg_rom usegs))
      (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LBall LB L f m lo B
             (fun _ : bptr => False) [] 15 14 1 8576 (ossl_method_store_new_res a0 LBall L)).

Theorem ossl_method_store_new_spec : crypto_zalloc_stmt -> ossl_method_store_new_stmt.
Proof.
  intros ZAL.
  pose proof (crypto_calloc_spec ZAL) as CAL.
  pose proof (T_sa_new_spec ZAL) as SAN.
  pose proof (T_lock_new_spec ZAL) as LKN.
  unfold ossl_method_store_new_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LBall LB L f lo B FUEL ROOM CST0 SLO.
  unfold ossl_method_store_new_STACK, LOCK_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK in SLO.
  pose proof CST0 as (HP0 & OWN0 & (errv & _ & SPB & ST & ALC & _ & MI & _) & _ & _ & _ & GTOP).
  unfold GLOBALS_TOP in GTOP.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (SPfU : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) = bv_unsigned sp + -80) by (rewrite unsigned_lit by lia; lia).
  unfold FZ_G_ossl_method_store_new.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MUf. pose proof (wmono_refl usegs m) as WMf.
  apply climpl_from_evt.
  step.
  carve_frame 80%nat ST.
  do 17 step.
  apply evt_done; cbv beta.
  rename m1 into mF.
  assert (CSf : cstate st LBall LB L mF (Z_to_bv 64 (bv_unsigned sp + -80)) tp lo B).
  { eapply (cstate_seg _ _ _ _ _ m mF _ (Z_to_bv 64 (bv_unsigned sp + -80)) tp lo B (bv_unsigned sp)); [exact CST0| exact MUf| exact WMf| exact MI| | lia| lia| | | lia].
    - apply Forall_cons; [apply cwin_stack; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. split; [lia| exact I].
    - rewrite SPfU. exact ST. }
  assert (FRf : cframe (fun _ : bptr => False) [] (bv_unsigned sp) st LBall L m st LBall L mF).
  { eapply cframe_seg; [apply cframe_refl| exact MUf| exact WMf| exact HP0| lia|].
    apply Forall_cons; [apply cseg_ok_stack; lia| apply Forall_nil]. }
  clear MUf WMf.
  eapply climpl_seq.
  { eapply ZAL with (n := 24); [lia| eapply croom_weaken; [exact ROOM| wp_wnorm; lia..]| lia| exact CSf| rewrite SPfU; unfold CZ_STACK, CM_STACK, RMALLOC_STACK; lia| reflexivity]. }
  (* call 1: zalloc *)
  intros f1 L1 st1 ms1 (v1 & m1 & LB1 & RET1 & FU1 & GR1 & CST1 & FRM1 & (qs & As & -> & -> & -> & RNGs & CELLs)).
  destruct RET1 as (r1_0 & r1_1 & r1_2 & r1_3 & r1_4 & r1_5 & r1_6 & r1_7 & r1_8 & r1_9 & r1_10 & r1_11 & r1_12 & r1_13 & ->).
  cret_lit.
  rewrite SPfU in FRM1.
  change (Z.to_nat (24)) with 24%nat in CELLs.
  pose proof (cframe_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FRf FRM1 ltac:(lia) (fun a X => X) (fun q _ X => X)) as SFn.
  pose proof (proj1 FRM1) as CF.
  repeat match goal with
  | H : rw_cells usegs ?mo (bv_unsigned sp + -80) _, CF : cfr _ _ _ _ ?mo ?mn |- _ =>
      apply (cfr_cells_stack _ _ _ _ _ _ _ _ CF) in H; [| lia]
  | H : rw_cells usegs ?mo ?A _, CF : cfr _ _ _ ?LBo ?mo ?mn |- _ =>
      lazymatch LBo with context [(?q, A, ?n)] =>
        apply (cfr_cells_block _ _ _ _ _ _ _ _ (q, A, n) CF) in H; [| wp_in_lit| intros X; exact X| cbn; lia| cbn; lia] end
  end.
  clear CF FRM1 FRf CSf MI ST HP0. rename SFn into SF.
  assert (FUc : (f <= f1 + 1)%nat) by lia. clear FU1.
  assert (GRc : cgrow L ((qs, 24) :: L) 1 0 0) by (eapply cgrow_weaken; [exact GR1| wp_wnorm; lia..]). clear GR1.
  pose proof RNGs as (P0s & ALs & _ & PCs & IMGs). wp_box1 IMGs.
  pose proof CST1 as (HP & _ & (errv1 & _ & _ & ST & _ & _ & MI & _) & _).
  rewrite unsigned_lit in ST by lia.
  pose proof (munch_refl [(As, As + 24)] m1) as MU. pose proof (wmono_refl usegs m1) as WM.
  apply climpl_from_evt.
  step. wp_brF. step. step. step. wp_brF. step. do 6 step.
  apply evt_done; cbv beta.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into mw1 end.
  assert (CSa : cstate st1 ((qs, As, 24) :: LBall) LB ((qs, 24) :: L) mw1 (Z_to_bv 64 (bv_unsigned sp + -80)) tp lo B).
  { eapply (cstate_seg _ _ _ _ _ m1 mw1 _ _ tp lo B (bv_unsigned sp)); [exact CST1| exact MU| exact WM| exact MI| | lia| lia| | rewrite SPfU; exact ST| rewrite SPfU; lia].
    - apply Forall_cons; [eapply cwin_block with (b := (qs, As, 24)); [wp_in_lit| cbn; lia| cbn; lia]| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. unfold wp_box in IMGs. repeat split; lia. }
  assert (SFa : cframe (fun _ : bptr => False) [] (bv_unsigned sp) st LBall L m st1 ((qs, As, 24) :: LBall) ((qs, 24) :: L) mw1).
  { eapply cframe_seg; [exact SF| exact MU| exact WM| exact HP| lia|].
    apply Forall_cons; [eapply cseg_ok_block with (b := (qs, As, 24)); [wp_in_lit| | cbn; lia| cbn; lia]|].
    { apply (t_fresh_notin (fun _ : bptr => False) LBall).
      apply (t_nodup_prefix blk_id [(qs, As, 24)] LBall (qs, As, 24)); [exact (proj1 (cstate_nodup _ _ _ _ _ _ _ _ _ CST1))| wp_in_lit]. }
    apply Forall_nil. }
  clear SF MU WM CST1. rename SFa into SF.
  (* call 2: calloc *)
  eapply climpl_seq.
  { eapply CAL with (num := 4) (sz := 96); [lia| eapply croom_weaken; [exact (croom_grow _ _ _ _ _ _ _ _ ROOM GRc)| wp_wnorm; lia..]| lia| lia| lia| exact CSa| rewrite SPfU; unfold CZ_STACK, CM_STACK, RMALLOC_STACK; lia| reflexivity| reflexivity]. }
  intros f2 L2 st2 ms2 (v2 & m2 & LB2 & RET2 & FU2 & GR2 & CST2 & FRM2 & (qh & Ah & -> & -> & -> & RNGh & CELLh)).
  destruct RET2 as (r2_0 & r2_1 & r2_2 & r2_3 & r2_4 & r2_5 & r2_6 & r2_7 & r2_8 & r2_9 & r2_10 & r2_11 & r2_12 & r2_13 & ->).
  cret_lit.
  rewrite SPfU in FRM2.
  change (Z.to_nat (4 * 96)) with 384%nat in CELLh.
  pose proof (cframe_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SF FRM2 ltac:(lia) (fun a X => X) (fun q _ X => X)) as SFn.
  pose proof (proj1 FRM2) as CF.
  repeat match goal with
  | H : rw_cells usegs ?mo (bv_unsigned sp + -80) _, CF : cfr _ _ _ _ ?mo ?mn |- _ =>
      apply (cfr_cells_stack _ _ _ _ _ _ _ _ CF) in H; [| lia]
  | H : rw_cells usegs ?mo ?A _, CF : cfr _ _ _ ?LBo ?mo ?mn |- _ =>
      lazymatch LBo with context [(?q, A, ?n)] =>
        apply (cfr_cells_block _ _ _ _ _ _ _ _ (q, A, n) CF) in H; [| wp_in_lit| intros X; exact X| cbn; lia| cbn; lia] end
  end.
  clear CF FRM2 SF CSa HP MI ST. rename SFn into SF.
  assert (FUn : (f <= f2 + 2)%nat) by lia. clear FU2 FUc. rename FUn into FUc.
  assert (GRn : cgrow L ((qh, 4 * 96) :: (qs, 24) :: L) 1 1 8576) by (eapply cgrow_weaken; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ GRc GR2)| wp_wnorm; lia..]).
  clear GRc GR2. rename GRn into GRc.
  pose proof RNGh as (P0h & ALh & _ & PCh & IMGh). wp_box1 IMGh.
  assert (APsh : wp_apbox (As + 24 <= Ah \/ Ah + 384 <= As)).
  { unfold wp_apbox. eapply cstate_apart; [exact CST2| wp_in_lit| left; reflexivity| eapply cstate_head_fresh; [exact CST2| wp_in_lit]]. }
  pose proof CST2 as (HP & _ & (errv2 & _ & _ & ST & _ & _ & MI & _) & _).
  rewrite unsigned_lit in ST by lia.
  apply climpl_from_evt.
  step. wp_brF. do 8 step.
  apply evt_done; cbv beta.
  (* call 3: sa *)
  eapply climpl_seq.
  { eapply SAN; [lia| eapply croom_weaken; [exact (croom_grow _ _ _ _ _ _ _ _ ROOM GRc)| wp_wnorm; lia..]| exact CST2| rewrite SPfU; unfold SA_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; lia]. }
  intros f3 L3 st3 ms3 (v3 & m3 & LB3 & RET3 & FU3 & GR3 & CST3 & FRM3 & (qa0 & Aa0 & -> & -> & -> & RNGa0 & CELLa0)).
  destruct RET3 as (r3_0 & r3_1 & r3_2 & r3_3 & r3_4 & r3_5 & r3_6 & r3_7 & r3_8 & r3_9 & r3_10 & r3_11 & r3_12 & r3_13 & ->).
  cret_lit.
  rewrite SPfU in FRM3.
  change (Z.to_nat (32)) with 32%nat in CELLa0.
  pose proof (cframe_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SF FRM3 ltac:(lia) (fun a X => X) (fun q _ X => X)) as SFn.
  pose proof (proj1 FRM3) as CF.
  repeat match goal with
  | H : rw_cells usegs ?mo (bv_unsigned sp + -80) _, CF : cfr _ _ _ _ ?mo ?mn |- _ =>
      apply (cfr_cells_stack _ _ _ _ _ _ _ _ CF) in H; [| lia]
  | H : rw_cells usegs ?mo ?A _, CF : cfr _ _ _ ?LBo ?mo ?mn |- _ =>
      lazymatch LBo with context [(?q, A, ?n)] =>
        apply (cfr_cells_block _ _ _ _ _ _ _ _ (q, A, n) CF) in H; [| wp_in_lit| intros X; exact X| cbn; lia| cbn; lia] end
  end.
  clear CF FRM3 SF CST2 HP MI ST. rename SFn into SF.
  assert (FUn : (f <= f3 + 3)%nat) by lia. clear FU3 FUc. rename FUn into FUc.
  assert (GRn : cgrow L ((qa0, 32) :: (qh, 4 * 96) :: (qs, 24) :: L) 2 1 8576) by (eapply cgrow_weaken; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ GRc GR3)| wp_wnorm; lia..]).
  clear GRc GR3. rename GRn into GRc.
  pose proof RNGa0 as (P0a0 & _ & _ & PCa0 & IMGa0). wp_box1 IMGa0.
  assert (APsa0 : wp_apbox (As + 24 <= Aa0 \/ Aa0 + 32 <= As)).
  { unfold wp_apbox. eapply cstate_apart; [exact CST3| wp_in_lit| left; reflexivity| eapply cstate_head_fresh; [exact CST3| wp_in_lit]]. }
  assert (APha0 : wp_apbox (Ah + 384 <= Aa0 \/ Aa0 + 32 <= Ah)).
  { unfold wp_apbox. eapply cstate_apart; [exact CST3| wp_in_lit| left; reflexivity| eapply cstate_head_fresh; [exact CST3| wp_in_lit]]. }
  pose proof CST3 as (HP & _ & (errv3 & _ & _ & ST & _ & _ & MI & _) & _).
  rewrite unsigned_lit in ST by lia.
  pose proof (munch_refl [(Ah, Ah + 384)] m3) as MU. pose proof (wmono_refl usegs m3) as WM.
  apply climpl_from_evt.
  step. wp_brF. step. wp_brF. step. step. step. wp_brF. step.
  apply evt_done; cbv beta.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into mw3 end.
  assert (CSa : cstate st3 ((qa0, Aa0, 32) :: (qh, Ah, 4 * 96) :: (qs, As, 24) :: LBall) LB ((qa0, 32) :: (qh, 4 * 96) :: (qs, 24) :: L) mw3 (Z_to_bv 64 (bv_unsigned sp + -80)) tp lo B).
  { eapply (cstate_seg _ _ _ _ _ m3 mw3 _ _ tp lo B (bv_unsigned sp)); [exact CST3| exact MU| exact WM| exact MI| | lia| lia| | rewrite SPfU; exact ST| rewrite SPfU; lia].
    - apply Forall_cons; [eapply cwin_block with (b := (qh, Ah, 4 * 96)); [wp_in_lit| cbn; lia| cbn; lia]| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. unfold wp_box in IMGh. repeat split; lia. }
  assert (SFa : cframe (fun _ : bptr => False) [] (bv_unsigned sp) st LBall L m st3 ((qa0, Aa0, 32) :: (qh, Ah, 4 * 96) :: (qs, As, 24) :: LBall) ((qa0, 32) :: (qh, 4 * 96) :: (qs, 24) :: L) mw3).
  { eapply cframe_seg; [exact SF| exact MU| exact WM| exact HP| lia|].
    apply Forall_cons; [eapply cseg_ok_block with (b := (qh, Ah, 4 * 96)); [wp_in_lit| | cbn; lia| cbn; lia]|].
    { apply (t_fresh_notin (fun _ : bptr => False) LBall).
      apply (t_nodup_prefix blk_id [(qa0, Aa0, 32); (qh, Ah, 4 * 96); (qs, As, 24)] LBall (qh, Ah, 4 * 96)); [exact (proj1 (cstate_nodup _ _ _ _ _ _ _ _ _ CST3))| wp_in_lit]. }
    apply Forall_nil. }
  clear SF MU WM CST3. rename SFa into SF.
  (* call 4: lock *)
  eapply climpl_seq.
  { eapply LKN; [lia| eapply croom_weaken; [exact (croom_grow _ _ _ _ _ _ _ _ ROOM GRc)| wp_wnorm; lia..]| exact CSa| rewrite SPfU; unfold LOCK_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; lia]. }
  intros f4 L4 st4 ms4 (v4 & m4 & LB4 & RET4 & FU4 & GR4 & CST4 & FRM4 & (qx0 & Ax0 & -> & -> & -> & RNGx0 & CELLx0)).
  destruct RET4 as (r4_0 & r4_1 & r4_2 & r4_3 & r4_4 & r4_5 & r4_6 & r4_7 & r4_8 & r4_9 & r4_10 & r4_11 & r4_12 & r4_13 & ->).
  cret_lit.
  rewrite SPfU in FRM4.
  pose proof (cframe_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SF FRM4 ltac:(lia) (fun a X => X) (fun q _ X => X)) as SFn.
  pose proof (proj1 FRM4) as CF.
  repeat match goal with
  | H : rw_cells usegs ?mo (bv_unsigned sp + -80) _, CF : cfr _ _ _ _ ?mo ?mn |- _ =>
      apply (cfr_cells_stack _ _ _ _ _ _ _ _ CF) in H; [| lia]
  | H : rw_cells usegs ?mo ?A _, CF : cfr _ _ _ ?LBo ?mo ?mn |- _ =>
      lazymatch LBo with context [(?q, A, ?n)] =>
        apply (cfr_cells_block _ _ _ _ _ _ _ _ (q, A, n) CF) in H; [| wp_in_lit| intros X; exact X| cbn; lia| cbn; lia] end
  end.
  clear CF FRM4 SF CSa HP MI ST. rename SFn into SF.
  assert (FUn : (f <= f4 + 4)%nat) by lia. clear FU4 FUc. rename FUn into FUc.
  assert (GRn : cgrow L ((qx0, 40) :: (qa0, 32) :: (qh, 4 * 96) :: (qs, 24) :: L) 3 1 8576) by (eapply cgrow_weaken; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ GRc GR4)| wp_wnorm; lia..]).
  clear GRc GR4. rename GRn into GRc.
  pose proof RNGx0 as (P0x0 & _ & _ & PCx0 & IMGx0). wp_box1 IMGx0.
  assert (APsx0 : wp_apbox (As + 24 <= Ax0 \/ Ax0 + 40 <= As)).
  { unfold wp_apbox. eapply cstate_apart; [exact CST4| wp_in_lit| left; reflexivity| eapply cstate_head_fresh; [exact CST4| wp_in_lit]]. }
  assert (APhx0 : wp_apbox (Ah + 384 <= Ax0 \/ Ax0 + 40 <= Ah)).
  { unfold wp_apbox. eapply cstate_apart; [exact CST4| wp_in_lit| left; reflexivity| eapply cstate_head_fresh; [exact CST4| wp_in_lit]]. }
  pose proof CST4 as (HP & _ & (errv4 & _ & _ & ST & _ & _ & MI & _) & _).
  rewrite unsigned_lit in ST by lia.
  pose proof (munch_refl [(Ah, Ah + 384)] m4) as MU. pose proof (wmono_refl usegs m4) as WM.
  apply climpl_from_evt.
  step. step. step. wp_brF. step.
  apply evt_done; cbv beta.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into mw4 end.
  assert (CSa : cstate st4 ((qx0, Ax0, 40) :: (qa0, Aa0, 32) :: (qh, Ah, 4 * 96) :: (qs, As, 24) :: LBall) LB ((qx0, 40) :: (qa0, 32) :: (qh, 4 * 96) :: (qs, 24) :: L) mw4 (Z_to_bv 64 (bv_unsigned sp + -80)) tp lo B).
  { eapply (cstate_seg _ _ _ _ _ m4 mw4 _ _ tp lo B (bv_unsigned sp)); [exact CST4| exact MU| exact WM| exact MI| | lia| lia| | rewrite SPfU; exact ST| rewrite SPfU; lia].
    - apply Forall_cons; [eapply cwin_block with (b := (qh, Ah, 4 * 96)); [wp_in_lit| cbn; lia| cbn; lia]| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. unfold wp_box in IMGh. repeat split; lia. }
  assert (SFa : cframe (fun _ : bptr => False) [] (bv_unsigned sp) st LBall L m st4 ((qx0, Ax0, 40) :: (qa0, Aa0, 32) :: (qh, Ah, 4 * 96) :: (qs, As, 24) :: LBall) ((qx0, 40) :: (qa0, 32) :: (qh, 4 * 96) :: (qs, 24) :: L) mw4).
  { eapply cframe_seg; [exact SF| exact MU| exact WM| exact HP| lia|].
    apply Forall_cons; [eapply cseg_ok_block with (b := (qh, Ah, 4 * 96)); [wp_in_lit| | cbn; lia| cbn; lia]|].
    { apply (t_fresh_notin (fun _ : bptr => False) LBall).
      apply (t_nodup_prefix blk_id [(qx0, Ax0, 40); (qa0, Aa0, 32); (qh, Ah, 4 * 96); (qs, As, 24)] LBall (qh, Ah, 4 * 96)); [exact (proj1 (cstate_nodup _ _ _ _ _ _ _ _ _ CST4))| wp_in_lit]. }
    apply Forall_nil. }
  clear SF MU WM CST4. rename SFa into SF.
  (* call 5: lock *)
  eapply climpl_seq.
  { eapply LKN; [lia| eapply croom_weaken; [exact (croom_grow _ _ _ _ _ _ _ _ ROOM GRc)| wp_wnorm; lia..]| exact CSa| rewrite SPfU; unfold LOCK_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; lia]. }
  intros f5 L5 st5 ms5 (v5 & m5 & LB5 & RET5 & FU5 & GR5 & CST5 & FRM5 & (qy0 & Ay0 & -> & -> & -> & RNGy0 & CELLy0)).
  destruct RET5 as (r5_0 & r5_1 & r5_2 & r5_3 & r5_4 & r5_5 & r5_6 & r5_7 & r5_8 & r5_9 & r5_10 & r5_11 & r5_12 & r5_13 & ->).
  cret_lit.
  rewrite SPfU in FRM5.
  pose proof (cframe_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SF FRM5 ltac:(lia) (fun a X => X) (fun q _ X => X)) as SFn.
  pose proof (proj1 FRM5) as CF.
  repeat match goal with
  | H : rw_cells usegs ?mo (bv_unsigned sp + -80) _, CF : cfr _ _ _ _ ?mo ?mn |- _ =>
      apply (cfr_cells_stack _ _ _ _ _ _ _ _ CF) in H; [| lia]
  | H : rw_cells usegs ?mo ?A _, CF : cfr _ _ _ ?LBo ?mo ?mn |- _ =>
      lazymatch LBo with context [(?q, A, ?n)] =>
        apply (cfr_cells_block _ _ _ _ _ _ _ _ (q, A, n) CF) in H; [| wp_in_lit| intros X; exact X| cbn; lia| cbn; lia] end
  end.
  clear CF FRM5 SF CSa HP MI ST. rename SFn into SF.
  assert (FUn : (f <= f5 + 5)%nat) by lia. clear FU5 FUc. rename FUn into FUc.
  assert (GRn : cgrow L ((qy0, 40) :: (qx0, 40) :: (qa0, 32) :: (qh, 4 * 96) :: (qs, 24) :: L) 4 1 8576) by (eapply cgrow_weaken; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ GRc GR5)| wp_wnorm; lia..]).
  clear GRc GR5. rename GRn into GRc.
  pose proof RNGy0 as (P0y0 & _ & _ & PCy0 & IMGy0). wp_box1 IMGy0.
  assert (APsy0 : wp_apbox (As + 24 <= Ay0 \/ Ay0 + 40 <= As)).
  { unfold wp_apbox. eapply cstate_apart; [exact CST5| wp_in_lit| left; reflexivity| eapply cstate_head_fresh; [exact CST5| wp_in_lit]]. }
  assert (APhy0 : wp_apbox (Ah + 384 <= Ay0 \/ Ay0 + 40 <= Ah)).
  { unfold wp_apbox. eapply cstate_apart; [exact CST5| wp_in_lit| left; reflexivity| eapply cstate_head_fresh; [exact CST5| wp_in_lit]]. }
  pose proof CST5 as (HP & _ & (errv5 & _ & _ & ST & _ & _ & MI & _) & _).
  rewrite unsigned_lit in ST by lia.
  pose proof (munch_refl [(Ah, Ah + 384)] m5) as MU. pose proof (wmono_refl usegs m5) as WM.
  apply climpl_from_evt.
  step. step. step. wp_brF. step. step. wp_brF. step. step.
  apply evt_done; cbv beta.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into mw5 end.
  assert (CSa : cstate st5 ((qy0, Ay0, 40) :: (qx0, Ax0, 40) :: (qa0, Aa0, 32) :: (qh, Ah, 4 * 96) :: (qs, As, 24) :: LBall) LB ((qy0, 40) :: (qx0, 40) :: (qa0, 32) :: (qh, 4 * 96) :: (qs, 24) :: L) mw5 (Z_to_bv 64 (bv_unsigned sp + -80)) tp lo B).
  { eapply (cstate_seg _ _ _ _ _ m5 mw5 _ _ tp lo B (bv_unsigned sp)); [exact CST5| exact MU| exact WM| exact MI| | lia| lia| | rewrite SPfU; exact ST| rewrite SPfU; lia].
    - apply Forall_cons; [eapply cwin_block with (b := (qh, Ah, 4 * 96)); [wp_in_lit| cbn; lia| cbn; lia]| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. unfold wp_box in IMGh. repeat split; lia. }
  assert (SFa : cframe (fun _ : bptr => False) [] (bv_unsigned sp) st LBall L m st5 ((qy0, Ay0, 40) :: (qx0, Ax0, 40) :: (qa0, Aa0, 32) :: (qh, Ah, 4 * 96) :: (qs, As, 24) :: LBall) ((qy0, 40) :: (qx0, 40) :: (qa0, 32) :: (qh, 4 * 96) :: (qs, 24) :: L) mw5).
  { eapply cframe_seg; [exact SF| exact MU| exact WM| exact HP| lia|].
    apply Forall_cons; [eapply cseg_ok_block with (b := (qh, Ah, 4 * 96)); [wp_in_lit| | cbn; lia| cbn; lia]|].
    { apply (t_fresh_notin (fun _ : bptr => False) LBall).
      apply (t_nodup_prefix blk_id [(qy0, Ay0, 40); (qx0, Ax0, 40); (qa0, Aa0, 32); (qh, Ah, 4 * 96); (qs, As, 24)] LBall (qh, Ah, 4 * 96)); [exact (proj1 (cstate_nodup _ _ _ _ _ _ _ _ _ CST5))| wp_in_lit]. }
    apply Forall_nil. }
  clear SF MU WM CST5. rename SFa into SF.
  (* call 6: sa *)
  eapply climpl_seq.
  { eapply SAN; [lia| eapply croom_weaken; [exact (croom_grow _ _ _ _ _ _ _ _ ROOM GRc)| wp_wnorm; lia..]| exact CSa| rewrite SPfU; unfold SA_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; lia]. }
  intros f6 L6 st6 ms6 (v6 & m6 & LB6 & RET6 & FU6 & GR6 & CST6 & FRM6 & (qa1 & Aa1 & -> & -> & -> & RNGa1 & CELLa1)).
  destruct RET6 as (r6_0 & r6_1 & r6_2 & r6_3 & r6_4 & r6_5 & r6_6 & r6_7 & r6_8 & r6_9 & r6_10 & r6_11 & r6_12 & r6_13 & ->).
  cret_lit.
  rewrite SPfU in FRM6.
  change (Z.to_nat (32)) with 32%nat in CELLa1.
  pose proof (cframe_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SF FRM6 ltac:(lia) (fun a X => X) (fun q _ X => X)) as SFn.
  pose proof (proj1 FRM6) as CF.
  repeat match goal with
  | H : rw_cells usegs ?mo (bv_unsigned sp + -80) _, CF : cfr _ _ _ _ ?mo ?mn |- _ =>
      apply (cfr_cells_stack _ _ _ _ _ _ _ _ CF) in H; [| lia]
  | H : rw_cells usegs ?mo ?A _, CF : cfr _ _ _ ?LBo ?mo ?mn |- _ =>
      lazymatch LBo with context [(?q, A, ?n)] =>
        apply (cfr_cells_block _ _ _ _ _ _ _ _ (q, A, n) CF) in H; [| wp_in_lit| intros X; exact X| cbn; lia| cbn; lia] end
  end.
  clear CF FRM6 SF CSa HP MI ST. rename SFn into SF.
  assert (FUn : (f <= f6 + 6)%nat) by lia. clear FU6 FUc. rename FUn into FUc.
  assert (GRn : cgrow L ((qa1, 32) :: (qy0, 40) :: (qx0, 40) :: (qa0, 32) :: (qh, 4 * 96) :: (qs, 24) :: L) 5 1 8576) by (eapply cgrow_weaken; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ GRc GR6)| wp_wnorm; lia..]).
  clear GRc GR6. rename GRn into GRc.
  pose proof RNGa1 as (P0a1 & _ & _ & PCa1 & IMGa1). wp_box1 IMGa1.
  assert (APsa1 : wp_apbox (As + 24 <= Aa1 \/ Aa1 + 32 <= As)).
  { unfold wp_apbox. eapply cstate_apart; [exact CST6| wp_in_lit| left; reflexivity| eapply cstate_head_fresh; [exact CST6| wp_in_lit]]. }
  assert (APha1 : wp_apbox (Ah + 384 <= Aa1 \/ Aa1 + 32 <= Ah)).
  { unfold wp_apbox. eapply cstate_apart; [exact CST6| wp_in_lit| left; reflexivity| eapply cstate_head_fresh; [exact CST6| wp_in_lit]]. }
  pose proof CST6 as (HP & _ & (errv6 & _ & _ & ST & _ & _ & MI & _) & _).
  rewrite unsigned_lit in ST by lia.
  pose proof (munch_refl [(Ah, Ah + 384)] m6) as MU. pose proof (wmono_refl usegs m6) as WM.
  apply climpl_from_evt.
  step. wp_brF. step. wp_brF. step. step. step. wp_brF. step.
  apply evt_done; cbv beta.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into mw6 end.
  assert (CSa : cstate st6 ((qa1, Aa1, 32) :: (qy0, Ay0, 40) :: (qx0, Ax0, 40) :: (qa0, Aa0, 32) :: (qh, Ah, 4 * 96) :: (qs, As, 24) :: LBall) LB ((qa1, 32) :: (qy0, 40) :: (qx0, 40) :: (qa0, 32) :: (qh, 4 * 96) :: (qs, 24) :: L) mw6 (Z_to_bv 64 (bv_unsigned sp + -80)) tp lo B).
  { eapply (cstate_seg _ _ _ _ _ m6 mw6 _ _ tp lo B (bv_unsigned sp)); [exact CST6| exact MU| exact WM| exact MI| | lia| lia| | rewrite SPfU; exact ST| rewrite SPfU; lia].
    - apply Forall_cons; [eapply cwin_block with (b := (qh, Ah, 4 * 96)); [wp_in_lit| cbn; lia| cbn; lia]| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. unfold wp_box in IMGh. repeat split; lia. }
  assert (SFa : cframe (fun _ : bptr => False) [] (bv_unsigned sp) st LBall L m st6 ((qa1, Aa1, 32) :: (qy0, Ay0, 40) :: (qx0, Ax0, 40) :: (qa0, Aa0, 32) :: (qh, Ah, 4 * 96) :: (qs, As, 24) :: LBall) ((qa1, 32) :: (qy0, 40) :: (qx0, 40) :: (qa0, 32) :: (qh, 4 * 96) :: (qs, 24) :: L) mw6).
  { eapply cframe_seg; [exact SF| exact MU| exact WM| exact HP| lia|].
    apply Forall_cons; [eapply cseg_ok_block with (b := (qh, Ah, 4 * 96)); [wp_in_lit| | cbn; lia| cbn; lia]|].
    { apply (t_fresh_notin (fun _ : bptr => False) LBall).
      apply (t_nodup_prefix blk_id [(qa1, Aa1, 32); (qy0, Ay0, 40); (qx0, Ax0, 40); (qa0, Aa0, 32); (qh, Ah, 4 * 96); (qs, As, 24)] LBall (qh, Ah, 4 * 96)); [exact (proj1 (cstate_nodup _ _ _ _ _ _ _ _ _ CST6))| wp_in_lit]. }
    apply Forall_nil. }
  clear SF MU WM CST6. rename SFa into SF.
  (* call 7: lock *)
  eapply climpl_seq.
  { eapply LKN; [lia| eapply croom_weaken; [exact (croom_grow _ _ _ _ _ _ _ _ ROOM GRc)| wp_wnorm; lia..]| exact CSa| rewrite SPfU; unfold LOCK_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; lia]. }
  intros f7 L7 st7 ms7 (v7 & m7 & LB7 & RET7 & FU7 & GR7 & CST7 & FRM7 & (qx1 & Ax1 & -> & -> & -> & RNGx1 & CELLx1)).
  destruct RET7 as (r7_0 & r7_1 & r7_2 & r7_3 & r7_4 & r7_5 & r7_6 & r7_7 & r7_8 & r7_9 & r7_10 & r7_11 & r7_12 & r7_13 & ->).
  cret_lit.
  rewrite SPfU in FRM7.
  pose proof (cframe_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SF FRM7 ltac:(lia) (fun a X => X) (fun q _ X => X)) as SFn.
  pose proof (proj1 FRM7) as CF.
  repeat match goal with
  | H : rw_cells usegs ?mo (bv_unsigned sp + -80) _, CF : cfr _ _ _ _ ?mo ?mn |- _ =>
      apply (cfr_cells_stack _ _ _ _ _ _ _ _ CF) in H; [| lia]
  | H : rw_cells usegs ?mo ?A _, CF : cfr _ _ _ ?LBo ?mo ?mn |- _ =>
      lazymatch LBo with context [(?q, A, ?n)] =>
        apply (cfr_cells_block _ _ _ _ _ _ _ _ (q, A, n) CF) in H; [| wp_in_lit| intros X; exact X| cbn; lia| cbn; lia] end
  end.
  clear CF FRM7 SF CSa HP MI ST. rename SFn into SF.
  assert (FUn : (f <= f7 + 7)%nat) by lia. clear FU7 FUc. rename FUn into FUc.
  assert (GRn : cgrow L ((qx1, 40) :: (qa1, 32) :: (qy0, 40) :: (qx0, 40) :: (qa0, 32) :: (qh, 4 * 96) :: (qs, 24) :: L) 6 1 8576) by (eapply cgrow_weaken; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ GRc GR7)| wp_wnorm; lia..]).
  clear GRc GR7. rename GRn into GRc.
  pose proof RNGx1 as (P0x1 & _ & _ & PCx1 & IMGx1). wp_box1 IMGx1.
  assert (APsx1 : wp_apbox (As + 24 <= Ax1 \/ Ax1 + 40 <= As)).
  { unfold wp_apbox. eapply cstate_apart; [exact CST7| wp_in_lit| left; reflexivity| eapply cstate_head_fresh; [exact CST7| wp_in_lit]]. }
  assert (APhx1 : wp_apbox (Ah + 384 <= Ax1 \/ Ax1 + 40 <= Ah)).
  { unfold wp_apbox. eapply cstate_apart; [exact CST7| wp_in_lit| left; reflexivity| eapply cstate_head_fresh; [exact CST7| wp_in_lit]]. }
  pose proof CST7 as (HP & _ & (errv7 & _ & _ & ST & _ & _ & MI & _) & _).
  rewrite unsigned_lit in ST by lia.
  pose proof (munch_refl [(Ah, Ah + 384)] m7) as MU. pose proof (wmono_refl usegs m7) as WM.
  apply climpl_from_evt.
  step. step. step. wp_brF. step.
  apply evt_done; cbv beta.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into mw7 end.
  assert (CSa : cstate st7 ((qx1, Ax1, 40) :: (qa1, Aa1, 32) :: (qy0, Ay0, 40) :: (qx0, Ax0, 40) :: (qa0, Aa0, 32) :: (qh, Ah, 4 * 96) :: (qs, As, 24) :: LBall) LB ((qx1, 40) :: (qa1, 32) :: (qy0, 40) :: (qx0, 40) :: (qa0, 32) :: (qh, 4 * 96) :: (qs, 24) :: L) mw7 (Z_to_bv 64 (bv_unsigned sp + -80)) tp lo B).
  { eapply (cstate_seg _ _ _ _ _ m7 mw7 _ _ tp lo B (bv_unsigned sp)); [exact CST7| exact MU| exact WM| exact MI| | lia| lia| | rewrite SPfU; exact ST| rewrite SPfU; lia].
    - apply Forall_cons; [eapply cwin_block with (b := (qh, Ah, 4 * 96)); [wp_in_lit| cbn; lia| cbn; lia]| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. unfold wp_box in IMGh. repeat split; lia. }
  assert (SFa : cframe (fun _ : bptr => False) [] (bv_unsigned sp) st LBall L m st7 ((qx1, Ax1, 40) :: (qa1, Aa1, 32) :: (qy0, Ay0, 40) :: (qx0, Ax0, 40) :: (qa0, Aa0, 32) :: (qh, Ah, 4 * 96) :: (qs, As, 24) :: LBall) ((qx1, 40) :: (qa1, 32) :: (qy0, 40) :: (qx0, 40) :: (qa0, 32) :: (qh, 4 * 96) :: (qs, 24) :: L) mw7).
  { eapply cframe_seg; [exact SF| exact MU| exact WM| exact HP| lia|].
    apply Forall_cons; [eapply cseg_ok_block with (b := (qh, Ah, 4 * 96)); [wp_in_lit| | cbn; lia| cbn; lia]|].
    { apply (t_fresh_notin (fun _ : bptr => False) LBall).
      apply (t_nodup_prefix blk_id [(qx1, Ax1, 40); (qa1, Aa1, 32); (qy0, Ay0, 40); (qx0, Ax0, 40); (qa0, Aa0, 32); (qh, Ah, 4 * 96); (qs, As, 24)] LBall (qh, Ah, 4 * 96)); [exact (proj1 (cstate_nodup _ _ _ _ _ _ _ _ _ CST7))| wp_in_lit]. }
    apply Forall_nil. }
  clear SF MU WM CST7. rename SFa into SF.
  (* call 8: lock *)
  eapply climpl_seq.
  { eapply LKN; [lia| eapply croom_weaken; [exact (croom_grow _ _ _ _ _ _ _ _ ROOM GRc)| wp_wnorm; lia..]| exact CSa| rewrite SPfU; unfold LOCK_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; lia]. }
  intros f8 L8 st8 ms8 (v8 & m8 & LB8 & RET8 & FU8 & GR8 & CST8 & FRM8 & (qy1 & Ay1 & -> & -> & -> & RNGy1 & CELLy1)).
  destruct RET8 as (r8_0 & r8_1 & r8_2 & r8_3 & r8_4 & r8_5 & r8_6 & r8_7 & r8_8 & r8_9 & r8_10 & r8_11 & r8_12 & r8_13 & ->).
  cret_lit.
  rewrite SPfU in FRM8.
  pose proof (cframe_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SF FRM8 ltac:(lia) (fun a X => X) (fun q _ X => X)) as SFn.
  pose proof (proj1 FRM8) as CF.
  repeat match goal with
  | H : rw_cells usegs ?mo (bv_unsigned sp + -80) _, CF : cfr _ _ _ _ ?mo ?mn |- _ =>
      apply (cfr_cells_stack _ _ _ _ _ _ _ _ CF) in H; [| lia]
  | H : rw_cells usegs ?mo ?A _, CF : cfr _ _ _ ?LBo ?mo ?mn |- _ =>
      lazymatch LBo with context [(?q, A, ?n)] =>
        apply (cfr_cells_block _ _ _ _ _ _ _ _ (q, A, n) CF) in H; [| wp_in_lit| intros X; exact X| cbn; lia| cbn; lia] end
  end.
  clear CF FRM8 SF CSa HP MI ST. rename SFn into SF.
  assert (FUn : (f <= f8 + 8)%nat) by lia. clear FU8 FUc. rename FUn into FUc.
  assert (GRn : cgrow L ((qy1, 40) :: (qx1, 40) :: (qa1, 32) :: (qy0, 40) :: (qx0, 40) :: (qa0, 32) :: (qh, 4 * 96) :: (qs, 24) :: L) 7 1 8576) by (eapply cgrow_weaken; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ GRc GR8)| wp_wnorm; lia..]).
  clear GRc GR8. rename GRn into GRc.
  pose proof RNGy1 as (P0y1 & _ & _ & PCy1 & IMGy1). wp_box1 IMGy1.
  assert (APsy1 : wp_apbox (As + 24 <= Ay1 \/ Ay1 + 40 <= As)).
  { unfold wp_apbox. eapply cstate_apart; [exact CST8| wp_in_lit| left; reflexivity| eapply cstate_head_fresh; [exact CST8| wp_in_lit]]. }
  assert (APhy1 : wp_apbox (Ah + 384 <= Ay1 \/ Ay1 + 40 <= Ah)).
  { unfold wp_apbox. eapply cstate_apart; [exact CST8| wp_in_lit| left; reflexivity| eapply cstate_head_fresh; [exact CST8| wp_in_lit]]. }
  pose proof CST8 as (HP & _ & (errv8 & _ & _ & ST & _ & _ & MI & _) & _).
  rewrite unsigned_lit in ST by lia.
  pose proof (munch_refl [(Ah, Ah + 384)] m8) as MU. pose proof (wmono_refl usegs m8) as WM.
  apply climpl_from_evt.
  step. step. step. wp_brF. step. step. wp_brF. step. step.
  apply evt_done; cbv beta.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into mw8 end.
  assert (CSa : cstate st8 ((qy1, Ay1, 40) :: (qx1, Ax1, 40) :: (qa1, Aa1, 32) :: (qy0, Ay0, 40) :: (qx0, Ax0, 40) :: (qa0, Aa0, 32) :: (qh, Ah, 4 * 96) :: (qs, As, 24) :: LBall) LB ((qy1, 40) :: (qx1, 40) :: (qa1, 32) :: (qy0, 40) :: (qx0, 40) :: (qa0, 32) :: (qh, 4 * 96) :: (qs, 24) :: L) mw8 (Z_to_bv 64 (bv_unsigned sp + -80)) tp lo B).
  { eapply (cstate_seg _ _ _ _ _ m8 mw8 _ _ tp lo B (bv_unsigned sp)); [exact CST8| exact MU| exact WM| exact MI| | lia| lia| | rewrite SPfU; exact ST| rewrite SPfU; lia].
    - apply Forall_cons; [eapply cwin_block with (b := (qh, Ah, 4 * 96)); [wp_in_lit| cbn; lia| cbn; lia]| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. unfold wp_box in IMGh. repeat split; lia. }
  assert (SFa : cframe (fun _ : bptr => False) [] (bv_unsigned sp) st LBall L m st8 ((qy1, Ay1, 40) :: (qx1, Ax1, 40) :: (qa1, Aa1, 32) :: (qy0, Ay0, 40) :: (qx0, Ax0, 40) :: (qa0, Aa0, 32) :: (qh, Ah, 4 * 96) :: (qs, As, 24) :: LBall) ((qy1, 40) :: (qx1, 40) :: (qa1, 32) :: (qy0, 40) :: (qx0, 40) :: (qa0, 32) :: (qh, 4 * 96) :: (qs, 24) :: L) mw8).
  { eapply cframe_seg; [exact SF| exact MU| exact WM| exact HP| lia|].
    apply Forall_cons; [eapply cseg_ok_block with (b := (qh, Ah, 4 * 96)); [wp_in_lit| | cbn; lia| cbn; lia]|].
    { apply (t_fresh_notin (fun _ : bptr => False) LBall).
      apply (t_nodup_prefix blk_id [(qy1, Ay1, 40); (qx1, Ax1, 40); (qa1, Aa1, 32); (qy0, Ay0, 40); (qx0, Ax0, 40); (qa0, Aa0, 32); (qh, Ah, 4 * 96); (qs, As, 24)] LBall (qh, Ah, 4 * 96)); [exact (proj1 (cstate_nodup _ _ _ _ _ _ _ _ _ CST8))| wp_in_lit]. }
    apply Forall_nil. }
  clear SF MU WM CST8. rename SFa into SF.
  (* call 9: sa *)
  eapply climpl_seq.
  { eapply SAN; [lia| eapply croom_weaken; [exact (croom_grow _ _ _ _ _ _ _ _ ROOM GRc)| wp_wnorm; lia..]| exact CSa| rewrite SPfU; unfold SA_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; lia]. }
  intros f9 L9 st9 ms9 (v9 & m9 & LB9 & RET9 & FU9 & GR9 & CST9 & FRM9 & (qa2 & Aa2 & -> & -> & -> & RNGa2 & CELLa2)).
  destruct RET9 as (r9_0 & r9_1 & r9_2 & r9_3 & r9_4 & r9_5 & r9_6 & r9_7 & r9_8 & r9_9 & r9_10 & r9_11 & r9_12 & r9_13 & ->).
  cret_lit.
  rewrite SPfU in FRM9.
  change (Z.to_nat (32)) with 32%nat in CELLa2.
  pose proof (cframe_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SF FRM9 ltac:(lia) (fun a X => X) (fun q _ X => X)) as SFn.
  pose proof (proj1 FRM9) as CF.
  repeat match goal with
  | H : rw_cells usegs ?mo (bv_unsigned sp + -80) _, CF : cfr _ _ _ _ ?mo ?mn |- _ =>
      apply (cfr_cells_stack _ _ _ _ _ _ _ _ CF) in H; [| lia]
  | H : rw_cells usegs ?mo ?A _, CF : cfr _ _ _ ?LBo ?mo ?mn |- _ =>
      lazymatch LBo with context [(?q, A, ?n)] =>
        apply (cfr_cells_block _ _ _ _ _ _ _ _ (q, A, n) CF) in H; [| wp_in_lit| intros X; exact X| cbn; lia| cbn; lia] end
  end.
  clear CF FRM9 SF CSa HP MI ST. rename SFn into SF.
  assert (FUn : (f <= f9 + 9)%nat) by lia. clear FU9 FUc. rename FUn into FUc.
  assert (GRn : cgrow L ((qa2, 32) :: (qy1, 40) :: (qx1, 40) :: (qa1, 32) :: (qy0, 40) :: (qx0, 40) :: (qa0, 32) :: (qh, 4 * 96) :: (qs, 24) :: L) 8 1 8576) by (eapply cgrow_weaken; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ GRc GR9)| wp_wnorm; lia..]).
  clear GRc GR9. rename GRn into GRc.
  pose proof RNGa2 as (P0a2 & _ & _ & PCa2 & IMGa2). wp_box1 IMGa2.
  assert (APsa2 : wp_apbox (As + 24 <= Aa2 \/ Aa2 + 32 <= As)).
  { unfold wp_apbox. eapply cstate_apart; [exact CST9| wp_in_lit| left; reflexivity| eapply cstate_head_fresh; [exact CST9| wp_in_lit]]. }
  assert (APha2 : wp_apbox (Ah + 384 <= Aa2 \/ Aa2 + 32 <= Ah)).
  { unfold wp_apbox. eapply cstate_apart; [exact CST9| wp_in_lit| left; reflexivity| eapply cstate_head_fresh; [exact CST9| wp_in_lit]]. }
  pose proof CST9 as (HP & _ & (errv9 & _ & _ & ST & _ & _ & MI & _) & _).
  rewrite unsigned_lit in ST by lia.
  pose proof (munch_refl [(Ah, Ah + 384)] m9) as MU. pose proof (wmono_refl usegs m9) as WM.
  apply climpl_from_evt.
  step. wp_brF. step. wp_brF. step. step. step. wp_brF. step.
  apply evt_done; cbv beta.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into mw9 end.
  assert (CSa : cstate st9 ((qa2, Aa2, 32) :: (qy1, Ay1, 40) :: (qx1, Ax1, 40) :: (qa1, Aa1, 32) :: (qy0, Ay0, 40) :: (qx0, Ax0, 40) :: (qa0, Aa0, 32) :: (qh, Ah, 4 * 96) :: (qs, As, 24) :: LBall) LB ((qa2, 32) :: (qy1, 40) :: (qx1, 40) :: (qa1, 32) :: (qy0, 40) :: (qx0, 40) :: (qa0, 32) :: (qh, 4 * 96) :: (qs, 24) :: L) mw9 (Z_to_bv 64 (bv_unsigned sp + -80)) tp lo B).
  { eapply (cstate_seg _ _ _ _ _ m9 mw9 _ _ tp lo B (bv_unsigned sp)); [exact CST9| exact MU| exact WM| exact MI| | lia| lia| | rewrite SPfU; exact ST| rewrite SPfU; lia].
    - apply Forall_cons; [eapply cwin_block with (b := (qh, Ah, 4 * 96)); [wp_in_lit| cbn; lia| cbn; lia]| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. unfold wp_box in IMGh. repeat split; lia. }
  assert (SFa : cframe (fun _ : bptr => False) [] (bv_unsigned sp) st LBall L m st9 ((qa2, Aa2, 32) :: (qy1, Ay1, 40) :: (qx1, Ax1, 40) :: (qa1, Aa1, 32) :: (qy0, Ay0, 40) :: (qx0, Ax0, 40) :: (qa0, Aa0, 32) :: (qh, Ah, 4 * 96) :: (qs, As, 24) :: LBall) ((qa2, 32) :: (qy1, 40) :: (qx1, 40) :: (qa1, 32) :: (qy0, 40) :: (qx0, 40) :: (qa0, 32) :: (qh, 4 * 96) :: (qs, 24) :: L) mw9).
  { eapply cframe_seg; [exact SF| exact MU| exact WM| exact HP| lia|].
    apply Forall_cons; [eapply cseg_ok_block with (b := (qh, Ah, 4 * 96)); [wp_in_lit| | cbn; lia| cbn; lia]|].
    { apply (t_fresh_notin (fun _ : bptr => False) LBall).
      apply (t_nodup_prefix blk_id [(qa2, Aa2, 32); (qy1, Ay1, 40); (qx1, Ax1, 40); (qa1, Aa1, 32); (qy0, Ay0, 40); (qx0, Ax0, 40); (qa0, Aa0, 32); (qh, Ah, 4 * 96); (qs, As, 24)] LBall (qh, Ah, 4 * 96)); [exact (proj1 (cstate_nodup _ _ _ _ _ _ _ _ _ CST9))| wp_in_lit]. }
    apply Forall_nil. }
  clear SF MU WM CST9. rename SFa into SF.
  (* call 10: lock *)
  eapply climpl_seq.
  { eapply LKN; [lia| eapply croom_weaken; [exact (croom_grow _ _ _ _ _ _ _ _ ROOM GRc)| wp_wnorm; lia..]| exact CSa| rewrite SPfU; unfold LOCK_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; lia]. }
  intros f10 L10 st10 ms10 (v10 & m10 & LB10 & RET10 & FU10 & GR10 & CST10 & FRM10 & (qx2 & Ax2 & -> & -> & -> & RNGx2 & CELLx2)).
  destruct RET10 as (r10_0 & r10_1 & r10_2 & r10_3 & r10_4 & r10_5 & r10_6 & r10_7 & r10_8 & r10_9 & r10_10 & r10_11 & r10_12 & r10_13 & ->).
  cret_lit.
  rewrite SPfU in FRM10.
  pose proof (cframe_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SF FRM10 ltac:(lia) (fun a X => X) (fun q _ X => X)) as SFn.
  pose proof (proj1 FRM10) as CF.
  repeat match goal with
  | H : rw_cells usegs ?mo (bv_unsigned sp + -80) _, CF : cfr _ _ _ _ ?mo ?mn |- _ =>
      apply (cfr_cells_stack _ _ _ _ _ _ _ _ CF) in H; [| lia]
  | H : rw_cells usegs ?mo ?A _, CF : cfr _ _ _ ?LBo ?mo ?mn |- _ =>
      lazymatch LBo with context [(?q, A, ?n)] =>
        apply (cfr_cells_block _ _ _ _ _ _ _ _ (q, A, n) CF) in H; [| wp_in_lit| intros X; exact X| cbn; lia| cbn; lia] end
  end.
  clear CF FRM10 SF CSa HP MI ST. rename SFn into SF.
  assert (FUn : (f <= f10 + 10)%nat) by lia. clear FU10 FUc. rename FUn into FUc.
  assert (GRn : cgrow L ((qx2, 40) :: (qa2, 32) :: (qy1, 40) :: (qx1, 40) :: (qa1, 32) :: (qy0, 40) :: (qx0, 40) :: (qa0, 32) :: (qh, 4 * 96) :: (qs, 24) :: L) 9 1 8576) by (eapply cgrow_weaken; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ GRc GR10)| wp_wnorm; lia..]).
  clear GRc GR10. rename GRn into GRc.
  pose proof RNGx2 as (P0x2 & _ & _ & PCx2 & IMGx2). wp_box1 IMGx2.
  assert (APsx2 : wp_apbox (As + 24 <= Ax2 \/ Ax2 + 40 <= As)).
  { unfold wp_apbox. eapply cstate_apart; [exact CST10| wp_in_lit| left; reflexivity| eapply cstate_head_fresh; [exact CST10| wp_in_lit]]. }
  assert (APhx2 : wp_apbox (Ah + 384 <= Ax2 \/ Ax2 + 40 <= Ah)).
  { unfold wp_apbox. eapply cstate_apart; [exact CST10| wp_in_lit| left; reflexivity| eapply cstate_head_fresh; [exact CST10| wp_in_lit]]. }
  pose proof CST10 as (HP & _ & (errv10 & _ & _ & ST & _ & _ & MI & _) & _).
  rewrite unsigned_lit in ST by lia.
  pose proof (munch_refl [(Ah, Ah + 384)] m10) as MU. pose proof (wmono_refl usegs m10) as WM.
  apply climpl_from_evt.
  step. step. step. wp_brF. step.
  apply evt_done; cbv beta.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into mw10 end.
  assert (CSa : cstate st10 ((qx2, Ax2, 40) :: (qa2, Aa2, 32) :: (qy1, Ay1, 40) :: (qx1, Ax1, 40) :: (qa1, Aa1, 32) :: (qy0, Ay0, 40) :: (qx0, Ax0, 40) :: (qa0, Aa0, 32) :: (qh, Ah, 4 * 96) :: (qs, As, 24) :: LBall) LB ((qx2, 40) :: (qa2, 32) :: (qy1, 40) :: (qx1, 40) :: (qa1, 32) :: (qy0, 40) :: (qx0, 40) :: (qa0, 32) :: (qh, 4 * 96) :: (qs, 24) :: L) mw10 (Z_to_bv 64 (bv_unsigned sp + -80)) tp lo B).
  { eapply (cstate_seg _ _ _ _ _ m10 mw10 _ _ tp lo B (bv_unsigned sp)); [exact CST10| exact MU| exact WM| exact MI| | lia| lia| | rewrite SPfU; exact ST| rewrite SPfU; lia].
    - apply Forall_cons; [eapply cwin_block with (b := (qh, Ah, 4 * 96)); [wp_in_lit| cbn; lia| cbn; lia]| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. unfold wp_box in IMGh. repeat split; lia. }
  assert (SFa : cframe (fun _ : bptr => False) [] (bv_unsigned sp) st LBall L m st10 ((qx2, Ax2, 40) :: (qa2, Aa2, 32) :: (qy1, Ay1, 40) :: (qx1, Ax1, 40) :: (qa1, Aa1, 32) :: (qy0, Ay0, 40) :: (qx0, Ax0, 40) :: (qa0, Aa0, 32) :: (qh, Ah, 4 * 96) :: (qs, As, 24) :: LBall) ((qx2, 40) :: (qa2, 32) :: (qy1, 40) :: (qx1, 40) :: (qa1, 32) :: (qy0, 40) :: (qx0, 40) :: (qa0, 32) :: (qh, 4 * 96) :: (qs, 24) :: L) mw10).
  { eapply cframe_seg; [exact SF| exact MU| exact WM| exact HP| lia|].
    apply Forall_cons; [eapply cseg_ok_block with (b := (qh, Ah, 4 * 96)); [wp_in_lit| | cbn; lia| cbn; lia]|].
    { apply (t_fresh_notin (fun _ : bptr => False) LBall).
      apply (t_nodup_prefix blk_id [(qx2, Ax2, 40); (qa2, Aa2, 32); (qy1, Ay1, 40); (qx1, Ax1, 40); (qa1, Aa1, 32); (qy0, Ay0, 40); (qx0, Ax0, 40); (qa0, Aa0, 32); (qh, Ah, 4 * 96); (qs, As, 24)] LBall (qh, Ah, 4 * 96)); [exact (proj1 (cstate_nodup _ _ _ _ _ _ _ _ _ CST10))| wp_in_lit]. }
    apply Forall_nil. }
  clear SF MU WM CST10. rename SFa into SF.
  (* call 11: lock *)
  eapply climpl_seq.
  { eapply LKN; [lia| eapply croom_weaken; [exact (croom_grow _ _ _ _ _ _ _ _ ROOM GRc)| wp_wnorm; lia..]| exact CSa| rewrite SPfU; unfold LOCK_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; lia]. }
  intros f11 L11 st11 ms11 (v11 & m11 & LB11 & RET11 & FU11 & GR11 & CST11 & FRM11 & (qy2 & Ay2 & -> & -> & -> & RNGy2 & CELLy2)).
  destruct RET11 as (r11_0 & r11_1 & r11_2 & r11_3 & r11_4 & r11_5 & r11_6 & r11_7 & r11_8 & r11_9 & r11_10 & r11_11 & r11_12 & r11_13 & ->).
  cret_lit.
  rewrite SPfU in FRM11.
  pose proof (cframe_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SF FRM11 ltac:(lia) (fun a X => X) (fun q _ X => X)) as SFn.
  pose proof (proj1 FRM11) as CF.
  repeat match goal with
  | H : rw_cells usegs ?mo (bv_unsigned sp + -80) _, CF : cfr _ _ _ _ ?mo ?mn |- _ =>
      apply (cfr_cells_stack _ _ _ _ _ _ _ _ CF) in H; [| lia]
  | H : rw_cells usegs ?mo ?A _, CF : cfr _ _ _ ?LBo ?mo ?mn |- _ =>
      lazymatch LBo with context [(?q, A, ?n)] =>
        apply (cfr_cells_block _ _ _ _ _ _ _ _ (q, A, n) CF) in H; [| wp_in_lit| intros X; exact X| cbn; lia| cbn; lia] end
  end.
  clear CF FRM11 SF CSa HP MI ST. rename SFn into SF.
  assert (FUn : (f <= f11 + 11)%nat) by lia. clear FU11 FUc. rename FUn into FUc.
  assert (GRn : cgrow L ((qy2, 40) :: (qx2, 40) :: (qa2, 32) :: (qy1, 40) :: (qx1, 40) :: (qa1, 32) :: (qy0, 40) :: (qx0, 40) :: (qa0, 32) :: (qh, 4 * 96) :: (qs, 24) :: L) 10 1 8576) by (eapply cgrow_weaken; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ GRc GR11)| wp_wnorm; lia..]).
  clear GRc GR11. rename GRn into GRc.
  pose proof RNGy2 as (P0y2 & _ & _ & PCy2 & IMGy2). wp_box1 IMGy2.
  assert (APsy2 : wp_apbox (As + 24 <= Ay2 \/ Ay2 + 40 <= As)).
  { unfold wp_apbox. eapply cstate_apart; [exact CST11| wp_in_lit| left; reflexivity| eapply cstate_head_fresh; [exact CST11| wp_in_lit]]. }
  assert (APhy2 : wp_apbox (Ah + 384 <= Ay2 \/ Ay2 + 40 <= Ah)).
  { unfold wp_apbox. eapply cstate_apart; [exact CST11| wp_in_lit| left; reflexivity| eapply cstate_head_fresh; [exact CST11| wp_in_lit]]. }
  pose proof CST11 as (HP & _ & (errv11 & _ & _ & ST & _ & _ & MI & _) & _).
  rewrite unsigned_lit in ST by lia.
  pose proof (munch_refl [(Ah, Ah + 384)] m11) as MU. pose proof (wmono_refl usegs m11) as WM.
  apply climpl_from_evt.
  step. step. step. wp_brF. step. step. wp_brF. step. step.
  apply evt_done; cbv beta.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into mw11 end.
  assert (CSa : cstate st11 ((qy2, Ay2, 40) :: (qx2, Ax2, 40) :: (qa2, Aa2, 32) :: (qy1, Ay1, 40) :: (qx1, Ax1, 40) :: (qa1, Aa1, 32) :: (qy0, Ay0, 40) :: (qx0, Ax0, 40) :: (qa0, Aa0, 32) :: (qh, Ah, 4 * 96) :: (qs, As, 24) :: LBall) LB ((qy2, 40) :: (qx2, 40) :: (qa2, 32) :: (qy1, 40) :: (qx1, 40) :: (qa1, 32) :: (qy0, 40) :: (qx0, 40) :: (qa0, 32) :: (qh, 4 * 96) :: (qs, 24) :: L) mw11 (Z_to_bv 64 (bv_unsigned sp + -80)) tp lo B).
  { eapply (cstate_seg _ _ _ _ _ m11 mw11 _ _ tp lo B (bv_unsigned sp)); [exact CST11| exact MU| exact WM| exact MI| | lia| lia| | rewrite SPfU; exact ST| rewrite SPfU; lia].
    - apply Forall_cons; [eapply cwin_block with (b := (qh, Ah, 4 * 96)); [wp_in_lit| cbn; lia| cbn; lia]| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. unfold wp_box in IMGh. repeat split; lia. }
  assert (SFa : cframe (fun _ : bptr => False) [] (bv_unsigned sp) st LBall L m st11 ((qy2, Ay2, 40) :: (qx2, Ax2, 40) :: (qa2, Aa2, 32) :: (qy1, Ay1, 40) :: (qx1, Ax1, 40) :: (qa1, Aa1, 32) :: (qy0, Ay0, 40) :: (qx0, Ax0, 40) :: (qa0, Aa0, 32) :: (qh, Ah, 4 * 96) :: (qs, As, 24) :: LBall) ((qy2, 40) :: (qx2, 40) :: (qa2, 32) :: (qy1, 40) :: (qx1, 40) :: (qa1, 32) :: (qy0, 40) :: (qx0, 40) :: (qa0, 32) :: (qh, 4 * 96) :: (qs, 24) :: L) mw11).
  { eapply cframe_seg; [exact SF| exact MU| exact WM| exact HP| lia|].
    apply Forall_cons; [eapply cseg_ok_block with (b := (qh, Ah, 4 * 96)); [wp_in_lit| | cbn; lia| cbn; lia]|].
    { apply (t_fresh_notin (fun _ : bptr => False) LBall).
      apply (t_nodup_prefix blk_id [(qy2, Ay2, 40); (qx2, Ax2, 40); (qa2, Aa2, 32); (qy1, Ay1, 40); (qx1, Ax1, 40); (qa1, Aa1, 32); (qy0, Ay0, 40); (qx0, Ax0, 40); (qa0, Aa0, 32); (qh, Ah, 4 * 96); (qs, As, 24)] LBall (qh, Ah, 4 * 96)); [exact (proj1 (cstate_nodup _ _ _ _ _ _ _ _ _ CST11))| wp_in_lit]. }
    apply Forall_nil. }
  clear SF MU WM CST11. rename SFa into SF.
  (* call 12: sa *)
  eapply climpl_seq.
  { eapply SAN; [lia| eapply croom_weaken; [exact (croom_grow _ _ _ _ _ _ _ _ ROOM GRc)| wp_wnorm; lia..]| exact CSa| rewrite SPfU; unfold SA_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; lia]. }
  intros f12 L12 st12 ms12 (v12 & m12 & LB12 & RET12 & FU12 & GR12 & CST12 & FRM12 & (qa3 & Aa3 & -> & -> & -> & RNGa3 & CELLa3)).
  destruct RET12 as (r12_0 & r12_1 & r12_2 & r12_3 & r12_4 & r12_5 & r12_6 & r12_7 & r12_8 & r12_9 & r12_10 & r12_11 & r12_12 & r12_13 & ->).
  cret_lit.
  rewrite SPfU in FRM12.
  change (Z.to_nat (32)) with 32%nat in CELLa3.
  pose proof (cframe_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SF FRM12 ltac:(lia) (fun a X => X) (fun q _ X => X)) as SFn.
  pose proof (proj1 FRM12) as CF.
  repeat match goal with
  | H : rw_cells usegs ?mo (bv_unsigned sp + -80) _, CF : cfr _ _ _ _ ?mo ?mn |- _ =>
      apply (cfr_cells_stack _ _ _ _ _ _ _ _ CF) in H; [| lia]
  | H : rw_cells usegs ?mo ?A _, CF : cfr _ _ _ ?LBo ?mo ?mn |- _ =>
      lazymatch LBo with context [(?q, A, ?n)] =>
        apply (cfr_cells_block _ _ _ _ _ _ _ _ (q, A, n) CF) in H; [| wp_in_lit| intros X; exact X| cbn; lia| cbn; lia] end
  end.
  clear CF FRM12 SF CSa HP MI ST. rename SFn into SF.
  assert (FUn : (f <= f12 + 12)%nat) by lia. clear FU12 FUc. rename FUn into FUc.
  assert (GRn : cgrow L ((qa3, 32) :: (qy2, 40) :: (qx2, 40) :: (qa2, 32) :: (qy1, 40) :: (qx1, 40) :: (qa1, 32) :: (qy0, 40) :: (qx0, 40) :: (qa0, 32) :: (qh, 4 * 96) :: (qs, 24) :: L) 11 1 8576) by (eapply cgrow_weaken; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ GRc GR12)| wp_wnorm; lia..]).
  clear GRc GR12. rename GRn into GRc.
  pose proof RNGa3 as (P0a3 & _ & _ & PCa3 & IMGa3). wp_box1 IMGa3.
  assert (APsa3 : wp_apbox (As + 24 <= Aa3 \/ Aa3 + 32 <= As)).
  { unfold wp_apbox. eapply cstate_apart; [exact CST12| wp_in_lit| left; reflexivity| eapply cstate_head_fresh; [exact CST12| wp_in_lit]]. }
  assert (APha3 : wp_apbox (Ah + 384 <= Aa3 \/ Aa3 + 32 <= Ah)).
  { unfold wp_apbox. eapply cstate_apart; [exact CST12| wp_in_lit| left; reflexivity| eapply cstate_head_fresh; [exact CST12| wp_in_lit]]. }
  pose proof CST12 as (HP & _ & (errv12 & _ & _ & ST & _ & _ & MI & _) & _).
  rewrite unsigned_lit in ST by lia.
  pose proof (munch_refl [(Ah, Ah + 384)] m12) as MU. pose proof (wmono_refl usegs m12) as WM.
  apply climpl_from_evt.
  step. wp_brF. step. wp_brF. step. step. step. wp_brF. step.
  apply evt_done; cbv beta.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into mw12 end.
  assert (CSa : cstate st12 ((qa3, Aa3, 32) :: (qy2, Ay2, 40) :: (qx2, Ax2, 40) :: (qa2, Aa2, 32) :: (qy1, Ay1, 40) :: (qx1, Ax1, 40) :: (qa1, Aa1, 32) :: (qy0, Ay0, 40) :: (qx0, Ax0, 40) :: (qa0, Aa0, 32) :: (qh, Ah, 4 * 96) :: (qs, As, 24) :: LBall) LB ((qa3, 32) :: (qy2, 40) :: (qx2, 40) :: (qa2, 32) :: (qy1, 40) :: (qx1, 40) :: (qa1, 32) :: (qy0, 40) :: (qx0, 40) :: (qa0, 32) :: (qh, 4 * 96) :: (qs, 24) :: L) mw12 (Z_to_bv 64 (bv_unsigned sp + -80)) tp lo B).
  { eapply (cstate_seg _ _ _ _ _ m12 mw12 _ _ tp lo B (bv_unsigned sp)); [exact CST12| exact MU| exact WM| exact MI| | lia| lia| | rewrite SPfU; exact ST| rewrite SPfU; lia].
    - apply Forall_cons; [eapply cwin_block with (b := (qh, Ah, 4 * 96)); [wp_in_lit| cbn; lia| cbn; lia]| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. unfold wp_box in IMGh. repeat split; lia. }
  assert (SFa : cframe (fun _ : bptr => False) [] (bv_unsigned sp) st LBall L m st12 ((qa3, Aa3, 32) :: (qy2, Ay2, 40) :: (qx2, Ax2, 40) :: (qa2, Aa2, 32) :: (qy1, Ay1, 40) :: (qx1, Ax1, 40) :: (qa1, Aa1, 32) :: (qy0, Ay0, 40) :: (qx0, Ax0, 40) :: (qa0, Aa0, 32) :: (qh, Ah, 4 * 96) :: (qs, As, 24) :: LBall) ((qa3, 32) :: (qy2, 40) :: (qx2, 40) :: (qa2, 32) :: (qy1, 40) :: (qx1, 40) :: (qa1, 32) :: (qy0, 40) :: (qx0, 40) :: (qa0, 32) :: (qh, 4 * 96) :: (qs, 24) :: L) mw12).
  { eapply cframe_seg; [exact SF| exact MU| exact WM| exact HP| lia|].
    apply Forall_cons; [eapply cseg_ok_block with (b := (qh, Ah, 4 * 96)); [wp_in_lit| | cbn; lia| cbn; lia]|].
    { apply (t_fresh_notin (fun _ : bptr => False) LBall).
      apply (t_nodup_prefix blk_id [(qa3, Aa3, 32); (qy2, Ay2, 40); (qx2, Ax2, 40); (qa2, Aa2, 32); (qy1, Ay1, 40); (qx1, Ax1, 40); (qa1, Aa1, 32); (qy0, Ay0, 40); (qx0, Ax0, 40); (qa0, Aa0, 32); (qh, Ah, 4 * 96); (qs, As, 24)] LBall (qh, Ah, 4 * 96)); [exact (proj1 (cstate_nodup _ _ _ _ _ _ _ _ _ CST12))| wp_in_lit]. }
    apply Forall_nil. }
  clear SF MU WM CST12. rename SFa into SF.
  (* call 13: lock *)
  eapply climpl_seq.
  { eapply LKN; [lia| eapply croom_weaken; [exact (croom_grow _ _ _ _ _ _ _ _ ROOM GRc)| wp_wnorm; lia..]| exact CSa| rewrite SPfU; unfold LOCK_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; lia]. }
  intros f13 L13 st13 ms13 (v13 & m13 & LB13 & RET13 & FU13 & GR13 & CST13 & FRM13 & (qx3 & Ax3 & -> & -> & -> & RNGx3 & CELLx3)).
  destruct RET13 as (r13_0 & r13_1 & r13_2 & r13_3 & r13_4 & r13_5 & r13_6 & r13_7 & r13_8 & r13_9 & r13_10 & r13_11 & r13_12 & r13_13 & ->).
  cret_lit.
  rewrite SPfU in FRM13.
  pose proof (cframe_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SF FRM13 ltac:(lia) (fun a X => X) (fun q _ X => X)) as SFn.
  pose proof (proj1 FRM13) as CF.
  repeat match goal with
  | H : rw_cells usegs ?mo (bv_unsigned sp + -80) _, CF : cfr _ _ _ _ ?mo ?mn |- _ =>
      apply (cfr_cells_stack _ _ _ _ _ _ _ _ CF) in H; [| lia]
  | H : rw_cells usegs ?mo ?A _, CF : cfr _ _ _ ?LBo ?mo ?mn |- _ =>
      lazymatch LBo with context [(?q, A, ?n)] =>
        apply (cfr_cells_block _ _ _ _ _ _ _ _ (q, A, n) CF) in H; [| wp_in_lit| intros X; exact X| cbn; lia| cbn; lia] end
  end.
  clear CF FRM13 SF CSa HP MI ST. rename SFn into SF.
  assert (FUn : (f <= f13 + 13)%nat) by lia. clear FU13 FUc. rename FUn into FUc.
  assert (GRn : cgrow L ((qx3, 40) :: (qa3, 32) :: (qy2, 40) :: (qx2, 40) :: (qa2, 32) :: (qy1, 40) :: (qx1, 40) :: (qa1, 32) :: (qy0, 40) :: (qx0, 40) :: (qa0, 32) :: (qh, 4 * 96) :: (qs, 24) :: L) 12 1 8576) by (eapply cgrow_weaken; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ GRc GR13)| wp_wnorm; lia..]).
  clear GRc GR13. rename GRn into GRc.
  pose proof RNGx3 as (P0x3 & _ & _ & PCx3 & IMGx3). wp_box1 IMGx3.
  assert (APsx3 : wp_apbox (As + 24 <= Ax3 \/ Ax3 + 40 <= As)).
  { unfold wp_apbox. eapply cstate_apart; [exact CST13| wp_in_lit| left; reflexivity| eapply cstate_head_fresh; [exact CST13| wp_in_lit]]. }
  assert (APhx3 : wp_apbox (Ah + 384 <= Ax3 \/ Ax3 + 40 <= Ah)).
  { unfold wp_apbox. eapply cstate_apart; [exact CST13| wp_in_lit| left; reflexivity| eapply cstate_head_fresh; [exact CST13| wp_in_lit]]. }
  pose proof CST13 as (HP & _ & (errv13 & _ & _ & ST & _ & _ & MI & _) & _).
  rewrite unsigned_lit in ST by lia.
  pose proof (munch_refl [(Ah, Ah + 384)] m13) as MU. pose proof (wmono_refl usegs m13) as WM.
  apply climpl_from_evt.
  step. step. step. wp_brF. step.
  apply evt_done; cbv beta.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into mw13 end.
  assert (CSa : cstate st13 ((qx3, Ax3, 40) :: (qa3, Aa3, 32) :: (qy2, Ay2, 40) :: (qx2, Ax2, 40) :: (qa2, Aa2, 32) :: (qy1, Ay1, 40) :: (qx1, Ax1, 40) :: (qa1, Aa1, 32) :: (qy0, Ay0, 40) :: (qx0, Ax0, 40) :: (qa0, Aa0, 32) :: (qh, Ah, 4 * 96) :: (qs, As, 24) :: LBall) LB ((qx3, 40) :: (qa3, 32) :: (qy2, 40) :: (qx2, 40) :: (qa2, 32) :: (qy1, 40) :: (qx1, 40) :: (qa1, 32) :: (qy0, 40) :: (qx0, 40) :: (qa0, 32) :: (qh, 4 * 96) :: (qs, 24) :: L) mw13 (Z_to_bv 64 (bv_unsigned sp + -80)) tp lo B).
  { eapply (cstate_seg _ _ _ _ _ m13 mw13 _ _ tp lo B (bv_unsigned sp)); [exact CST13| exact MU| exact WM| exact MI| | lia| lia| | rewrite SPfU; exact ST| rewrite SPfU; lia].
    - apply Forall_cons; [eapply cwin_block with (b := (qh, Ah, 4 * 96)); [wp_in_lit| cbn; lia| cbn; lia]| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. unfold wp_box in IMGh. repeat split; lia. }
  assert (SFa : cframe (fun _ : bptr => False) [] (bv_unsigned sp) st LBall L m st13 ((qx3, Ax3, 40) :: (qa3, Aa3, 32) :: (qy2, Ay2, 40) :: (qx2, Ax2, 40) :: (qa2, Aa2, 32) :: (qy1, Ay1, 40) :: (qx1, Ax1, 40) :: (qa1, Aa1, 32) :: (qy0, Ay0, 40) :: (qx0, Ax0, 40) :: (qa0, Aa0, 32) :: (qh, Ah, 4 * 96) :: (qs, As, 24) :: LBall) ((qx3, 40) :: (qa3, 32) :: (qy2, 40) :: (qx2, 40) :: (qa2, 32) :: (qy1, 40) :: (qx1, 40) :: (qa1, 32) :: (qy0, 40) :: (qx0, 40) :: (qa0, 32) :: (qh, 4 * 96) :: (qs, 24) :: L) mw13).
  { eapply cframe_seg; [exact SF| exact MU| exact WM| exact HP| lia|].
    apply Forall_cons; [eapply cseg_ok_block with (b := (qh, Ah, 4 * 96)); [wp_in_lit| | cbn; lia| cbn; lia]|].
    { apply (t_fresh_notin (fun _ : bptr => False) LBall).
      apply (t_nodup_prefix blk_id [(qx3, Ax3, 40); (qa3, Aa3, 32); (qy2, Ay2, 40); (qx2, Ax2, 40); (qa2, Aa2, 32); (qy1, Ay1, 40); (qx1, Ax1, 40); (qa1, Aa1, 32); (qy0, Ay0, 40); (qx0, Ax0, 40); (qa0, Aa0, 32); (qh, Ah, 4 * 96); (qs, As, 24)] LBall (qh, Ah, 4 * 96)); [exact (proj1 (cstate_nodup _ _ _ _ _ _ _ _ _ CST13))| wp_in_lit]. }
    apply Forall_nil. }
  clear SF MU WM CST13. rename SFa into SF.
  (* call 14: lock *)
  eapply climpl_seq.
  { eapply LKN; [lia| eapply croom_weaken; [exact (croom_grow _ _ _ _ _ _ _ _ ROOM GRc)| wp_wnorm; lia..]| exact CSa| rewrite SPfU; unfold LOCK_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; lia]. }
  intros f14 L14 st14 ms14 (v14 & m14 & LB14 & RET14 & FU14 & GR14 & CST14 & FRM14 & (qy3 & Ay3 & -> & -> & -> & RNGy3 & CELLy3)).
  destruct RET14 as (r14_0 & r14_1 & r14_2 & r14_3 & r14_4 & r14_5 & r14_6 & r14_7 & r14_8 & r14_9 & r14_10 & r14_11 & r14_12 & r14_13 & ->).
  cret_lit.
  rewrite SPfU in FRM14.
  pose proof (cframe_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SF FRM14 ltac:(lia) (fun a X => X) (fun q _ X => X)) as SFn.
  pose proof (proj1 FRM14) as CF.
  repeat match goal with
  | H : rw_cells usegs ?mo (bv_unsigned sp + -80) _, CF : cfr _ _ _ _ ?mo ?mn |- _ =>
      apply (cfr_cells_stack _ _ _ _ _ _ _ _ CF) in H; [| lia]
  | H : rw_cells usegs ?mo ?A _, CF : cfr _ _ _ ?LBo ?mo ?mn |- _ =>
      lazymatch LBo with context [(?q, A, ?n)] =>
        apply (cfr_cells_block _ _ _ _ _ _ _ _ (q, A, n) CF) in H; [| wp_in_lit| intros X; exact X| cbn; lia| cbn; lia] end
  end.
  clear CF FRM14 SF CSa HP MI ST. rename SFn into SF.
  assert (FUn : (f <= f14 + 14)%nat) by lia. clear FU14 FUc. rename FUn into FUc.
  assert (GRn : cgrow L ((qy3, 40) :: (qx3, 40) :: (qa3, 32) :: (qy2, 40) :: (qx2, 40) :: (qa2, 32) :: (qy1, 40) :: (qx1, 40) :: (qa1, 32) :: (qy0, 40) :: (qx0, 40) :: (qa0, 32) :: (qh, 4 * 96) :: (qs, 24) :: L) 13 1 8576) by (eapply cgrow_weaken; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ GRc GR14)| wp_wnorm; lia..]).
  clear GRc GR14. rename GRn into GRc.
  pose proof RNGy3 as (P0y3 & _ & _ & PCy3 & IMGy3). wp_box1 IMGy3.
  assert (APsy3 : wp_apbox (As + 24 <= Ay3 \/ Ay3 + 40 <= As)).
  { unfold wp_apbox. eapply cstate_apart; [exact CST14| wp_in_lit| left; reflexivity| eapply cstate_head_fresh; [exact CST14| wp_in_lit]]. }
  assert (APhy3 : wp_apbox (Ah + 384 <= Ay3 \/ Ay3 + 40 <= Ah)).
  { unfold wp_apbox. eapply cstate_apart; [exact CST14| wp_in_lit| left; reflexivity| eapply cstate_head_fresh; [exact CST14| wp_in_lit]]. }
  pose proof CST14 as (HP & _ & (errv14 & _ & _ & ST & _ & _ & MI & _) & _).
  rewrite unsigned_lit in ST by lia.
  pose proof (munch_refl [(Ah, Ah + 384); (As, As + 24)] m14) as MU. pose proof (wmono_refl usegs m14) as WM.
  apply climpl_from_evt.
  step. step. step. wp_brF. step. step. wp_brT. step. step. wp_brF. step.
  apply evt_done; cbv beta.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into mw14 end.
  assert (CSa : cstate st14 ((qy3, Ay3, 40) :: (qx3, Ax3, 40) :: (qa3, Aa3, 32) :: (qy2, Ay2, 40) :: (qx2, Ax2, 40) :: (qa2, Aa2, 32) :: (qy1, Ay1, 40) :: (qx1, Ax1, 40) :: (qa1, Aa1, 32) :: (qy0, Ay0, 40) :: (qx0, Ax0, 40) :: (qa0, Aa0, 32) :: (qh, Ah, 4 * 96) :: (qs, As, 24) :: LBall) LB ((qy3, 40) :: (qx3, 40) :: (qa3, 32) :: (qy2, 40) :: (qx2, 40) :: (qa2, 32) :: (qy1, 40) :: (qx1, 40) :: (qa1, 32) :: (qy0, 40) :: (qx0, 40) :: (qa0, 32) :: (qh, 4 * 96) :: (qs, 24) :: L) mw14 (Z_to_bv 64 (bv_unsigned sp + -80)) tp lo B).
  { eapply (cstate_seg _ _ _ _ _ m14 mw14 _ _ tp lo B (bv_unsigned sp)); [exact CST14| exact MU| exact WM| exact MI| | lia| lia| | rewrite SPfU; exact ST| rewrite SPfU; lia].
    - apply Forall_cons; [eapply cwin_block with (b := (qh, Ah, 4 * 96)); [wp_in_lit| cbn; lia| cbn; lia]| apply Forall_cons; [eapply cwin_block with (b := (qs, As, 24)); [wp_in_lit| cbn; lia| cbn; lia]| apply Forall_nil]].
    - cbn [disjoint_from]. unfold LX_FLAGS. unfold wp_box in IMGh, IMGs. repeat split; lia. }
  assert (SFa : cframe (fun _ : bptr => False) [] (bv_unsigned sp) st LBall L m st14 ((qy3, Ay3, 40) :: (qx3, Ax3, 40) :: (qa3, Aa3, 32) :: (qy2, Ay2, 40) :: (qx2, Ax2, 40) :: (qa2, Aa2, 32) :: (qy1, Ay1, 40) :: (qx1, Ax1, 40) :: (qa1, Aa1, 32) :: (qy0, Ay0, 40) :: (qx0, Ax0, 40) :: (qa0, Aa0, 32) :: (qh, Ah, 4 * 96) :: (qs, As, 24) :: LBall) ((qy3, 40) :: (qx3, 40) :: (qa3, 32) :: (qy2, 40) :: (qx2, 40) :: (qa2, 32) :: (qy1, 40) :: (qx1, 40) :: (qa1, 32) :: (qy0, 40) :: (qx0, 40) :: (qa0, 32) :: (qh, 4 * 96) :: (qs, 24) :: L) mw14).
  { eapply cframe_seg; [exact SF| exact MU| exact WM| exact HP| lia|].
    apply Forall_cons; [eapply cseg_ok_block with (b := (qh, Ah, 4 * 96)); [wp_in_lit| | cbn; lia| cbn; lia]|].
    { apply (t_fresh_notin (fun _ : bptr => False) LBall).
      apply (t_nodup_prefix blk_id [(qy3, Ay3, 40); (qx3, Ax3, 40); (qa3, Aa3, 32); (qy2, Ay2, 40); (qx2, Ax2, 40); (qa2, Aa2, 32); (qy1, Ay1, 40); (qx1, Ax1, 40); (qa1, Aa1, 32); (qy0, Ay0, 40); (qx0, Ax0, 40); (qa0, Aa0, 32); (qh, Ah, 4 * 96); (qs, As, 24)] LBall (qh, Ah, 4 * 96)); [exact (proj1 (cstate_nodup _ _ _ _ _ _ _ _ _ CST14))| wp_in_lit]. }
    apply Forall_cons; [eapply cseg_ok_block with (b := (qs, As, 24)); [wp_in_lit| | cbn; lia| cbn; lia]|].
    { apply (t_fresh_notin (fun _ : bptr => False) LBall).
      apply (t_nodup_prefix blk_id [(qy3, Ay3, 40); (qx3, Ax3, 40); (qa3, Aa3, 32); (qy2, Ay2, 40); (qx2, Ax2, 40); (qa2, Aa2, 32); (qy1, Ay1, 40); (qx1, Ax1, 40); (qa1, Aa1, 32); (qy0, Ay0, 40); (qx0, Ax0, 40); (qa0, Aa0, 32); (qh, Ah, 4 * 96); (qs, As, 24)] LBall (qs, As, 24)); [exact (proj1 (cstate_nodup _ _ _ _ _ _ _ _ _ CST14))| wp_in_lit]. }
    apply Forall_nil. }
  clear SF MU WM CST14. rename SFa into SF.
  (* call 15: lock *)
  eapply climpl_seq.
  { eapply LKN; [lia| eapply croom_weaken; [exact (croom_grow _ _ _ _ _ _ _ _ ROOM GRc)| wp_wnorm; lia..]| exact CSa| rewrite SPfU; unfold LOCK_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; lia]. }
  intros f15 L15 st15 ms15 (v15 & m15 & LB15 & RET15 & FU15 & GR15 & CST15 & FRM15 & (qb & Ab & -> & -> & -> & RNGb & CELLb)).
  destruct RET15 as (r15_0 & r15_1 & r15_2 & r15_3 & r15_4 & r15_5 & r15_6 & r15_7 & r15_8 & r15_9 & r15_10 & r15_11 & r15_12 & r15_13 & ->).
  cret_lit.
  rewrite SPfU in FRM15.
  pose proof (cframe_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SF FRM15 ltac:(lia) (fun a X => X) (fun q _ X => X)) as SFn.
  pose proof (proj1 FRM15) as CF.
  repeat match goal with
  | H : rw_cells usegs ?mo (bv_unsigned sp + -80) _, CF : cfr _ _ _ _ ?mo ?mn |- _ =>
      apply (cfr_cells_stack _ _ _ _ _ _ _ _ CF) in H; [| lia]
  | H : rw_cells usegs ?mo ?A _, CF : cfr _ _ _ ?LBo ?mo ?mn |- _ =>
      lazymatch LBo with context [(?q, A, ?n)] =>
        apply (cfr_cells_block _ _ _ _ _ _ _ _ (q, A, n) CF) in H; [| wp_in_lit| intros X; exact X| cbn; lia| cbn; lia] end
  end.
  clear CF FRM15 SF CSa HP MI ST. rename SFn into SF.
  assert (FUn : (f <= f15 + 15)%nat) by lia. clear FU15 FUc. rename FUn into FUc.
  assert (GRn : cgrow L ((qb, 40) :: (qy3, 40) :: (qx3, 40) :: (qa3, 32) :: (qy2, 40) :: (qx2, 40) :: (qa2, 32) :: (qy1, 40) :: (qx1, 40) :: (qa1, 32) :: (qy0, 40) :: (qx0, 40) :: (qa0, 32) :: (qh, 4 * 96) :: (qs, 24) :: L) 14 1 8576) by (eapply cgrow_weaken; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ GRc GR15)| wp_wnorm; lia..]).
  clear GRc GR15. rename GRn into GRc.
  pose proof RNGb as (P0b & _ & _ & PCb & IMGb). wp_box1 IMGb.
  assert (APsb : wp_apbox (As + 24 <= Ab \/ Ab + 40 <= As)).
  { unfold wp_apbox. eapply cstate_apart; [exact CST15| wp_in_lit| left; reflexivity| eapply cstate_head_fresh; [exact CST15| wp_in_lit]]. }
  assert (APhb : wp_apbox (Ah + 384 <= Ab \/ Ab + 40 <= Ah)).
  { unfold wp_apbox. eapply cstate_apart; [exact CST15| wp_in_lit| left; reflexivity| eapply cstate_head_fresh; [exact CST15| wp_in_lit]]. }
  pose proof CST15 as (HP & _ & (errv15 & _ & _ & ST & _ & _ & MI & _) & _).
  rewrite unsigned_lit in ST by lia.
  pose proof (munch_refl [(As, As + 24)] m15) as MU. pose proof (wmono_refl usegs m15) as WM.
  apply climpl_from_evt.
  step. step. wp_brT. step. do 10 step. step. step.
  apply evt_done; cbv beta.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into mE end.
  assert (STE : stk usegs mE lo (bv_unsigned sp)).
  { pose proof (stk_release _ _ _ _ _ ST FR ltac:(lia)) as STR. cbn [cells_size csize Nat.add] in STR.
    replace (bv_unsigned sp) with (bv_unsigned sp + -80 + Z.of_nat 80) by lia. exact STR. }
  apply climpl_done.
  exists (Z_to_bv 64 As), mE. eexists.
  split; [do 14 eexists; reflexivity|].
  split; [lia|].
  split; [exact GRc|].
  split.
  { eapply (cstate_seg _ _ _ _ _ m15 mE _ sp tp lo B (bv_unsigned sp)); [exact CST15| exact MU| exact WM| exact MI| | lia| lia| | exact STE| lia].
    - apply Forall_cons; [eapply cwin_block with (b := (qs, As, 24)); [wp_in_lit| cbn; lia| cbn; lia]| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. unfold wp_box in IMGs. repeat split; lia. }
  split.
  { eapply cframe_seg; [exact SF| exact MU| exact WM| exact HP| lia|].
    apply Forall_cons; [eapply cseg_ok_block with (b := (qs, As, 24)); [wp_in_lit| | cbn; lia| cbn; lia]|].
    { apply (t_fresh_notin (fun _ : bptr => False) LBall).
      apply (t_nodup_prefix blk_id [(qb, Ab, 40); (qy3, Ay3, 40); (qx3, Ax3, 40); (qa3, Aa3, 32); (qy2, Ay2, 40); (qx2, Ax2, 40); (qa2, Aa2, 32); (qy1, Ay1, 40); (qx1, Ax1, 40); (qa1, Aa1, 32); (qy0, Ay0, 40); (qx0, Ax0, 40); (qa0, Aa0, 32); (qh, Ah, 4 * 96); (qs, As, 24)] LBall (qs, As, 24)); [exact (proj1 (cstate_nodup _ _ _ _ _ _ _ _ _ CST15))| wp_in_lit]. }
    apply Forall_nil. }
  unfold ossl_method_store_new_res.
  exists qs, As, qh, Ah, qa0, Aa0, qx0, Ax0, qy0, Ay0, qa1, Aa1, qx1, Ax1, qy1, Ay1, qa2, Aa2, qx2, Ax2, qy2, Ay2, qa3, Aa3, qx3, Ax3, qy3, Ay3, qb, Ab.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  repeat (split; [assumption|]).
  assumption.
Qed.
End WithCeiling0.
