(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_G_pkit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_M_malloc Fz_M_zalloc Th_mutex Fz_T_lock_new.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac tslia ::= wp_tslia.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition FZ_G_ossl_prov_conf_ctx_new : Z := 0xf1b2c.
Definition ossl_prov_conf_ctx_new_STACK : Z := 32 + LOCK_NEW_STACK.

Definition ossl_prov_conf_ctx_new_res (LBall : list block) (L : @clist bptr) : word -> list block -> @clist bptr -> mem -> Prop :=
  fun v LBall' L' m' => exists q1_1 A1_1 q2_1 A2_1,
       v = (Z_to_bv 64 A1_1)
    /\ LBall' = (q2_1, A2_1, 40) :: (q1_1, A1_1, 16) :: LBall /\ L' = (q2_1, 40) :: (q1_1, 16) :: L
    /\ rblock_range A1_1 16 /\ rblock_range A2_1 40
    /\ rw_cells usegs m' A1_1 [C8 (Z_to_bv 64 A2_1); CB 8 (repeat (Z_to_bv 8 0) 8)]
    /\ rw_cells usegs m' A2_1 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].

Definition ossl_prov_conf_ctx_new_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo B : Z),
  (2 <= f)%nat -> croom L (wA 16 + wA 40) (wB 16 + wB 40) (wBig 16 + wBig 40) ->
  cstate st LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - ossl_prov_conf_ctx_new_STACK ->
  climpl f L st (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 FZ_G_ossl_prov_conf_ctx_new) fc None m (seg_rom usegs))
         (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LBall LB L f m lo B (fun _ => False) []%Z 2
                (wA 16 + wA 40) (wB 16 + wB 40) (wBig 16 + wBig 40) (ossl_prov_conf_ctx_new_res LBall L)).

Theorem ossl_prov_conf_ctx_new_spec : crypto_zalloc_stmt -> ossl_prov_conf_ctx_new_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros HB_crypto_zalloc_stmt ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LBall LB L f lo B
         Hf ROOM CST SLO.
  pose proof CST as (HP & _ & (errv & _ & HB & ST & LO & _ & MI & _) & _ & _ & _ & GLO).
  unfold ossl_prov_conf_ctx_new_STACK, LOCK_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK, FZ_G_ossl_prov_conf_ctx_new, GLOBALS_TOP in *. unfold ceil_window in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (w_bounds 16 ltac:(lia)) as WB16.
  pose proof (w_bounds 40 ltac:(lia)) as WB40.
  (* [comment removed for export] *)
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU0. pose proof (wmono_refl usegs m) as WM0.
  cprefix. step. carve_frame 32%nat ST. do 3 ths. do 6 step.
  chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into ma0 end.
  assert (CSTa0 : cstate st LBall LB L ma0 (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo B).
  { eapply (cstate_seg _ _ _ _ _ m ma0 _ (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo B (bv_unsigned sp)); [exact CST| exact MU0| exact WM0| wp_mi| | wp_lia| wp_lia| | wp_stk|].
    - apply Forall_cons; [apply cwin_stack; wp_lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. tslia.
    - rewrite unsigned_lit by wp_lia. wp_lia. }
  assert (FRa0 : cframe (fun _ => False) []%Z (bv_unsigned sp) st LBall L m st LBall L ma0).
  { eapply cframe_seg; [apply cframe_refl| exact MU0| exact WM0| exact HP| wp_lia|].
    apply Forall_cons; [apply cseg_ok_stack; wp_lia| apply Forall_nil]. }
  (* [comment removed for export] *)
  eapply climpl_seq.
  { eapply HB_crypto_zalloc_stmt with (n := 16); [wp_lia| eapply croom_weaken; [exact ROOM| wp_lia..]| wp_lia| exact CSTa0| rewrite unsigned_lit by wp_lia; unfold CZ_STACK, CM_STACK, RMALLOC_STACK; wp_lia| reflexivity]. }
  intros f1 L1 st1 ms1 (v1 & mb1 & LB1 & RET1 & FU1 & GR1 & CST1 & FRM1 & (q1_1 & A1_1 & -> & -> & -> & RNG_A1_1 & BC1_0)).
  destruct RET1 as (u0_1 & u1_1 & u2_1 & b1_1 & b2_1 & b3_1 & b4_1 & b5_1 & b6_1 & b7_1 & u3_1 & u4_1 & u5_1 & u6_1 & ->).
  cret_lit. rewrite unsigned_lit in * by wp_lia.
  pose proof FRM1 as (CFR1 & _).
  lazymatch goal with FRh : rw_cells _ ma0 (bv_unsigned sp + -32) _ |- _ => pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FRh ltac:(wp_lia)) as FRs1 end.
  pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _).
  rewrite unsigned_lit in ST1 by wp_lia.
  pose proof RNG_A1_1 as (P0_A1_1 & P16_A1_1 & _ & PC_A1_1 & PIMG_A1_1). wp_box1 P16_A1_1. wp_box1 PIMG_A1_1.
  assert (FUc1 : (f <= f1 + 1)%nat) by (clear - FU1; lia). clear FU1.
  change (Z.to_nat 16) with 16%nat in *.
  assert (IN_A1_1_1 : In (q1_1, A1_1, 16) ((q1_1, A1_1, 16) :: LBall)) by (left; reflexivity).
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST1) as [ND1 _].
  (* [comment removed for export] *)
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z mb1) as MU1. pose proof (wmono_refl usegs mb1) as WM1.
  wp_clear_aps.
  cprefix. step. wp_brF. do 2 step.
  chere.
  assert (CSTa1 : cstate st1 ((q1_1, A1_1, 16) :: LBall) LB ((q1_1, 16) :: L) mb1 (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo B).
  { eapply (cstate_seg _ _ _ _ _ mb1 mb1 _ (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo B (bv_unsigned sp)); [exact CST1| exact MU1| exact WM1| wp_mi| | wp_lia| wp_lia| | wp_stk|].
    - apply Forall_cons; [apply cwin_stack; wp_lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. tslia.
    - rewrite unsigned_lit by wp_lia. wp_lia. }
  assert (FRa1 : cframe (fun _ => False) []%Z (bv_unsigned sp) st LBall L m st1 ((q1_1, A1_1, 16) :: LBall) ((q1_1, 16) :: L) mb1).
  { eapply cframe_seg; [eapply cframe_call; [exact FRa0| exact FRM1| wp_lia| intros a X; first [destruct X | exact X | cbn [rin_ivs fst snd] in *; wp_lia]| intros q0 _ X; exact X]| exact MU1| exact WM1| exact HP1| wp_lia|].
    apply Forall_cons; [apply cseg_ok_stack; wp_lia| apply Forall_nil]. }
  (* [comment removed for export] *)
  eapply climpl_seq.
  { eapply (T_lock_new_spec HB_crypto_zalloc_stmt); [wp_lia| eapply croom_weaken; [exact (croom_grow _ _ _ _ _ _ _ _ ROOM GR1)| wp_lia..]| exact CSTa1| rewrite unsigned_lit by wp_lia; unfold LOCK_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; wp_lia]. }
  intros f2 L2 st2 ms2 (v2 & mb2 & LB2 & RET2 & FU2 & GR2 & CST2 & FRM2 & (q2_1 & A2_1 & -> & -> & -> & RNG_A2_1 & BC2_0)).
  destruct RET2 as (u0_2 & u1_2 & u2_2 & b1_2 & b2_2 & b3_2 & b4_2 & b5_2 & b6_2 & b7_2 & u3_2 & u4_2 & u5_2 & u6_2 & ->).
  cret_lit. rewrite unsigned_lit in * by wp_lia.
  pose proof FRM2 as (CFR2 & _).
  lazymatch goal with FRh : rw_cells _ mb1 (bv_unsigned sp + -32) _ |- _ => pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 FRh ltac:(wp_lia)) as FRs2 end.
  repeat match goal with Hb : rw_cells _ mb1 A1_1 _ |- _ => let Hn := fresh "BK" in pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q1_1, A1_1, 16) CFR2 Hb IN_A1_1_1 ltac:(intros X; exact X) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as Hn; clear Hb end.
  pose proof CST2 as (HP2 & _ & (errv2 & _ & _ & ST2 & _ & _ & MI2 & _) & _).
  rewrite unsigned_lit in ST2 by wp_lia.
  pose proof RNG_A2_1 as (P0_A2_1 & P16_A2_1 & _ & PC_A2_1 & PIMG_A2_1). wp_box1 P16_A2_1. wp_box1 PIMG_A2_1.
  assert (FUc2 : (f <= f2 + 2)%nat) by (clear - FU2 FUc1; lia). clear FU2.
  unfold mutex_cells in *.
  change (Z.to_nat 40) with 40%nat in *.
  assert (IN_A2_1_2 : In (q2_1, A2_1, 40) ((q2_1, A2_1, 40) :: (q1_1, A1_1, 16) :: LBall)) by (left; reflexivity).
  assert (IN_A1_1_2 : In (q1_1, A1_1, 16) ((q2_1, A2_1, 40) :: (q1_1, A1_1, 16) :: LBall)) by (do 1 right; left; reflexivity).
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST2) as [ND2 _].
  (* [comment removed for export] *)
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (A1_1, A1_1 + 16)]%Z mb2) as MU2. pose proof (wmono_refl usegs mb2) as WM2.
  wp_clear_aps.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ q1_1 A1_1 16 q2_1 A2_1 40 CST2 IN_A1_1_2 IN_A2_1_2 (wp_nodup_apart [(q2_1, A2_1, 40); (q1_1, A1_1, 16)] LBall 1%nat 0%nat (q1_1, A1_1, 16) (q2_1, A2_1, 40) ND2 eq_refl eq_refl ltac:(discriminate))) as AP_A1_1_A2_1_s2.
  wp_box_aps.
  cprefix. step. step. wp_brF. ths. step. wp_brT. do 6 step.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -32) _, STh : stk _ _ _ _ |- _ => release_frame FRh STh (bv_unsigned sp) end.
  chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into mz end.
  assert (CSTz : cstate st2 ((q2_1, A2_1, 40) :: (q1_1, A1_1, 16) :: LBall) LB ((q2_1, 40) :: (q1_1, 16) :: L) mz sp tp lo B).
  { eapply (cstate_seg _ _ _ _ _ mb2 mz _ sp tp lo B (bv_unsigned sp)); [exact CST2| exact MU2| exact WM2| wp_mi| | wp_lia| wp_lia| | wp_stk|].
    - apply Forall_cons; [apply cwin_stack; wp_lia| apply Forall_cons; [apply (cwin_block _ _ _ (q1_1, A1_1, 16)); [exact IN_A1_1_2| |]; unfold blk_addr, blk_size; cbn [fst snd]; wp_lia| apply Forall_nil]].
    - cbn [disjoint_from]. unfold LX_FLAGS. tslia.
    - exact HB. }
  assert (FRz : cframe (fun _ => False) []%Z (bv_unsigned sp) st LBall L m st2 ((q2_1, A2_1, 40) :: (q1_1, A1_1, 16) :: LBall) ((q2_1, 40) :: (q1_1, 16) :: L) mz).
  { eapply cframe_seg; [eapply cframe_call; [exact FRa1| exact FRM2| wp_lia| intros a X; first [destruct X | exact X | cbn [rin_ivs fst snd] in *; wp_lia]| intros q0 _ X; exact X]| exact MU2| exact WM2| exact HP2| wp_lia|].
    apply Forall_cons; [apply cseg_ok_stack; wp_lia| apply Forall_cons; [apply (cseg_ok_block _ _ _ _ _ (q1_1, A1_1, 16)); [exact IN_A1_1_2| exact (t_fresh_notin (fun _ => False) LBall (q1_1, A1_1, 16) (t_nodup_prefix blk_id [(q2_1, A2_1, 40); (q1_1, A1_1, 16)] LBall (q1_1, A1_1, 16) ND2 ltac:(do 1 right; left; reflexivity)))| |]; unfold blk_addr, blk_size; cbn [fst snd]; wp_lia| apply Forall_nil]]. }
  apply climpl_done.
  exists (Z_to_bv 64 A1_1), mz, ((q2_1, A2_1, 40) :: (q1_1, A1_1, 16) :: LBall).
  split; [unfold cret; do 14 eexists; reflexivity|]. split; [wp_lia|].
  split; [eapply cgrow_weaken; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ GR1 GR2)| wp_lia..]|].
  split; [exact CSTz|]. split; [exact FRz|].
  exists q1_1, A1_1, q2_1, A2_1.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact RNG_A1_1|]. split; [exact RNG_A2_1|]. split; [wp_cells|]. wp_cells.
Qed.
End WithCeiling0.
