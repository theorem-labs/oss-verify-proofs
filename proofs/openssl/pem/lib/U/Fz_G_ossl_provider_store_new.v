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
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_G_pkit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_M_malloc Fz_M_zalloc Fz_T_sk Fz_G_OPENSSL_sk_new Th_mutex Fz_T_lock_new.
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

Definition FZ_G_ossl_provider_store_new : Z := 0xf2b80.
Definition ossl_provider_store_new_STACK : Z := 48 + LOCK_NEW_STACK.

Definition ossl_provider_store_new_res (a0 : word) (LBall : list block) (L : @clist bptr) : word -> list block -> @clist bptr -> mem -> Prop :=
  fun v LBall' L' m' => exists q1_1 A1_1 q2_1 A2_1 q3_1 A3_1 q4_1 A4_1 q5_1 A5_1,
       v = (Z_to_bv 64 A1_1)
    /\ LBall' = (q5_1, A5_1, 40) :: (q4_1, A4_1, 56) :: (q3_1, A3_1, 40) :: (q2_1, A2_1, 56) :: (q1_1, A1_1, 80) :: LBall /\ L' = (q5_1, 40) :: (q4_1, 56) :: (q3_1, 40) :: (q2_1, 56) :: (q1_1, 80) :: L
    /\ rblock_range A1_1 80 /\ rblock_range A2_1 56 /\ rblock_range A3_1 40 /\ rblock_range A4_1 56 /\ rblock_range A5_1 40
    /\ rw_cells usegs m' A1_1 [C8 a0; C8 (Z_to_bv 64 A2_1); C8 (Z_to_bv 64 A4_1); C8 (Z_to_bv 64 A3_1); C8 (Z_to_bv 64 A5_1); CB 32 (repeat (Z_to_bv 8 0) 32); C1 (Z_to_bv 8 (Z.lor (bv_unsigned (zxb (Z_to_bv 8 0))) 1)); CB 7 (repeat (Z_to_bv 8 0) 7)]
    /\ rw_cells usegs m' A4_1 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 1004432); C8 (Z_to_bv 64 1004308); C8 (Z_to_bv 64 1004476)]
    /\ rw_cells usegs m' A3_1 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells usegs m' A2_1 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 994472); C8 (Z_to_bv 64 1004348); C8 (Z_to_bv 64 1004268); C8 (Z_to_bv 64 1004392)]
    /\ rw_cells usegs m' A5_1 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].

Definition ossl_provider_store_new_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo B : Z),
  (5 <= f)%nat -> croom L (wA 80 + wA 56 + wA 40 + wA 56 + wA 40) (wB 80 + wB 56 + wB 40 + wB 56 + wB 40) (wBig 80 + wBig 56 + wBig 40 + wBig 56 + wBig 40) ->
  cstate st LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - ossl_provider_store_new_STACK ->
  climpl f L st (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 FZ_G_ossl_provider_store_new) fc None m (seg_rom usegs))
         (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LBall LB L f m lo B (fun _ => False) []%Z 5
                (wA 80 + wA 56 + wA 40 + wA 56 + wA 40) (wB 80 + wB 56 + wB 40 + wB 56 + wB 40) (wBig 80 + wBig 56 + wBig 40 + wBig 56 + wBig 40) (ossl_provider_store_new_res a0 LBall L)).

Theorem ossl_provider_store_new_spec : crypto_zalloc_stmt -> ossl_provider_store_new_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros HB_crypto_zalloc_stmt ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LBall LB L f lo B
         Hf ROOM CST SLO.
  pose proof CST as (HP & _ & (errv & _ & HB & ST & LO & _ & MI & _) & _ & _ & _ & GLO).
  unfold ossl_provider_store_new_STACK, LOCK_NEW_STACK, OPENSSL_sk_new_STACK, SK_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK, FZ_G_ossl_provider_store_new, GLOBALS_TOP in *. unfold ceil_window in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (w_bounds 40 ltac:(lia)) as WB40.
  pose proof (w_bounds 56 ltac:(lia)) as WB56.
  pose proof (w_bounds 80 ltac:(lia)) as WB80.
  (* [comment removed for export] *)
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU0. pose proof (wmono_refl usegs m) as WM0.
  cprefix. step. carve_frame 48%nat ST. do 5 ths. do 7 step.
  chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into ma0 end.
  assert (CSTa0 : cstate st LBall LB L ma0 (Z_to_bv 64 (bv_unsigned sp + -48)) tp lo B).
  { eapply (cstate_seg _ _ _ _ _ m ma0 _ (Z_to_bv 64 (bv_unsigned sp + -48)) tp lo B (bv_unsigned sp)); [exact CST| exact MU0| exact WM0| wp_mi| | wp_lia| wp_lia| | wp_stk|].
    - apply Forall_cons; [apply cwin_stack; wp_lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. tslia.
    - rewrite unsigned_lit by wp_lia. wp_lia. }
  assert (FRa0 : cframe (fun _ => False) []%Z (bv_unsigned sp) st LBall L m st LBall L ma0).
  { eapply cframe_seg; [apply cframe_refl| exact MU0| exact WM0| exact HP| wp_lia|].
    apply Forall_cons; [apply cseg_ok_stack; wp_lia| apply Forall_nil]. }
  (* [comment removed for export] *)
  eapply climpl_seq.
  { eapply HB_crypto_zalloc_stmt with (n := 80); [wp_lia| eapply croom_weaken; [exact ROOM| wp_lia..]| wp_lia| exact CSTa0| rewrite unsigned_lit by wp_lia; unfold CZ_STACK, CM_STACK, RMALLOC_STACK; wp_lia| reflexivity]. }
  intros f1 L1 st1 ms1 (v1 & mb1 & LB1 & RET1 & FU1 & GR1 & CST1 & FRM1 & (q1_1 & A1_1 & -> & -> & -> & RNG_A1_1 & BC1_0)).
  destruct RET1 as (u0_1 & u1_1 & u2_1 & b1_1 & b2_1 & b3_1 & b4_1 & b5_1 & b6_1 & b7_1 & u3_1 & u4_1 & u5_1 & u6_1 & ->).
  cret_lit. rewrite unsigned_lit in * by wp_lia.
  pose proof FRM1 as (CFR1 & _).
  lazymatch goal with FRh : rw_cells _ ma0 (bv_unsigned sp + -48) _ |- _ => pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FRh ltac:(wp_lia)) as FRs1 end.
  pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _).
  rewrite unsigned_lit in ST1 by wp_lia.
  pose proof RNG_A1_1 as (P0_A1_1 & P16_A1_1 & _ & PC_A1_1 & PIMG_A1_1). wp_box1 P16_A1_1. wp_box1 PIMG_A1_1.
  assert (FUc1 : (f <= f1 + 1)%nat) by (clear - FU1; lia). clear FU1.
  change (Z.to_nat 80) with 80%nat in *.
  assert (IN_A1_1_1 : In (q1_1, A1_1, 80) ((q1_1, A1_1, 80) :: LBall)) by (left; reflexivity).
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST1) as [ND1 _].
  (* [comment removed for export] *)
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z mb1) as MU1. pose proof (wmono_refl usegs mb1) as WM1.
  wp_clear_aps.
  cprefix. step. step. wp_brF. do 3 step.
  chere.
  assert (CSTa1 : cstate st1 ((q1_1, A1_1, 80) :: LBall) LB ((q1_1, 80) :: L) mb1 (Z_to_bv 64 (bv_unsigned sp + -48)) tp lo B).
  { eapply (cstate_seg _ _ _ _ _ mb1 mb1 _ (Z_to_bv 64 (bv_unsigned sp + -48)) tp lo B (bv_unsigned sp)); [exact CST1| exact MU1| exact WM1| wp_mi| | wp_lia| wp_lia| | wp_stk|].
    - apply Forall_cons; [apply cwin_stack; wp_lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. tslia.
    - rewrite unsigned_lit by wp_lia. wp_lia. }
  assert (FRa1 : cframe (fun _ => False) []%Z (bv_unsigned sp) st LBall L m st1 ((q1_1, A1_1, 80) :: LBall) ((q1_1, 80) :: L) mb1).
  { eapply cframe_seg; [eapply cframe_call; [exact FRa0| exact FRM1| wp_lia| intros a X; first [destruct X | exact X | cbn [rin_ivs fst snd] in *; wp_lia]| intros q0 _ X; exact X]| exact MU1| exact WM1| exact HP1| wp_lia|].
    apply Forall_cons; [apply cseg_ok_stack; wp_lia| apply Forall_nil]. }
  (* [comment removed for export] *)
  eapply climpl_seq.
  { eapply (OPENSSL_sk_new_spec HB_crypto_zalloc_stmt); [wp_lia| eapply croom_weaken; [exact (croom_grow _ _ _ _ _ _ _ _ ROOM GR1)| wp_lia..]| exact CSTa1| rewrite unsigned_lit by wp_lia; unfold OPENSSL_sk_new_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; wp_lia]. }
  intros f2 L2 st2 ms2 (v2 & mb2 & LB2 & RET2 & FU2 & GR2 & CST2 & FRM2 & (q2_1 & A2_1 & -> & -> & -> & RNG_A2_1 & BC2_0)).
  destruct RET2 as (u0_2 & u1_2 & u2_2 & b1_2 & b2_2 & b3_2 & b4_2 & b5_2 & b6_2 & b7_2 & u3_2 & u4_2 & u5_2 & u6_2 & ->).
  cret_lit. rewrite unsigned_lit in * by wp_lia.
  pose proof FRM2 as (CFR2 & _).
  lazymatch goal with FRh : rw_cells _ mb1 (bv_unsigned sp + -48) _ |- _ => pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR2 FRh ltac:(wp_lia)) as FRs2 end.
  repeat match goal with Hb : rw_cells _ mb1 A1_1 _ |- _ => let Hn := fresh "BK" in pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q1_1, A1_1, 80) CFR2 Hb IN_A1_1_1 ltac:(intros X; exact X) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as Hn; clear Hb end.
  pose proof CST2 as (HP2 & _ & (errv2 & _ & _ & ST2 & _ & _ & MI2 & _) & _).
  rewrite unsigned_lit in ST2 by wp_lia.
  pose proof RNG_A2_1 as (P0_A2_1 & P16_A2_1 & _ & PC_A2_1 & PIMG_A2_1). wp_box1 P16_A2_1. wp_box1 PIMG_A2_1.
  assert (FUc2 : (f <= f2 + 2)%nat) by (clear - FU2 FUc1; lia). clear FU2.
  change (Z.to_nat 56) with 56%nat in *.
  assert (IN_A2_1_2 : In (q2_1, A2_1, 56) ((q2_1, A2_1, 56) :: (q1_1, A1_1, 80) :: LBall)) by (left; reflexivity).
  assert (IN_A1_1_2 : In (q1_1, A1_1, 80) ((q2_1, A2_1, 56) :: (q1_1, A1_1, 80) :: LBall)) by (do 1 right; left; reflexivity).
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST2) as [ND2 _].
  (* [comment removed for export] *)
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (A1_1, A1_1 + 80); (A2_1, A2_1 + 56)]%Z mb2) as MU5. pose proof (wmono_refl usegs mb2) as WM5.
  wp_clear_aps.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ q1_1 A1_1 80 q2_1 A2_1 56 CST2 IN_A1_1_2 IN_A2_1_2 (wp_nodup_apart [(q2_1, A2_1, 56); (q1_1, A1_1, 80)] LBall 1%nat 0%nat (q1_1, A1_1, 80) (q2_1, A2_1, 56) ND2 eq_refl eq_refl ltac:(discriminate))) as AP_A1_1_A2_1_s5.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ q2_1 A2_1 56 q1_1 A1_1 80 CST2 IN_A2_1_2 IN_A1_1_2 (wp_nodup_apart [(q2_1, A2_1, 56); (q1_1, A1_1, 80)] LBall 0%nat 1%nat (q2_1, A2_1, 56) (q1_1, A1_1, 80) ND2 eq_refl eq_refl ltac:(discriminate))) as AP_A2_1_A1_1_s5.
  wp_box_aps.
  cprefix. do 5 step. tcallr T_sk_set_cmp_thunks_proof. all: try first [wp_hyp | reflexivity | eassumption | wp_lia | split; eassumption]. cbv beta delta [mkR]. unfold sk_cells in *. cbn [fst snd] in *. do 4 step. tcallr T_sk_set_copy_thunks_proof. all: try first [wp_hyp | reflexivity | eassumption | wp_lia | split; eassumption]. cbv beta delta [mkR]. unfold sk_cells in *. cbn [fst snd] in *. do 4 step. tcallr T_sk_set_thunks_proof. all: try first [wp_hyp | reflexivity | eassumption | wp_lia | split; eassumption]. cbv beta delta [mkR]. unfold sk_cells in *. cbn [fst snd] in *. step. step. wp_brF. ths. step. wp_brF. step.
  chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into ma5 end.
  assert (CSTa5 : cstate st2 ((q2_1, A2_1, 56) :: (q1_1, A1_1, 80) :: LBall) LB ((q2_1, 56) :: (q1_1, 80) :: L) ma5 (Z_to_bv 64 (bv_unsigned sp + -48)) tp lo B).
  { eapply (cstate_seg _ _ _ _ _ mb2 ma5 _ (Z_to_bv 64 (bv_unsigned sp + -48)) tp lo B (bv_unsigned sp)); [exact CST2| exact MU5| exact WM5| wp_mi| | wp_lia| wp_lia| | wp_stk|].
    - apply Forall_cons; [apply cwin_stack; wp_lia| apply Forall_cons; [apply (cwin_block _ _ _ (q1_1, A1_1, 80)); [exact IN_A1_1_2| |]; unfold blk_addr, blk_size; cbn [fst snd]; wp_lia| apply Forall_cons; [apply (cwin_block _ _ _ (q2_1, A2_1, 56)); [exact IN_A2_1_2| |]; unfold blk_addr, blk_size; cbn [fst snd]; wp_lia| apply Forall_nil]]].
    - cbn [disjoint_from]. unfold LX_FLAGS. tslia.
    - rewrite unsigned_lit by wp_lia. wp_lia. }
  assert (FRa5 : cframe (fun _ => False) []%Z (bv_unsigned sp) st LBall L m st2 ((q2_1, A2_1, 56) :: (q1_1, A1_1, 80) :: LBall) ((q2_1, 56) :: (q1_1, 80) :: L) ma5).
  { eapply cframe_seg; [eapply cframe_call; [exact FRa1| exact FRM2| wp_lia| intros a X; first [destruct X | exact X | cbn [rin_ivs fst snd] in *; wp_lia]| intros q0 _ X; exact X]| exact MU5| exact WM5| exact HP2| wp_lia|].
    apply Forall_cons; [apply cseg_ok_stack; wp_lia| apply Forall_cons; [apply (cseg_ok_block _ _ _ _ _ (q1_1, A1_1, 80)); [exact IN_A1_1_2| exact (t_fresh_notin (fun _ => False) LBall (q1_1, A1_1, 80) (t_nodup_prefix blk_id [(q2_1, A2_1, 56); (q1_1, A1_1, 80)] LBall (q1_1, A1_1, 80) ND2 ltac:(do 1 right; left; reflexivity)))| |]; unfold blk_addr, blk_size; cbn [fst snd]; wp_lia| apply Forall_cons; [apply (cseg_ok_block _ _ _ _ _ (q2_1, A2_1, 56)); [exact IN_A2_1_2| exact (t_fresh_notin (fun _ => False) LBall (q2_1, A2_1, 56) (t_nodup_prefix blk_id [(q2_1, A2_1, 56); (q1_1, A1_1, 80)] LBall (q2_1, A2_1, 56) ND2 ltac:(left; reflexivity)))| |]; unfold blk_addr, blk_size; cbn [fst snd]; wp_lia| apply Forall_nil]]]. }
  (* [comment removed for export] *)
  eapply climpl_seq.
  { eapply (T_lock_new_spec HB_crypto_zalloc_stmt); [wp_lia| eapply croom_weaken; [exact (croom_grow _ _ _ _ _ _ _ _ ROOM (cgrow_trans _ _ _ _ _ _ _ _ _ GR1 GR2))| wp_lia..]| exact CSTa5| rewrite unsigned_lit by wp_lia; unfold LOCK_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; wp_lia]. }
  intros f3 L3 st3 ms3 (v3 & mb3 & LB3 & RET3 & FU3 & GR3 & CST3 & FRM3 & (q3_1 & A3_1 & -> & -> & -> & RNG_A3_1 & BC3_0)).
  destruct RET3 as (u0_3 & u1_3 & u2_3 & b1_3 & b2_3 & b3_3 & b4_3 & b5_3 & b6_3 & b7_3 & u3_3 & u4_3 & u5_3 & u6_3 & ->).
  cret_lit. rewrite unsigned_lit in * by wp_lia.
  pose proof FRM3 as (CFR3 & _).
  lazymatch goal with FRh : rw_cells _ ma5 (bv_unsigned sp + -48) _ |- _ => pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR3 FRh ltac:(wp_lia)) as FRs3 end.
  repeat match goal with Hb : rw_cells _ ma5 A1_1 _ |- _ => let Hn := fresh "BK" in pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q1_1, A1_1, 80) CFR3 Hb IN_A1_1_2 ltac:(intros X; exact X) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as Hn; clear Hb end.
  repeat match goal with Hb : rw_cells _ ma5 A2_1 _ |- _ => let Hn := fresh "BK" in pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q2_1, A2_1, 56) CFR3 Hb IN_A2_1_2 ltac:(intros X; exact X) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as Hn; clear Hb end.
  pose proof CST3 as (HP3 & _ & (errv3 & _ & _ & ST3 & _ & _ & MI3 & _) & _).
  rewrite unsigned_lit in ST3 by wp_lia.
  pose proof RNG_A3_1 as (P0_A3_1 & P16_A3_1 & _ & PC_A3_1 & PIMG_A3_1). wp_box1 P16_A3_1. wp_box1 PIMG_A3_1.
  assert (FUc3 : (f <= f3 + 3)%nat) by (clear - FU3 FUc2; lia). clear FU3.
  unfold mutex_cells in *.
  change (Z.to_nat 40) with 40%nat in *.
  assert (IN_A3_1_3 : In (q3_1, A3_1, 40) ((q3_1, A3_1, 40) :: (q2_1, A2_1, 56) :: (q1_1, A1_1, 80) :: LBall)) by (left; reflexivity).
  assert (IN_A2_1_3 : In (q2_1, A2_1, 56) ((q3_1, A3_1, 40) :: (q2_1, A2_1, 56) :: (q1_1, A1_1, 80) :: LBall)) by (do 1 right; left; reflexivity).
  assert (IN_A1_1_3 : In (q1_1, A1_1, 80) ((q3_1, A3_1, 40) :: (q2_1, A2_1, 56) :: (q1_1, A1_1, 80) :: LBall)) by (do 2 right; left; reflexivity).
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST3) as [ND3 _].
  (* [comment removed for export] *)
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (A1_1, A1_1 + 80)]%Z mb3) as MU6. pose proof (wmono_refl usegs mb3) as WM6.
  wp_clear_aps.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ q1_1 A1_1 80 q2_1 A2_1 56 CST3 IN_A1_1_3 IN_A2_1_3 (wp_nodup_apart [(q3_1, A3_1, 40); (q2_1, A2_1, 56); (q1_1, A1_1, 80)] LBall 2%nat 1%nat (q1_1, A1_1, 80) (q2_1, A2_1, 56) ND3 eq_refl eq_refl ltac:(discriminate))) as AP_A1_1_A2_1_s6.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ q1_1 A1_1 80 q3_1 A3_1 40 CST3 IN_A1_1_3 IN_A3_1_3 (wp_nodup_apart [(q3_1, A3_1, 40); (q2_1, A2_1, 56); (q1_1, A1_1, 80)] LBall 2%nat 0%nat (q1_1, A1_1, 80) (q3_1, A3_1, 40) ND3 eq_refl eq_refl ltac:(discriminate))) as AP_A1_1_A3_1_s6.
  wp_box_aps.
  cprefix. ths. step. wp_brF. step.
  chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into ma6 end.
  assert (CSTa6 : cstate st3 ((q3_1, A3_1, 40) :: (q2_1, A2_1, 56) :: (q1_1, A1_1, 80) :: LBall) LB ((q3_1, 40) :: (q2_1, 56) :: (q1_1, 80) :: L) ma6 (Z_to_bv 64 (bv_unsigned sp + -48)) tp lo B).
  { eapply (cstate_seg _ _ _ _ _ mb3 ma6 _ (Z_to_bv 64 (bv_unsigned sp + -48)) tp lo B (bv_unsigned sp)); [exact CST3| exact MU6| exact WM6| wp_mi| | wp_lia| wp_lia| | wp_stk|].
    - apply Forall_cons; [apply cwin_stack; wp_lia| apply Forall_cons; [apply (cwin_block _ _ _ (q1_1, A1_1, 80)); [exact IN_A1_1_3| |]; unfold blk_addr, blk_size; cbn [fst snd]; wp_lia| apply Forall_nil]].
    - cbn [disjoint_from]. unfold LX_FLAGS. tslia.
    - rewrite unsigned_lit by wp_lia. wp_lia. }
  assert (FRa6 : cframe (fun _ => False) []%Z (bv_unsigned sp) st LBall L m st3 ((q3_1, A3_1, 40) :: (q2_1, A2_1, 56) :: (q1_1, A1_1, 80) :: LBall) ((q3_1, 40) :: (q2_1, 56) :: (q1_1, 80) :: L) ma6).
  { eapply cframe_seg; [eapply cframe_call; [exact FRa5| exact FRM3| wp_lia| intros a X; first [destruct X | exact X | cbn [rin_ivs fst snd] in *; wp_lia]| intros q0 _ X; exact X]| exact MU6| exact WM6| exact HP3| wp_lia|].
    apply Forall_cons; [apply cseg_ok_stack; wp_lia| apply Forall_cons; [apply (cseg_ok_block _ _ _ _ _ (q1_1, A1_1, 80)); [exact IN_A1_1_3| exact (t_fresh_notin (fun _ => False) LBall (q1_1, A1_1, 80) (t_nodup_prefix blk_id [(q3_1, A3_1, 40); (q2_1, A2_1, 56); (q1_1, A1_1, 80)] LBall (q1_1, A1_1, 80) ND3 ltac:(do 2 right; left; reflexivity)))| |]; unfold blk_addr, blk_size; cbn [fst snd]; wp_lia| apply Forall_nil]]. }
  (* [comment removed for export] *)
  eapply climpl_seq.
  { eapply (T_sk_new_null_spec HB_crypto_zalloc_stmt); [wp_lia| eapply croom_weaken; [exact (croom_grow _ _ _ _ _ _ _ _ ROOM (cgrow_trans _ _ _ _ _ _ _ _ _ (cgrow_trans _ _ _ _ _ _ _ _ _ GR1 GR2) GR3))| wp_lia..]| exact CSTa6| rewrite unsigned_lit by wp_lia; unfold SK_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; wp_lia]. }
  intros f4 L4 st4 ms4 (v4 & mb4 & LB4 & RET4 & FU4 & GR4 & CST4 & FRM4 & (q4_1 & A4_1 & -> & -> & -> & RNG_A4_1 & BC4_0)).
  destruct RET4 as (u0_4 & u1_4 & u2_4 & b1_4 & b2_4 & b3_4 & b4_4 & b5_4 & b6_4 & b7_4 & u3_4 & u4_4 & u5_4 & u6_4 & ->).
  cret_lit. rewrite unsigned_lit in * by wp_lia.
  pose proof FRM4 as (CFR4 & _).
  lazymatch goal with FRh : rw_cells _ ma6 (bv_unsigned sp + -48) _ |- _ => pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR4 FRh ltac:(wp_lia)) as FRs4 end.
  repeat match goal with Hb : rw_cells _ ma6 A1_1 _ |- _ => let Hn := fresh "BK" in pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q1_1, A1_1, 80) CFR4 Hb IN_A1_1_3 ltac:(intros X; exact X) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as Hn; clear Hb end.
  repeat match goal with Hb : rw_cells _ ma6 A2_1 _ |- _ => let Hn := fresh "BK" in pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q2_1, A2_1, 56) CFR4 Hb IN_A2_1_3 ltac:(intros X; exact X) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as Hn; clear Hb end.
  repeat match goal with Hb : rw_cells _ ma6 A3_1 _ |- _ => let Hn := fresh "BK" in pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q3_1, A3_1, 40) CFR4 Hb IN_A3_1_3 ltac:(intros X; exact X) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as Hn; clear Hb end.
  pose proof CST4 as (HP4 & _ & (errv4 & _ & _ & ST4 & _ & _ & MI4 & _) & _).
  rewrite unsigned_lit in ST4 by wp_lia.
  pose proof RNG_A4_1 as (P0_A4_1 & P16_A4_1 & _ & PC_A4_1 & PIMG_A4_1). wp_box1 P16_A4_1. wp_box1 PIMG_A4_1.
  assert (FUc4 : (f <= f4 + 4)%nat) by (clear - FU4 FUc3; lia). clear FU4.
  unfold sk_cells in *.
  change (Z.to_nat 56) with 56%nat in *.
  assert (IN_A4_1_4 : In (q4_1, A4_1, 56) ((q4_1, A4_1, 56) :: (q3_1, A3_1, 40) :: (q2_1, A2_1, 56) :: (q1_1, A1_1, 80) :: LBall)) by (left; reflexivity).
  assert (IN_A3_1_4 : In (q3_1, A3_1, 40) ((q4_1, A4_1, 56) :: (q3_1, A3_1, 40) :: (q2_1, A2_1, 56) :: (q1_1, A1_1, 80) :: LBall)) by (do 1 right; left; reflexivity).
  assert (IN_A2_1_4 : In (q2_1, A2_1, 56) ((q4_1, A4_1, 56) :: (q3_1, A3_1, 40) :: (q2_1, A2_1, 56) :: (q1_1, A1_1, 80) :: LBall)) by (do 2 right; left; reflexivity).
  assert (IN_A1_1_4 : In (q1_1, A1_1, 80) ((q4_1, A4_1, 56) :: (q3_1, A3_1, 40) :: (q2_1, A2_1, 56) :: (q1_1, A1_1, 80) :: LBall)) by (do 3 right; left; reflexivity).
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST4) as [ND4 _].
  (* [comment removed for export] *)
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (A1_1, A1_1 + 80); (A4_1, A4_1 + 56)]%Z mb4) as MU10. pose proof (wmono_refl usegs mb4) as WM10.
  wp_clear_aps.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ q1_1 A1_1 80 q2_1 A2_1 56 CST4 IN_A1_1_4 IN_A2_1_4 (wp_nodup_apart [(q4_1, A4_1, 56); (q3_1, A3_1, 40); (q2_1, A2_1, 56); (q1_1, A1_1, 80)] LBall 3%nat 2%nat (q1_1, A1_1, 80) (q2_1, A2_1, 56) ND4 eq_refl eq_refl ltac:(discriminate))) as AP_A1_1_A2_1_s10.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ q1_1 A1_1 80 q3_1 A3_1 40 CST4 IN_A1_1_4 IN_A3_1_4 (wp_nodup_apart [(q4_1, A4_1, 56); (q3_1, A3_1, 40); (q2_1, A2_1, 56); (q1_1, A1_1, 80)] LBall 3%nat 1%nat (q1_1, A1_1, 80) (q3_1, A3_1, 40) ND4 eq_refl eq_refl ltac:(discriminate))) as AP_A1_1_A3_1_s10.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ q1_1 A1_1 80 q4_1 A4_1 56 CST4 IN_A1_1_4 IN_A4_1_4 (wp_nodup_apart [(q4_1, A4_1, 56); (q3_1, A3_1, 40); (q2_1, A2_1, 56); (q1_1, A1_1, 80)] LBall 3%nat 0%nat (q1_1, A1_1, 80) (q4_1, A4_1, 56) ND4 eq_refl eq_refl ltac:(discriminate))) as AP_A1_1_A4_1_s10.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ q4_1 A4_1 56 q1_1 A1_1 80 CST4 IN_A4_1_4 IN_A1_1_4 (wp_nodup_apart [(q4_1, A4_1, 56); (q3_1, A3_1, 40); (q2_1, A2_1, 56); (q1_1, A1_1, 80)] LBall 0%nat 3%nat (q4_1, A4_1, 56) (q1_1, A1_1, 80) ND4 eq_refl eq_refl ltac:(discriminate))) as AP_A4_1_A1_1_s10.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ q4_1 A4_1 56 q2_1 A2_1 56 CST4 IN_A4_1_4 IN_A2_1_4 (wp_nodup_apart [(q4_1, A4_1, 56); (q3_1, A3_1, 40); (q2_1, A2_1, 56); (q1_1, A1_1, 80)] LBall 0%nat 2%nat (q4_1, A4_1, 56) (q2_1, A2_1, 56) ND4 eq_refl eq_refl ltac:(discriminate))) as AP_A4_1_A2_1_s10.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ q4_1 A4_1 56 q3_1 A3_1 40 CST4 IN_A4_1_4 IN_A3_1_4 (wp_nodup_apart [(q4_1, A4_1, 56); (q3_1, A3_1, 40); (q2_1, A2_1, 56); (q1_1, A1_1, 80)] LBall 0%nat 1%nat (q4_1, A4_1, 56) (q3_1, A3_1, 40) ND4 eq_refl eq_refl ltac:(discriminate))) as AP_A4_1_A3_1_s10.
  wp_box_aps.
  cprefix. do 5 step. tcallr T_sk_set_cmp_thunks_proof. all: try first [wp_hyp | reflexivity | eassumption | wp_lia | split; eassumption]. cbv beta delta [mkR]. unfold sk_cells in *. cbn [fst snd] in *. do 4 step. tcallr T_sk_set_copy_thunks_proof. all: try first [wp_hyp | reflexivity | eassumption | wp_lia | split; eassumption]. cbv beta delta [mkR]. unfold sk_cells in *. cbn [fst snd] in *. do 4 step. tcallr T_sk_set_thunks_proof. all: try first [wp_hyp | reflexivity | eassumption | wp_lia | split; eassumption]. cbv beta delta [mkR]. unfold sk_cells in *. cbn [fst snd] in *. ths. step. wp_brF. step.
  chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into ma10 end.
  assert (CSTa10 : cstate st4 ((q4_1, A4_1, 56) :: (q3_1, A3_1, 40) :: (q2_1, A2_1, 56) :: (q1_1, A1_1, 80) :: LBall) LB ((q4_1, 56) :: (q3_1, 40) :: (q2_1, 56) :: (q1_1, 80) :: L) ma10 (Z_to_bv 64 (bv_unsigned sp + -48)) tp lo B).
  { eapply (cstate_seg _ _ _ _ _ mb4 ma10 _ (Z_to_bv 64 (bv_unsigned sp + -48)) tp lo B (bv_unsigned sp)); [exact CST4| exact MU10| exact WM10| wp_mi| | wp_lia| wp_lia| | wp_stk|].
    - apply Forall_cons; [apply cwin_stack; wp_lia| apply Forall_cons; [apply (cwin_block _ _ _ (q1_1, A1_1, 80)); [exact IN_A1_1_4| |]; unfold blk_addr, blk_size; cbn [fst snd]; wp_lia| apply Forall_cons; [apply (cwin_block _ _ _ (q4_1, A4_1, 56)); [exact IN_A4_1_4| |]; unfold blk_addr, blk_size; cbn [fst snd]; wp_lia| apply Forall_nil]]].
    - cbn [disjoint_from]. unfold LX_FLAGS. tslia.
    - rewrite unsigned_lit by wp_lia. wp_lia. }
  assert (FRa10 : cframe (fun _ => False) []%Z (bv_unsigned sp) st LBall L m st4 ((q4_1, A4_1, 56) :: (q3_1, A3_1, 40) :: (q2_1, A2_1, 56) :: (q1_1, A1_1, 80) :: LBall) ((q4_1, 56) :: (q3_1, 40) :: (q2_1, 56) :: (q1_1, 80) :: L) ma10).
  { eapply cframe_seg; [eapply cframe_call; [exact FRa6| exact FRM4| wp_lia| intros a X; first [destruct X | exact X | cbn [rin_ivs fst snd] in *; wp_lia]| intros q0 _ X; exact X]| exact MU10| exact WM10| exact HP4| wp_lia|].
    apply Forall_cons; [apply cseg_ok_stack; wp_lia| apply Forall_cons; [apply (cseg_ok_block _ _ _ _ _ (q1_1, A1_1, 80)); [exact IN_A1_1_4| exact (t_fresh_notin (fun _ => False) LBall (q1_1, A1_1, 80) (t_nodup_prefix blk_id [(q4_1, A4_1, 56); (q3_1, A3_1, 40); (q2_1, A2_1, 56); (q1_1, A1_1, 80)] LBall (q1_1, A1_1, 80) ND4 ltac:(do 3 right; left; reflexivity)))| |]; unfold blk_addr, blk_size; cbn [fst snd]; wp_lia| apply Forall_cons; [apply (cseg_ok_block _ _ _ _ _ (q4_1, A4_1, 56)); [exact IN_A4_1_4| exact (t_fresh_notin (fun _ => False) LBall (q4_1, A4_1, 56) (t_nodup_prefix blk_id [(q4_1, A4_1, 56); (q3_1, A3_1, 40); (q2_1, A2_1, 56); (q1_1, A1_1, 80)] LBall (q4_1, A4_1, 56) ND4 ltac:(left; reflexivity)))| |]; unfold blk_addr, blk_size; cbn [fst snd]; wp_lia| apply Forall_nil]]]. }
  (* [comment removed for export] *)
  eapply climpl_seq.
  { eapply (T_lock_new_spec HB_crypto_zalloc_stmt); [wp_lia| eapply croom_weaken; [exact (croom_grow _ _ _ _ _ _ _ _ ROOM (cgrow_trans _ _ _ _ _ _ _ _ _ (cgrow_trans _ _ _ _ _ _ _ _ _ (cgrow_trans _ _ _ _ _ _ _ _ _ GR1 GR2) GR3) GR4))| wp_lia..]| exact CSTa10| rewrite unsigned_lit by wp_lia; unfold LOCK_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; wp_lia]. }
  intros f5 L5 st5 ms5 (v5 & mb5 & LB5 & RET5 & FU5 & GR5 & CST5 & FRM5 & (q5_1 & A5_1 & -> & -> & -> & RNG_A5_1 & BC5_0)).
  destruct RET5 as (u0_5 & u1_5 & u2_5 & b1_5 & b2_5 & b3_5 & b4_5 & b5_5 & b6_5 & b7_5 & u3_5 & u4_5 & u5_5 & u6_5 & ->).
  cret_lit. rewrite unsigned_lit in * by wp_lia.
  pose proof FRM5 as (CFR5 & _).
  lazymatch goal with FRh : rw_cells _ ma10 (bv_unsigned sp + -48) _ |- _ => pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR5 FRh ltac:(wp_lia)) as FRs5 end.
  repeat match goal with Hb : rw_cells _ ma10 A1_1 _ |- _ => let Hn := fresh "BK" in pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q1_1, A1_1, 80) CFR5 Hb IN_A1_1_4 ltac:(intros X; exact X) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as Hn; clear Hb end.
  repeat match goal with Hb : rw_cells _ ma10 A2_1 _ |- _ => let Hn := fresh "BK" in pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q2_1, A2_1, 56) CFR5 Hb IN_A2_1_4 ltac:(intros X; exact X) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as Hn; clear Hb end.
  repeat match goal with Hb : rw_cells _ ma10 A3_1 _ |- _ => let Hn := fresh "BK" in pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q3_1, A3_1, 40) CFR5 Hb IN_A3_1_4 ltac:(intros X; exact X) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as Hn; clear Hb end.
  repeat match goal with Hb : rw_cells _ ma10 A4_1 _ |- _ => let Hn := fresh "BK" in pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (q4_1, A4_1, 56) CFR5 Hb IN_A4_1_4 ltac:(intros X; exact X) ltac:(unfold blk_addr; cbn [fst snd]; wp_lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; wp_lia)) as Hn; clear Hb end.
  pose proof CST5 as (HP5 & _ & (errv5 & _ & _ & ST5 & _ & _ & MI5 & _) & _).
  rewrite unsigned_lit in ST5 by wp_lia.
  pose proof RNG_A5_1 as (P0_A5_1 & P16_A5_1 & _ & PC_A5_1 & PIMG_A5_1). wp_box1 P16_A5_1. wp_box1 PIMG_A5_1.
  assert (FUc5 : (f <= f5 + 5)%nat) by (clear - FU5 FUc4; lia). clear FU5.
  unfold mutex_cells in *.
  change (Z.to_nat 40) with 40%nat in *.
  assert (IN_A5_1_5 : In (q5_1, A5_1, 40) ((q5_1, A5_1, 40) :: (q4_1, A4_1, 56) :: (q3_1, A3_1, 40) :: (q2_1, A2_1, 56) :: (q1_1, A1_1, 80) :: LBall)) by (left; reflexivity).
  assert (IN_A4_1_5 : In (q4_1, A4_1, 56) ((q5_1, A5_1, 40) :: (q4_1, A4_1, 56) :: (q3_1, A3_1, 40) :: (q2_1, A2_1, 56) :: (q1_1, A1_1, 80) :: LBall)) by (do 1 right; left; reflexivity).
  assert (IN_A3_1_5 : In (q3_1, A3_1, 40) ((q5_1, A5_1, 40) :: (q4_1, A4_1, 56) :: (q3_1, A3_1, 40) :: (q2_1, A2_1, 56) :: (q1_1, A1_1, 80) :: LBall)) by (do 2 right; left; reflexivity).
  assert (IN_A2_1_5 : In (q2_1, A2_1, 56) ((q5_1, A5_1, 40) :: (q4_1, A4_1, 56) :: (q3_1, A3_1, 40) :: (q2_1, A2_1, 56) :: (q1_1, A1_1, 80) :: LBall)) by (do 3 right; left; reflexivity).
  assert (IN_A1_1_5 : In (q1_1, A1_1, 80) ((q5_1, A5_1, 40) :: (q4_1, A4_1, 56) :: (q3_1, A3_1, 40) :: (q2_1, A2_1, 56) :: (q1_1, A1_1, 80) :: LBall)) by (do 4 right; left; reflexivity).
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST5) as [ND5 _].
  (* [comment removed for export] *)
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (A1_1, A1_1 + 80)]%Z mb5) as MU11. pose proof (wmono_refl usegs mb5) as WM11.
  wp_clear_aps.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ q1_1 A1_1 80 q2_1 A2_1 56 CST5 IN_A1_1_5 IN_A2_1_5 (wp_nodup_apart [(q5_1, A5_1, 40); (q4_1, A4_1, 56); (q3_1, A3_1, 40); (q2_1, A2_1, 56); (q1_1, A1_1, 80)] LBall 4%nat 3%nat (q1_1, A1_1, 80) (q2_1, A2_1, 56) ND5 eq_refl eq_refl ltac:(discriminate))) as AP_A1_1_A2_1_s11.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ q1_1 A1_1 80 q3_1 A3_1 40 CST5 IN_A1_1_5 IN_A3_1_5 (wp_nodup_apart [(q5_1, A5_1, 40); (q4_1, A4_1, 56); (q3_1, A3_1, 40); (q2_1, A2_1, 56); (q1_1, A1_1, 80)] LBall 4%nat 2%nat (q1_1, A1_1, 80) (q3_1, A3_1, 40) ND5 eq_refl eq_refl ltac:(discriminate))) as AP_A1_1_A3_1_s11.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ q1_1 A1_1 80 q4_1 A4_1 56 CST5 IN_A1_1_5 IN_A4_1_5 (wp_nodup_apart [(q5_1, A5_1, 40); (q4_1, A4_1, 56); (q3_1, A3_1, 40); (q2_1, A2_1, 56); (q1_1, A1_1, 80)] LBall 4%nat 1%nat (q1_1, A1_1, 80) (q4_1, A4_1, 56) ND5 eq_refl eq_refl ltac:(discriminate))) as AP_A1_1_A4_1_s11.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ q1_1 A1_1 80 q5_1 A5_1 40 CST5 IN_A1_1_5 IN_A5_1_5 (wp_nodup_apart [(q5_1, A5_1, 40); (q4_1, A4_1, 56); (q3_1, A3_1, 40); (q2_1, A2_1, 56); (q1_1, A1_1, 80)] LBall 4%nat 0%nat (q1_1, A1_1, 80) (q5_1, A5_1, 40) ND5 eq_refl eq_refl ltac:(discriminate))) as AP_A1_1_A5_1_s11.
  wp_box_aps.
  cprefix. ths. step. wp_brF. step. ths. step. ths. do 9 step.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -48) _, STh : stk _ _ _ _ |- _ => release_frame FRh STh (bv_unsigned sp) end.
  chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into mz end.
  assert (CSTz : cstate st5 ((q5_1, A5_1, 40) :: (q4_1, A4_1, 56) :: (q3_1, A3_1, 40) :: (q2_1, A2_1, 56) :: (q1_1, A1_1, 80) :: LBall) LB ((q5_1, 40) :: (q4_1, 56) :: (q3_1, 40) :: (q2_1, 56) :: (q1_1, 80) :: L) mz sp tp lo B).
  { eapply (cstate_seg _ _ _ _ _ mb5 mz _ sp tp lo B (bv_unsigned sp)); [exact CST5| exact MU11| exact WM11| wp_mi| | wp_lia| wp_lia| | wp_stk|].
    - apply Forall_cons; [apply cwin_stack; wp_lia| apply Forall_cons; [apply (cwin_block _ _ _ (q1_1, A1_1, 80)); [exact IN_A1_1_5| |]; unfold blk_addr, blk_size; cbn [fst snd]; wp_lia| apply Forall_nil]].
    - cbn [disjoint_from]. unfold LX_FLAGS. tslia.
    - exact HB. }
  assert (FRz : cframe (fun _ => False) []%Z (bv_unsigned sp) st LBall L m st5 ((q5_1, A5_1, 40) :: (q4_1, A4_1, 56) :: (q3_1, A3_1, 40) :: (q2_1, A2_1, 56) :: (q1_1, A1_1, 80) :: LBall) ((q5_1, 40) :: (q4_1, 56) :: (q3_1, 40) :: (q2_1, 56) :: (q1_1, 80) :: L) mz).
  { eapply cframe_seg; [eapply cframe_call; [exact FRa10| exact FRM5| wp_lia| intros a X; first [destruct X | exact X | cbn [rin_ivs fst snd] in *; wp_lia]| intros q0 _ X; exact X]| exact MU11| exact WM11| exact HP5| wp_lia|].
    apply Forall_cons; [apply cseg_ok_stack; wp_lia| apply Forall_cons; [apply (cseg_ok_block _ _ _ _ _ (q1_1, A1_1, 80)); [exact IN_A1_1_5| exact (t_fresh_notin (fun _ => False) LBall (q1_1, A1_1, 80) (t_nodup_prefix blk_id [(q5_1, A5_1, 40); (q4_1, A4_1, 56); (q3_1, A3_1, 40); (q2_1, A2_1, 56); (q1_1, A1_1, 80)] LBall (q1_1, A1_1, 80) ND5 ltac:(do 4 right; left; reflexivity)))| |]; unfold blk_addr, blk_size; cbn [fst snd]; wp_lia| apply Forall_nil]]. }
  apply climpl_done.
  exists (Z_to_bv 64 A1_1), mz, ((q5_1, A5_1, 40) :: (q4_1, A4_1, 56) :: (q3_1, A3_1, 40) :: (q2_1, A2_1, 56) :: (q1_1, A1_1, 80) :: LBall).
  split; [unfold cret; do 14 eexists; reflexivity|]. split; [wp_lia|].
  split; [eapply cgrow_weaken; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ (cgrow_trans _ _ _ _ _ _ _ _ _ (cgrow_trans _ _ _ _ _ _ _ _ _ (cgrow_trans _ _ _ _ _ _ _ _ _ GR1 GR2) GR3) GR4) GR5)| wp_lia..]|].
  split; [exact CSTz|]. split; [exact FRz|].
  exists q1_1, A1_1, q2_1, A2_1, q3_1, A3_1, q4_1, A4_1, q5_1, A5_1.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact RNG_A1_1|]. split; [exact RNG_A2_1|]. split; [exact RNG_A3_1|]. split; [exact RNG_A4_1|]. split; [exact RNG_A5_1|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. split; [wp_cells|]. wp_cells.
Qed.
End WithCeiling0.
