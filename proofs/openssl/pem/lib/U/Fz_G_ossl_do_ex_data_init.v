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
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_G_pkit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_M_malloc Fz_M_zalloc Th_mutex Fz_T_lock_new Fz_G_ossl_lib_ctx_get_ex_data_global.
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

Definition FZ_G_ossl_do_ex_data_init : Z := 0xe4de4.
Definition ossl_do_ex_data_init_STACK : Z := 32 + LOCK_NEW_STACK.

Definition ossl_do_ex_data_init_res (LBall : list block) (L : @clist bptr) : word -> list block -> @clist bptr -> mem -> Prop :=
  fun v LBall' L' m' => exists q1_1 A1_1,
       v = (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 A1_1))
    /\ LBall' = (q1_1, A1_1, 40) :: LBall /\ L' = (q1_1, 40) :: L
    /\ rblock_range A1_1 40
    /\ rw_cells usegs m' 3333840 [C8 (Z_to_bv 64 A1_1)]
    /\ rw_cells usegs m' A1_1 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].

Definition ossl_do_ex_data_init_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (x_2e8340 : list byte)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo B : Z),
  (1 <= f)%nat -> croom L (wA 40) (wB 40) (wBig 40) ->
  cstate st LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - ossl_do_ex_data_init_STACK ->
  a0 = Z_to_bv 64 0x32dec8 ->
  rw_cells usegs m 0x32ded0 [CB 8 x_2e8340] ->
  climpl f L st (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 FZ_G_ossl_do_ex_data_init) fc None m (seg_rom usegs))
         (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LBall LB L f m lo B (fun _ => False) [(0x32ded0, 0x32ded8)]%Z 1
                (wA 40) (wB 40) (wBig 40) (ossl_do_ex_data_init_res LBall L)).

Theorem ossl_do_ex_data_init_spec : crypto_zalloc_stmt -> ossl_do_ex_data_init_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros HB_crypto_zalloc_stmt ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x_2e8340 F fc m st LBall LB L f lo B
         Hf ROOM CST SLO PIN_a0 SC_2e8340. subst a0.
  pose proof CST as (HP & OWN & (errv & _ & HB & ST & LO & _ & MI & _) & _ & _ & _ & GLO).
  unfold ossl_do_ex_data_init_STACK, LOCK_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK, FZ_G_ossl_do_ex_data_init, GLOBALS_TOP in *. unfold ceil_window in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (w_bounds 40 ltac:(lia)) as WB40.
  (* [comment removed for export] *)
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU1. pose proof (wmono_refl usegs m) as WM1.
  wp_clear_aps.
  cprefix. step. carve_frame 32%nat ST. do 3 ths. do 2 step. tcallr ossl_lib_ctx_get_ex_data_global_s0_walk. all: try first [wp_hyp | reflexivity | eassumption | wp_lia | split; eassumption]. cbv beta delta [mkR].  step. wp_brF. do 2 step.
  chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into ma1 end.
  assert (CSTa1 : cstate st LBall LB L ma1 (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo B).
  { eapply (cstate_seg _ _ _ _ _ m ma1 _ (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo B (bv_unsigned sp)); [exact CST| exact MU1| exact WM1| wp_mi| | wp_lia| wp_lia| | wp_stk|].
    - apply Forall_cons; [apply cwin_stack; wp_lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. tslia.
    - rewrite unsigned_lit by wp_lia. wp_lia. }
  assert (FRa1 : cframe (fun _ => False) [(0x32ded0, 0x32ded8)]%Z (bv_unsigned sp) st LBall L m st LBall L ma1).
  { eapply cframe_seg; [apply cframe_refl| exact MU1| exact WM1| exact HP| wp_lia|].
    apply Forall_cons; [apply cseg_ok_stack; wp_lia| apply Forall_nil]. }
  (* [comment removed for export] *)
  eapply climpl_seq.
  { eapply (T_lock_new_spec HB_crypto_zalloc_stmt); [wp_lia| eapply croom_weaken; [exact ROOM| wp_wnorm; wp_lia..]| exact CSTa1| rewrite unsigned_lit by wp_lia; unfold LOCK_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK; wp_lia]. }
  intros f1 L1 st1 ms1 (v1 & mb1 & LB1 & RET1 & FU1 & GR1 & CST1 & FRM1 & (q1_1 & A1_1 & -> & -> & -> & RNG_A1_1 & BC1_0)).
  destruct RET1 as (u0_1 & u1_1 & u2_1 & b1_1 & b2_1 & b3_1 & b4_1 & b5_1 & b6_1 & b7_1 & u3_1 & u4_1 & u5_1 & u6_1 & ->).
  cret_lit. rewrite unsigned_lit in * by wp_lia.
  pose proof FRM1 as (CFR1 & _).
  lazymatch goal with FRh : rw_cells _ ma1 (bv_unsigned sp + -32) _ |- _ => pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FRh ltac:(wp_lia)) as FRs1 end.
  match goal with Hs : rw_cells _ ma1 0x32ded0 _ |- _ => let Hn := fresh "SK" in cst_static CFR1 Hs Hn; clear Hs end.
  pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _).
  rewrite unsigned_lit in ST1 by wp_lia.
  pose proof RNG_A1_1 as (P0_A1_1 & P16_A1_1 & _ & PC_A1_1 & PIMG_A1_1). wp_box1 P16_A1_1. wp_box1 PIMG_A1_1.
  assert (FUc1 : (f <= f1 + 1)%nat) by (clear - FU1; lia). clear FU1.
  unfold mutex_cells in *.
  change (Z.to_nat 40) with 40%nat in *.
  assert (IN_A1_1_1 : In (q1_1, A1_1, 40) ((q1_1, A1_1, 40) :: LBall)) by (left; reflexivity).
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST1) as [ND1 _].
  (* [comment removed for export] *)
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (0x32ded0, 0x32ded8)]%Z mb1) as MU2. pose proof (wmono_refl usegs mb1) as WM2.
  wp_clear_aps.
  cprefix. do 2 step. wp_brF. ths. do 6 step.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -32) _, STh : stk _ _ _ _ |- _ => release_frame FRh STh (bv_unsigned sp) end.
  chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into mz end.
  assert (CSTz : cstate st1 ((q1_1, A1_1, 40) :: LBall) LB ((q1_1, 40) :: L) mz sp tp lo B).
  { eapply (cstate_seg _ _ _ _ _ mb1 mz _ sp tp lo B (bv_unsigned sp)); [exact CST1| exact MU2| exact WM2| wp_mi| | wp_lia| wp_lia| | wp_stk|].
    - apply Forall_cons; [apply cwin_stack; wp_lia| apply Forall_cons; [first [apply cwin_bss; wp_lia | unfold cwin; cbn [fst snd]; wp_lia]| apply Forall_nil]].
    - cbn [disjoint_from]. unfold LX_FLAGS. tslia.
    - exact HB. }
  assert (FRz : cframe (fun _ => False) [(0x32ded0, 0x32ded8)]%Z (bv_unsigned sp) st LBall L m st1 ((q1_1, A1_1, 40) :: LBall) ((q1_1, 40) :: L) mz).
  { eapply cframe_seg; [eapply cframe_call; [exact FRa1| exact FRM1| wp_lia| intros a X; first [destruct X | exact X | cbn [rin_ivs fst snd] in *; wp_lia]| intros q0 _ X; exact X]| exact MU2| exact WM2| exact HP1| wp_lia|].
    apply Forall_cons; [apply cseg_ok_stack; wp_lia| apply Forall_cons; [apply cseg_ok_static; [wp_lia| wp_lia| intros a Ha; cbn [rin_ivs fst snd]; wp_lia]| apply Forall_nil]]. }
  apply climpl_done.
  exists (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 A1_1)), mz, ((q1_1, A1_1, 40) :: LBall).
  split; [unfold cret; do 14 eexists; reflexivity|]. split; [wp_lia|].
  split; [eapply cgrow_weaken; [exact GR1| wp_lia..]|].
  split; [exact CSTz|]. split; [exact FRz|].
  exists q1_1, A1_1.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact RNG_A1_1|]. split; [wp_cells|]. wp_cells.
Qed.
End WithCeiling0.
