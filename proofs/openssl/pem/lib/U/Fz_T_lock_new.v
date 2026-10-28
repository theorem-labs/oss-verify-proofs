(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit Fz_M_malloc Fz_M_zalloc.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy Th_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Th_mutex Th_mutex_init. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_T_kit.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
Lemma rheap_ssp : forall st LB m, RHEAP st LB m -> ssp_cells m rr_guard.
Proof.
  intros st LB m (rs & LB0 & _ & _ & REP & _). destruct REP as (_ & _ & GL & _). destruct GL as (_ & _ & _ & G4 & G5 & _).
  split; [exact G4 | exact G5].
Qed.

Definition FZ_LOCK_NEW : Z := 0xe37d8.
Definition LOCK_NEW_STACK : Z := 48 + CZ_STACK.

Definition lock_new_res (LBall : list block) (L : @clist bptr) : word -> list block -> @clist bptr -> mem -> Prop :=
  fun v LBall' L' m' => exists p A, v = Z_to_bv 64 A /\ LBall' = (p, A, 40) :: LBall /\ L' = (p, 40) :: L
                                /\ rblock_range A 40 /\ rw_cells usegs m' A (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0)).

Definition T_lock_new_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo B : Z),
  (1 <= f)%nat -> croom L (wA 40) (wB 40) (wBig 40) ->
  cstate st LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - LOCK_NEW_STACK ->
  climpl f L st (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 FZ_LOCK_NEW) fc None m (seg_rom usegs))
         (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LBall LB L f m lo B (fun _ => False) [] 1 (wA 40) (wB 40) (wBig 40)
                (lock_new_res LBall L)).

Theorem T_lock_new_spec : crypto_zalloc_stmt -> T_lock_new_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CZ ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LBall LB L f lo B
         Hf ROOM CST SLO.
  pose proof CST as (HP & _ & (errv & _ & HB & ST & LO & _ & MI & _) & _ & _ & _ & GLO).
  unfold LOCK_NEW_STACK, CZ_STACK, CM_STACK, RMALLOC_STACK, FZ_LOCK_NEW, GLOBALS_TOP in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  (* [comment removed for export] *)
  cprefix. step. carve_frame 48%nat ST. do 5 step. do 5 step. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into m0 end.
  assert (CSTc : cstate st LBall LB L m0 (Z_to_bv 64 (bv_unsigned sp + -48)) tp lo B).
  { eapply (cstate_seg _ st LBall LB L m m0 sp _ tp lo B (bv_unsigned sp)); try eassumption.
    - repeat constructor; unfold cwin; cbn [fst snd]; lia.
    - lia.
    - cbn [disjoint_from]. unfold LX_FLAGS. unfold ceil_window in *. lia.
    - rewrite unsigned_lit by lia. exact ST.
    - rewrite unsigned_lit by lia. lia. }
  assert (FR0 : cframe (fun _ => False) [] (bv_unsigned sp) st LBall L m st LBall L m0).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|].
    repeat constructor; unfold cseg_ok; cbn [fst snd]; lia. }
  eapply climpl_seq.
  { eapply CZ with (n := 40); [exact Hf| exact ROOM| lia| exact CSTc| rewrite unsigned_lit by lia; unfold CZ_STACK, CM_STACK, RMALLOC_STACK; lia| reflexivity]. }
  intros f1 L1 st1 ms1 (v & m1 & LB1 & RET & FU & GR & CST1 & FRM1 & (p & A & -> & -> & -> & RNG & BLK)).
  destruct RET as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & ->).
  cret_lit. rewrite unsigned_lit in * by lia.
  pose proof FRM1 as (CFR1 & _).
  lazymatch goal with FRh : rw_cells _ m0 (bv_unsigned sp + -48) _ |- _ => pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FRh ltac:(lia)) as FR1 end.
  pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _).
  rewrite unsigned_lit in ST1 by lia.
  pose proof RNG as (A0 & A16 & _ & AC & AIMG).
  destruct (rheap_ssp _ _ _ HP1) as [GOT GU]. unfold got_ssp, ssp_guard in GOT, GU.
  (* [comment removed for export] *)
  apply (rw_cells_split_CB usegs _ _ [] 16%nat _ _ [12; 4]%nat) in FR1; [|reflexivity].
  cbn [mk_CB_cells app] in FR1.
  lazymatch type of FR1 with rw_cells _ _ _ (?c1 :: ?c2 :: ?rest) =>
    change (c1 :: c2 :: rest) with ([c1] ++ [c2] ++ rest) in FR1 end.
  apply (proj1 (rw_cells_app usegs _ _ _ _)) in FR1. destruct FR1 as [FRlo FR1]. cbn [cells_size csize Nat.add] in FR1.
  apply (proj1 (rw_cells_app usegs _ _ _ _)) in FR1. destruct FR1 as [ATTR FRhi]. cbn [cells_size csize Nat.add] in FRhi.
  replace (bv_unsigned sp + -48 + Z.of_nat 12) with (bv_unsigned sp + -36) in ATTR, FRhi by lia.
  replace (bv_unsigned sp + -36 + Z.of_nat 4) with (bv_unsigned sp + -32) in FRhi by lia.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (A, A + 40)]%Z m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
  unfold ceil_window in *.
  cprefix. step. if_cases K3; zify_cond K3. { exfalso. rewrite ?unsigned_lit in K3 by lia. lia. }
  do 3 step.
  tcall (mutexattr_init_proof).
  1-2: first [eassumption | lia].
  cbv beta delta [mkR].
  do 3 step.
  pose proof mutex_init_attr_proof as MIA. unfold mutex_init_attr_stmt, ssp_cells, got_ssp, ssp_guard in MIA.
  tcall (MIA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo (repeat (Z_to_bv 8 0) (Z.to_nat 40)) rr_guard).
  1-14: first [eassumption | lia | split; eassumption].
  clear MIA. cbv beta delta [mkR].
  do 2 step.
  step.
  eapply evt_cut; [eapply mutexattr_destroy_proof|]. intros ms' ->. cbv beta delta [mkR]. th_ret_lit.
  step. th_if_lit.
  do 7 step.
  (* [comment removed for export] *)
  assert (FRall : rw_cells usegs x3 (bv_unsigned sp + -48)
                    ([CB 12 (take 12 (take 16 (take 24 (take 32 (take 40 junk)))))] ++ [C4 (Z_to_bv 64 0)] ++ [C8 s2; C8 s1; C8 s0; C8 ra])).
  { apply (proj2 (rw_cells_app usegs _ _ _ _)). split; [exact FRlo|]. cbn [cells_size csize Nat.add].
    apply (proj2 (rw_cells_app usegs _ _ _ _)). replace (bv_unsigned sp + -48 + Z.of_nat 12) with (bv_unsigned sp + -36) by lia.
    split; [exact PC1|]. cbn [cells_size csize Nat.add]. replace (bv_unsigned sp + -36 + Z.of_nat 4) with (bv_unsigned sp + -32) by lia. exact FRhi. }
  cbn [app] in FRall.
  release_frame FRall PC (bv_unsigned sp).
  chere.
  apply climpl_done.
  exists (Z_to_bv 64 A), x3, ((p, A, 40) :: LBall).
  assert (INB : In (p, A, 40) ((p, A, 40) :: LBall)) by (left; reflexivity).
  split; [unfold cret; do 14 eexists; reflexivity|]. split; [exact FU|]. split; [exact GR|].
  split. { eapply (cstate_seg [(bv_unsigned sp - 112, bv_unsigned sp); (A, A + 40)]%Z _ _ _ _ m1 x3 _ sp tp lo B (bv_unsigned sp));
           [exact CST1| exact MU1| exact WM1| exact MI1| | lia| lia| | exact PC | exact HB].
    - constructor; [| constructor; [| constructor]]; unfold cwin; cbn [fst snd].
      + do 4 right. left. lia.
      + do 5 right. exists (p, A, 40). split; [exact INB|]. unfold blk_addr, blk_size. cbn [fst snd]. lia.
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  split. { eapply cframe_seg; [eapply cframe_call; [exact FR0| exact FRM1| lia| intros a X; exact X| intros q _ X; exact X]| exact MU1| exact WM1| exact HP1| lia|].
    constructor; [| constructor; [| constructor]]; unfold cseg_ok; cbn [fst snd].
    - left. lia.
    - do 3 right. exists (p, A, 40). split; [exact INB|]. split.
      + destruct FR0 as (_ & KP0 & _). destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST1) as [ND1 _]. exact (cfresh_new _ _ _ _ _ _ KP0 ND1).
      + unfold blk_addr, blk_size. cbn [fst snd]. lia. }
  exists p, A. auto 6.
Qed.
End WithCeiling0.
