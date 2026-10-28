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
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition CF_STACK : Z := 16 + RFREE_STACK.

Definition crypto_free_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (p : bptr) (A n nm lo B : Z),
  (1 <= f)%nat -> cown LBall L p A n nm ->
  cstate s LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - CF_STACK -> a0 = Z_to_bv 64 A ->
  climpl f L s (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 FZ_CRYPTO_FREE) fc None m (seg_rom usegs))
         (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo B (eq p) [] 1 (- wA nm) (- wB nm) (- wBig nm)
                (fun _ LBall' L' _ => LBall' = lb_remove p LBall /\ exists i, nth_error L i = Some (p, nm) /\ L' = cremove i L)).

(* [comment removed for export] *)
Lemma crypto_free_head : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
  lx_statics m -> stk usegs m lo (bv_unsigned sp) -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - 16 -> mem_inv usegs m ->
  evt usegs (fun ms' => exists q1 q3 q4 m',
               ms' = MS (mkR ra sp gp tp t0 q1 t2 s0 s1 a0 a1 a2 q3 q4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 RFREE_SYM) fc None m' (seg_rom usegs)
               /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FZ_CRYPTO_FREE) fc None m (seg_rom usegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until lo. intros (_ & _ & _ & _ & GOTF & IMPL & _) ST GLO SLO MI.
  change (LX_GOT_FLAGS + 16) with 0x31c088 in GOTF. change (LX_STORAGE_FN + 16) with 0x31d4f0 in IMPL.
  unfold LX_GOT_FLAGS, LX_STORAGE_FN, FZ_CRYPTO_FREE, GLOBALS_TOP, RFREE_SYM in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  step. carve_frame 16%nat ST. do 7 step.
  step. if_cases K0; zify_cond K0. 2:{ exfalso. apply K0. reflexivity. }
  do 4 step.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -16) _ |- _ => release_frame FRh ST (bv_unsigned sp) end.
  apply evt_done. do 4 eexists. split; [reflexivity|]. auto.
Qed.

Theorem crypto_free_spec : rfree_stmt -> crypto_free_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros FRE ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB L f p A n nm lo B
         Hf OWNp CST SLO A0. subst a0.
  pose proof CST as (HP & _ & (errv & _ & HB & ST & LO & _ & MI & _) & LXS & _ & _ & GLO).
  unfold CF_STACK, RFREE_STACK in *.
  eapply climpl_evt; [eapply (crypto_free_head ra sp); [exact LXS| exact ST| exact GLO| lia| exact MI]|].
  intros ms1 (q1 & q3 & q4 & m1 & -> & MU & WM & MI1 & ST1).
  assert (CSTc : cstate s LBall LB L m1 sp tp lo B).
  { eapply (cstate_seg _ s LBall LB L m m1 sp sp tp lo B (bv_unsigned sp)); try eassumption; try lia.
    - repeat constructor; unfold cwin; cbn [fst snd]; lia.
    - cbn [disjoint_from]. unfold LX_FLAGS, GLOBALS_TOP in *. lia. }
  assert (FR0 : cframe (eq p) [] (bv_unsigned sp) s LBall L m s LBall L m1).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|].
    repeat constructor; unfold cseg_ok; cbn [fst snd]; lia. }
  eapply climpl_seq.
  { eapply (cs_free FRE) with (p := p) (A := A); [exact Hf| exact OWNp| exact CSTc| unfold RFREE_STACK; lia| reflexivity]. }
  intros f1 L1 st1 ms1 (v & m2 & LB1 & RET & FU & GR & CST1 & FRM1 & RES).
  apply climpl_done. exists v, m2, LB1.
  split; [exact RET|]. split; [exact FU|]. split; [exact GR|]. split; [exact CST1|].
  split; [| exact RES].
  eapply cframe_call; [exact FR0| exact FRM1| lia| intros a X; exact X| intros q _ X; exact X].
Qed.

(* [comment removed for export] *)
Lemma crypto_free_null : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
  a0 = Z_to_bv 64 0 ->
  lx_statics m -> stk usegs m lo (bv_unsigned sp) -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - 16 -> mem_inv usegs m ->
  evt usegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
               ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (ret_pc ra) fc None m' (seg_rom usegs)
               /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FZ_CRYPTO_FREE) fc None m (seg_rom usegs)).
Proof.
  intros until lo. intros A0 LXS ST GLO SLO MI. subst a0.
  eapply evt_cut; [eapply (crypto_free_head ra sp); eassumption|].
  intros ms1 (q1 & q3 & q4 & m1 & -> & MU & WM & MI1 & ST1).
  eapply evt_mono; [eapply rfree_null_spec; reflexivity|].
  intros ms2 ->. do 15 eexists. exists m1. split; [reflexivity| auto].
Qed.
End WithCeiling0.
