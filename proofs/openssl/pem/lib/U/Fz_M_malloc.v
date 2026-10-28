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

Definition CM_STACK : Z := 48 + RMALLOC_STACK.

(* [comment removed for export] *)
Definition crypto_malloc_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (n lo B : Z),
  (1 <= f)%nat -> croom L (wA n) (wB n) (wBig n) -> 0 < n < 2^31 ->
  cstate s LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - CM_STACK -> a0 = Z_to_bv 64 n ->
  climpl f L s (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 FZ_CRYPTO_MALLOC) fc None m (seg_rom usegs))
         (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo B (fun _ => False) [] 1 (wA n) (wB n) (wBig n)
                (cs_malloc_res n LBall L)).

Theorem crypto_malloc_spec : rmalloc_stmt -> crypto_malloc_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros MAL ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB L f n lo B
         Hf ROOM N CST SLO A0. subst a0.
  pose proof CST as (HP & _ & (errv & _ & HB & ST & LO & _ & MI & _) & (_ & _ & GOTM & IMPL & _ & _) & (lb & LATCH) & _ & GLO).
  unfold CM_STACK, RMALLOC_STACK, LX_GOT_FLAGS, LX_STORAGE_FN, LX_FLAGS, FZ_CRYPTO_MALLOC, GLOBALS_TOP in *.
  pose proof (munch_refl [(3334184, 3334184 + 1); (bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  (* [comment removed for export] *)
  assert (TAIL : forall (y10 y11 y12 y13 : word) (mc : mem) (bc : byte) (j8 : list byte),
    rw_cells usegs mc (bv_unsigned sp + -48) [CB 8 j8; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk usegs mc lo (bv_unsigned sp + -48) -> rw_cells usegs mc 3334184 [C1 bc] ->
    munch [(3334184, 3334184 + 1); (bv_unsigned sp - 48, bv_unsigned sp)]%Z m mc -> wmono usegs m mc -> mem_inv usegs mc ->
    climpl f L s
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp a2 y10 y11 y12 y13 a4 a5 a6 a7
               a1 (Z_to_bv 64 n) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xe91c4) fc None mc (seg_rom usegs))
      (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo B (fun _ => False) [] 1 (wA n) (wB n) (wBig n)
             (cs_malloc_res n LBall L))).
  { intros y10 y11 y12 y13 mc bc j8 FRc STc LAc MUc WMc MIc.
    (* [comment removed for export] *)
    cprefix. step. step. chere.
    assert (CSTc : cstate s LBall LB L mc (Z_to_bv 64 (bv_unsigned sp + -48)) tp lo B).
    { eapply (cstate_seg' _ s LBall LB L m mc sp _ tp lo B (bv_unsigned sp)); try eassumption.
      - repeat constructor; unfold cwin; cbn [fst snd]; lia.
      - lia.
      - exists bc. exact LAc.
      - rewrite unsigned_lit by lia. exact STc.
      - rewrite unsigned_lit by lia. lia. }
    assert (FR0 : cframe (fun _ => False) [] (bv_unsigned sp) s LBall L m s LBall L mc).
    { eapply cframe_seg; [apply cframe_refl| exact MUc| exact WMc| exact HP| lia|].
      repeat constructor; unfold cseg_ok, LX_FLAGS; cbn [fst snd]; lia. }
    eapply climpl_seq.
    { eapply (cs_malloc MAL) with (n := n); [exact Hf| exact ROOM| lia| exact CSTc| rewrite unsigned_lit by lia; unfold RMALLOC_STACK; lia| reflexivity]. }
    intros f1 L1 st1 ms1 (v & m1 & LB1 & RET & FU & GR & CST1 & FRM1 & (p & A & jk & -> & -> & -> & RNG & BLK)).
    destruct RET as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & ->).
    cret_lit. rewrite unsigned_lit in * by lia.
    pose proof FRM1 as (CFR1 & _).
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FRc ltac:(lia)) as FR1.
    pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _).
    rewrite unsigned_lit in ST1 by lia.
    pose proof RNG as (A0 & _ & _ & AC & _).
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
    (* [comment removed for export] *)
    cprefix. step. if_cases K3; zify_cond K3. 2:{ exfalso. rewrite ?unsigned_lit in K3 by (unfold ceil_window in *; lia). lia. }
    do 7 step.
    release_frame FR1 ST1 (bv_unsigned sp).
    chere. apply climpl_done.
    exists (Z_to_bv 64 A), m1, ((p, A, n) :: LBall).
    split; [unfold cret; do 14 eexists; reflexivity|]. split; [exact FU|]. split; [exact GR|].
    split. { eapply (cstate_seg [] _ _ _ _ m1 m1 _ sp tp lo B (bv_unsigned sp)); [exact CST1| apply munch_refl| apply wmono_refl| exact MI1| apply Forall_nil| lia| lia| exact I| exact ST1| exact HB]. }
    split. { eapply cframe_call; [exact FR0| exact FRM1| lia| intros a X; exact X| intros q _ X; exact X]. }
    exists p, A, jk. auto 6. }
  cprefix.
  step. carve_frame 48%nat ST. do 5 step. do 8 step.
  (* [comment removed for export] *)
  step. if_cases K0; zify_cond K0. 2:{ exfalso. apply K0. reflexivity. }
  step. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  (* [comment removed for export] *)
  step. step.
  step. if_cases K2; zify_cond K2.
  - (* [comment removed for export] *)
    chere. eapply TAIL; eassumption.
  - (* [comment removed for export] *)
    step. cstep. chere. eapply TAIL; eassumption.
Qed.
End WithCeiling0.
