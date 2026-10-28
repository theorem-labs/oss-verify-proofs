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
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import InitMem. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import F_memset Fz_kit Fz_M_cleanse.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition FZ_CLEAR_FREE : Z := 0xe9654.
Definition CCF_STACK : Z := 64 + RFREE_STACK.

(* [comment removed for export] *)
Definition crypto_clear_free_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (p : bptr) (A n nm num lo B : Z) (junk : list byte),
  (1 <= f)%nat -> cown LBall L p A n nm -> 0 <= num <= n -> rw_cells usegs m A [CB (Z.to_nat num) junk] ->
  cstate s LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - CCF_STACK -> a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 num ->
  climpl f L s (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 FZ_CLEAR_FREE) fc None m (seg_rom usegs))
         (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo B (eq p) [] 1 (- wA nm) (- wB nm) (- wBig nm)
                (fun _ LBall' L' _ => LBall' = lb_remove p LBall /\ exists i, nth_error L i = Some (p, nm) /\ L' = cremove i L)).

Theorem crypto_clear_free_spec : rfree_stmt -> crypto_clear_free_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros FRE ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB L f p A n nm num lo B junk
         Hf OWNp NUM BLK CST SLO A0 A1. subst a0 a1.
  pose proof CST as (HP & _ & (errv & _ & HB & ST & LO & _ & MI & _) & (_ & _ & _ & _ & GOTF & IMPL & _) & _ & CIMG & GLO).
  change (LX_GOT_FLAGS + 16) with 0x31c088 in GOTF. change (LX_STORAGE_FN + 16) with 0x31d4f0 in IMPL.
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNp)) as RNG.
  destruct RNG as (A0 & _ & _ & AC & AIMG).
  unfold CCF_STACK, RFREE_STACK, FZ_CLEAR_FREE, GLOBALS_TOP in *.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (A, A + num)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  (* [comment removed for export] *)
  assert (TAIL : forall (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 : word) (mc : mem) (j8 : list byte),
    rw_cells usegs mc (bv_unsigned sp + -48) [CB 8 j8; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk usegs mc lo (bv_unsigned sp + -48) ->
    munch [(bv_unsigned sp - 64, bv_unsigned sp); (A, A + num)]%Z m mc -> wmono usegs m mc -> mem_inv usegs mc ->
    climpl f L s
      (MS (mkR y0 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp y1 y2 y3 sp y4 y5 y6 y7 y8 y9 y10 y11 y12
               y13 (Z_to_bv 64 A) s4 s5 s6 s7 s8 s9 s10 s11 y14 y15 y16 y17)
          F (Z_to_bv 64 0xe968c) fc None mc (seg_rom usegs))
      (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo B (eq p) [] 1 (- wA nm) (- wB nm) (- wBig nm)
             (fun _ LBall' L' _ => LBall' = lb_remove p LBall /\ exists i, nth_error L i = Some (p, nm) /\ L' = cremove i L))).
  { intros y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 mc j8 FRc STc MUc WMc MIc.
    assert (GOTFc : rw_cells usegs mc 3260552 [C8 (wz FZ_CRYPTO_FREE)]).
    { eapply rw_cells_transport; [exact GOTF| exact MUc| exact WMc|]. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. unfold ceil_window in *. lia. }
    assert (IMPLc : rw_cells usegs mc 3265776 [C8 (wz FZ_CRYPTO_FREE)]).
    { eapply rw_cells_transport; [exact IMPL| exact MUc| exact WMc|]. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. unfold ceil_window in *. lia. }
    unfold FZ_CRYPTO_FREE in *.
    cprefix. do 4 step.
    step. if_cases K0; zify_cond K0. 2:{ exfalso. apply K0. reflexivity. }
    do 8 step.
    release_frame FRc STc (bv_unsigned sp).
    chere.
    assert (CSTc : cstate s LBall LB L mc sp tp lo B).
    { eapply (cstate_seg _ s LBall LB L m mc sp sp tp lo B (bv_unsigned sp)); try eassumption; try lia.
      - constructor; [| constructor; [| constructor]]; unfold cwin; cbn [fst snd]; [do 4 right; left; lia|].
        do 5 right. exists (p, A, n). split; [exact (proj1 OWNp)|]. unfold blk_addr, blk_size. cbn [fst snd]. lia.
      - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
    assert (FR0 : cframe (eq p) [] (bv_unsigned sp) s LBall L m s LBall L mc).
    { eapply cframe_seg; [apply cframe_refl| exact MUc| exact WMc| exact HP| lia|].
      constructor; [| constructor; [| constructor]]; unfold cseg_ok; cbn [fst snd]; [left; lia|].
      do 3 right. exists (p, A, n). split; [exact (proj1 OWNp)|]. split; [| unfold blk_addr, blk_size; cbn [fst snd]; lia].
      intros b0 _ NT E. apply NT. symmetry. exact E. }
    eapply climpl_mono.
    { eapply (cs_free FRE) with (p := p) (A := A); [exact Hf| exact OWNp| exact CSTc| unfold RFREE_STACK; lia| reflexivity]. }
    intros f' L' s' ms'. apply cpost_rebase; [exact FR0| intros a X; exact X| intros q _ X; exact X]. }
  cprefix. step. carve_frame 48%nat ST. do 6 step.
  (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by (unfold ceil_window in *; lia). lia. }
  do 3 step.
  (* [comment removed for export] *)
  step. if_cases K2; zify_cond K2.
  - chere. eapply TAIL; eassumption.
  - do 2 step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (CIMG0 : cimg mm) by (eapply cimg_seg; [exact CIMG| exact MU|]; intros a Ha; unfold cimg_addr, RMallocRep.RGOT_SSP in Ha; cbn [outside]; unfold ceil_window in *; lia) end.
    calle (eapply openssl_cleanse_spec with (D := A) (N := num) (lo := lo) (junk := junk)); try (unfold ceil_window in *; lia).
    chere. eapply TAIL; eassumption.
Qed.
End WithCeiling0.
