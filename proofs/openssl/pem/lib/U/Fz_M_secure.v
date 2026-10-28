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
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import InitMem. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_kit Fz_M_malloc Fz_M_free Fz_M_cleanse.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition FZ_SECURE_MALLOC : Z := 0xeb288.
Definition FZ_SECURE_FREE : Z := 0xeb944.
Definition FZ_SECURE_CLEAR_FREE : Z := 0xebd54.
Definition CSM_STACK : Z := 128 + CM_STACK.
Definition CSF_STACK : Z := 64 + CF_STACK.

Definition crypto_secure_malloc_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (n lo B : Z),
  (1 <= f)%nat -> croom L (wA n) (wB n) (wBig n) -> 0 < n < 2^31 ->
  cstate s LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - CSM_STACK -> a0 = Z_to_bv 64 n ->
  climpl f L s (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 FZ_SECURE_MALLOC) fc None m (seg_rom usegs))
         (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo B (fun _ => False) [] 1 (wA n) (wB n) (wBig n)
                (cs_malloc_res n LBall L)).

Theorem crypto_secure_malloc_spec : crypto_malloc_stmt -> crypto_secure_malloc_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CM ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB L f n lo B
         Hf ROOM N CST SLO A0. subst a0.
  pose proof CST as (HP & _ & (errv & _ & HB & ST & LO & _ & MI & _) & _ & _ & CIMG & GLO).
  unfold CSM_STACK, CM_STACK, RMALLOC_STACK, FZ_SECURE_MALLOC, GLOBALS_TOP in *.
  cimg_cell CIMG m 0x32e030 [C1 (Z_to_bv 8 0)] SMI.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  (* [comment removed for export] *)
  cprefix. step. carve_frame 144%nat ST. do 20 step.
  step. if_cases K0; zify_cond K0. 2:{ exfalso. apply K0. reflexivity. }
  do 18 step.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -144) _ |- _ => release_frame FRh ST (bv_unsigned sp) end.
  chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into m1 end.
  assert (CSTc : cstate s LBall LB L m1 sp tp lo B).
  { eapply (cstate_seg _ s LBall LB L m m1 sp sp tp lo B (bv_unsigned sp)); try eassumption; try lia.
    - constructor; [apply cwin_stack; lia| constructor].
    - cbn [disjoint_from]. unfold LX_FLAGS. unfold ceil_window in *. lia. }
  assert (FR0 : cframe (fun _ => False) [] (bv_unsigned sp) s LBall L m s LBall L m1).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|]. constructor; [apply cseg_ok_stack; lia| constructor]. }
  eapply climpl_mono.
  { eapply CM with (n := n); [exact Hf| exact ROOM| lia| exact CSTc| unfold CM_STACK, RMALLOC_STACK; lia| reflexivity]. }
  intros f' L' s' ms'. apply cpost_rebase; [exact FR0| intros a X; exact X| intros q _ X; exact X].
Qed.
(* [comment removed for export] *)
Definition crypto_secure_free_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (p : bptr) (A n nm lo B : Z),
  (1 <= f)%nat -> cown LBall L p A n nm ->
  cstate s LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - CSF_STACK -> a0 = Z_to_bv 64 A ->
  climpl f L s (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 FZ_SECURE_FREE) fc None m (seg_rom usegs))
         (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo B (eq p) [] 1 (- wA nm) (- wB nm) (- wBig nm)
                (fun _ LBall' L' _ => LBall' = lb_remove p LBall /\ exists i, nth_error L i = Some (p, nm) /\ L' = cremove i L)).

Theorem crypto_secure_free_spec : crypto_free_stmt -> crypto_secure_free_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB L f p A n nm lo B
         Hf OWNp CST SLO A0. subst a0.
  pose proof CST as (HP & _ & (errv & _ & HB & ST & LO & _ & MI & _) & _ & _ & CIMG & GLO).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNp)) as (A0 & _ & N0 & AC & AIMG).
  unfold CSF_STACK, CF_STACK, RFREE_STACK, FZ_SECURE_FREE, GLOBALS_TOP in *.
  cimg_cell CIMG m 0x32e030 [C1 (Z_to_bv 8 0)] SMI.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  cprefix. step. carve_frame 48%nat ST. do 6 step.
  step. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by (unfold ceil_window in *; lia). lia. }
  do 4 step.
  step. carve_frame 16%nat ST. cstep. do 5 step.
  step. if_cases KH; zify_cond KH. 2:{ exfalso. apply KH. reflexivity. }
  do 5 step.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -64) _ |- _ => release_frame FRh ST (bv_unsigned sp + -48) end.
  step.
  step. if_cases K1; zify_cond K1. 2:{ exfalso. apply K1. reflexivity. }
  do 10 step.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -48) _ |- _ => release_frame FRh ST (bv_unsigned sp) end.
  chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into m1 end.
  assert (CSTc : cstate s LBall LB L m1 sp tp lo B).
  { eapply (cstate_seg _ s LBall LB L m m1 sp sp tp lo B (bv_unsigned sp)); try eassumption; try lia.
    - constructor; [apply cwin_stack; lia| constructor].
    - cbn [disjoint_from]. unfold LX_FLAGS. unfold ceil_window in *. lia. }
  assert (FR0 : cframe (eq p) [] (bv_unsigned sp) s LBall L m s LBall L m1).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|]. constructor; [apply cseg_ok_stack; lia| constructor]. }
  eapply climpl_mono.
  { eapply CF with (p := p) (A := A); [exact Hf| exact OWNp| exact CSTc| unfold CF_STACK, RFREE_STACK; lia| reflexivity]. }
  intros f' L' s' ms'. apply cpost_rebase; [exact FR0| intros a X; exact X| intros q _ X; exact X].
Qed.

(* [comment removed for export] *)
Definition crypto_secure_clear_free_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (p : bptr) (A n nm num lo B : Z) (junk : list byte),
  (1 <= f)%nat -> cown LBall L p A n nm -> 0 <= num <= n -> rw_cells usegs m A [CB (Z.to_nat num) junk] ->
  cstate s LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - CSF_STACK -> a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 num ->
  climpl f L s (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 FZ_SECURE_CLEAR_FREE) fc None m (seg_rom usegs))
         (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo B (eq p) [] 1 (- wA nm) (- wB nm) (- wBig nm)
                (fun _ LBall' L' _ => LBall' = lb_remove p LBall /\ exists i, nth_error L i = Some (p, nm) /\ L' = cremove i L)).

Theorem crypto_secure_clear_free_spec : crypto_free_stmt -> crypto_secure_clear_free_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB L f p A n nm num lo B junk
         Hf OWNp NUM BLK CST SLO A0 A1. subst a0 a1.
  pose proof CST as (HP & _ & (errv & _ & HB & ST & LO & _ & MI & _) & _ & _ & CIMG & GLO).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNp)) as (A0 & _ & N0 & AC & AIMG).
  unfold CSF_STACK, CF_STACK, RFREE_STACK, FZ_SECURE_CLEAR_FREE, GLOBALS_TOP in *.
  cimg_cell CIMG m 0x32e030 [C1 (Z_to_bv 8 0)] SMI.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (A, A + num)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  cprefix. step. carve_frame 48%nat ST. do 7 step.
  step. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by (unfold ceil_window in *; lia). lia. }
  do 5 step.
  step. carve_frame 16%nat ST. cstep. do 5 step.
  step. if_cases KH; zify_cond KH. 2:{ exfalso. apply KH. reflexivity. }
  do 5 step.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -64) _ |- _ => release_frame FRh ST (bv_unsigned sp + -48) end.
  step.
  step. if_cases K1; zify_cond K1. 2:{ exfalso. apply K1. reflexivity. }
  do 3 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (CIMG0 : cimg mm) by (eapply cimg_seg; [exact CIMG| exact MU|]; intros a Ha; unfold cimg_addr, RMallocRep.RGOT_SSP in Ha; cbn [outside]; unfold ceil_window in *; lia) end.
  calle (eapply openssl_cleanse_spec with (D := A) (N := num) (lo := lo) (junk := junk)); try (unfold ceil_window in *; lia).
  do 11 step.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -48) _, STh : stk _ _ _ _ |- _ => release_frame FRh STh (bv_unsigned sp) end.
  chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into mz end.
  assert (CSTc : cstate s LBall LB L mz sp tp lo B).
  { eapply (cstate_seg _ s LBall LB L m mz sp sp tp lo B (bv_unsigned sp)); try eassumption; try lia.
    - constructor; [apply cwin_stack; lia| constructor; [| constructor]].
      apply (cwin_block _ _ _ (p, A, n)); [exact (proj1 OWNp)| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia.
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  assert (FR0 : cframe (eq p) [] (bv_unsigned sp) s LBall L m s LBall L mz).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|].
    constructor; [apply cseg_ok_stack; lia| constructor; [| constructor]].
    apply (cseg_ok_block _ _ _ _ _ (p, A, n)); [exact (proj1 OWNp)| | |]; unfold blk_addr, blk_size; cbn [fst snd]; try lia.
    intros b0 _ NT E. apply NT. symmetry. exact E. }
  eapply climpl_mono.
  { eapply CF with (p := p) (A := A); [exact Hf| exact OWNp| exact CSTc| unfold CF_STACK, RFREE_STACK; lia| reflexivity]. }
  intros f' L' s' ms'. apply cpost_rebase; [exact FR0| intros a X; exact X| intros q _ X; exact X].
Qed.

(* [comment removed for export] *)
Lemma crypto_secure_free_null : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
  a0 = Z_to_bv 64 0 -> stk usegs m lo (bv_unsigned sp) -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv usegs m ->
  evt usegs (fun ms' => exists m', ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                            F (ret_pc ra) fc None m' (seg_rom usegs)
               /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FZ_SECURE_FREE) fc None m (seg_rom usegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until lo. intros A0 ST GLO SLO MI. subst a0. unfold FZ_SECURE_FREE, GLOBALS_TOP in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  step. carve_frame 48%nat ST. do 6 step.
  step. if_cases K0; zify_cond K0. 2:{ exfalso. apply K0. reflexivity. }
  do 7 step.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -48) _ |- _ => release_frame FRh ST (bv_unsigned sp) end.
  apply evt_done. eexists. split; [reflexivity|]. replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by lia. auto.
Qed.

Lemma crypto_secure_clear_free_null : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
  a0 = Z_to_bv 64 0 -> stk usegs m lo (bv_unsigned sp) -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv usegs m ->
  evt usegs (fun ms' => exists m', ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                            F (ret_pc ra) fc None m' (seg_rom usegs)
               /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FZ_SECURE_CLEAR_FREE) fc None m (seg_rom usegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until lo. intros A0 ST GLO SLO MI. subst a0. unfold FZ_SECURE_CLEAR_FREE, GLOBALS_TOP in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  step. carve_frame 48%nat ST. do 7 step.
  step. if_cases K0; zify_cond K0. 2:{ exfalso. apply K0. reflexivity. }
  do 8 step.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -48) _ |- _ => release_frame FRh ST (bv_unsigned sp) end.
  apply evt_done. eexists. split; [reflexivity|]. replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by lia. auto.
Qed.
End WithCeiling0.
