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
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit F_memset Fz_kit Fz_M_malloc.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition FZ_CRYPTO_ZALLOC_E : Z := 0xe9224.
Definition CZ_STACK : Z := 32 + CM_STACK.

Definition cs_zalloc_res (n : Z) (LBall : list block) (L : @clist bptr) : word -> list block -> @clist bptr -> mem -> Prop :=
  fun v LBall' L' m' => exists p A, v = Z_to_bv 64 A /\ LBall' = (p, A, n) :: LBall /\ L' = (p, n) :: L
                                  /\ rblock_range A n /\ rw_cells usegs m' A [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))].

Definition crypto_zalloc_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (n lo B : Z),
  (1 <= f)%nat -> croom L (wA n) (wB n) (wBig n) -> 0 < n < 2^31 ->
  cstate s LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - CZ_STACK -> a0 = Z_to_bv 64 n ->
  climpl f L s (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 FZ_CRYPTO_ZALLOC_E) fc None m (seg_rom usegs))
         (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo B (fun _ => False) [] 1 (wA n) (wB n) (wBig n)
                (cs_zalloc_res n LBall L)).

Theorem crypto_zalloc_spec : crypto_malloc_stmt -> crypto_zalloc_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CM ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB L f n lo B
         Hf ROOM N CST SLO A0. subst a0.
  pose proof CST as (HP & _ & (errv & _ & HB & ST & LO & _ & MI & _) & _ & _ & _ & GLO).
  unfold CZ_STACK, CM_STACK, RMALLOC_STACK, FZ_CRYPTO_ZALLOC_E, GLOBALS_TOP in *.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  (* [comment removed for export] *)
  cprefix. step. carve_frame 32%nat ST. do 6 step. chere.
  assert (CSTc : cstate s LBall LB L m0 (Z_to_bv 64 (bv_unsigned sp + -32)) tp lo B).
  { eapply (cstate_seg _ s LBall LB L m m0 sp _ tp lo B (bv_unsigned sp)); try eassumption.
    - repeat constructor; unfold cwin; cbn [fst snd]; lia.
    - lia.
    - cbn [disjoint_from]. unfold LX_FLAGS. unfold ceil_window in *. lia.
    - rewrite unsigned_lit by lia. exact ST.
    - rewrite unsigned_lit by lia. lia. }
  assert (FR0 : cframe (fun _ => False) [] (bv_unsigned sp) s LBall L m s LBall L m0).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|].
    repeat constructor; unfold cseg_ok; cbn [fst snd]; lia. }
  eapply climpl_seq.
  { eapply CM with (n := n); [exact Hf| exact ROOM| lia| exact CSTc| rewrite unsigned_lit by lia; unfold CM_STACK, RMALLOC_STACK; lia| reflexivity]. }
  intros f1 L1 st1 ms1 (v & m1 & LB1 & RET & FU & GR & CST1 & FRM1 & (p & A & jk & -> & -> & -> & RNG & BLK)).
  destruct RET as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & ->).
  cret_lit. rewrite unsigned_lit in * by lia.
  pose proof FRM1 as (CFR1 & _).
  lazymatch goal with FRh : rw_cells _ m0 (bv_unsigned sp + -32) _ |- _ => pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FRh ltac:(lia)) as FR1 end.
  pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _).
  rewrite unsigned_lit in ST1 by lia.
  pose proof RNG as (A0 & _ & _ & AC & _).
  (* [comment removed for export] *)
  cprefix. step. if_cases K3; zify_cond K3. { exfalso. rewrite ?unsigned_lit in K3 by (unfold ceil_window in *; lia). lia. }
  do 7 step.
  release_frame FR1 ST1 (bv_unsigned sp).
  chere.
  eapply climpl_evt.
  { eapply (memset_callZ ra sp) with (D := A) (C := 0) (N := n); [exact BLK| exact MI1| | | |]; unfold ceil_window in *; lia. }
  intros ms2 (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & -> & MU2 & WM2 & MI2 & ZB).
  apply climpl_done.
  exists (Z_to_bv 64 A), m2, ((p, A, n) :: LBall).
  assert (INB : In (p, A, n) ((p, A, n) :: LBall)) by (left; reflexivity).
  split; [unfold cret; do 14 eexists; reflexivity|]. split; [exact FU|]. split; [exact GR|].
  split. { eapply (cstate_seg [(A, A + n)]%Z _ _ _ _ m1 m2 _ sp tp lo B (bv_unsigned sp)); [exact CST1| exact MU2| exact WM2| exact MI2| | lia| lia| | | exact HB].
    - constructor; [| constructor]. unfold cwin. cbn [fst snd]. do 5 right. exists (p, A, n). split; [exact INB|]. unfold blk_addr, blk_size. cbn [fst snd]. lia.
    - cbn [disjoint_from]. unfold LX_FLAGS. destruct RNG as (_ & _ & _ & _ & [X|X]); lia.
    - eapply stk_transport_disjoint; [exact ST1| exact MU2| exact WM2|]. cbn [disjoint_from]. unfold ceil_window in *. lia. }
  split. { eapply cframe_seg; [eapply cframe_call; [exact FR0| exact FRM1| lia| intros a X; exact X| intros q _ X; exact X]| exact MU2| exact WM2| exact HP1| lia|].
    constructor; [| constructor]. unfold cseg_ok. cbn [fst snd]. do 3 right. exists (p, A, n). split; [exact INB|]. split.
    - destruct FR0 as (_ & KP0 & _). destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST1) as [ND1 _]. exact (cfresh_new _ _ _ _ _ _ KP0 ND1).
    - unfold blk_addr, blk_size. cbn [fst snd]. lia. }
  exists p, A. auto 6.
Qed.
End WithCeiling0.
