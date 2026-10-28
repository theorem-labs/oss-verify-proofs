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
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit F_memset Fz_kit Fz_M_malloc Fz_M_zalloc.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition FZ_CRYPTO_CALLOC : Z := 0xe7170.

Definition crypto_calloc_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (num sz lo B : Z),
  (1 <= f)%nat -> croom L (wA (num * sz)) (wB (num * sz)) (wBig (num * sz)) -> 0 <= num < 2^32 -> 0 <= sz < 2^32 -> 0 < num * sz < 2^31 ->
  cstate s LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - CZ_STACK -> a0 = Z_to_bv 64 num -> a1 = Z_to_bv 64 sz ->
  climpl f L s (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 FZ_CRYPTO_CALLOC) fc None m (seg_rom usegs))
         (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo B (fun _ => False) [] 1
                (wA (num * sz)) (wB (num * sz)) (wBig (num * sz)) (cs_zalloc_res (num * sz) LBall L)).

Theorem crypto_calloc_spec : crypto_zalloc_stmt -> crypto_calloc_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CZ ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB L f num sz lo B
         Hf ROOM NUM SZ N CST SLO A0 A1. subst a0 a1.
  pose proof CST as (HP & _ & (errv & _ & HB & ST & LO & _ & MI & _) & _ & _ & _ & GLO).
  unfold CZ_STACK, CM_STACK, RMALLOC_STACK, FZ_CRYPTO_CALLOC, GLOBALS_TOP in *.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (MH : (bv_unsigned (Z_to_bv 64 num) * bv_unsigned (Z_to_bv 64 sz)) ≫ 64 = 0).
  { rewrite !unsigned_lit by lia. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia. }
  (* [comment removed for export] *)
  cprefix. step. carve_frame 32%nat ST. do 8 step.
  step. rewrite MH. if_true.
  do 9 step.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -32) _ |- _ => release_frame FRh ST (bv_unsigned sp) end.
  chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into m1 end.
  assert (CSTc : cstate s LBall LB L m1 sp tp lo B).
  { eapply (cstate_seg _ s LBall LB L m m1 sp sp tp lo B (bv_unsigned sp)); try eassumption; try lia.
    - repeat constructor; unfold cwin; cbn [fst snd]; lia.
    - cbn [disjoint_from]. unfold LX_FLAGS. unfold ceil_window in *. lia. }
  assert (FR0 : cframe (fun _ => False) [] (bv_unsigned sp) s LBall L m s LBall L m1).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|].
    repeat constructor; unfold cseg_ok; cbn [fst snd]; lia. }
  eapply climpl_mono.
  { eapply CZ with (n := num * sz); [exact Hf| exact ROOM| lia| exact CSTc| unfold CZ_STACK, CM_STACK, RMALLOC_STACK; lia|].
    rewrite !unsigned_lit by lia. reflexivity. }
  intros f' L' s' ms'. apply cpost_rebase; [exact FR0| intros a X; exact X| intros q _ X; exact X].
Qed.
End WithCeiling0.
