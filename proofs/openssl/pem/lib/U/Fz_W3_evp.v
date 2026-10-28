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
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit Fz_M_malloc Fz_M_zalloc Fz_M_free Fz_W1_defs Fz_W3_iface.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Theorem evp_ctx_new_spec : crypto_zalloc_stmt -> evp_ctx_new_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CG. unfold evp_ctx_new_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LBall LB L f lo B Hf ROOM CST SLO.
  pose proof CST as (HP & _ & (errv & _ & HB & ST & LO & _ & MI & _) & _ & _ & _ & GLO).
  unfold CZ_STACK, CM_STACK, RMALLOC_STACK, FZ_EVP_CTX_NEW, GLOBALS_TOP in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  destruct (wA_small ECTX ltac:(unfold ECTX, TIER_A_MAX; lia)) as (WA & WB & WC).
  cprefix. step. carve_frame 16%nat ST. do 10 step.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -16) _ |- _ => release_frame FRh ST (bv_unsigned sp) end.
  step. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into m1 end.
  assert (CSTc : cstate st LBall LB L m1 sp tp lo B).
  { eapply (cstate_seg _ st LBall LB L m m1 sp sp tp lo B (bv_unsigned sp)); try eassumption; try lia.
    - repeat constructor; unfold cwin; cbn [fst snd]; lia.
    - cbn [disjoint_from]. unfold LX_FLAGS. unfold ceil_window in *. lia. }
  assert (FR0 : cframe (fun _ => False) [] (bv_unsigned sp) st LBall L m st LBall L m1).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|].
    repeat constructor; unfold cseg_ok; cbn [fst snd]; lia. }
  unfold crypto_zalloc_stmt in CG.
  eapply climpl_mono.
  { eapply CG with (n := ECTX); [exact Hf| rewrite WA, WB, WC; exact ROOM| unfold ECTX; lia| exact CSTc| unfold CZ_STACK, CM_STACK, RMALLOC_STACK; lia| reflexivity]. }
  intros f' L' s' ms'. rewrite WA, WB, WC. apply cpost_rebase; [exact FR0| intros a X; exact X| intros q _ X; exact X].
Qed.

Theorem evp_ctx_free_spec : crypto_free_stmt -> evp_ctx_free_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CF. unfold evp_ctx_free_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LBall LB L f p A lo B Hf OWN CST SLO ->.
  pose proof CST as (HP & _ & (errv & _ & HB & ST & LO & _ & MI & _) & _ & _ & _ & GLO).
  unfold CF_STACK, RFREE_STACK, FZ_EVP_CTX_FREE, GLOBALS_TOP in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  destruct (wA_small ECTX ltac:(unfold ECTX, TIER_A_MAX; lia)) as (WA & WB & WC).
  cprefix. step. carve_frame 16%nat ST. do 9 step.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -16) _ |- _ => release_frame FRh ST (bv_unsigned sp) end.
  step. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mc _) _ => rename mc into m1 end.
  assert (CSTc : cstate st LBall LB L m1 sp tp lo B).
  { eapply (cstate_seg _ st LBall LB L m m1 sp sp tp lo B (bv_unsigned sp)); try eassumption; try lia.
    - repeat constructor; unfold cwin; cbn [fst snd]; lia.
    - cbn [disjoint_from]. unfold LX_FLAGS. unfold ceil_window in *. lia. }
  assert (FR0 : cframe (eq p) [] (bv_unsigned sp) st LBall L m st LBall L m1).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|].
    repeat constructor; unfold cseg_ok; cbn [fst snd]; lia. }
  unfold crypto_free_stmt in CF.
  eapply climpl_mono.
  { eapply CF with (p := p) (n := ECTX) (nm := ECTX); [exact Hf| exact OWN| exact CSTc| unfold CF_STACK, RFREE_STACK; lia| reflexivity]. }
  intros f' L' s' ms'. rewrite WA, WB, WC. apply cpost_rebase; [exact FR0| intros a X; exact X| intros q _ X; exact X].
Qed.

Theorem evp_ctx_free_null_spec : evp_ctx_free_null_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  unfold evp_ctx_free_null_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LBall LB L f lo B CST SLO ->.
  pose proof CST as (HP & _ & (errv & _ & HB & ST & LO & _ & MI & _) & LXS & _ & _ & GLO).
  unfold CF_STACK, RFREE_STACK, FZ_EVP_CTX_FREE, GLOBALS_TOP in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  cprefix. step. carve_frame 16%nat ST. do 9 step.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -16) _ |- _ => release_frame FRh ST (bv_unsigned sp) end.
  step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
  assert (LXS1 : lx_statics m1).
  { lazymatch goal with MUx : munch _ m m1, WMx : wmono usegs m m1 |- _ =>
      eapply lx_statics_agree; [exact (agree_on_of_munch _ _ _ MUx WMx)| | exact LXS];
      intros a Ha; cbn [outside fst snd]; unfold lxs_addr, LX_GOT_STDERR, LX_STDERR_PTR, LX_GOT_FLAGS, LX_STORAGE_FN in Ha; lia end. }
  tcallr crypto_free_null. all: try first [eassumption | reflexivity | lia].
  chere. apply climpl_done.
  lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => rename mx into mz end.
  lazymatch goal with H : stk usegs mz lo _ |- _ => rename H into STz end. lazymatch goal with H : mem_inv usegs mz |- _ => rename H into MIz end.
  lazymatch goal with H : munch _ m mz |- _ => rename H into MUz end. lazymatch goal with H : wmono usegs m mz |- _ => rename H into WMz end.
  do 2 eexists. exists LBall. split; [unfold cret; do 14 eexists; reflexivity|]. split; [lia|]. split; [unfold cgrow; lia|].
  split. { eapply (cstate_seg _ _ _ _ _ m mz _ sp _ lo B (bv_unsigned sp)); [exact CST| exact MUz| exact WMz| exact MIz| | lia| exact HB| | exact STz| exact HB].
    - constructor; [apply cwin_stack; lia| constructor]. - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  split; [| auto]. eapply cframe_seg; [apply cframe_refl| exact MUz| exact WMz| exact HP| lia|]. constructor; [apply cseg_ok_stack; lia| constructor].
Qed.
End WithCeiling0.
