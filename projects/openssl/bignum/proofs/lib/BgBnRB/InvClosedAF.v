(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac ZBridge RzCPS. 
From OSSVerify.Proofs.openssl.bignum.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Malloc Prog BnBase BnWords BnWordsCorrect BnModel BnTree BnInv BnSpecs BnMInv BgState BgInv BgLib.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout R_unwind_chain RT_iface RT_iface2 RT_client_kit D_defs I_lkit.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import LibKitA ARun BnHeapA ImplA ImplAX UnwindA EdgesA.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BgWords BgArith.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import W_ctxA W_ctx_getA W_ctx_endA.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import BnAKitAF BnCallAF W_small3A W_small4A AFrameKit AFrameCall AFrameTac AFrameEnv AFrameComp ExpKitAF.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import W_ctxAF W_ctx_getAF W_ctx_endAF W_copyAF W_cmpAF W_uaddAF W_usubAF W_subAF W_set_wordAF ShiftKitAF W_shiftAF W_nnmodAF.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require W_rshift1AF.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import InvKitAF W_int_invAF Fr_int_inv Fr_mod_inv W_mod_inverseAF.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Closed.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).

  Local Ltac cle := vm_compute; intros XXc; discriminate XXc.

  Definition INV_CS_A : Z := BN_NNMOD_STACK.

  Lemma rshift1_cl : forall AR1 : ARun, @rshift1_stmtA AR1 UK INV_CS_A MC.
  Proof.
    intros AR1. unfold rshift1_stmtA. intros until ax. intros PRE UW CTX TP HA WR E0 E1.
    eapply (@W_rshift1AF.BN_rshift1_walkA AR1 UK);
      [eapply bn_preA_wk; [exact PRE | cle | clear; lia] | exact UW | exact CTX | exact TP | exact HA | exact WR | exact E0 | exact E1].
  Qed.

  Definition INT_INV_STACK_A : Z := INT_INV_STACK INV_CS_A.
  Definition MOD_INV_STACK_A : Z := BN_MOD_INVERSE_STACK INV_CS_A.

  Definition int_bn_mod_inverse_closedA : int_inv_stmtA INT_INV_STACK_A INT_INV_COST 1 :=
    int_bn_mod_inverse_walkA INV_CS_A ltac:(cle) ltac:(cle) ltac:(cle) ltac:(cle) ltac:(cle) ltac:(cle) ltac:(cle) ltac:(cle) ltac:(cle)
      ltac:(cle) ltac:(cle) ltac:(cle) ltac:(cle) ltac:(cle) ltac:(cle) rshift1_cl.

  Definition BN_mod_inverse_closedA :=
    BN_mod_inverse_walkA INV_CS_A ltac:(cle) ltac:(cle) ltac:(cle) ltac:(cle) ltac:(cle) ltac:(cle) ltac:(cle) ltac:(cle) ltac:(cle)
      ltac:(cle) ltac:(cle) ltac:(cle) ltac:(cle) ltac:(cle) ltac:(cle) rshift1_cl.
End Closed.

