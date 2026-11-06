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
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BgWords BgArith BgMont.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import BnAKitAF BnCallAF AFrameKit AFrameCall AFrameTac AFrameEnv AFrameComp ExpKitAF.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require InvClosedAF.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import MontSetSimF MontSetKitAF Fr_mont_set W_mont_setAF.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require FixFillB.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Closed.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).

  Local Ltac cle := vm_compute; intros XXc; discriminate XXc.

  Definition MONT_SET_CS_A : Z := InvClosedAF.MOD_INV_STACK_A.
  Definition MONT_SET_STACK_A : Z := BN_MONT_CTX_SET_STACK MONT_SET_CS_A.

  Definition BN_MONT_CTX_set_closedA : mont_set_stmtA MONT_SET_STACK_A BN_MONT_CTX_SET_COST 3 :=
    BN_MONT_CTX_set_walkA MONT_SET_CS_A ltac:(cle) ltac:(cle) ltac:(cle) ltac:(cle) ltac:(cle) ltac:(cle) ltac:(cle) ltac:(cle) ltac:(cle)
      ltac:(cle) ltac:(cle) ltac:(cle) ltac:(cle) ltac:(cle) ltac:(cle) (fun AR1 : ARun => @FixFillB.fix_fill AR1).
End Closed.

