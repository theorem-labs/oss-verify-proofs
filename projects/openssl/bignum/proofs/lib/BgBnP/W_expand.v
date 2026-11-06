(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OSSVerify.Proofs.openssl.bignum.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bignum.lib.BgMallocP Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnModel BnTree BnInv BnSpecs BnMInv BnBridge.
From OSSVerify.Proofs.openssl.bignum.lib.BgP Require Import Layout Lib_iface Lib_kit F_memset F_memcpy.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnMem.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnArr.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnP Require Import BnHeap BnRep BnIface W_crypto.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.openssl.bignum.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Ltac to_implM :=
  lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
    lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition BN_EXPAND2 : Z := 0xf5a98.
Definition BN_WEXPAND : Z := 0xf5d18.
Definition BN_EXPAND2_STACK : Z := 48 + 8400.

Definition bn_expanded (b : bignum bptr) (pn : bptr) (words : nat) : bignum bptr :=
  mkBN (Some pn) (firstn (bn_top b) (bn_buf b) ++ repeat 0 (words - bn_top b)) (bn_top b) (bn_neg b) (bn_flags b).

Definition wexpand_res (r : bnref) (words : nat) (ls ls' : lstate bptr) : Prop :=
  ((words <= bn_dmax (getbn r ls))%nat /\ ls' = ls)
  \/ ((bn_dmax (getbn r ls) < words)%nat /\ exists pn, ls' = setbn r (bn_expanded (getbn r ls) pn words) ls).

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Definition BN_WEXPAND_STACK : Z := 16 + BN_EXPAND2_STACK.

  End Proofs.
End WithCeiling0.
