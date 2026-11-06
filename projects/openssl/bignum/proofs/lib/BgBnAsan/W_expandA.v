(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.

From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac ZBridge RzCPS. 
From OSSVerify.Proofs.openssl.bignum.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Malloc Prog BnBase BnModel BnTree BnInv BnSpecs BnMInv.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgA Require Import Layout R_unwind_chain RT_iface RT_client_kit D_defs I_lkit.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnArr.
From OSSVerify.Proofs.openssl.bignum.lib.BnAsan Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require Import LibKitA ARun BnHeapA BnRepDefs BnRepA BnRepX ImplA BnIfaceA UnwindA EdgesA AsStruct RtCallA W_cryptoA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition BN_FREE_D : Z := 0x2240c0.
Definition BN_FREE_D_STACK : Z := 16 + CRYPTO_CLEAR_FREE_STACK.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Local Notation E_bfd_tail := (E_bn_free_d_223f68 : uk_tail BN_FREE_D CRYPTO_CLEAR_FREE).

Definition BN_EXPAND2 : Z := 0x224400.
Definition BN_WEXPAND : Z := 0x224928.
Definition BN_EXPAND2_STACK : Z := 80 + CRYPTO_CALLOC_STACK.
Local Notation E_be_calloc := (E_bn_expand2_2242bc : uk_call BN_EXPAND2 0x2244a4 CRYPTO_CALLOC).
Local Notation E_be_freed := (E_bn_expand2_224330 : uk_call BN_EXPAND2 0x224518 BN_FREE_D).

Definition bn_expanded (b : bignum bptr) (pn : bptr) (words : nat) : bignum bptr :=
  mkBN (Some pn) (firstn (bn_top b) (bn_buf b) ++ repeat 0 (words - bn_top b)) (bn_top b) (bn_neg b) (bn_flags b).

Definition wexpand_res (r : bnref) (words : nat) (ls ls' : lstate bptr) : Prop :=
  ((words <= bn_dmax (getbn r ls))%nat /\ ls' = ls)
  \/ ((bn_dmax (getbn r ls) < words)%nat /\ exists pn, ls' = setbn r (bn_expanded (getbn r ls) pn words) ls).

Definition BN_WEXPAND_STACK : Z := 16 + BN_EXPAND2_STACK.
Local Notation E_bw_tail := (E_bn_wexpand_224788 : uk_tail BN_WEXPAND BN_EXPAND2).

End WithRT.
