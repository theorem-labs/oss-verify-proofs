(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac ZBridge Arr. 
From OSSVerify.Proofs.openssl.bignum.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Malloc Prog BnBase BnWords BnModel BnTree BnInv BnSpecs BnMInv.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout RT_iface D_defs.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnMem.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OSSVerify.Proofs.openssl.bignum.lib.BnWU Require Import BnUTac.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import LibKitA ARun BnHeapA BnRepDefs BnRepA BnIfaceA AsStruct BnAKitA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Lemma arr_ubA : forall Σ OW LB m D (b : bignum bptr),
  AHEAP Σ OW LB m -> bn_arr m OW D b -> (0 < bn_dmax b)%nat -> 0 < D /\ D mod 16 = 0.
Proof.
  intros Σ OW LB m D b HEAP ARR HD. unfold bn_arr in ARR. destruct (bn_d b) as [p|] eqn:Ed.
  - destruct ARR as [Hin _]. pose proof (AH_range _ _ _ _ _ _ _ HEAP Hin) as (R0 & R16 & _). split; assumption.
  - destruct ARR as [_ Eb]. unfold bn_dmax in HD. rewrite Eb in HD. cbn in HD. lia.
Qed.

Lemma arr_ub_okA : forall Σ OW LB m D (b : bignum bptr) n,
  AHEAP Σ OW LB m -> bn_arr m OW D b -> n <= Z.of_nat (bn_dmax b) -> ub_ptr_ok n D.
Proof.
  intros Σ OW LB m D b n HEAP ARR Hn Hpos.
  destruct (arr_ubA Σ OW LB m D b HEAP ARR ltac:(lia)) as (H0 & H16). split; [exact H0|]. clear - H16. Z.div_mod_to_equations. lia.
Qed.

End WithRT.
