(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import ImageA.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac ImageA ZBridge Arr.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import Malloc Prog BnBase BnWords BnModel BnTree BnInv BnSpecs BnMInv.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout RT_iface D_defs.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnW Require Import BnMem.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnP Require Import BnKit BnKit2 BnArr.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnWU Require Import BnUTac.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import LibKitA ARun BnHeapA BnRepDefs BnRepA BnIfaceA AsStruct BnAKitA.
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
