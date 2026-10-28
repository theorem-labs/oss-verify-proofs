(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr ImageA.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnModel BnInv BnMInv.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import RT_iface.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnAsan Require Import AsKit. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import LibKitA ARun BnHeapA BnRepDefs BnRepA BnRepX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Theorem lib_state_h_icall2 : forall Σ LB cxo hs ls m m' OW AD EA SP d1 n1 d2 n2,
  AHEAP Σ OW LB m -> lib_state_hc cxo hs ls m OW AD EA ->
  agree_on (fun a => aclient_addr (OW ++ LB) SP a /\ ~ (d1 <= a < d1 + n1) /\ ~ (d2 <= a < d2 + n2)) m m' ->
  w_okc OW LB ls AD EA cxo hs (d1, d1 + n1) -> w_okc OW LB ls AD EA cxo hs (d2, d2 + n2) ->
  lib_state_hc cxo hs ls m' OW AD EA.
Proof.
  intros Σ LB cxo hs ls m m' OW AD EA SP d1 n1 d2 n2 HEAP HS AG HW1 HW2.
  destruct (lib_state_h_parts _ _ _ _ _ _ HS) as (IDS & ADB & ERRB & _).
  eapply lib_state_hc_agree; [exact HS|]. eapply agree_on_mono; [exact AG|]. intros x Hx. split.
  - destruct (own_fp_lib _ _ _ _ _ _ _ HS Hx) as [HL|(b & Hb & Hr)]; [apply libw_client; exact HL|].
    right; right. exists b. split; [apply in_or_app; left; exact Hb | exact Hr].
  - assert (FW : Forall (w_okc OW LB ls AD EA cxo hs) [(d1, d1 + n1); (d2, d2 + n2)]) by (constructor; [exact HW1 | constructor; [exact HW2 | constructor]]).
    pose proof (own_fp_outside Σ OW LB m HEAP ls AD EA IDS ADB ERRB cxo hs [(d1, d1 + n1); (d2, d2 + n2)] x FW Hx) as O.
    cbn [outside] in O. tauto.
Qed.

End WithRT.
