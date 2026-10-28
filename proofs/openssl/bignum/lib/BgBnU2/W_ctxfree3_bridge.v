(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image Arr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prog BnBase BnModel BnTree BnInv BgState BgInv.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnMem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap BnRep.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU2 Require Import W_ctxfree3.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition Rfree (m : mem) (L : list block) : bnR := fun a b _ => bn_rep_rw m L None a b /\ bg_ok b /\ bn_flags b = 0.

Lemma Rfree_pbn : forall m L a b r, Rfree m L a b r -> pbn m L a b.
Proof.
  intros m L a b r ((D & CE & AR) & (OK1 & OK2 & OK3 & OK4) & FL). exists D. split; [exact CE|].
  unfold bn_arr in AR. split; [| split; [unfold BG_DMAX in OK3; lia| exact FL]].
  destruct (bn_d b) as [p|]; [exact AR| exact (proj1 AR)].
Qed.

Lemma bns_gen_pbns : forall m L l a i, bns_gen (Rfree m L) a l i -> pbns m L a l.
Proof.
  intros m L l. induction l as [|b l IH]; intros a i H; [exact I|]. cbn [bns_gen pbns] in *. destruct H as [H1 H2].
  split; [eapply Rfree_pbn; exact H1| eapply IH; exact H2].
Qed.

Lemma items_gen_pitems : forall m L items Hs vals k prev,
  items_gen (Rfree m L) false m L items Hs vals k prev -> pitems m L items Hs vals prev.
Proof.
  intros m L items. induction items as [|q items IH]; intros Hs vals k prev HG; destruct Hs as [|H Hs]; cbn [items_gen pitems] in *;
    [exact I| exact HG| contradiction|].
  destruct HG as (Hin & H16 & Hb & HL & HG). split; [exact Hin|]. split; [exact H16|].
  split; [eapply bns_gen_pbns; exact Hb|]. split; [exact (HL eq_refl)| eapply IH; exact HG].
Qed.

