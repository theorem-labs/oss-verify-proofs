(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image ITree Nodes.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnModel BnTree BnInv BnSpecs BnMInv BnBridge.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section WithCeiling0. Context {CE__ : Ceiling}.

Notation bgusegs := ImageBg.bgusegs.

Lemma impl_ebind_post : forall {A B} (t : itree node (exc A)) (g : A -> itree node (exc B)) (Q Q' : B -> machine_state -> Prop) ms,
  (forall a ms', impl bgusegs (at_node bgusegs) (g a) (epost Q) ms' -> impl bgusegs (at_node bgusegs) (g a) (epost Q') ms') ->
  impl bgusegs (at_node bgusegs) (ebind t g) (epost Q) ms -> impl bgusegs (at_node bgusegs) (ebind t g) (epost Q') ms.
Proof.
  intros A B t. induction t as [r|n k IH]; intros g Q Q' ms Hg H.
  - destruct r as [|a]; [|apply Hg; exact H]. cbn in *. eapply evt_mono; [exact H|]. intros ms' _. exact I.
  - cbn in H |- *. eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
    intros rsp. eapply IH; [exact Hg| exact (Hk rsp)].
Qed.

Lemma implM_embed_leaves : forall {A} (t : btree bptr A) (phi : A -> Prop) s (Q : A -> PState -> machine_state -> Prop) ms,
  leaves t phi -> implM bgusegs (interp (embed t)) s Q ms ->
  implM bgusegs (interp (embed t)) s (fun a s' ms' => Q a s' ms' /\ phi a) ms.
Proof.
  intros A t phi. induction t as [a| |n k IH|p k IH]; intros s Q ms HL H; cbn [embed interp leaves] in *.
  - unfold implM, mret in *. cbn in *. eapply evt_mono; [exact H|]. intros ms' HQ. split; [exact HQ| exact HL].
  - apply implM_unr.
  - unfold implM, mbind in *. eapply impl_ebind_post; [|exact H].
    intros [r s1] ms1 H1. cbn [fst snd] in *. apply (IH r s1 Q ms1 (HL r) H1).
  - unfold implM, mbind in *. eapply impl_ebind_post; [|exact H].
    intros [u s1] ms1 H1. cbn [fst snd] in *. apply (IH s1 Q ms1 HL H1).
Qed.

End WithCeiling0.

Definition wexp_leaf (r : bnref) (ls : lstate bptr) (a : unit * lstate bptr) : Prop :=
  (forall r', r <> r' -> getbn r' (snd a) = getbn r' ls)
  /\ bn_top (getbn r (snd a)) = bn_top (getbn r ls) /\ bn_neg (getbn r (snd a)) = bn_neg (getbn r ls)
  /\ bn_flags (getbn r (snd a)) = bn_flags (getbn r ls)
  /\ firstn (bn_top (getbn r ls)) (bn_buf (getbn r (snd a))) = firstn (bn_top (getbn r ls)) (bn_buf (getbn r ls)).

