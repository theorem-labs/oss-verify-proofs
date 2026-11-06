(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Tac Image ITree Nodes.
From OSSVerify.Proofs.openssl.bndiv.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnModel BnTree BnInv BnSpecs BnMInv BnBridge.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section WithCeiling0. Context {CE__ : Ceiling}.

Notation usegs := Image.usegs.

Lemma impl_ebind_post : forall {A B} (t : itree node (exc A)) (g : A -> itree node (exc B)) (Q Q' : B -> machine_state -> Prop) ms,
  (forall a ms', impl usegs (at_node usegs) (g a) (epost Q) ms' -> impl usegs (at_node usegs) (g a) (epost Q') ms') ->
  impl usegs (at_node usegs) (ebind t g) (epost Q) ms -> impl usegs (at_node usegs) (ebind t g) (epost Q') ms.
Proof.
  intros A B t. induction t as [r|n k IH]; intros g Q Q' ms Hg H.
  - destruct r as [|a]; [|apply Hg; exact H]. cbn in *. eapply evt_mono; [exact H|]. intros ms' _. exact I.
  - cbn in H |- *. eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
    intros rsp. eapply IH; [exact Hg| exact (Hk rsp)].
Qed.

(* [comment removed for export] *)
Lemma implM_embed_leaves : forall {A} (t : btree bptr A) (phi : A -> Prop) s (Q : A -> PState -> machine_state -> Prop) ms,
  leaves t phi -> implM usegs (interp (embed t)) s Q ms ->
  implM usegs (interp (embed t)) s (fun a s' ms' => Q a s' ms' /\ phi a) ms.
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

(* [comment removed for export] *)

Definition wexp_leaf (r : bnref) (ls : lstate bptr) (a : unit * lstate bptr) : Prop :=
  (forall r', r <> r' -> getbn r' (snd a) = getbn r' ls)
  /\ bn_top (getbn r (snd a)) = bn_top (getbn r ls) /\ bn_neg (getbn r (snd a)) = bn_neg (getbn r ls)
  /\ bn_flags (getbn r (snd a)) = bn_flags (getbn r ls)
  /\ firstn (bn_top (getbn r ls)) (bn_buf (getbn r (snd a))) = firstn (bn_top (getbn r ls)) (bn_buf (getbn r ls)).

Lemma bn_wexpand_leaves : forall r words (ls : lstate bptr), valid_refm r ls -> (bn_top (getbn r ls) <= bn_dmax (getbn r ls))%nat ->
  leaves (bn_wexpand (tree_ops bptr) r words ls) (wexp_leaf r ls).
Proof.
  intros r words ls HV HT. unfold bn_wexpand, bbind, bget, bret, bunr, bmalloc, bfree_opt, bset, bfree.
  cbn [bind ret unreachable lib_malloc lib_free tree_ops tbind fst snd].
  set (b := getbn r ls) in *.
  assert (ID : wexp_leaf r ls (tt, ls)) by (unfold wexp_leaf; cbn [snd]; auto).
  destruct (words <=? bn_dmax b)%nat; [exact ID|].
  destruct (BN_WORDS_MAX <? Z.of_nat words); [exact I|].
  destruct (negb (Z.land (bn_flags b) BN_FLG_STATIC_DATA =? 0)); [exact I|].
  destruct (negb (Z.land (bn_flags b) BN_FLG_SECURE =? 0)); [exact I|].
  cbn [tbind leaves]. intros [p|]; [|exact I].
  assert (NEW : wexp_leaf r ls (tt, setbn r (mkBN (Some p) (firstn (bn_top b) (bn_buf b) ++ repeat 0 (words - bn_top b)) (bn_top b) (bn_neg b) (bn_flags b)) ls)).
  { unfold wexp_leaf. cbn [snd]. split; [intros r' Hne; apply getbn_setbn_other; exact Hne|].
    rewrite getbn_setbn_same_m by exact HV. cbn [bn_top bn_neg bn_flags bn_buf]. fold b.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    unfold bn_dmax in HT. rewrite firstn_app, firstn_firstn, Nat.min_id, length_firstn, Nat.min_l by exact HT.
    rewrite Nat.sub_diag. cbn [firstn]. apply app_nil_r. }
  destruct (bn_d b) as [q|]; cbn [tbind leaves]; exact NEW.
Qed.
