(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image ITree Nodes.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnModel BnTree BnInv BnBridge BgState BgInv BgLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition wexp_leaf (r : bnref) (bs : bstate bptr) (a : unit * bstate bptr) : Prop :=
  (forall r', r <> r' -> getbn r' (snd a) = getbn r' bs)
  /\ bn_top (getbn r (snd a)) = bn_top (getbn r bs) /\ bn_neg (getbn r (snd a)) = bn_neg (getbn r bs)
  /\ bn_flags (getbn r (snd a)) = bn_flags (getbn r bs)
  /\ firstn (bn_top (getbn r bs)) (bn_buf (getbn r (snd a))) = firstn (bn_top (getbn r bs)) (bn_buf (getbn r bs))
  /\ st_ctx (snd a) = st_ctx bs.

Lemma bn_wexpand_leaves : forall r words (bs : bstate bptr), (r < length (st_bns bs))%nat -> (bn_top (getbn r bs) <= bn_dmax (getbn r bs))%nat ->
  leaves (bn_wexpand (tree_ops bptr) r words bs) (wexp_leaf r bs).
Proof.
  intros r words bs HV HT. unfold bn_wexpand, bbind, bget, bret, bunr, bmalloc, bfree_opt, bset, bfree, has_flag.
  cbn [bind ret unreachable lib_malloc lib_free tree_ops tbind fst snd].
  set (b := getbn r bs) in *.
  assert (ID : wexp_leaf r bs (tt, bs)) by (unfold wexp_leaf; cbn [snd]; auto 10).
  destruct (words <=? bn_dmax b)%nat; [exact ID|].
  destruct (BN_WORDS_MAX <? Z.of_nat words); [exact I|].
  destruct (512 <? Z.of_nat words); [exact I|].
  destruct (negb (Z.land (bn_flags b) BN_FLG_STATIC_DATA =? 0)); [exact I|].
  destruct (negb (Z.land (bn_flags b) BN_FLG_SECURE =? 0)); [exact I|].
  cbn [tbind leaves]. intros [p|]; [|exact I].
  assert (NEW : wexp_leaf r bs (tt, setbn r (mkBN (Some p) (firstn (bn_top b) (bn_buf b) ++ repeat 0 (words - bn_top b)) (bn_top b) (bn_neg b) (bn_flags b)) bs)).
  { unfold wexp_leaf. cbn [snd]. split; [intros r' Hne; apply getbn_setbn_other; exact Hne|].
    rewrite getbn_setbn_same by exact HV. cbn [bn_top bn_neg bn_flags bn_buf]. fold b.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [|reflexivity].
    unfold bn_dmax in HT. rewrite firstn_app, firstn_firstn, Nat.min_id, length_firstn, Nat.min_l by exact HT.
    rewrite Nat.sub_diag. cbn [firstn]. apply app_nil_r. }
  destruct (bn_d b) as [q|]; cbn [tbind leaves]; exact NEW.
Qed.
