(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnKara BnModel BnTree BnInv BgState BgLib BgInv BgSpecs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Frame.
Context {ptr : Type}.
Local Notation ST := (bstate ptr) (only parsing).

Definition inner (u : nat) (outs : list bnref) (s s' : ST) : Prop :=
  (length (st_bns s) <= length (st_bns s'))%nat /\ scal_same s s' /\ slots_same u outs s s'.

Lemma inner_refl : forall u o s, inner u o s s.
Proof. intros. split; [lia|]. split; [apply scal_same_refl|apply slots_same_refl]. Qed.

Lemma inner_trans : forall u o1 o2 s s1 s2, inner u o1 s s1 -> inner u o2 s1 s2 -> inner u (o1 ++ o2) s s2.
Proof.
  intros u o1 o2 s s1 s2 (A1 & A2 & A3) (B1 & B2 & B3). split; [lia|]. split; [eapply scal_same_trans; eassumption|].
  eapply slots_same_trans; eassumption.
Qed.

Lemma inner_weaken : forall u o o' s s', (forall r, In r o -> (r < NFIX + u)%nat -> In r o') -> inner u o s s' -> inner u o' s s'.
Proof. intros u o o' s s' H (A1 & A2 & A3). split; [exact A1|]. split; [exact A2|]. eapply slots_same_weaken; [apply Nat.le_refl|exact H|exact A3]. Qed.

Lemma inner_of_keeps : forall u u' o s s', keeps u' o s s' -> (u <= u')%nat -> inner u o s s'.
Proof.
  intros u u' o s s' [[(A1 & _ & _) A2] A3] Hu. split; [exact A1|]. split; [exact A3|].
  eapply slots_same_weaken; [exact Hu| |exact A2]. intros r Hin _. exact Hin.
Qed.

Lemma inner_bns_eq : forall u s s', st_bns s' = st_bns s -> scal_same s s' -> inner u [] s s'.
Proof. intros u s s' E Sc. split; [rewrite E; lia|]. split; [exact Sc|]. intros r _ _. unfold getbn. rewrite E. reflexivity. Qed.

Lemma inner_get : forall u a s s', (length (st_bns s) <= length (st_bns s'))%nat -> scal_same s s' ->
  (forall r, r <> a -> getbn r s' = getbn r s) -> (NFIX + u <= a)%nat -> inner u [] s s'.
Proof. intros u a s s' L Sc H Ha. split; [exact L|]. split; [exact Sc|]. intros r Hr _. apply H. lia. Qed.

Lemma inner_setbn : forall u r b (s : ST), inner u [r] s (setbn r b s).
Proof. intros. split; [rewrite length_setbn; lia|]. split; [unfold scal_same; repeat split; reflexivity|apply slots_same_setbn]. Qed.

Lemma keeps_of_inner : forall u o s s', inner u o s s' ->
  gx_used (st_ctx s') = gx_used (st_ctx s) -> gx_frames (st_ctx s') = gx_frames (st_ctx s) -> keeps u o s s'.
Proof. intros u o s s' (A1 & A2 & A3) Eu Ef. split; [split; [split; [exact A1|split; assumption]|exact A3]|exact A2]. Qed.

Lemma inner_get_slot : forall u o s s' r, inner u o s s' -> (r < NFIX + u)%nat -> ~ In r o -> getbn r s' = getbn r s.
Proof. intros u o s s' r (_ & _ & H) Hr Hn. apply H; assumption. Qed.

End Frame.
