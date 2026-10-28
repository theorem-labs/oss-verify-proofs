(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From Stdlib Require Import ZArith List Lia Bool Arith.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import RT_iface RT_unwind_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Fixpoint lead_cnt (R : Z) (l : list Z) : nat := match l with x :: t => if x =? R then S (lead_cnt R t) else O | [] => O end.
Definition cntR (R : Z) (p : list Z) : nat := lead_cnt R (rev p).

Lemma cntR_app_R : forall R p, cntR R (p ++ [R]) = S (cntR R p).
Proof. intros R p. unfold cntR. rewrite rev_app_distr. cbn [rev app lead_cnt]. rewrite Z.eqb_refl. reflexivity. Qed.

Lemma cntR_app_other : forall R r p, r <> R -> cntR R (p ++ [r]) = O.
Proof. intros R r p H. unfold cntR. rewrite rev_app_distr. cbn [rev app lead_cnt]. destruct (Z.eqb_spec r R); [contradiction | reflexivity]. Qed.

(* [comment removed for export] *)
Definition rec_closedb (f R : Z) (d : nat) : bool :=
  forallb (fun p => (d <=? cntR R p)%nat || path_memb (p ++ [R]) (paths_from f)) (paths_from f).

Lemma rec_closed_step : forall f R d p, rec_closedb f R d = true -> In p (paths_from f) -> (cntR R p < d)%nat -> In (p ++ [R]) (paths_from f).
Proof.
  intros f R d p H Hp Hc. pose proof (proj1 (forallb_forall _ _) H p Hp) as X. cbv beta in X.
  apply Bool.orb_true_iff in X as [X|X]; [apply Nat.leb_le in X; lia|]. exact (path_memb_In _ _ X).
Qed.

Lemma rec_closed_iter : forall f R d, rec_closedb f R d = true ->
  forall j p, In p (paths_from f) -> (cntR R p + j <= d)%nat -> In (p ++ repeat R j) (paths_from f).
Proof.
  intros f R d H j. induction j as [|j IH]; intros p Hp Hc.
  - rewrite app_nil_r. exact Hp.
  - cbn [repeat]. replace (p ++ R :: repeat R j) with ((p ++ [R]) ++ repeat R j) by (rewrite <- app_assoc; reflexivity).
    apply IH; [exact (rec_closed_step f R d p H Hp ltac:(lia))|]. rewrite cntR_app_R. lia.
Qed.

(* [comment removed for export] *)
Definition site_ctxJ (f : Z) (d j : nat) (X0 : list Z) : Prop := (j <= d)%nat /\ site_ctx f X0.

Lemma site_ctxJ_enter : forall f d X0, site_ctx f X0 -> site_ctxJ f d 0 X0.
Proof. intros f d X0 H. split; [lia | exact H]. Qed.

Lemma site_ctxJ_rec : forall f d j X0, site_ctxJ f d j X0 -> (S j <= d)%nat -> site_ctxJ f d (S j) X0.
Proof. intros f d j X0 [_ H] Hj. split; [exact Hj | exact H]. Qed.

Lemma site_ctxJ_call : forall f R d, rec_closedb f R d = true ->
  forall j X0 r g, call_edgeb f r g = true -> r <> R -> site_ctxJ f d j X0 -> site_ctx g (r :: repeat R j ++ X0).
Proof.
  intros f R d HC j X0 r g HE Hr [Hj HX] p Hp.
  pose proof (proj1 (forallb_forall _ _) HE p Hp) as X. cbv beta in X. apply path_memb_In in X.
  pose proof (rec_closed_iter f R d HC j (p ++ [r]) X ltac:(rewrite (cntR_app_other R r p Hr); lia)) as Y.
  pose proof (HX _ Y) as Z. rewrite <- !app_assoc in Z. exact Z.
Qed.

Lemma site_ctxJ_leaf : forall f R d, rec_closedb f R d = true ->
  forall j X0 r, leaf_edgeb f r = true -> r <> R -> site_ctxJ f d j X0 -> In (r :: repeat R j ++ X0) SITE_TRACES.
Proof.
  intros f R d HC j X0 r HE Hr [Hj HX]. apply path_memb_In in HE.
  pose proof (cntR_app_other R r [] Hr) as C. cbn [app] in C.
  pose proof (rec_closed_iter f R d HC j [r] HE ltac:(rewrite C; lia)) as Y.
  exact (HX _ Y).
Qed.
