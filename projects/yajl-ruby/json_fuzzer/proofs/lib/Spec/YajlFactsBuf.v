(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlBuf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ypost_bind_w : forall {A B} (m : yprog A) (f : A -> yprog B) (Q : A -> Prop) (R : B -> Prop),
  (forall a, Q a -> ypost (f a) R) -> ypost m Q -> ypost (ybind m f) R.
Proof. intros; eapply ypost_bind; eauto. Qed.

Lemma ypost_ymalloc : forall n (Q : option yptr -> Prop), (forall r, Q r) -> ypost (ymalloc n) Q.
Proof. intros; cbn; auto. Qed.
Lemma ypost_yrealloc : forall p n (Q : option yptr -> Prop), (forall r, Q r) -> ypost (yrealloc p n) Q.
Proof. intros; cbn; auto. Qed.
Lemma ypost_yfree : forall p (Q : unit -> Prop), Q tt -> ypost (yfree p) Q.
Proof. intros; cbn; auto. Qed.
Lemma ypost_yemit : forall bs (Q : unit -> Prop), Q tt -> ypost (yemit bs) Q.
Proof. intros; cbn; auto. Qed.
Lemma ypost_yassert : forall b (Q : unit -> Prop), b = true -> Q tt -> ypost (yassert b) Q.
Proof. intros b Q -> HQ; exact HQ. Qed.

(* [comment removed for export] *)
Ltac ystep Q := eapply (ypost_bind_w _ _ Q).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition buf_inv (b : ybuf) : Prop :=
  0 <= yb_used b /\ yb_used b = zlength (yb_bytes b) /\ 0 <= yb_len b /\
  (yb_data b = None -> yb_len b = 0 /\ yb_used b = 0) /\
  (yb_data b <> None -> yb_used b < yb_len b) /\
  (yb_state b <> BS_ok -> yb_data b = None).

Ltac buf_tac :=
  unfold buf_inv in *;
  cbn [ypost ybind yfree ymalloc yrealloc yassert ybuf_set_error
       yb_state yb_len yb_used yb_data yb_bytes buf_state_ok negb andb orb] in *;
  intuition (subst; auto; try lia; try congruence).

Lemma buf_inv_zero : buf_inv ybuf_zero.
Proof. unfold buf_inv; cbn. repeat split; intros; try lia; congruence. Qed.

Lemma buf_inv_error : forall e, buf_inv (mkBuf e 0 0 None []).
Proof. intros; unfold buf_inv; cbn. repeat split; intros; try lia; congruence. Qed.

Lemma zlength_app : forall {A} (l1 l2 : list A), zlength (l1 ++ l2) = zlength l1 + zlength l2.
Proof. intros; unfold zlength; rewrite length_app; lia. Qed.

Lemma zlength_nil : forall {A}, zlength (@nil A) = 0.
Proof. reflexivity. Qed.

Lemma zlength_nonneg : forall {A} (l : list A), 0 <= zlength l.
Proof. intros; unfold zlength; lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ens_need_loop_spec : forall fuel want need used,
  0 < need -> 0 <= used < need -> 0 <= want ->
  want + used < need * 2 ^ (Z.of_nat fuel) ->
  let r := ens_need_loop fuel want need used in
  used + want < r /\ need <= r /\ (r = need \/ r <= 2 * (used + want)).
Proof.
  induction fuel as [|fuel IH]; intros want need used Hn Hu Hw Hf; cbn [ens_need_loop].
  - cbn in Hf. lia.
  - destruct (Z.leb_spec (need - used) want); cbn [andb].
    + destruct (Z.ltb_spec 0 need); [|lia].
      assert (Hf' : want + used < need * 2 * 2 ^ Z.of_nat fuel).
      { rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hf; lia. }
      specialize (IH want (need * 2) used ltac:(lia) ltac:(lia) Hw Hf'). cbv zeta in IH. lia.
    + lia.
Qed.

(* [comment removed for export] *)
Lemma ens_need_loop_bounds : forall want need used,
  0 < need -> 0 <= used < need -> 0 <= want -> want + used < 2^64 ->
  let r := ens_need_loop ENS_FUEL want need used in
  used + want < r /\ need <= r /\ (r = need \/ r <= 2 * (used + want)).
Proof.
  intros. apply ens_need_loop_spec; auto. unfold ENS_FUEL. cbn [Z.of_nat].
  assert (2^64 <= need * 2 ^ Z.of_nat 64) by (change (Z.of_nat 64) with 64; nia). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ybuf_set_error_post : forall b e, e <> BS_ok ->
  ypost (ybuf_set_error b e) (fun b' => buf_inv b' /\ yb_state b' = e /\ yb_data b' = None /\ yb_bytes b' = []).
Proof.
  intros b e He. unfold ybuf_set_error. cbn. split; [apply buf_inv_error|auto].
Qed.

(* [comment removed for export] *)
Definition ens_post (b : ybuf) (want : Z) (b' : ybuf) : Prop :=
  buf_inv b' /\
  (yb_state b' <> BS_ok -> yb_bytes b' = []) /\
  (yb_state b' = BS_ok ->
     yb_data b' <> None /\ yb_used b' = yb_used b /\ yb_bytes b' = yb_bytes b /\
     yb_used b' + want < yb_len b' /\
     yb_len b' <= Z.max (Z.max (yb_len b) YAJL_BUF_INIT_SIZE) (2 * (yb_used b + want))).

Lemma ybuf_ensure_available_post : forall b want,
  buf_inv b -> yb_state b = BS_ok -> 0 <= want -> yb_used b + want < 2^64 ->
  ypost (ybuf_ensure_available b want) (ens_post b want).
Proof.
  intros b want Hinv Hst Hw Hbig.
  destruct Hinv as (Hu0 & Hub & Hl0 & Hnone & Hsome & Herr).
  unfold ybuf_ensure_available. rewrite Hst.
  ystep (fun (first : ybuf + ybuf) =>
           match first with
           | inr b' => buf_inv b' /\ yb_state b' = BS_overflow /\ yb_bytes b' = []
           | inl b1 => buf_inv b1 /\ yb_state b1 = BS_ok /\ yb_data b1 <> None /\
                       yb_used b1 = yb_used b /\ yb_bytes b1 = yb_bytes b /\
                       yb_len b1 <= Z.max (yb_len b) YAJL_BUF_INIT_SIZE /\ 0 < yb_len b1
           end).
  2:{ destruct (yb_data b) as [d|] eqn:Hd.
      - cbn. specialize (Hsome ltac:(congruence)). rewrite Hd in *. buf_tac.
      - cbn. intros [p|]; cbn.
        + specialize (Hnone eq_refl). unfold YAJL_BUF_INIT_SIZE. buf_tac.
        + split; [apply buf_inv_error|auto]. }
  intros [b1|b'].
  - intros (Hinv1 & Hst1 & Hd1 & Hu1 & Hby1 & Hlen1 & Hlpos).
    destruct Hinv1 as (H1 & H2 & H3 & H4 & H5 & H6).
    destruct (Z.eqb_spec want 0).
    + cbn -[Z.mul Z.add]. unfold ens_post. rewrite Hst1. specialize (H5 Hd1). buf_tac.
    + pose proof (ens_need_loop_bounds want (yb_len b1) (yb_used b1) Hlpos
                    ltac:(specialize (H5 Hd1); lia) Hw ltac:(lia)) as Hr.
      cbv zeta in Hr.
      remember (ens_need_loop ENS_FUEL want (yb_len b1) (yb_used b1)) as r eqn:Er; clear Er.
      destruct Hr as (Hr1 & Hr2 & Hr3).
      destruct (Z.ltb_spec r (yb_used b1)); [lia|].
      destruct (Z.eqb_spec r 0); [lia|]. cbn [orb].
      destruct (Z.eqb_spec r (yb_len b1)); cbn [negb].
      * cbn -[Z.mul Z.add]. unfold ens_post. rewrite Hst1. buf_tac.
      * cbn -[Z.mul Z.add]. intros [p|]; unfold ens_post; buf_tac.
  - intros (Hinv' & Hst' & Hby'). cbn -[Z.mul Z.add]. unfold ens_post. rewrite Hst'. buf_tac.
Qed.

(* [comment removed for export] *)
Definition app_post (b : ybuf) (src : list Z) (b' : ybuf) : Prop :=
  buf_inv b' /\
  (yb_state b' <> BS_ok -> yb_bytes b' = []) /\
  (yb_state b' = BS_ok ->
     yb_data b' <> None /\ yb_bytes b' = yb_bytes b ++ src /\
     yb_len b' <= Z.max (Z.max (yb_len b) YAJL_BUF_INIT_SIZE) (2 * (yb_used b + zlength src))).

Lemma ybuf_append_post : forall b src,
  buf_inv b -> yb_state b = BS_ok -> yb_used b + zlength src < 2^64 ->
  ypost (ybuf_append b src) (app_post b src).
Proof.
  intros b src Hinv Hst Hbig. unfold ybuf_append.
  ystep (ens_post b (zlength src)).
  2:{ apply ybuf_ensure_available_post; auto. apply zlength_nonneg. }
  intros b1 (Hinv1 & Herr1 & Hok1).
  destruct (yb_state b1) eqn:Hs1.
  - specialize (Hok1 eq_refl). destruct Hok1 as (Hd & Hu & Hby & Hroom & Hlen).
    destruct (Z.ltb_spec 0 (zlength src)); cbn.
    + unfold app_post. rewrite Hby in *. pose proof (zlength_app (yb_bytes b) src). buf_tac.
    + unfold app_post. rewrite Hs1. split; [auto|]. split; [congruence|]. intros _.
      assert (src = []) as ->.
      { destruct src; auto. unfold zlength in *; cbn in *; lia. }
      rewrite app_nil_r. cbn [zlength length Z.of_nat] in *. rewrite Z.add_0_r in *. buf_tac.
  - unfold app_post. cbn [ypost]. rewrite Hs1 in *. buf_tac.
  - unfold app_post. cbn [ypost]. rewrite Hs1 in *. buf_tac.
Qed.

Lemma ybuf_clear_post : forall b, buf_inv b -> yb_state b = BS_ok ->
  ypost (ybuf_clear b) (fun b' => buf_inv b' /\ b' = mkBuf BS_ok (yb_len b) 0 (yb_data b) []).
Proof.
  intros b Hinv Hst. unfold ybuf_clear. rewrite Hst. cbn. split; auto.
  destruct (yb_data b) eqn:Hd; buf_tac.
Qed.

Lemma ybuf_free_safe : forall blk b, ysafe (ybuf_free blk b).
Proof. intros; unfold ybuf_free. destruct (yb_data b); cbn; auto. Qed.

(* [comment removed for export] *)
Lemma ybuf_append_post2 : forall b src,
  buf_inv b -> yb_used b + zlength src < 2^64 ->
  ypost (ybuf_append b src)
        (fun b' => buf_inv b' /\
                   (yb_state b' = BS_ok -> yb_state b = BS_ok /\ yb_used b' = yb_used b + zlength src /\
                                           yb_bytes b' = yb_bytes b ++ src /\ yb_data b' <> None) /\
                   (yb_state b' <> BS_ok -> yb_used b' = 0 /\ yb_bytes b' = [])).
Proof.
  intros b src Hinv Hbig.
  destruct (yb_state b) eqn:Hs.
  - eapply ypost_mono. apply ybuf_append_post; auto.
    intros b' (Hinv' & Herr' & Hok'). split; [auto|]. split.
    + intros Hs'. specialize (Hok' Hs'). destruct Hok' as (Hd & Hby & _).
      destruct Hinv' as (?&Hu&?&?&?&?). rewrite Hu, Hby, zlength_app.
      destruct Hinv as (?&Hu0&?&?&?&?). rewrite Hu0. repeat split; auto.
    + intros Hs'. specialize (Herr' Hs'). destruct Hinv' as (?&Hu&?&?&?&?). rewrite Hu, Herr'. split; auto.
  - unfold ybuf_append, ybuf_ensure_available. rewrite Hs. cbn. rewrite Hs.
    split; [auto|]. split; [intros; congruence|]. intros _.
    destruct Hinv as (?&Hu&?&Hn&?&He). specialize (He ltac:(congruence)). specialize (Hn He).
    split; [lia|]. destruct (yb_bytes b); auto. unfold zlength in Hu; cbn in Hu; lia.
  - unfold ybuf_append, ybuf_ensure_available. rewrite Hs. cbn. rewrite Hs.
    split; [auto|]. split; [intros; congruence|]. intros _.
    destruct Hinv as (?&Hu&?&Hn&?&He). specialize (He ltac:(congruence)). specialize (Hn He).
    split; [lia|]. destruct (yb_bytes b); auto. unfold zlength in Hu; cbn in Hu; lia.
Qed.
