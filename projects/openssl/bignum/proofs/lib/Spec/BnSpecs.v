(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnKara BnModel BnTree BnWordsCorrect BnDivWords BnInv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Specs.
Context {ptr : Type}.
Local Notation LS := (lstate ptr) (only parsing).
Local Notation BN := (bignum ptr) (only parsing).
Local Notation ops := (tree_ops ptr) (only parsing).

Definition bn_mag (b : BN) : Z := lval (firstn (bn_top b) (bn_buf b)).
Definition bn_norm (b : BN) : Prop := bn_top b = 0%nat \/ nth (bn_top b - 1) (bn_buf b) 0 <> 0.
Definition bn_canon (b : BN) : Prop := bn_norm b /\ (bn_top b = 0%nat -> bn_neg b = false).
Definition bn_val (b : BN) : Z := if bn_neg b then - bn_mag b else bn_mag b.

Lemma bn_mag_top0 : forall b : BN, bn_top b = 0%nat -> bn_mag b = 0.
Proof. intros b E. unfold bn_mag. rewrite E. reflexivity. Qed.

Lemma bn_mag_nonneg : forall b, bn_ok b -> 0 <= bn_mag b.
Proof. intros b (H & _). apply lval_nonneg, limbs_firstn. exact H. Qed.

Lemma bn_mag_lt : forall b, bn_ok b -> bn_mag b < Bp (bn_top b).
Proof.
  intros b (H & Ht & _). unfold bn_mag. pose proof (lval_bound _ (limbs_firstn (bn_top b) _ H)) as Hb.
  rewrite firstn_length_le in Hb by exact Ht. lia.
Qed.

Lemma bn_mag_ge : forall b, bn_ok b -> bn_norm b -> (0 < bn_top b)%nat -> Bp (bn_top b - 1) <= bn_mag b.
Proof.
  intros b (H & Ht & _) [Hn|Hn] Hpos; [lia|]. unfold bn_mag.
  set (l := firstn (bn_top b) (bn_buf b)).
  assert (Hl : limbs l) by (apply limbs_firstn; exact H).
  assert (Hll : length l = bn_top b) by (apply firstn_length_le; exact Ht).
  pose proof (nth_limb_val l (bn_top b - 1) Hl ltac:(lia)) as E.
  assert (En : nth (bn_top b - 1) l 0 = nth (bn_top b - 1) (bn_buf b) 0).
  { subst l. rewrite nth_firstn. destruct (Nat.ltb_spec (bn_top b - 1) (bn_top b)); [reflexivity|lia]. }
  rewrite En in E. pose proof (limbs_nth (bn_buf b) (bn_top b - 1) H) as [Hx0 _].
  pose proof (lval_nonneg _ (limbs_firstn (bn_top b - 1) l Hl)). pose proof (lval_nonneg _ (limbs_skipn (S (bn_top b - 1)) l Hl)).
  pose proof (Bp_pos (bn_top b - 1)). pose proof (Bp_pos (S (bn_top b - 1))). nia.
Qed.

Lemma bn_norm_zero_iff : forall b, bn_ok b -> bn_norm b -> (bn_top b = 0%nat <-> bn_mag b = 0).
Proof.
  intros b Hb Hn. split.
  - intros E. unfold bn_mag. rewrite E. reflexivity.
  - intros E. destruct (Nat.eq_dec (bn_top b) 0) as [|Hne]; [assumption|exfalso].
    pose proof (bn_mag_ge b Hb Hn ltac:(lia)). pose proof (Bp_pos (bn_top b - 1)). lia.
Qed.

Lemma bn_norm_mag_inj : forall a b, bn_ok a -> bn_ok b -> bn_norm a -> bn_norm b -> bn_mag a = bn_mag b ->
  bn_top a = bn_top b /\ firstn (bn_top a) (bn_buf a) = firstn (bn_top b) (bn_buf b).
Proof.
  intros a b Ha Hb Hna Hnb E.
  assert (Ht : bn_top a = bn_top b).
  { destruct (Nat.lt_trichotomy (bn_top a) (bn_top b)) as [Hlt|[Heq|Hgt]]; [exfalso|exact Heq|exfalso].
    - pose proof (bn_mag_lt a Ha). pose proof (bn_mag_ge b Hb Hnb ltac:(lia)).
      pose proof (Bp_mono (bn_top a) (bn_top b - 1) ltac:(lia)). lia.
    - pose proof (bn_mag_lt b Hb). pose proof (bn_mag_ge a Ha Hna ltac:(lia)).
      pose proof (Bp_mono (bn_top b) (bn_top a - 1) ltac:(lia)). lia. }
  split; [exact Ht|]. destruct Ha as (Ha1 & Ha2 & _). destruct Hb as (Hb1 & Hb2 & _).
  apply lval_inj; [apply limbs_firstn; assumption|apply limbs_firstn; assumption| |exact E].
  unfold bn_dmax in *. rewrite !firstn_length_le by lia. exact Ht.
Qed.

Lemma bn_correct_top_ok : forall b, bn_ok b ->
  let b' := bn_correct_top_pure b in
  bn_ok b' /\ bn_canon b' /\ bn_mag b' = bn_mag b /\ (bn_top b' <= bn_top b)%nat /\
  bn_buf b' = bn_buf b /\ bn_d b' = bn_d b /\ bn_flags b' = bn_flags b /\
  bn_neg b' = (bn_neg b && negb (bn_top b' =? 0)%nat).
Proof.
  intros b (H1 & H2 & H3 & H4). cbv zeta. unfold bn_correct_top_pure.
  destruct (strip_top_spec (bn_buf b) (bn_top b) H2) as (S1 & S2 & S3).
  set (t := strip_top (bn_buf b) (bn_top b)) in *.
  unfold bn_ok, bn_canon, bn_norm, bn_mag, bn_dmax. cbn [bn_buf bn_top bn_neg bn_flags bn_d].
  repeat split; try assumption; try lia.
  - unfold bn_dmax in *. lia.
  - intros E. rewrite E. reflexivity.
  - destruct (Nat.eqb_spec t 0); cbn [negb]; [rewrite andb_false_r|rewrite andb_true_r]; reflexivity.
Qed.

Lemma nth_list_set_other : forall {A} (l : list A) i j a d, i <> j -> nth j (list_set l i a) d = nth j l d.
Proof.
  induction l as [|x l IH]; intros [|i] [|j] a d H; cbn [list_set nth]; try reflexivity; try lia.
  apply IH. lia.
Qed.

Lemma list_set_nil_iff : forall {A} (l : list A) i a, list_set l i a = [] <-> l = [].
Proof. intros A [|x l] [|i] a; cbn [list_set]; split; intros H; try reflexivity; try discriminate. Qed.

Lemma getbn_setbn_other : forall r r' b (s : LS), r <> r' -> getbn r' (setbn r b s) = getbn r' s.
Proof.
  intros r r' b s Hne. destruct r as [| | | | |i]; destruct r' as [| | | | |j]; try reflexivity; try congruence.
  cbn [getbn setbn set_ctx ls_ctx ctx_set_vals cx_vals]. apply nth_list_set_other. congruence.
Qed.

Definition ctx_same (c c' : bn_ctx ptr) : Prop :=
  cx_head c' = cx_head c /\ cx_current c' = cx_current c /\ cx_pused c' = cx_pused c /\ cx_psize c' = cx_psize c /\
  cx_indexes c' = cx_indexes c /\ cx_frames c' = cx_frames c /\ cx_ssize c' = cx_ssize c /\ cx_used c' = cx_used c /\
  cx_err_stack c' = cx_err_stack c /\ cx_too_many c' = cx_too_many c /\ (cx_vals c' = [] <-> cx_vals c = []).

Lemma ctx_same_refl : forall c, ctx_same c c.
Proof. intros c. unfold ctx_same. tauto. Qed.

Lemma ctx_same_setbn : forall r b (s : LS), ctx_same (ls_ctx s) (ls_ctx (setbn r b s)).
Proof.
  intros r b s. destruct r as [| | | | |i]; try apply ctx_same_refl.
  unfold ctx_same. cbn [setbn set_ctx ls_ctx ctx_set_vals cx_vals cx_head cx_current cx_pused cx_psize
       cx_indexes cx_frames cx_ssize cx_used cx_err_stack cx_too_many].
  repeat split; try reflexivity; apply list_set_nil_iff.
Qed.

Definition ctx_wf (c : bn_ctx ptr) : Prop :=
  cx_err_stack c = 0%nat /\ cx_too_many c = false /\ cx_pused c = cx_used c /\ (cx_used c <= 3)%nat /\
  ((cx_psize c = 0%nat /\ cx_vals c = [] /\ cx_head c = None /\ cx_used c = 0%nat) \/ (cx_psize c = 16%nat /\ cx_vals c <> [])) /\
  ((cx_ssize c = 0%nat /\ cx_frames c = [] /\ cx_indexes c = None) \/ cx_ssize c = 32%nat) /\
  (cx_frames c = [] \/ cx_frames c = [0%nat]) /\ (cx_frames c = [] -> cx_used c = 0%nat).

Definition ctx_rest (c : bn_ctx ptr) : Prop := ctx_wf c /\ cx_frames c = [].

End Specs.
