(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnKara BnModel BnTree BnWordsCorrect BnInv BnSpecs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma add_carry_words_spec : forall a c, limbs a -> 0 <= c <= 1 ->
  let '(r, c') := add_carry_words a c in
  limbs r /\ length r = length a /\ 0 <= c' <= 1 /\ lval r + Bp (length a) * c' = lval a + c.
Proof.
  induction a as [|t a IH]; intros c Ha Hc.
  - cbn [add_carry_words lval length]. rewrite Bp_0. repeat split; try lia. constructor.
  - apply limbs_cons_inv in Ha. destruct Ha as [[Ht0 Ht1] Ha]. cbn [add_carry_words]. unfold addw.
    pose proof BW_pos as BWp.
    set (c1 := if (t + c) mod BW =? 0 then c else 0).
    assert (Hc1 : 0 <= c1 <= 1 /\ (t + c) mod BW + BW * c1 = t + c).
    { subst c1. destruct (Z.eq_dec (t + c) BW) as [E|E].
      - assert (Ec : c = 1) by lia. rewrite E, Z.mod_same by lia. cbn [Z.eqb]. rewrite Ec. lia.
      - rewrite (Z.mod_small (t + c) BW) by lia. destruct (Z.eqb_spec (t + c) 0); lia. }
    destruct Hc1 as [Hc1 Ec1]. specialize (IH c1 Ha Hc1). destruct (add_carry_words a c1) as [r c'].
    destruct IH as (H1 & H2 & H3 & H4). cbn [lval length]. rewrite Bp_S.
    split; [constructor; [apply limb_mod|exact H1]|]. split; [lia|]. split; [lia|]. nia.
Qed.

Lemma top_limb_nonzero : forall l n, limbs l -> length l = n -> (1 <= n)%nat -> Bp (n - 1) <= lval l -> nth (n - 1) l 0 <> 0.
Proof.
  intros l n Hl Hlen Hn Hv E. pose proof (nth_limb_val l (n - 1) Hl ltac:(lia)) as Ev. rewrite E in Ev.
  rewrite (skipn_all2 l) in Ev by lia. cbn [lval] in Ev.
  pose proof (lval_bound _ (limbs_firstn (n - 1) l Hl)) as Hb. rewrite firstn_length_le in Hb by lia. lia.
Qed.

Lemma uadd_pure : forall a b, limbs a -> limbs b -> (length b <= length a)%nat ->
  let min := length b in
  let '(s, c1) := add_words (firstn min a) b in
  let '(s2, c2) := add_carry_words (skipn min a) c1 in
  let w := s ++ s2 ++ [c2] in
  limbs w /\ length w = S (length a) /\ 0 <= c2 <= 1 /\ lval w = lval a + lval b /\
  lval (firstn (length a) w) + Bp (length a) * c2 = lval a + lval b.
Proof.
  intros a b Ha Hb Hlen. cbv zeta.
  pose proof (add_words_spec (firstn (length b) a) b (limbs_firstn _ _ Ha) Hb ltac:(rewrite firstn_length_le; lia)) as H1.
  destruct (add_words (firstn (length b) a) b) as [s c1]. destruct H1 as (S1 & S2 & S3 & S4).
  rewrite firstn_length_le in S2, S4 by lia.
  pose proof (add_carry_words_spec (skipn (length b) a) c1 (limbs_skipn _ _ Ha) S3) as H2.
  destruct (add_carry_words (skipn (length b) a) c1) as [s2 c2]. destruct H2 as (T1 & T2 & T3 & T4).
  rewrite length_skipn in T2, T4.
  pose proof (lval_split_le (length b) a Hlen) as Ea.
  assert (EB : Bp (length a) = Bp (length b) * Bp (length a - length b)) by (rewrite <- Bp_add; f_equal; lia).
  assert (Hw : lval (s ++ s2 ++ [c2]) = lval a + lval b).
  { rewrite !lval_app. cbn [lval]. rewrite S2, T2. nia. }
  split; [apply limbs_app; [exact S1|apply limbs_app; [exact T1|constructor; [unfold limb, BW; lia|constructor]]]|].
  split; [rewrite !length_app; cbn [length]; lia|]. split; [exact T3|]. split; [exact Hw|].
  assert (Ef : firstn (length a) (s ++ s2 ++ [c2]) = s ++ s2).
  { rewrite app_assoc. rewrite firstn_app. rewrite firstn_all2 by (rewrite length_app; lia).
    replace (length a - length (s ++ s2))%nat with 0%nat by (rewrite length_app; lia). cbn [firstn]. apply app_nil_r. }
  rewrite Ef. rewrite lval_app, S2. nia.
Qed.

Lemma usub_pure : forall a b, limbs a -> limbs b -> (length b <= length a)%nat -> lval b <= lval a ->
  let min := length b in
  let '(s, bw) := sub_words (firstn min a) b in
  let '(s2, _) := sub_part_pos (skipn min a) bw in
  let w := s ++ s2 in
  limbs w /\ length w = length a /\ lval w = lval a - lval b.
Proof.
  intros a b Ha Hb Hlen Hge. cbv zeta.
  pose proof (sub_words_spec (firstn (length b) a) b (limbs_firstn _ _ Ha) Hb ltac:(rewrite firstn_length_le; lia)) as H1.
  destruct (sub_words (firstn (length b) a) b) as [s bw]. destruct H1 as (S1 & S2 & S3 & S4).
  rewrite firstn_length_le in S2, S4 by lia.
  pose proof (sub_part_pos_spec (skipn (length b) a) bw (limbs_skipn _ _ Ha) S3) as H2.
  destruct (sub_part_pos (skipn (length b) a) bw) as [s2 c2]. destruct H2 as (T1 & T2 & T3 & T4).
  rewrite length_skipn in T2, T4.
  pose proof (lval_split_le (length b) a Hlen) as Ea.
  assert (EB : Bp (length a) = Bp (length b) * Bp (length a - length b)) by (rewrite <- Bp_add; f_equal; lia).
  assert (Hw : limbs (s ++ s2)) by (apply limbs_app; assumption).
  assert (Hwl : length (s ++ s2) = length a) by (rewrite length_app; lia).
  split; [exact Hw|]. split; [exact Hwl|].
  assert (E : lval (s ++ s2) - Bp (length a) * c2 = lval a - lval b) by (rewrite lval_app, S2; nia).
  pose proof (lval_bound _ Hw) as Hb1. rewrite Hwl in Hb1. pose proof (lval_bound a Ha). pose proof (lval_nonneg b Hb).
  pose proof (Bp_pos (length a)). assert (c2 = 0 \/ c2 = 1) as [E0|E1] by lia; [rewrite E0 in E; lia|rewrite E1 in E; lia].
Qed.

Section AddSpec.
Context {ptr : Type}.
Local Notation LS := (lstate ptr) (only parsing).
Local Notation BN := (bignum ptr) (only parsing).
Local Notation ops := (tree_ops ptr) (only parsing).

Lemma slice_of_firstn : forall (l : list Z) m n, (m <= n)%nat -> slice l m (n - m) = skipn m (firstn n l).
Proof. intros l m n H. unfold slice. rewrite skipn_firstn_comm. reflexivity. Qed.

Lemma firstn_of_firstn : forall (l : list Z) m n, (m <= n)%nat -> firstn m l = firstn m (firstn n l).
Proof. intros l m n H. rewrite firstn_firstn, Nat.min_l by lia. reflexivity. Qed.

Definition uadd_body (rr ra rb : bnref) : BM (M:=btree ptr) (ptr:=ptr) unit :=
  bbind ops (bget ops ra) (fun a => bbind ops (bget ops rb) (fun b =>
  let max := bn_top a in let min := bn_top b in
  bbind ops (bn_wexpand ops rr (max + 1)) (fun _ =>
  bbind ops (bbind ops (bget ops rr) (fun r => bset ops rr (bn_with_top r max))) (fun _ =>
  bbind ops (if (max =? 0)%nat then bret ops tt
             else bbind ops (bget ops ra) (fun a => bbind ops (bget ops rb) (fun b => bbind ops (bget ops rr) (fun r =>
                  let '(s, carry) := add_words (firstn min (bn_buf a)) (firstn min (bn_buf b)) in
                  let '(s2, carry) := add_carry_words (slice (bn_buf a) min (max - min)) carry in
                  bset ops rr (mkBN (bn_d r) (splice (bn_buf r) 0 (s ++ s2 ++ [carry])) (max + Z.to_nat carry) (bn_neg r) (bn_flags r))))))
    (fun _ => bbind ops (bget ops rr) (fun r => bset ops rr (bn_with_neg r false))))))).

Lemma cmp_pure_eq : forall a b : BN, bn_ok a -> bn_ok b -> bn_canon a -> bn_canon b -> bn_val a = bn_val b -> cmp_pure a b = 0.
Proof.
  intros a b Ha Hb [Hna Hza] [Hnb Hzb] Hv. unfold cmp_pure, bn_val in *.
  pose proof (bn_mag_nonneg a Ha). pose proof (bn_mag_nonneg b Hb).
  pose proof (bn_norm_zero_iff a Ha Hna) as Za. pose proof (bn_norm_zero_iff b Hb Hnb) as Zb.
  assert (Hneg : bn_neg a = bn_neg b).
  { destruct (bn_neg a) eqn:Ea; destruct (bn_neg b) eqn:Eb; try reflexivity.
    - assert (bn_mag a = 0) by lia. apply Za in H1. specialize (Hza H1). congruence.
    - assert (bn_mag b = 0) by lia. apply Zb in H1. specialize (Hzb H1). congruence. }
  assert (Hmag : bn_mag a = bn_mag b) by (rewrite Hneg in Hv; destruct (bn_neg b); lia).
  destruct (bn_norm_mag_inj a b Ha Hb Hna Hnb Hmag) as [Et Ef].
  rewrite Hneg. rewrite Bool.eqb_reflx. cbn [negb].
  rewrite Et. rewrite Nat.ltb_irrefl. rewrite <- Et at 1. rewrite Ef.
  destruct Hb as (B1 & B2 & _). unfold bn_dmax in *.
  rewrite cmp_words_spec by (try (apply limbs_firstn; assumption); reflexivity). rewrite sgn3_eq. reflexivity.
Qed.

End AddSpec.
