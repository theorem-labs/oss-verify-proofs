(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia Znumtheory.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VMap VLin VItv VStore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition TWO64c : Z := 2 ^ 64.
Definition two_part (k : Z) : Z :=
  match k with
  | Zpos (xI _) | Zneg (xI _) | Zpos xH | Zneg xH => 1
  | _ => Z.gcd k TWO64c
  end.

Lemma gcd_odd_2 k : Z.odd k = true -> Z.gcd k 2 = 1.
Proof.
  intros Hk.
  pose proof (Z.gcd_divide_l k 2) as H1. pose proof (Z.gcd_divide_r k 2) as H2. pose proof (Z.gcd_nonneg k 2) as H0.
  assert (Hle : Z.gcd k 2 <= 2) by (apply Z.divide_pos_le; [lia|exact H2]).
  assert (Hne : Z.gcd k 2 <> 0) by (intros E; rewrite E in H2; destruct H2 as [q Hq]; lia).
  assert (Hn2 : Z.gcd k 2 <> 2).
  { intros E. rewrite E in H1. destruct H1 as [q Hq]. rewrite Hq in Hk. rewrite Z.mul_comm, Z.odd_mul in Hk. discriminate. }
  lia.
Qed.

Lemma gcd_odd_pow2 k n : 0 <= n -> Z.odd k = true -> Z.gcd k (2 ^ n) = 1.
Proof.
  intros Hn Hk. revert n Hn. apply natlike_ind.
  - rewrite Z.pow_0_r. apply Z.gcd_1_r.
  - intros n Hn IH. rewrite Z.pow_succ_r by exact Hn.
    set (g := Z.gcd k (2 * 2 ^ n)).
    pose proof (Z.gcd_divide_l k (2 * 2 ^ n)) as G1. pose proof (Z.gcd_divide_r k (2 * 2 ^ n)) as G2.
    pose proof (Z.gcd_nonneg k (2 * 2 ^ n)) as G0. fold g in G1, G2, G0.
    assert (Hg2 : Z.gcd g 2 = 1).
    { apply gcd_odd_2. destruct G1 as [q Hq]. rewrite Hq, Z.odd_mul in Hk. apply andb_prop in Hk. tauto. }
    assert (Hd : (g | 2 ^ n)) by (apply Z.gauss with 2; assumption).
    assert (Hd1 : (g | 1)) by (rewrite <- IH; apply Z.gcd_greatest; assumption).
    apply Z.divide_1_r_nonneg; assumption.
Qed.

Lemma two_part_eq k : two_part k = Z.gcd k (2 ^ 64).
Proof.
  unfold two_part, TWO64c.
  destruct k as [|p|p]; try reflexivity; destruct p as [p|p|]; try reflexivity;
    symmetry; apply gcd_odd_pow2; (lia || reflexivity).
Qed.

Lemma two_part_divide k : (two_part k | k).
Proof. rewrite two_part_eq. apply Z.gcd_divide_l. Qed.

Fixpoint terms_cong (C : cong) (l : list term) (m r : Z) : Z * Z :=
  match l with
  | [] => (m, r)
  | (s, k) :: t =>
      let '(ms, rs) := cong_get C s in
      let m' := Z.gcd m (two_part k * ms) in
      if Z.eqb m' 1 then (1, 0) else terms_cong C t m' (r + k * rs)
  end.

Definition cong_norm (mr : Z * Z) : Z * Z :=
  let '(m, r) := mr in if Z.eqb m 0 then (0, r) else (m, r mod m).

Definition lin_cong (C : cong) (a : lin) : Z * Z :=
  cong_norm (terms_cong C (lt a) 0 (lc a)).

(* [comment removed for export] *)
Definition lin_low_bits (C : cong) (a : lin) (j : Z) : option Z :=
  let '(m, r) := lin_cong C a in
  if Z.eqb (m mod 2 ^ j) 0 then Some (r mod 2 ^ j) else None.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cong_bare_eq (C : cong) (a : lin) (m r : Z) : bool :=
  match a with
  | mkLin Z0 [(s, Zpos xH)] => let '(ms, rs) := cong_get C s in if Z.eqb ms m then Z.eqb rs r else false
  | _ => false
  end.

Definition entails_cong (C : cong) (a : lin) (m r : Z) : bool :=
  if Z.eqb m 1 then true
  else if cong_bare_eq C a m r then true
  else let '(m', r') := lin_cong C a in
       if Z.eqb m 0 then Z.eqb m' 0 && Z.eqb r' r
       else if Z.ltb 0 m then (if Z.eqb (zmod2 m' m) 0 then Z.eqb (zmod2 (r' - r) m) 0 else false) else false.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma divide_gcd_l m n x : (m | x) -> (Z.gcd m n | x).
Proof. intros H. apply Z.divide_trans with m; auto. apply Z.gcd_divide_l. Qed.

Lemma divide_gcd_r m n x : (n | x) -> (Z.gcd m n | x).
Proof. intros H. apply Z.divide_trans with n; auto. apply Z.gcd_divide_r. Qed.

Lemma terms_cong_sound v C l : in_cong v C -> forall m r x,
  (m | x - r) ->
  let '(m', r') := terms_cong C l m r in (m' | x + eval_terms v l - r').
Proof.
  intros HC. induction l as [|[s k] t IH]; intros m r x Hx; simpl.
  - replace (x + 0 - r) with (x - r) by lia. exact Hx.
  - pose proof (in_cong_get v C s HC) as Hs.
    destruct (cong_get C s) as [ms rs]. simpl in Hs.
    destruct (Z.eqb_spec (Z.gcd m (two_part k * ms)) 1) as [E|E].
    + exists (x + (k * v s + eval_terms v t) - 0). lia.
    + specialize (IH (Z.gcd m (two_part k * ms)) (r + k * rs) (x + k * v s)).
      destruct (terms_cong C t (Z.gcd m (two_part k * ms)) (r + k * rs)) as [m' r'].
      replace (x + (k * v s + eval_terms v t) - r') with (x + k * v s + eval_terms v t - r') by lia.
      apply IH.
      replace (x + k * v s - (r + k * rs)) with ((x - r) + k * (v s - rs)) by lia.
      apply Z.divide_add_r.
      * now apply divide_gcd_l.
      * apply divide_gcd_r.
        destruct (two_part_divide k) as [q Hq]. destruct Hs as [q' Hq'].
        exists (q * q'). rewrite Hq'. rewrite Hq at 1. ring.
Qed.


Lemma terms_cong_nonneg C l : forall m r, 0 <= m -> 0 <= fst (terms_cong C l m r).
Proof.
  induction l as [|[s k] t IH]; intros m r Hm; simpl; auto.
  destruct (cong_get C s) as [ms rs].
  destruct (Z.eqb (Z.gcd m (two_part k * ms)) 1); simpl; [lia|].
  apply IH. apply Z.gcd_nonneg.
Qed.

Theorem lin_cong_sound v C a :
  in_cong v C -> let '(m, r) := lin_cong C a in (m | eval v a - r) /\ 0 <= m /\ (0 < m -> 0 <= r < m).
Proof.
  intros HC. unfold lin_cong, eval.
  pose proof (terms_cong_sound v C (lt a) HC 0 (lc a) (lc a) ltac:(exists 0; lia)) as H.
  pose proof (terms_cong_nonneg C (lt a) 0 (lc a) ltac:(lia)) as Hnn.
  destruct (terms_cong C (lt a) 0 (lc a)) as [m r]. simpl in Hnn. unfold cong_norm.
  destruct (Z.eqb_spec m 0).
  - subst. split; [exact H|lia].
  - split; [|split; [lia|intros; apply Z.mod_pos_bound; lia]].
    destruct H as [q Hq]. exists (q + r / m).
    pose proof (Z.div_mod r m n). lia.
Qed.

Corollary lin_cong_divide v C a : in_cong v C -> (fst (lin_cong C a) | eval v a - snd (lin_cong C a)).
Proof.
  intros HC. pose proof (lin_cong_sound v C a HC) as H. destruct (lin_cong C a); simpl. tauto.
Qed.

Lemma divide_mod_eq' m a b : 0 < m -> (m | a - b) -> a mod m = b mod m.
Proof. intros; now apply divide_mod_eq. Qed.

Theorem lin_low_bits_sound v C a j r :
  in_cong v C -> 0 <= j -> lin_low_bits C a j = Some r ->
  (eval v a) mod 2 ^ j = r /\ 0 <= r < 2 ^ j.
Proof.
  intros HC Hj. unfold lin_low_bits.
  pose proof (lin_cong_sound v C a HC) as H. destruct (lin_cong C a) as [m r0].
  destruct H as [Hd [Hm _]].
  assert (Hp : 0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia).
  destruct (Z.eqb_spec (m mod 2 ^ j) 0) as [E|E]; [|discriminate].
  intros X; inversion X; subst.
  split; [|apply Z.mod_pos_bound; lia].
  apply divide_mod_eq; auto.
  apply Z.divide_trans with m; auto. apply Z.mod_divide; lia.
Qed.

Theorem entails_cong_sound v C a m r :
  in_cong v C -> entails_cong C a m r = true -> (m | eval v a - r).
Proof.
  intros HC. unfold entails_cong.
  destruct (Z.eqb_spec m 1) as [->|Hm1].
  { intros _. exists (eval v a - r). lia. }
  destruct (cong_bare_eq C a m r) eqn:FB.
  { intros _. unfold cong_bare_eq in FB. destruct a as [c l]. destruct c; try discriminate.
    destruct l as [|[s k] t]; try discriminate. destruct k as [|[k|k|]|k]; try discriminate. destruct t; try discriminate.
    pose proof (in_cong_get v C s HC) as Hs. destruct (cong_get C s) as [ms rs]. cbn [fst snd] in Hs.
    destruct (Z.eqb_spec ms m) as [->|]; [|discriminate]. apply Z.eqb_eq in FB. subst rs.
    unfold eval. cbn [lc lt eval_terms]. replace (0 + (1 * v s + 0) - r) with (v s - r) by lia. exact Hs. }
  pose proof (lin_cong_sound v C a HC) as H. destruct (lin_cong C a) as [m' r'].
  destruct H as [Hd [Hm' _]].
  destruct (Z.eqb_spec m 0) as [->|Hm0].
  - intros X. apply andb_prop in X as [X1 X2].
    apply Z.eqb_eq in X1. apply Z.eqb_eq in X2. subst.
    destruct Hd as [q Hq]. exists 0. lia.
  - intros X. rewrite !zmod2_eq, !if_andb in X. apply andb_prop in X as [X1 X]. apply andb_prop in X as [X2 X3].
    apply Z.ltb_lt in X1. apply Z.eqb_eq in X2. apply Z.eqb_eq in X3.
    assert (H1 : (m | eval v a - r')).
    { apply Z.divide_trans with m'; auto. apply Z.mod_divide; lia. }
    assert (H2 : (m | r' - r)) by (apply Z.mod_divide; lia).
    replace (eval v a - r) with ((eval v a - r') + (r' - r)) by lia.
    now apply Z.divide_add_r.
Qed.

(* [comment removed for export] *)
Lemma cong_get_sound v C s : in_cong v C -> (fst (cong_get C s) | v s - snd (cong_get C s)).
Proof. apply in_cong_get. Qed.
