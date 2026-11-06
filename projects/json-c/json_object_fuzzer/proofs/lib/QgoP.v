(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition b0 : bv 8 := Z_to_bv 8 0.

Lemma byte_range8 : forall b : bv 8, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. cbn in H. lia. Qed.

Lemma bv8_zero_iff : forall b : bv 8, bv_unsigned b = 0 <-> b = b0.
Proof.
intros b; split.
- intros H. apply bv_eq. rewrite H. reflexivity.
- intros ->. reflexivity.
Qed.

Lemma notin0_nth : forall (s : list (bv 8)) i b, ~ In b0 s -> nth_error s i = Some b -> bv_unsigned b <> 0.
Proof.
intros s i b Hn Hi Hb. apply Hn. apply bv8_zero_iff in Hb. subst b. eapply nth_error_In; eauto.
Qed.

Fixpoint strcmp_walk (l r : list (bv 8)) {struct l} : Z :=
match l, r with
| a :: l', b :: r' =>
if ((bv_unsigned a =? 0) || negb (bv_unsigned a =? bv_unsigned b))%bool
then bv_unsigned a - bv_unsigned b
else strcmp_walk l' r'
| a :: _, [] => bv_unsigned a
| [], _ => 0
end.

Definition strcmp_model (ls rs : list (bv 8)) : Z := strcmp_walk (ls ++ [b0]) (rs ++ [b0]).

Lemma strcmp_walk_range : forall l r, -255 <= strcmp_walk l r <= 255.
Proof.
induction l as [|a l IH]; intros [|b r]; cbn; try lia.
- pose proof (byte_range8 a). lia.
- pose proof (byte_range8 a). pose proof (byte_range8 b).
destruct (_ || _)%bool; [lia|apply IH].
Qed.

Lemma strcmp_model_zero : forall ls rs, ~ In b0 ls -> ~ In b0 rs ->
(strcmp_model ls rs = 0 <-> ls = rs).
Proof.
unfold strcmp_model. induction ls as [|a ls IH]; intros rs Hl Hr.
- destruct rs as [|b rs].
+ split; auto.
+ assert (Hb : bv_unsigned b <> 0) by (apply (notin0_nth (b :: rs) 0 b Hr); reflexivity).
cbn -[Z.sub Z.eqb]. change (bv_unsigned b0) with 0. cbn [Z.eqb orb].
split; [intros; exfalso; lia | intros; discriminate].
- assert (Ha : bv_unsigned a <> 0) by (apply (notin0_nth (a :: ls) 0 a Hl); reflexivity).
destruct rs as [|b rs]; cbn -[Z.sub Z.eqb].
+ change (bv_unsigned b0) with 0.
replace (bv_unsigned a =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
destruct (Z.eqb_spec (bv_unsigned a) 0); [lia|]. cbn. split; [intros; exfalso; lia | intros; discriminate].
+ replace (bv_unsigned a =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [orb].
destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [E|NE]; cbn [negb].
* assert (a = b) by (apply bv_eq; exact E). subst b.
rewrite IH; [| intros K; apply Hl; right; exact K | intros K; apply Hr; right; exact K].
split; [intros ->; reflexivity | intros K; injection K; auto].
* split; [intros; exfalso; lia|]. intros K. injection K as -> ->. lia.
Qed.

Fixpoint strchr_idx (c : Z) (s : list (bv 8)) : nat :=
match s with
| [] => 0
| a :: s' => if ((bv_unsigned a =? c) || (bv_unsigned a =? 0))%bool then 0 else S (strchr_idx c s')
end.

Lemma strchr_idx_le : forall c s, (strchr_idx c s <= length s)%nat.
Proof. induction s as [|a s IH]; cbn; [lia|]. destruct (_ || _)%bool; cbn; lia. Qed.

Lemma strchr_idx_before : forall c s i a, (i < strchr_idx c s)%nat -> nth_error s i = Some a ->
bv_unsigned a <> c /\ bv_unsigned a <> 0.
Proof.
induction s as [|x s IH]; intros i a Hi Hn; cbn in *; [lia|].
destruct ((bv_unsigned x =? c) || (bv_unsigned x =? 0))%bool eqn:E; [lia|].
apply orb_false_iff in E. destruct E as [E1 E2]. apply Z.eqb_neq in E1. apply Z.eqb_neq in E2.
destruct i as [|i]; cbn in Hn. { injection Hn as ->. auto. }
eapply IH; [|exact Hn]. lia.
Qed.

Lemma strchr_idx_at : forall c s a, nth_error (s ++ [b0]) (strchr_idx c s) = Some a ->
bv_unsigned a = c \/ bv_unsigned a = 0.
Proof.
induction s as [|x s IH]; intros a Hn; cbn in *.
- injection Hn as <-. right; reflexivity.
- destruct ((bv_unsigned x =? c) || (bv_unsigned x =? 0))%bool eqn:E; cbn in Hn.
+ injection Hn as ->. apply orb_true_iff in E. destruct E as [E|E]; apply Z.eqb_eq in E; auto.
+ apply IH. exact Hn.
Qed.

Lemma strchr_idx_zero : forall s, ~ In b0 s -> strchr_idx 0 s = length s.
Proof.
induction s as [|a s IH]; intros Hn; cbn; [reflexivity|].
rewrite orb_diag. destruct (Z.eqb_spec (bv_unsigned a) 0) as [E|NE].
- exfalso. apply Hn. left. apply (proj1 (bv8_zero_iff a)). exact E.
- cbn. rewrite IH; [reflexivity|]. intros K. apply Hn. right. exact K.
Qed.

Definition strchr_model (A c : Z) (s : list (bv 8)) : Z :=
match nth_error (s ++ [b0]) (strchr_idx c s) with
| Some b => if bv_unsigned b =? c then A + Z.of_nat (strchr_idx c s) else 0
| None => 0
end.

Lemma sel_mask : forall (t : bool) (x : Z), 0 <= x < 2^64 ->
Z.land ((Z.b2z t + -1) mod 2^64) x = if t then 0 else x.
Proof.
intros t x Hx. destruct t; cbn [Z.b2z].
- rewrite Z.mod_small by lia. apply Z.land_0_l.
- change ((0 + -1) mod 2^64) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

Lemma lxor_pos_iff : forall a b, 0 <= a -> 0 <= b -> (0 <? Z.lxor a b) = negb (a =? b).
Proof.
intros a b Ha Hb. destruct (Z.eqb_spec a b) as [->|NE]; cbn.
- rewrite Z.lxor_nilpotent. reflexivity.
- pose proof (Z.lxor_nonneg a b). apply Z.ltb_lt.
destruct (Z.eq_dec (Z.lxor a b) 0) as [E|]; [|lia]. exfalso. apply NE. apply Z.lxor_eq. exact E.
Qed.

Definition lower8 (c : Z) : Z := if ((65 <=? c) && (c <=? 90))%bool then c + 32 else c.

Lemma lower8_range : forall c, 0 <= c < 256 -> 0 <= lower8 c < 256 + 32.
Proof. intros c Hc. unfold lower8. destruct (_ && _)%bool; lia. Qed.

Fixpoint strncasecmp_walk (l r : list (bv 8)) (k : nat) {struct l} : Z :=
match l, r with
| a :: l', b :: r' =>
if ((bv_unsigned a =? 0) || (bv_unsigned b =? 0) || Nat.eqb k 0
|| negb ((bv_unsigned a =? bv_unsigned b) || (lower8 (bv_unsigned a) =? lower8 (bv_unsigned b))))%bool
then lower8 (bv_unsigned a) - lower8 (bv_unsigned b)
else match k with O => lower8 (bv_unsigned a) - lower8 (bv_unsigned b) | S k' => strncasecmp_walk l' r' k' end
| a :: _, [] => lower8 (bv_unsigned a)
| [], _ => 0
end.
Definition strncasecmp_model (ls rs : list (bv 8)) (n : Z) : Z :=
if n =? 0 then 0 else strncasecmp_walk (ls ++ [b0]) (rs ++ [b0]) (Z.to_nat (n - 1)).
