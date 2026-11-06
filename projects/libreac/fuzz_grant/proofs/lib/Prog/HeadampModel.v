From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
Import ListNotations.
Open Scope Z_scope.

Definition dflt (p : Z) : Z := if p =? 2 then 32 else 0.

Definition legal (p v : Z) : Prop :=
  (0 <= p < 2 /\ 0 <= v <= 1) \/ (p = 2 /\ 0 <= v <= 55).

Definition tb (T : list byte) (i : Z) : Z := bv_unsigned (nth (Z.to_nat i) T (Z_to_bv 8 0)).

Definition eff (T : list byte) (t ch p : Z) : Z :=
  if 3 <=? p then 0
  else if (t =? 0) || (48 <=? ch) then dflt p
  else if tb T (144 + 3 * ch + p) =? 0 then dflt p
  else tb T (3 * ch + p).

Lemma firstn1_skipn_nth : forall (T : list byte) k d,
  (k < length T)%nat -> firstn 1 (skipn k T) = [nth k T d].
Proof.
  induction T as [|x T IH]; intros k d H; cbn in H; [lia|].
  destruct k as [|k]; cbn; [reflexivity|]. apply IH. lia.
Qed.


Lemma eff_p3 : forall T t ch p, 3 <= p -> eff T t ch p = 0.
Proof. intros. unfold eff. rewrite (proj2 (Z.leb_le 3 p)) by lia. reflexivity. Qed.

Lemma eff_t0 : forall T ch p, p < 3 -> eff T 0 ch p = dflt p.
Proof. intros. unfold eff. rewrite (proj2 (Z.leb_gt 3 p)) by lia. reflexivity. Qed.

Lemma eff_ch : forall T t ch p, p < 3 -> 48 <= ch -> eff T t ch p = dflt p.
Proof.
  intros. unfold eff. rewrite (proj2 (Z.leb_gt 3 p)) by lia. rewrite (proj2 (Z.leb_le 48 ch)) by lia.
  rewrite orb_true_r. reflexivity.
Qed.

Lemma eff_cell : forall T t ch p, p < 3 -> t <> 0 -> ch < 48 ->
  eff T t ch p = if tb T (144 + 3 * ch + p) =? 0 then dflt p else tb T (3 * ch + p).
Proof.
  intros. unfold eff. rewrite (proj2 (Z.leb_gt 3 p)) by lia. rewrite (proj2 (Z.leb_gt 48 ch)) by lia.
  rewrite (proj2 (Z.eqb_neq t 0)) by lia. reflexivity.
Qed.

Lemma dflt_code_all : forall p, 0 <= p < 18446744073709551616 ->
  Z.shiftl (Z.b2z ((p + -2) mod 18446744073709551616 <? 1)) 5 = dflt p.
Proof.
  intros p H. unfold dflt. destruct (Z.eq_dec p 2) as [E|Hne]; [subst p; reflexivity|].
  rewrite (proj2 (Z.eqb_neq p 2) Hne).
  assert (Hm : 1 <= (p + -2) mod 18446744073709551616).
  { destruct (Z_lt_le_dec p 2).
    - rewrite <- (Z.mod_add (p + -2) 1 18446744073709551616) by lia. rewrite Z.mod_small by lia. lia.
    - rewrite Z.mod_small by lia. lia. }
  rewrite (proj2 (Z.ltb_ge _ 1) Hm). reflexivity.
Qed.

Definition legalb (p v : Z) : bool := ((p <? 2) && (v <=? 1)) || ((p =? 2) && (v <=? 55)).