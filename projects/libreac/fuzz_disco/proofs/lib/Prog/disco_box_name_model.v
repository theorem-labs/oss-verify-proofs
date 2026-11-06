From Stdlib Require Import ZArith List Bool Lia.
Import ListNotations.
Open Scope Z_scope.

Definition bn_ok (x : Z) : bool := (x =? 0) || ((2 <=? x) && (x <=? 40) && Z.even x).

Definition bn_STEM (f : Z) : list Z :=
  if f =? 1 then [83; 45; 48; 56; 48; 56]
  else if f =? 2 then [83; 45; 49; 54; 48; 56]
  else if f =? 3 then [83; 45; 52; 48; 48; 48; 83]
  else [82; 69; 65; 67].

Definition bn_stem (f : Z) (sd : list Z) : list Z :=
  match sd with [] => bn_STEM f | _ :: _ => sd end.

Fixpoint bn_digits (k : nat) (x : Z) : list Z :=
  match k with
  | O => []
  | S k' => if x <? 10 then [48 + x] else bn_digits k' (x / 10) ++ [48 + x mod 10]
  end.

Definition bn_dec (x md : Z) : list Z :=
  let d := bn_digits (S (Z.to_nat x)) x in repeat 48 (Z.to_nat (md - Z.of_nat (length d))) ++ d.

Definition bn_w4 (i o : Z) : list Z := bn_dec i 2 ++ bn_dec o 2.

Fixpoint bn_leq (a b : list Z) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => (x =? y) && bn_leq a' b'
  | _, _ => false
  end.

Definition bn_NM (f : Z) (sd : list Z) (i o : Z) : list Z :=
  let s := bn_stem f sd in
  let w := bn_w4 i o in
  if (4 <=? Z.of_nat (length s)) && bn_leq (skipn (length s - 4) s) w then s else s ++ 45 :: w.

Fixpoint bn_tk (seen : bool) (l : list Z) : list Z :=
  match l with
  | [] => []
  | c :: r =>
      if (c =? 45) && negb seen then bn_tk true r
      else (if (65 <=? c) && (c <=? 90) then c + 32 else c) :: bn_tk seen r
  end.

Definition bn_TK (nm : list Z) : list Z := bn_tk false nm.

Definition bn_DP (nm : list Z) (i o : Z) : list Z :=
  nm ++ [32; 40] ++ bn_dec i 1 ++ [32; 105; 110; 32; 47; 32] ++ bn_dec o 1 ++ [32; 111; 117; 116; 41].

Definition bn_ret (f : Z) (sd : list Z) (i o : Z) : Z :=
  if bn_ok i && bn_ok o && negb ((i =? 0) && (o =? 0)) && (Z.of_nat (length (bn_NM f sd i o)) <=? 23)
  then 0 else -1.

Definition box_name_model (f : Z) (sd : list Z) (i o : Z) : Z * list Z * list Z * list Z :=
  let nm := bn_NM f sd i o in (bn_ret f sd i o, nm, bn_TK nm, bn_DP nm i o).

Definition bn_tok_char (c : Z) : bool := ((97 <=? c) && (c <=? 122)) || ((48 <=? c) && (c <=? 57)) || (c =? 45).

Definition bn_oks : list Z := 0 :: map (fun k => 2 * Z.of_nat k) (seq 1 20).

Lemma bn_ok_in : forall x, bn_ok x = true -> In x bn_oks.
Proof.
  intros x H. unfold bn_ok in H. apply orb_true_iff in H. destruct H as [H | H].
  - apply Z.eqb_eq in H. subst x. left. reflexivity.
  - apply andb_true_iff in H. destruct H as [H He]. apply andb_true_iff in H. destruct H as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2. right. apply in_map_iff.
    apply Zeven_bool_iff in He. apply Zeven_ex in He. destruct He as [k Hk]. subst x.
    exists (Z.to_nat k). split; [rewrite Z2Nat.id by lia; reflexivity|]. apply in_seq. lia.
Qed.

Definition bn_c17_b (f i o : Z) : bool :=
  let nm := bn_NM f [] i o in
  let tk := bn_TK nm in
  (bn_ret f [] i o =? 0) && (Z.of_nat (length nm) <=? 12) && (Z.of_nat (length tk) <=? 11) &&
  (Z.of_nat (length (bn_DP nm i o)) <=? 29) && forallb bn_tok_char tk.

Lemma bn_c17_all : forallb (fun f => forallb (fun i => forallb (fun o =>
  ((i =? 0) && (o =? 0)) || bn_c17_b f i o) bn_oks) bn_oks) [0; 1; 2; 3] = true.
Proof. vm_compute. reflexivity. Qed.

Lemma bn_STEM_cases : forall f, bn_STEM f = bn_STEM (if f =? 1 then 1 else if f =? 2 then 2 else if f =? 3 then 3 else 0).
Proof.
  intros f. unfold bn_STEM.
  destruct (f =? 1); [reflexivity|]. destruct (f =? 2); [reflexivity|]. destruct (f =? 3); reflexivity.
Qed.

Lemma bn_c17_f : forall f i o, bn_c17_b f i o = bn_c17_b (if f =? 1 then 1 else if f =? 2 then 2 else if f =? 3 then 3 else 0) i o.
Proof.
  intros f i o. unfold bn_c17_b, bn_ret, bn_NM, bn_stem. rewrite (bn_STEM_cases f). reflexivity.
Qed.

Lemma bn_c17 : forall f i o, bn_ok i = true -> bn_ok o = true -> (i =? 0) && (o =? 0) = false ->
  let nm := bn_NM f [] i o in
  let tk := bn_TK nm in
  bn_ret f [] i o = 0 /\ (length nm <= 12)%nat /\ (length tk <= 11)%nat /\ (length (bn_DP nm i o) <= 29)%nat /\
  Forall (fun c => bn_tok_char c = true) tk.
Proof.
  intros f i o Hi Ho Hz.
  assert (B : bn_c17_b f i o = true).
  { rewrite bn_c17_f.
    pose proof bn_c17_all as A.
    assert (Hf : In (if f =? 1 then 1 else if f =? 2 then 2 else if f =? 3 then 3 else 0) [0; 1; 2; 3]).
    { destruct (f =? 1); [cbn; tauto|]. destruct (f =? 2); [cbn; tauto|]. destruct (f =? 3); cbn; tauto. }
    rewrite forallb_forall in A. specialize (A _ Hf). rewrite forallb_forall in A.
    specialize (A i (bn_ok_in i Hi)). rewrite forallb_forall in A. specialize (A o (bn_ok_in o Ho)).
    rewrite Hz in A. exact A. }
  unfold bn_c17_b in B. cbv zeta in B.
  apply andb_true_iff in B. destruct B as [B B5]. apply andb_true_iff in B. destruct B as [B B4].
  apply andb_true_iff in B. destruct B as [B B3]. apply andb_true_iff in B. destruct B as [B1 B2].
  apply Z.eqb_eq in B1. apply Z.leb_le in B2. apply Z.leb_le in B3. apply Z.leb_le in B4.
  cbv zeta. split; [exact B1|]. split; [lia|]. split; [lia|]. split; [lia|].
  apply Forall_forall. intros c Hc. rewrite forallb_forall in B5. apply B5. exact Hc.
Qed.

Lemma bn_ret_refuse : forall f sd i o, bn_ok i && bn_ok o && negb ((i =? 0) && (o =? 0)) = false -> bn_ret f sd i o = -1.
Proof. intros f sd i o H. unfold bn_ret. rewrite H. reflexivity. Qed.

Lemma bn_w4_length : forall i o, bn_ok i = true -> bn_ok o = true -> length (bn_w4 i o) = 4%nat.
Proof.
  intros i o Hi Ho. apply bn_ok_in in Hi. apply bn_ok_in in Ho.
  assert (A : forallb (fun i => forallb (fun o => Nat.eqb (length (bn_w4 i o)) 4) bn_oks) bn_oks = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in A. specialize (A i Hi). rewrite forallb_forall in A. specialize (A o Ho).
  apply Nat.eqb_eq. exact A.
Qed.

Lemma bn_NM_length : forall f sd i o,
  (length (bn_NM f sd i o) <= length (bn_stem f sd) + 1 + length (bn_w4 i o))%nat.
Proof.
  intros f sd i o. unfold bn_NM. cbv zeta.
  match goal with |- context [if ?b then _ else _] => destruct b end; [lia|].
  rewrite length_app. cbn [length]. lia.
Qed.
