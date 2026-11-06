(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module UTF8F.

Lemma utf8_valid_f_S f l :
  utf8_valid_f (S f) l =
  match l with
  | [] => true
  | b0 :: _ => let n := Z.to_nat (utf8_trail b0 + 1) in
               if (length l <? n)%nat then false else utf8_legal (firstn n l) && utf8_valid_f f (skipn n l)
  end.
Proof. destruct l; reflexivity. Qed.

Lemma utf8_trail_range b : 0 <= utf8_trail b <= 5.
Proof. unfold utf8_trail. repeat (destruct (_ <? _)); lia. Qed.

Lemma utf8_valid_f_fuel : forall f g l, (length l <= f)%nat -> (length l <= g)%nat -> utf8_valid_f f l = utf8_valid_f g l.
Proof.
  induction f as [|f IH]; intros g l Hf Hg.
  - destruct l; [destruct g; reflexivity| cbn in Hf; lia].
  - destruct g as [|g]; [destruct l; [reflexivity| cbn in Hg; lia]|].
    rewrite !utf8_valid_f_S. destruct l as [|b t]; [reflexivity|].
    cbv zeta. destruct (length (b :: t) <? Z.to_nat (utf8_trail b + 1))%nat eqn:E; [reflexivity|].
    apply Nat.ltb_ge in E. pose proof (utf8_trail_range b) as Tb.
    f_equal. apply IH; rewrite length_skipn; cbn [length] in *; lia.
Qed.

Lemma utf8_valid_cons b t :
  utf8_valid (b :: t) =
    let n := Z.to_nat (utf8_trail b + 1) in
    if (length (b :: t) <? n)%nat then false else utf8_legal (firstn n (b :: t)) && utf8_valid (skipn n (b :: t)).
Proof.
  unfold utf8_valid. change (length (b :: t)) with (S (length t)) at 1. rewrite utf8_valid_f_S. cbv zeta.
  destruct (length (b :: t) <? Z.to_nat (utf8_trail b + 1))%nat eqn:E; [reflexivity|].
  apply Nat.ltb_ge in E. pose proof (utf8_trail_range b) as Tb.
  f_equal. apply utf8_valid_f_fuel; rewrite length_skipn; cbn [length] in *; lia.
Qed.

Lemma utf8_valid_nil : utf8_valid [] = true.
Proof. reflexivity. Qed.

Lemma utf8_trail_spec b :
  (b < 192 -> utf8_trail b = 0) /\ (192 <= b < 224 -> utf8_trail b = 1) /\ (224 <= b < 240 -> utf8_trail b = 2)
  /\ (240 <= b < 248 -> utf8_trail b = 3) /\ (248 <= b -> 4 <= utf8_trail b <= 5).
Proof.
  unfold utf8_trail.
  destruct (Z.ltb_spec b 192); [lia|]. destruct (Z.ltb_spec b 224); [lia|]. destruct (Z.ltb_spec b 240); [lia|].
  destruct (Z.ltb_spec b 248); [lia|]. destruct (Z.ltb_spec b 252); lia.
Qed.

Lemma is_cont_iff b : is_cont b = true <-> 128 <= b < 192.
Proof. unfold is_cont. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. tauto. Qed.

Definition second_okb (b0 b1 : Z) : bool :=
  if b0 =? 224 then 160 <=? b1 else if b0 =? 237 then b1 <=? 159 else if b0 =? 240 then 144 <=? b1 else if b0 =? 244 then b1 <=? 143 else true.
Definition second_ok (b0 b1 : Z) : Prop :=
  (b0 = 224 -> 160 <= b1) /\ (b0 = 237 -> b1 <= 159) /\ (b0 = 240 -> 144 <= b1) /\ (b0 = 244 -> b1 <= 143).

Definition lead_ok (b0 : Z) : Prop := ~ (128 <= b0 < 194) /\ b0 <= 244.

Lemma legal1_eq b0 : utf8_legal [b0] = negb ((128 <=? b0) && (b0 <? 194)) && (b0 <=? 244).
Proof. reflexivity. Qed.
Lemma legal2_eq b0 b1 : utf8_legal [b0; b1] = is_cont b1 && second_okb b0 b1 && negb ((128 <=? b0) && (b0 <? 194)) && (b0 <=? 244).
Proof. reflexivity. Qed.
Lemma legal3_eq b0 b1 b2 :
  utf8_legal [b0; b1; b2] = is_cont b2 && (is_cont b1 && second_okb b0 b1) && negb ((128 <=? b0) && (b0 <? 194)) && (b0 <=? 244).
Proof. reflexivity. Qed.
Lemma legal4_eq b0 b1 b2 b3 :
  utf8_legal [b0; b1; b2; b3] = is_cont b3 && is_cont b2 && (is_cont b1 && second_okb b0 b1) && negb ((128 <=? b0) && (b0 <? 194)) && (b0 <=? 244).
Proof. reflexivity. Qed.

Lemma lead_okb_iff b0 : (negb ((128 <=? b0) && (b0 <? 194)) = true /\ (b0 <=? 244) = true) <-> lead_ok b0.
Proof. unfold lead_ok. rewrite negb_true_iff, andb_false_iff, Z.leb_le, Z.leb_gt, Z.ltb_ge. lia. Qed.
Lemma second_okb_iff b0 b1 : second_okb b0 b1 = true <-> second_ok b0 b1.
Proof.
  unfold second_ok, second_okb.
  destruct (Z.eqb_spec b0 224); [rewrite Z.leb_le; lia|]. destruct (Z.eqb_spec b0 237); [rewrite Z.leb_le; lia|].
  destruct (Z.eqb_spec b0 240); [rewrite Z.leb_le; lia|]. destruct (Z.eqb_spec b0 244); [rewrite Z.leb_le; lia|]. lia.
Qed.

Lemma legal1_iff b0 : utf8_legal [b0] = true <-> lead_ok b0.
Proof. rewrite legal1_eq, andb_true_iff. apply lead_okb_iff. Qed.
Lemma legal2_iff b0 b1 : utf8_legal [b0; b1] = true <-> (128 <= b1 < 192 /\ second_ok b0 b1 /\ lead_ok b0).
Proof. rewrite legal2_eq, !andb_true_iff, is_cont_iff, second_okb_iff, <- lead_okb_iff. tauto. Qed.
Lemma legal3_iff b0 b1 b2 : utf8_legal [b0; b1; b2] = true <-> (128 <= b2 < 192 /\ 128 <= b1 < 192 /\ second_ok b0 b1 /\ lead_ok b0).
Proof. rewrite legal3_eq, !andb_true_iff, !is_cont_iff, second_okb_iff, <- lead_okb_iff. tauto. Qed.
Lemma legal4_iff b0 b1 b2 b3 :
  utf8_legal [b0; b1; b2; b3] = true <-> (128 <= b3 < 192 /\ 128 <= b2 < 192 /\ 128 <= b1 < 192 /\ second_ok b0 b1 /\ lead_ok b0).
Proof. rewrite legal4_eq, !andb_true_iff, !is_cont_iff, second_okb_iff, <- lead_okb_iff. tauto. Qed.

Lemma not_true_false (x : bool) : ~ (x = true) -> x = false.
Proof. destruct x; [intros H; exfalso; apply H; reflexivity| reflexivity]. Qed.

Lemma legal_long l : (4 < length l)%nat -> utf8_legal l = false.
Proof.
  intros H. destruct l as [|b0 t]; [cbn in H; lia|]. unfold utf8_legal.
  destruct (Z.ltb_spec 4 (Z.of_nat (length (b0 :: t)))); [reflexivity| lia].
Qed.

Lemma bat_eq l i : bat l i = nth (Z.to_nat i) l 0.
Proof. reflexivity. Qed.

Lemma skipn_bat l i : 0 <= i < blen l -> skipn (Z.to_nat i) l = bat l i :: skipn (Z.to_nat (i + 1)) l.
Proof.
  intros Hi. unfold bat, blen in *. replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  assert (Hn : (Z.to_nat i < length l)%nat) by lia. revert Hn. generalize (Z.to_nat i) as k. clear Hi.
  intros k. revert l. induction k as [|k IH]; intros l Hk.
  - destruct l; [cbn in Hk; lia| reflexivity].
  - destruct l as [|x t]; [cbn in Hk; lia|]. cbn [skipn nth]. apply IH. cbn in Hk. lia.
Qed.

Lemma length_skipn_z (l : list Z) i : 0 <= i <= blen l -> Z.of_nat (length (skipn (Z.to_nat i) l)) = blen l - i.
Proof. intros Hi. unfold blen in *. rewrite length_skipn. lia. Qed.

Lemma skipn_skipn_z (l : list Z) i k : 0 <= i -> 0 <= k -> skipn (Z.to_nat k) (skipn (Z.to_nat i) l) = skipn (Z.to_nat (i + k)) l.
Proof. intros Hi Hk. rewrite skipn_skipn. f_equal. lia. Qed.

Lemma firstn_skipn_1 l i : 0 <= i -> i + 1 <= blen l -> firstn 1 (skipn (Z.to_nat i) l) = [bat l i].
Proof. intros H0 H1. rewrite (skipn_bat l i) by lia. reflexivity. Qed.
Lemma firstn_skipn_2 l i : 0 <= i -> i + 2 <= blen l -> firstn 2 (skipn (Z.to_nat i) l) = [bat l i; bat l (i + 1)].
Proof. intros H0 H1. rewrite (skipn_bat l i), (skipn_bat l (i + 1)) by lia. reflexivity. Qed.
Lemma firstn_skipn_3 l i : 0 <= i -> i + 3 <= blen l -> firstn 3 (skipn (Z.to_nat i) l) = [bat l i; bat l (i + 1); bat l (i + 2)].
Proof.
  intros H0 H1. rewrite (skipn_bat l i), (skipn_bat l (i + 1)), (skipn_bat l (i + 1 + 1)) by lia.
  replace (i + 1 + 1) with (i + 2) by lia. reflexivity.
Qed.
Lemma firstn_skipn_4 l i : 0 <= i -> i + 4 <= blen l ->
  firstn 4 (skipn (Z.to_nat i) l) = [bat l i; bat l (i + 1); bat l (i + 2); bat l (i + 3)].
Proof.
  intros H0 H1. rewrite (skipn_bat l i), (skipn_bat l (i + 1)), (skipn_bat l (i + 1 + 1)), (skipn_bat l (i + 1 + 1 + 1)) by lia.
  replace (i + 1 + 1 + 1) with (i + 3) by lia. replace (i + 1 + 1) with (i + 2) by lia. reflexivity.
Qed.

Lemma bat_range l i : Forall (fun b => 0 <= b < 256) l -> 0 <= bat l i < 256.
Proof.
  intros F. unfold bat. destruct (Nat.lt_ge_cases (Z.to_nat i) (length l)) as [H|H].
  - rewrite Forall_nth in F. apply F. exact H.
  - rewrite nth_overflow by lia. lia.
Qed.

Lemma valid_short l i : 0 <= i < blen l -> blen l - i < utf8_trail (bat l i) + 1 -> utf8_valid (skipn (Z.to_nat i) l) = false.
Proof.
  intros Hi Hs. rewrite skipn_bat by lia. rewrite utf8_valid_cons. cbv zeta. rewrite <- (skipn_bat l i) by lia.
  pose proof (utf8_trail_range (bat l i)) as Tr.
  destruct (Nat.ltb_spec (length (skipn (Z.to_nat i) l)) (Z.to_nat (utf8_trail (bat l i) + 1))) as [H|H]; [reflexivity|].
  exfalso. rewrite length_skipn in H. unfold blen in *. lia.
Qed.

Lemma valid_bad l i : 0 <= i < blen l -> utf8_trail (bat l i) + 1 <= blen l - i ->
  utf8_legal (firstn (Z.to_nat (utf8_trail (bat l i) + 1)) (skipn (Z.to_nat i) l)) = false ->
  utf8_valid (skipn (Z.to_nat i) l) = false.
Proof.
  intros Hi Hs Hl. rewrite skipn_bat by lia. rewrite utf8_valid_cons. cbv zeta. rewrite <- (skipn_bat l i) by lia.
  destruct (Nat.ltb_spec (length (skipn (Z.to_nat i) l)) (Z.to_nat (utf8_trail (bat l i) + 1))) as [H|H]; [reflexivity|].
  rewrite Hl. reflexivity.
Qed.

Lemma valid_step l i : 0 <= i < blen l -> utf8_trail (bat l i) + 1 <= blen l - i ->
  utf8_legal (firstn (Z.to_nat (utf8_trail (bat l i) + 1)) (skipn (Z.to_nat i) l)) = true ->
  utf8_valid (skipn (Z.to_nat i) l) = utf8_valid (skipn (Z.to_nat (i + (utf8_trail (bat l i) + 1))) l).
Proof.
  intros Hi Hs Hl. rewrite skipn_bat at 1 by lia. rewrite utf8_valid_cons. cbv zeta. rewrite <- (skipn_bat l i) by lia.
  pose proof (utf8_trail_range (bat l i)) as Tr.
  destruct (Nat.ltb_spec (length (skipn (Z.to_nat i) l)) (Z.to_nat (utf8_trail (bat l i) + 1))) as [H|H].
  - exfalso. rewrite length_skipn in H. unfold blen in *. lia.
  - rewrite Hl, andb_true_l. rewrite skipn_skipn_z by lia. reflexivity.
Qed.

Lemma valid_ascii l i : 0 <= i < blen l -> 0 <= bat l i < 128 ->
  utf8_valid (skipn (Z.to_nat i) l) = utf8_valid (skipn (Z.to_nat (i + 1)) l).
Proof.
  intros Hi Hb. pose proof (utf8_trail_spec (bat l i)) as (T0 & _).
  rewrite (valid_step l i Hi); rewrite ?T0 by lia; [reflexivity| lia|].
  change (Z.to_nat (0 + 1)) with 1%nat. rewrite firstn_skipn_1 by lia. apply (proj2 (legal1_iff _)). unfold lead_ok. lia.
Qed.

Lemma valid_ascii_run_n (n : nat) : forall l i, 0 <= i -> i + Z.of_nat n <= blen l -> (forall j, i <= j < i + Z.of_nat n -> 0 <= bat l j < 128) ->
  utf8_valid (skipn (Z.to_nat i) l) = utf8_valid (skipn (Z.to_nat (i + Z.of_nat n)) l).
Proof.
  induction n as [|n IH]; intros l i Hi Hl Hb.
  - rewrite Z.add_0_r. reflexivity.
  - rewrite (valid_ascii l i) by (first [apply Hb| idtac]; lia).
    replace (i + Z.of_nat (S n)) with (i + 1 + Z.of_nat n) by lia. apply IH; [lia| lia|]. intros j Hj. apply Hb. lia.
Qed.
Lemma valid_ascii_run l i k : 0 <= i -> 0 <= k -> i + k <= blen l -> (forall j, i <= j < i + k -> 0 <= bat l j < 128) ->
  utf8_valid (skipn (Z.to_nat i) l) = utf8_valid (skipn (Z.to_nat (i + k)) l).
Proof.
  intros Hi Hk Hl Hb. rewrite <- (Z2Nat.id k) in Hl, Hb |- * by lia. apply valid_ascii_run_n; assumption.
Qed.

Definition sx8u (b : Z) : Z := if b <? 128 then b else b + 18446744073709551360.
Lemma sx8u_range b : 0 <= b < 256 -> 0 <= sx8u b < 2 ^ 64.
Proof. unfold sx8u. destruct (Z.ltb_spec b 128); lia. Qed.
Lemma sx8u_land b : 0 <= b < 256 -> Z.land (sx8u b) 255 = b.
Proof.
  intros Hb. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. unfold sx8u.
  destruct (Z.ltb_spec b 128); [apply Z.mod_small; lia|].
  replace (b + 18446744073709551360) with (b + 72057594037927935 * 2 ^ 8) by lia. rewrite Z.mod_add, Z.mod_small by lia. reflexivity.
Qed.

Lemma trail_0 b : utf8_trail b = 0 -> b < 192.
Proof. pose proof (utf8_trail_spec b). lia. Qed.
Lemma trail_1 b : utf8_trail b = 1 -> 192 <= b < 224.
Proof. pose proof (utf8_trail_spec b). lia. Qed.
Lemma trail_2 b : utf8_trail b = 2 -> 224 <= b < 240.
Proof. pose proof (utf8_trail_spec b). lia. Qed.
Lemma trail_3 b : utf8_trail b = 3 -> 240 <= b < 248.
Proof. pose proof (utf8_trail_spec b). lia. Qed.
Lemma trail_ge4 b : 4 <= utf8_trail b -> 248 <= b.
Proof. pose proof (utf8_trail_spec b). lia. Qed.

Local Ltac fin_iff L := apply not_true_false; intros HL; apply (proj1 L) in HL; unfold second_ok, lead_ok in HL; lia.
Local Ltac fin_false :=
  lazymatch goal with
  | |- utf8_legal [?a] = false => fin_iff (legal1_iff a)
  | |- utf8_legal [?a; ?b] = false => fin_iff (legal2_iff a b)
  | |- utf8_legal [?a; ?b; ?c] = false => fin_iff (legal3_iff a b c)
  | |- utf8_legal [?a; ?b; ?c; ?d] = false => fin_iff (legal4_iff a b c d)
  | |- utf8_legal _ = false => apply legal_long; cbn; lia
  end.
Lemma legal_false_lead1 x1 r : 128 <= x1 < 194 -> utf8_legal (x1 :: r) = false.
Proof. intros H. destruct r as [|? [|? [|? [|? r]]]]; fin_false. Qed.
Lemma legal_false_lead2 x1 r : 245 <= x1 -> utf8_legal (x1 :: r) = false.
Proof. intros H. destruct r as [|? [|? [|? [|? r]]]]; fin_false. Qed.
Lemma legal_false_c1 x1 x2 r : x2 < 128 \/ 192 <= x2 -> utf8_legal (x1 :: x2 :: r) = false.
Proof. intros H. destruct r as [|? [|? [|? r]]]; fin_false. Qed.
Lemma legal_false_e0 x1 x2 r : x1 = 224 -> x2 < 160 -> utf8_legal (x1 :: x2 :: r) = false.
Proof. intros H H1. destruct r as [|? [|? [|? r]]]; fin_false. Qed.
Lemma legal_false_ed x1 x2 r : x1 = 237 -> 159 < x2 -> utf8_legal (x1 :: x2 :: r) = false.
Proof. intros H H1. destruct r as [|? [|? [|? r]]]; fin_false. Qed.
Lemma legal_false_f0 x1 x2 r : x1 = 240 -> x2 < 144 -> utf8_legal (x1 :: x2 :: r) = false.
Proof. intros H H1. destruct r as [|? [|? [|? r]]]; fin_false. Qed.
Lemma legal_false_f4 x1 x2 r : x1 = 244 -> 143 < x2 -> utf8_legal (x1 :: x2 :: r) = false.
Proof. intros H H1. destruct r as [|? [|? [|? r]]]; fin_false. Qed.
Lemma legal_false_c2 x1 x2 x3 r : x3 < 128 \/ 192 <= x3 -> utf8_legal (x1 :: x2 :: x3 :: r) = false.
Proof. intros H. destruct r as [|? [|? r]]; fin_false. Qed.
Lemma legal_false_c3 x1 x2 x3 x4 r : x4 < 128 \/ 192 <= x4 -> utf8_legal (x1 :: x2 :: x3 :: x4 :: r) = false.
Proof. intros H. destruct r as [|? r]; fin_false. Qed.

Lemma legal1_true b0 : b0 < 128 \/ 194 <= b0 -> b0 <= 244 -> utf8_legal [b0] = true.
Proof. intros A B. apply (proj2 (legal1_iff _)). unfold lead_ok. lia. Qed.
Lemma legal2_true b0 b1 : 128 <= b1 < 192 -> (b0 = 224 -> 160 <= b1) -> (b0 = 237 -> b1 <= 159) -> (b0 = 240 -> 144 <= b1) -> (b0 = 244 -> b1 <= 143) ->
  b0 < 128 \/ 194 <= b0 -> b0 <= 244 -> utf8_legal [b0; b1] = true.
Proof. intros. apply (proj2 (legal2_iff _ _)). unfold second_ok, lead_ok. lia. Qed.
Lemma legal3_true b0 b1 b2 : 128 <= b2 < 192 -> 128 <= b1 < 192 -> (b0 = 224 -> 160 <= b1) -> (b0 = 237 -> b1 <= 159) -> (b0 = 240 -> 144 <= b1) ->
  (b0 = 244 -> b1 <= 143) -> b0 < 128 \/ 194 <= b0 -> b0 <= 244 -> utf8_legal [b0; b1; b2] = true.
Proof. intros. apply (proj2 (legal3_iff _ _ _)). unfold second_ok, lead_ok. lia. Qed.
Lemma legal4_true b0 b1 b2 b3 : 128 <= b3 < 192 -> 128 <= b2 < 192 -> 128 <= b1 < 192 -> (b0 = 224 -> 160 <= b1) -> (b0 = 237 -> b1 <= 159) ->
  (b0 = 240 -> 144 <= b1) -> (b0 = 244 -> b1 <= 143) -> b0 < 128 \/ 194 <= b0 -> b0 <= 244 -> utf8_legal [b0; b1; b2; b3] = true.
Proof. intros. apply (proj2 (legal4_iff _ _ _ _)). unfold second_ok, lead_ok. lia. Qed.

Lemma valid_short_bt l i b0 t : 0 <= i < blen l -> b0 = bat l i -> t = utf8_trail b0 -> blen l - i < t + 1 -> utf8_valid (skipn (Z.to_nat i) l) = false.
Proof. intros Hi -> -> Hs. apply valid_short; assumption. Qed.
Lemma valid_bad_bt l i b0 t : 0 <= i < blen l -> b0 = bat l i -> t = utf8_trail b0 -> t + 1 <= blen l - i ->
  utf8_legal (firstn (Z.to_nat (t + 1)) (skipn (Z.to_nat i) l)) = false -> utf8_valid (skipn (Z.to_nat i) l) = false.
Proof. intros Hi -> -> Hs Hl. apply valid_bad; assumption. Qed.
Lemma valid_step_bt l i b0 t i' : 0 <= i < blen l -> b0 = bat l i -> t = utf8_trail b0 -> t + 1 <= blen l - i -> i' = i + (t + 1) ->
  utf8_legal (firstn (Z.to_nat (t + 1)) (skipn (Z.to_nat i) l)) = true -> utf8_valid (skipn (Z.to_nat i) l) = utf8_valid (skipn (Z.to_nat i') l).
Proof. intros Hi -> -> Hs -> Hl. apply valid_step; assumption. Qed.

Lemma ascii_pref l i k : Forall (fun b => 0 <= b < 256) l -> 0 <= i -> 0 <= k <= 8 -> i + k <= blen l ->
  (0 < k -> bat l (i + 0) < 128) -> (1 < k -> bat l (i + 1) < 128) -> (2 < k -> bat l (i + 2) < 128) -> (3 < k -> bat l (i + 3) < 128) ->
  (4 < k -> bat l (i + 4) < 128) -> (5 < k -> bat l (i + 5) < 128) -> (6 < k -> bat l (i + 6) < 128) -> (7 < k -> bat l (i + 7) < 128) ->
  utf8_valid (skipn (Z.to_nat i) l) = utf8_valid (skipn (Z.to_nat (i + k)) l).
Proof.
  intros LB Hi Hk Hl B0 B1 B2 B3 B4 B5 B6 B7. apply valid_ascii_run; [lia| lia| lia|].
  intros j Hj. split; [apply (proj1 (bat_range l j LB))|].
  assert (C : j = i + 0 \/ j = i + 1 \/ j = i + 2 \/ j = i + 3 \/ j = i + 4 \/ j = i + 5 \/ j = i + 6 \/ j = i + 7) by lia.
  destruct C as [-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]];
    [apply B0| apply B1| apply B2| apply B3| apply B4| apply B5| apply B6| apply B7]; lia.
Qed.

End UTF8F.
