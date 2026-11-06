(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnWords.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma div_mod_BW : forall s, s = BW * (s / BW) + s mod BW.
Proof. intros s. apply Z.div_mod. unfold BW; lia. Qed.

Lemma div_small_range : forall s k, 0 <= s < BW * k -> 0 <= s / BW < k.
Proof.
  intros s k H. pose proof BW_pos. split; [apply Z.div_pos; lia|].
  apply Z.div_lt_upper_bound; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma add_words_c_spec : forall a b c, limbs a -> limbs b -> length a = length b -> 0 <= c <= 1 ->
  let '(r, c') := add_words_c a b c in
  limbs r /\ length r = length a /\ 0 <= c' <= 1 /\ lval r + Bp (length a) * c' = lval a + lval b + c.
Proof.
  induction a as [|x a IH]; intros [|y b] c Ha Hb Hlen Hc; cbn [length] in Hlen; try discriminate.
  - cbn [add_words_c lval length]. rewrite Bp_0. repeat split; try lia. constructor.
  - apply limbs_cons_inv in Ha. destruct Ha as [Hx Ha]. apply limbs_cons_inv in Hb. destruct Hb as [Hy Hb].
    cbn [add_words_c]. unfold limb in *.
    assert (Hs : 0 <= (x + y + c) / BW <= 1).
    { pose proof (div_small_range (x + y + c) 2). unfold BW in *. lia. }
    specialize (IH b ((x + y + c) / BW) Ha Hb ltac:(lia) Hs).
    destruct (add_words_c a b ((x + y + c) / BW)) as [r c'].
    destruct IH as (Hr & Hl & Hc' & Hv). cbn [lval length]. rewrite Bp_S.
    repeat split; try lia.
    + constructor; [apply limb_mod|exact Hr].
    + pose proof (div_mod_BW (x + y + c)). nia.
Qed.

Lemma add_words_spec : forall a b, limbs a -> limbs b -> length a = length b ->
  let '(r, c) := add_words a b in
  limbs r /\ length r = length a /\ 0 <= c <= 1 /\ lval r + Bp (length a) * c = lval a + lval b.
Proof.
  intros a b Ha Hb Hl. unfold add_words. pose proof (add_words_c_spec a b 0 Ha Hb Hl ltac:(lia)) as H.
  destruct (add_words_c a b 0) as [r c]. rewrite Z.add_0_r in H. exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sub_words_c_spec : forall a b c, limbs a -> limbs b -> length a = length b -> 0 <= c <= 1 ->
  let '(r, c') := sub_words_c a b c in
  limbs r /\ length r = length a /\ 0 <= c' <= 1 /\ lval r - Bp (length a) * c' = lval a - lval b - c.
Proof.
  induction a as [|x a IH]; intros [|y b] c Ha Hb Hlen Hc; cbn [length] in Hlen; try discriminate.
  - cbn [sub_words_c lval length]. rewrite Bp_0. repeat split; try lia. constructor.
  - apply limbs_cons_inv in Ha. destruct Ha as [Hx Ha]. apply limbs_cons_inv in Hb. destruct Hb as [Hy Hb].
    cbn [sub_words_c]. unfold limb in *.
    set (d := x - y - c).
    assert (Hs : 0 <= (if d <? 0 then 1 else 0) <= 1) by (destruct (d <? 0); lia).
    specialize (IH b (if d <? 0 then 1 else 0) Ha Hb ltac:(lia) Hs).
    destruct (sub_words_c a b (if d <? 0 then 1 else 0)) as [r c'].
    destruct IH as (Hr & Hl & Hc' & Hv). cbn [lval length]. rewrite Bp_S.
    repeat split; try lia.
    + constructor; [apply limb_mod|exact Hr].
    + assert (E : d mod BW = d + BW * (if d <? 0 then 1 else 0)).
      { destruct (Z.ltb_spec d 0).
        - rewrite <- (Z.mod_add d 1 BW) by (unfold BW; lia). rewrite Z.mod_small; unfold BW in *; lia.
        - rewrite Z.mod_small; unfold BW in *; lia. }
      rewrite E. subst d. nia.
Qed.

Lemma sub_words_spec : forall a b, limbs a -> limbs b -> length a = length b ->
  let '(r, c) := sub_words a b in
  limbs r /\ length r = length a /\ 0 <= c <= 1 /\ lval r - Bp (length a) * c = lval a - lval b.
Proof.
  intros a b Ha Hb Hl. unfold sub_words. pose proof (sub_words_c_spec a b 0 Ha Hb Hl ltac:(lia)) as H.
  destruct (sub_words_c a b 0) as [r c]. rewrite Z.sub_0_r in H. exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mul_words_c_spec : forall a w c, limbs a -> limb w -> limb c ->
  let '(r, c') := mul_words_c a w c in
  limbs r /\ length r = length a /\ limb c' /\ lval r + Bp (length a) * c' = lval a * w + c.
Proof.
  induction a as [|x a IH]; intros w c Ha Hw Hc.
  - cbn [mul_words_c lval length]. rewrite Bp_0. repeat split; try lia; try constructor; apply Hc.
  - apply limbs_cons_inv in Ha. destruct Ha as [Hx Ha]. cbn [mul_words_c].
    assert (Hs : limb ((x * w + c) / BW)).
    { unfold limb in *. apply div_small_range. nia. }
    specialize (IH w ((x * w + c) / BW) Ha Hw Hs).
    destruct (mul_words_c a w ((x * w + c) / BW)) as [r c'].
    destruct IH as (Hr & Hl & Hc' & Hv). cbn [lval length]. rewrite Bp_S.
    repeat split; try lia; try apply Hc'.
    + constructor; [apply limb_mod|exact Hr].
    + pose proof (div_mod_BW (x * w + c)). nia.
Qed.

Lemma mul_words_spec : forall a w, limbs a -> limb w ->
  let '(r, c) := mul_words a w in
  limbs r /\ length r = length a /\ limb c /\ lval r + Bp (length a) * c = lval a * w.
Proof.
  intros a w Ha Hw. unfold mul_words. pose proof (mul_words_c_spec a w 0 Ha Hw limb_0) as H.
  destruct (mul_words_c a w 0) as [r c]. rewrite Z.add_0_r in H. exact H.
Qed.

Lemma mul_add_words_c_spec : forall r a w c, limbs r -> limbs a -> length r = length a -> limb w -> limb c ->
  let '(o, c') := mul_add_words_c r a w c in
  limbs o /\ length o = length a /\ limb c' /\ lval o + Bp (length a) * c' = lval a * w + lval r + c.
Proof.
  induction r as [|y r IH]; intros [|x a] w c Hr Ha Hlen Hw Hc; cbn [length] in Hlen; try discriminate.
  - cbn [mul_add_words_c lval length]. rewrite Bp_0. repeat split; try lia; try constructor; apply Hc.
  - apply limbs_cons_inv in Ha. destruct Ha as [Hx Ha]. apply limbs_cons_inv in Hr. destruct Hr as [Hy Hr].
    cbn [mul_add_words_c].
    assert (Hs : limb ((x * w + y + c) / BW)).
    { unfold limb in *. apply div_small_range. nia. }
    specialize (IH a w ((x * w + y + c) / BW) Hr Ha ltac:(lia) Hw Hs).
    destruct (mul_add_words_c r a w ((x * w + y + c) / BW)) as [o c'].
    destruct IH as (Ho & Hl & Hc' & Hv). cbn [lval length]. rewrite Bp_S.
    repeat split; try lia; try apply Hc'.
    + constructor; [apply limb_mod|exact Ho].
    + pose proof (div_mod_BW (x * w + y + c)). nia.
Qed.

Lemma mul_add_words_spec : forall r a w, limbs r -> limbs a -> length r = length a -> limb w ->
  let '(o, c) := mul_add_words r a w in
  limbs o /\ length o = length a /\ limb c /\ lval o + Bp (length a) * c = lval a * w + lval r.
Proof.
  intros r a w Hr Ha Hl Hw. unfold mul_add_words.
  pose proof (mul_add_words_c_spec r a w 0 Hr Ha Hl Hw limb_0) as H.
  destruct (mul_add_words_c r a w 0) as [o c]. rewrite Z.add_0_r in H. exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mul_normal_loop_spec : forall a bs r i, limbs a -> limbs bs -> limbs r -> length r = (length a + i)%nat ->
  let R := mul_normal_loop a bs r i in
  limbs R /\ length R = (length a + i + length bs)%nat /\ lval R = lval r + Bp i * (lval a * lval bs).
Proof.
  intros a bs. induction bs as [|w bs IH]; intros r i Ha Hbs Hr Hlen; cbn [mul_normal_loop].
  - cbn [lval length]. repeat split; [exact Hr|lia|lia].
  - apply limbs_cons_inv in Hbs. destruct Hbs as [Hw Hbs].
    pose proof (mul_add_words_spec (skipn i r) a w (limbs_skipn i r Hr) Ha
                  ltac:(rewrite length_skipn; lia) Hw) as Hm.
    destruct (mul_add_words (skipn i r) a w) as [seg c]. destruct Hm as (Hseg & Hsl & Hc & Hv).
    assert (Hr' : limbs (firstn i r ++ seg ++ [c])).
    { apply limbs_app; [apply limbs_firstn; exact Hr|]. apply limbs_app; [exact Hseg|]. constructor; [exact Hc|constructor]. }
    assert (Hlen' : length (firstn i r ++ seg ++ [c]) = (length a + S i)%nat).
    { rewrite !length_app, length_firstn. cbn [length]. lia. }
    specialize (IH _ (S i) Ha Hbs Hr' Hlen'). cbv zeta in IH. destruct IH as (H1 & H2 & H3).
    repeat split; [exact H1|cbn [length]; lia|].
    rewrite H3. rewrite !lval_app, length_firstn, Nat.min_l by lia. cbn [lval]. rewrite Bp_S.
    rewrite (lval_split_le i r) by lia. rewrite Hsl. nia.
Qed.

Lemma mul_words_zero : forall a, fst (mul_words a 0) = repeat 0 (length a).
Proof.
  intros a. unfold mul_words. induction a as [|x a IH]; cbn [mul_words_c fst repeat length]; [reflexivity|].
  rewrite Z.mul_0_r, Z.add_0_l. cbn. destruct (mul_words_c a 0 0) as [r c] eqn:E. cbn [fst] in *. rewrite IH. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mul_normal_ord_spec : forall a b, limbs a -> limbs b ->
  let R := match b with
           | [] => fst (mul_words a 0)
           | w :: b' => let '(seg, c) := mul_words a w in mul_normal_loop a b' (seg ++ [c]) 1
           end in
  limbs R /\ lval R = lval a * lval b /\
  length R = match b with [] => length a | _ => (length a + length b)%nat end.
Proof.
  intros a [|w b'] Ha Hb; cbv zeta.
  - rewrite mul_words_zero. cbn [lval]. rewrite lval_repeat0, repeat_length.
    repeat split; [apply limbs_repeat; exact limb_0|lia].
  - apply limbs_cons_inv in Hb. destruct Hb as [Hw Hb'].
    pose proof (mul_words_spec a w Ha Hw) as Hm. destruct (mul_words a w) as [seg c]. destruct Hm as (Hseg & Hsl & Hc & Hv).
    assert (Hr : limbs (seg ++ [c])) by (apply limbs_app; [exact Hseg|constructor; [exact Hc|constructor]]).
    assert (Hlen : length (seg ++ [c]) = (length a + 1)%nat) by (rewrite length_app; cbn [length]; lia).
    pose proof (mul_normal_loop_spec a b' (seg ++ [c]) 1 Ha Hb' Hr Hlen) as H. cbv zeta in H.
    destruct H as (H1 & H2 & H3). repeat split; [exact H1| |cbn [length]; lia].
    rewrite H3, lval_app. cbn [lval]. rewrite Hsl, Bp_1. nia.
Qed.

Lemma mul_normal_spec : forall a b, limbs a -> limbs b ->
  limbs (mul_normal a b) /\ lval (mul_normal a b) = lval a * lval b /\
  length (mul_normal a b) = if ((length a =? 0) || (length b =? 0))%nat then Nat.max (length a) (length b)
                            else (length a + length b)%nat.
Proof.
  intros a b Ha Hb. unfold mul_normal. destruct (Nat.ltb_spec (length a) (length b)) as [Hlt|Hge].
  - pose proof (mul_normal_ord_spec b a Hb Ha) as H. cbv zeta in H. destruct H as (H1 & H2 & H3).
    repeat split; [exact H1|rewrite H2; ring|]. rewrite H3. destruct a as [|x a]; cbn [length] in *.
    + rewrite Nat.eqb_refl. cbn [orb]. lia.
    + destruct b as [|y b]; cbn [length] in *; [lia|]. cbn [Nat.eqb orb]. lia.
  - pose proof (mul_normal_ord_spec a b Ha Hb) as H. cbv zeta in H. destruct H as (H1 & H2 & H3).
    repeat split; [exact H1|exact H2|]. rewrite H3. destruct b as [|y b]; cbn [length] in *.
    + rewrite Nat.eqb_refl, orb_true_r. lia.
    + destruct a as [|x a]; cbn [length] in *; [lia|]. cbn [Nat.eqb orb]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mul_normal_limbs : forall a b, limbs a -> limbs b -> (0 < length a)%nat -> (0 < length b)%nat ->
  mul_normal a b = to_limbs (length a + length b) (lval a * lval b).
Proof.
  intros a b Ha Hb Hla Hlb. destruct (mul_normal_spec a b Ha Hb) as (H1 & H2 & H3).
  assert (E : length (mul_normal a b) = (length a + length b)%nat).
  { rewrite H3. destruct (Nat.eqb_spec (length a) 0); [lia|]. destruct (Nat.eqb_spec (length b) 0); [lia|]. reflexivity. }
  rewrite <- E, <- H2. symmetry. apply to_limbs_lval. exact H1.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition sgn3 (x y : Z) : Z := if x <? y then -1 else if y <? x then 1 else 0.

Lemma sgn3_lt : forall x y, x < y -> sgn3 x y = -1.
Proof. intros x y H. unfold sgn3. destruct (Z.ltb_spec x y); lia. Qed.
Lemma sgn3_gt : forall x y, y < x -> sgn3 x y = 1.
Proof. intros x y H. unfold sgn3. destruct (Z.ltb_spec x y); [lia|]. destruct (Z.ltb_spec y x); lia. Qed.
Lemma sgn3_eq : forall x, sgn3 x x = 0.
Proof. intros x. unfold sgn3. rewrite Z.ltb_irrefl. reflexivity. Qed.
Lemma sgn3_0_iff : forall x y, sgn3 x y = 0 <-> x = y.
Proof. intros x y. unfold sgn3. destruct (Z.ltb_spec x y); destruct (Z.ltb_spec y x); lia. Qed.
Lemma sgn3_range : forall x y, sgn3 x y = -1 \/ sgn3 x y = 0 \/ sgn3 x y = 1.
Proof. intros x y. unfold sgn3. destruct (x <? y); [auto|]. destruct (y <? x); auto. Qed.
Lemma sgn3_neg_iff : forall x y, sgn3 x y = -1 <-> x < y.
Proof. intros x y. unfold sgn3. destruct (Z.ltb_spec x y); destruct (Z.ltb_spec y x); lia. Qed.
Lemma sgn3_pos_iff : forall x y, sgn3 x y = 1 <-> y < x.
Proof. intros x y. unfold sgn3. destruct (Z.ltb_spec x y); destruct (Z.ltb_spec y x); lia. Qed.

Lemma cmp_words_spec : forall a b, limbs a -> limbs b -> length a = length b ->
  cmp_words a b = sgn3 (lval a) (lval b).
Proof.
  induction a as [|x a IH]; intros [|y b] Ha Hb Hlen; cbn [length] in Hlen; try discriminate.
  - reflexivity.
  - apply limbs_cons_inv in Ha. destruct Ha as [Hx Ha]. apply limbs_cons_inv in Hb. destruct Hb as [Hy Hb].
    cbn [cmp_words lval]. rewrite (IH b Ha Hb ltac:(lia)). unfold limb in *.
    unfold sgn3 at 1 2.
    destruct (Z.ltb_spec (lval a) (lval b)) as [H1|H1].
    + cbn. symmetry. apply sgn3_lt. assert (BW * lval a + BW <= BW * lval b) by nia. lia.
    + destruct (Z.ltb_spec (lval b) (lval a)) as [H2|H2].
      * cbn. symmetry. apply sgn3_gt. assert (BW * lval b + BW <= BW * lval a) by nia. lia.
      * assert (E : lval a = lval b) by lia. cbn. rewrite E.
        destruct (Z.eqb_spec x y) as [->|Hne]; [symmetry; apply sgn3_eq|].
        destruct (Z.ltb_spec y x); symmetry; [apply sgn3_gt|apply sgn3_lt]; lia.
Qed.

Lemma existsb_nonzero_false : forall l, limbs l -> existsb nonzero l = false -> lval l = 0.
Proof.
  induction l as [|x l IH]; intros Hl H; cbn [existsb lval] in *; [reflexivity|].
  apply limbs_cons_inv in Hl. destruct Hl as [_ Hl]. apply orb_false_iff in H. destruct H as [Hx H].
  unfold nonzero in Hx. apply negb_false_iff in Hx. apply Z.eqb_eq in Hx. rewrite (IH Hl H). lia.
Qed.

Lemma existsb_nonzero_true : forall l, limbs l -> existsb nonzero l = true -> 1 <= lval l.
Proof.
  induction l as [|x l IH]; intros Hl H; cbn [existsb lval] in *; [discriminate|].
  apply limbs_cons_inv in Hl. destruct Hl as [[Hx0 Hx1] Hl]. pose proof (lval_nonneg l Hl).
  apply orb_true_iff in H. destruct H as [Hx|H].
  - unfold nonzero in Hx. apply negb_true_iff in Hx. apply Z.eqb_neq in Hx. unfold BW in *. lia.
  - specialize (IH Hl H). unfold BW in *. lia.
Qed.

(* [comment removed for export] *)
Lemma cmp_part_words_spec : forall a b cl, limbs a -> limbs b ->
  (length a = cl /\ cl <= length b)%nat \/ (length b = cl /\ cl <= length a)%nat ->
  cmp_part_words a b cl = sgn3 (lval a) (lval b).
Proof.
  intros a b cl Ha Hb Hlen. unfold cmp_part_words.
  pose proof (lval_split_le cl a) as Ea. pose proof (lval_split_le cl b) as Eb.
  pose proof (lval_bound (firstn cl a) (limbs_firstn cl a Ha)) as Ba.
  pose proof (lval_bound (firstn cl b) (limbs_firstn cl b Hb)) as Bb.
  pose proof (lval_nonneg (skipn cl a) (limbs_skipn cl a Ha)) as Na.
  pose proof (lval_nonneg (skipn cl b) (limbs_skipn cl b Hb)) as Nb.
  rewrite firstn_length_le in Ba by lia. rewrite firstn_length_le in Bb by lia.
  rewrite Ea, Eb by lia. pose proof (Bp_pos cl) as Hp.
  destruct (existsb nonzero (skipn cl b)) eqn:E1.
  - apply existsb_nonzero_true in E1; [|apply limbs_skipn; exact Hb].
    destruct Hlen as [[Hl1 Hl2]|[Hl1 Hl2]].
    + rewrite (skipn_all2 a) by lia. cbn [lval]. symmetry. apply sgn3_lt. nia.
    + rewrite (skipn_all2 b) in E1 by lia. cbn [lval] in E1. lia.
  - apply existsb_nonzero_false in E1; [|apply limbs_skipn; exact Hb]. rewrite E1.
    destruct (existsb nonzero (skipn cl a)) eqn:E2.
    + apply existsb_nonzero_true in E2; [|apply limbs_skipn; exact Ha]. symmetry. apply sgn3_gt. nia.
    + apply existsb_nonzero_false in E2; [|apply limbs_skipn; exact Ha]. rewrite E2.
      rewrite cmp_words_spec; [f_equal; lia|apply limbs_firstn; exact Ha|apply limbs_firstn; exact Hb|].
      rewrite !firstn_length_le by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sub_part_neg_spec : forall b c, limbs b -> 0 <= c <= 1 ->
  let '(r, c') := sub_part_neg b c in
  limbs r /\ length r = length b /\ 0 <= c' <= 1 /\ lval r - Bp (length b) * c' = 0 - lval b - c.
Proof.
  induction b as [|t b IH]; intros c Hb Hc.
  - cbn [sub_part_neg lval length]. rewrite Bp_0. repeat split; try lia. constructor.
  - apply limbs_cons_inv in Hb. destruct Hb as [Ht Hb]. cbn [sub_part_neg].
    assert (Hc1 : 0 <= (if t =? 0 then c else 1) <= 1) by (destruct (t =? 0); lia).
    specialize (IH _ Hb Hc1). destruct (sub_part_neg b (if t =? 0 then c else 1)) as [r c'].
    destruct IH as (Hr & Hl & Hc' & Hv). cbn [lval length]. rewrite Bp_S. unfold limb in *.
    repeat split; try lia.
    + constructor; [apply limb_mod|exact Hr].
    + assert (E : (0 - t - c) mod BW = 0 - t - c + BW * (if t =? 0 then c else 1)).
      { destruct (Z.eqb_spec t 0) as [->|Hne].
        - assert (c = 0 \/ c = 1) as [->| ->] by lia; reflexivity.
        - rewrite <- (Z.mod_add (0 - t - c) 1 BW) by (unfold BW; lia). rewrite Z.mod_small; unfold BW in *; lia. }
      rewrite E. nia.
Qed.

Lemma sub_part_pos_spec : forall a c, limbs a -> 0 <= c <= 1 ->
  let '(r, c') := sub_part_pos a c in
  limbs r /\ length r = length a /\ 0 <= c' <= 1 /\ lval r - Bp (length a) * c' = lval a - c.
Proof.
  induction a as [|t a IH]; intros c Ha Hc.
  - cbn [sub_part_pos lval length]. rewrite Bp_0. repeat split; try lia. constructor.
  - apply limbs_cons_inv in Ha. destruct Ha as [Ht Ha]. cbn [sub_part_pos].
    assert (Hc1 : 0 <= (if t =? 0 then c else 0) <= 1) by (destruct (t =? 0); lia).
    specialize (IH _ Ha Hc1). destruct (sub_part_pos a (if t =? 0 then c else 0)) as [r c'].
    destruct IH as (Hr & Hl & Hc' & Hv). cbn [lval length]. rewrite Bp_S. unfold limb in *.
    repeat split; try lia.
    + constructor; [apply limb_mod|exact Hr].
    + assert (E : (t - c) mod BW = t - c + BW * (if t =? 0 then c else 0)).
      { destruct (Z.eqb_spec t 0) as [->|Hne].
        - assert (c = 0 \/ c = 1) as [->| ->] by lia; reflexivity.
        - rewrite Z.mod_small; unfold BW in *; lia. }
      rewrite E. nia.
Qed.

Lemma sub_part_words_spec : forall a b cl, limbs a -> limbs b ->
  (length a = cl /\ cl <= length b)%nat \/ (length b = cl /\ cl <= length a)%nat ->
  let '(r, c) := sub_part_words a b cl in
  limbs r /\ length r = Nat.max (length a) (length b) /\ 0 <= c <= 1 /\
  lval r - Bp (length r) * c = lval a - lval b.
Proof.
  intros a b cl Ha Hb Hlen. unfold sub_part_words.
  pose proof (sub_words_spec (firstn cl a) (firstn cl b) (limbs_firstn _ _ Ha) (limbs_firstn _ _ Hb)
                ltac:(rewrite !firstn_length_le by lia; reflexivity)) as Hs.
  destruct (sub_words (firstn cl a) (firstn cl b)) as [r c]. destruct Hs as (Hr & Hl & Hc & Hv).
  rewrite firstn_length_le in Hl, Hv by lia.
  pose proof (lval_split_le cl a ltac:(lia)) as Ea. pose proof (lval_split_le cl b ltac:(lia)) as Eb.
  destruct (skipn cl b) as [|t b'] eqn:Esb.
  - pose proof (sub_part_pos_spec (skipn cl a) c (limbs_skipn _ _ Ha) Hc) as Hp.
    destruct (sub_part_pos (skipn cl a) c) as [r2 c2]. destruct Hp as (Hr2 & Hl2 & Hc2 & Hv2).
    rewrite length_skipn in Hl2, Hv2.
    assert (Hlb : (length b <= cl)%nat).
    { assert (E : length (skipn cl b) = 0%nat) by (rewrite Esb; reflexivity). rewrite length_skipn in E. lia. }
    cbn [lval] in Eb.
    split; [apply limbs_app; assumption|]. split; [rewrite length_app; lia|]. split; [lia|].
    rewrite lval_app, length_app, Hl, Hl2. replace (cl + (length a - cl))%nat with (length a) by lia.
    replace (length a) with (cl + (length a - cl))%nat at 1 by lia. rewrite Bp_add. nia.
  - rewrite <- Esb in *.
    pose proof (sub_part_neg_spec (skipn cl b) c (limbs_skipn _ _ Hb) Hc) as Hp.
    destruct (sub_part_neg (skipn cl b) c) as [r2 c2]. destruct Hp as (Hr2 & Hl2 & Hc2 & Hv2).
    rewrite length_skipn in Hl2, Hv2.
    assert (Hlb : (cl < length b)%nat).
    { assert (E : length (skipn cl b) = S (length b')) by (rewrite Esb; reflexivity). rewrite length_skipn in E. lia. }
    assert (Hla : length a = cl) by lia.
    rewrite (skipn_all2 a) in Ea by lia. cbn [lval] in Ea.
    split; [apply limbs_app; assumption|]. split; [rewrite length_app; lia|]. split; [lia|].
    rewrite lval_app, length_app, Hl, Hl2. replace (cl + (length b - cl))%nat with (length b) by lia.
    replace (length b) with (cl + (length b - cl))%nat at 1 by lia. rewrite Bp_add. nia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma land_disjoint : forall a m k, 0 <= k -> 0 <= m < 2 ^ k -> a mod 2 ^ k = 0 -> Z.land a m = 0.
Proof.
  intros a m k Hk Hm Ha. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i k) as [Hlt|Hge].
  - assert (E : Z.testbit a i = false).
    { rewrite <- (Z.mod_pow2_bits_low a k i) by lia. rewrite Ha. apply Z.bits_0. }
    rewrite E. reflexivity.
  - assert (E : Z.testbit m i = false).
    { destruct (Z.eq_dec m 0) as [->|Hne]; [apply Z.bits_0|].
      apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with k; [|exact Hge].
      apply Z.log2_lt_pow2; lia. }
    rewrite E. apply andb_false_r.
Qed.

Lemma lor_disjoint : forall a m k, 0 <= k -> 0 <= m < 2 ^ k -> a mod 2 ^ k = 0 -> Z.lor a m = a + m.
Proof. intros a m k Hk Hm Ha. pose proof (Z.add_lor_land a m) as E. rewrite (land_disjoint a m k Hk Hm Ha) in E. lia. Qed.

Lemma BW_split : forall k, 0 <= k <= 64 -> BW = 2 ^ k * 2 ^ (64 - k).
Proof. intros k Hk. rewrite <- Z.pow_add_r by lia. replace (k + (64 - k)) with 64 by lia. reflexivity. Qed.

Lemma BW_split' : forall k, 0 <= k <= 64 -> BW = 2 ^ (64 - k) * 2 ^ k.
Proof. intros k Hk. rewrite (BW_split k Hk). ring. Qed.

(* [comment removed for export] *)
Lemma shl_split : forall n lb, 0 <= n -> 0 <= lb <= 64 ->
  shlw n lb + BW * (n / 2 ^ (64 - lb)) = n * 2 ^ lb /\ shlw n lb mod 2 ^ lb = 0.
Proof.
  intros n lb Hn Hlb. unfold shlw.
  assert (Hp1 : 0 < 2 ^ lb) by (apply Z.pow_pos_nonneg; lia).
  assert (Hp2 : 0 < 2 ^ (64 - lb)) by (apply Z.pow_pos_nonneg; lia).
  rewrite (BW_split (64 - lb)) by lia. replace (64 - (64 - lb)) with lb by lia.
  rewrite Z.mul_mod_distr_r by lia.
  pose proof (Z.div_mod n (2 ^ (64 - lb)) ltac:(lia)) as E.
  split; [nia|]. apply Z.mod_mul. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma lshift_limbs_spec : forall l lb m, limbs l -> 0 <= lb < 64 -> 0 <= m < 2 ^ lb ->
  let '(r, mo) := lshift_limbs l lb m in
  limbs r /\ length r = length l /\ 0 <= mo < 2 ^ lb /\ lval r + Bp (length l) * mo = lval l * 2 ^ lb + m.
Proof.
  induction l as [|n l IH]; intros lb m Hl Hlb Hm.
  - cbn [lshift_limbs lval length]. rewrite Bp_0. repeat split; try lia. constructor.
  - apply limbs_cons_inv in Hl. destruct Hl as [[Hn0 Hn1] Hl]. cbn [lshift_limbs].
    assert (Hp1 : 0 < 2 ^ lb) by (apply Z.pow_pos_nonneg; lia).
    set (mo1 := if lb =? 0 then 0 else shrw n (64 - lb)).
    assert (Hmo1 : 0 <= mo1 < 2 ^ lb /\ BW * mo1 + shlw n lb = n * 2 ^ lb).
    { subst mo1. destruct (Z.eqb_spec lb 0) as [->|Hne].
      - unfold shlw. rewrite Z.pow_0_r, Z.mul_1_r, Z.mod_small by lia. lia.
      - unfold shrw. destruct (shl_split n lb Hn0 ltac:(lia)) as [E _].
        assert (Hp2 : 0 < 2 ^ (64 - lb)) by (apply Z.pow_pos_nonneg; lia).
        split; [|lia]. split; [apply Z.div_pos; lia|].
        apply Z.div_lt_upper_bound; [lia|]. rewrite <- (BW_split' lb) by lia. lia. }
    specialize (IH lb mo1 Hl Hlb (proj1 Hmo1)). destruct (lshift_limbs l lb mo1) as [r mo].
    destruct IH as (Hr & Hlen & Hmo & Hv). cbn [lval length]. rewrite Bp_S.
    rewrite (lor_disjoint (shlw n lb) m lb) by (try lia; apply shl_split; lia).
    repeat split; try lia.
    + constructor; [|exact Hr]. unfold limb. pose proof (shlw_limb n lb) as [Hs0 Hs1].
      destruct Hmo1 as [Hmo1 E]. split; [lia|].
      (* [comment removed for export] *)
      destruct (shl_split n lb Hn0 ltac:(lia)) as [_ Hmod].
      apply Z.mod_divide in Hmod; [|lia]. destruct Hmod as [k Hk].
      rewrite (BW_split lb) in Hs1 by lia. rewrite (BW_split lb) by lia.
      assert (Hp2 : 0 < 2 ^ (64 - lb)) by (apply Z.pow_pos_nonneg; lia).
      rewrite Hk in *. assert (k < 2 ^ (64 - lb)) by nia. nia.
Qed.

(* [comment removed for export] *)
Lemma rshift_step : forall m L2 rb, 0 <= m < BW -> 0 <= L2 -> 0 < rb < 64 ->
  2 ^ (64 - rb) * (m + BW * L2) = shlw m (64 - rb) + BW * ((m + BW * L2) / 2 ^ rb).
Proof.
  intros m L2 rb Hm HL Hrb.
  assert (Hp1 : 0 < 2 ^ rb) by (apply Z.pow_pos_nonneg; lia).
  assert (Hp2 : 0 < 2 ^ (64 - rb)) by (apply Z.pow_pos_nonneg; lia).
  destruct (shl_split m (64 - rb) ltac:(lia) ltac:(lia)) as [E _].
  replace (64 - (64 - rb)) with rb in E by lia.
  assert (E2 : (m + BW * L2) / 2 ^ rb = m / 2 ^ rb + 2 ^ (64 - rb) * L2).
  { rewrite (BW_split rb) by lia.
    replace (m + 2 ^ rb * 2 ^ (64 - rb) * L2) with (m + (2 ^ (64 - rb) * L2) * 2 ^ rb) by ring.
    rewrite Z.div_add by lia. reflexivity. }
  rewrite E2. lia.
Qed.

Lemma rshift_limbs_spec : forall l rb, limbs l -> 0 <= rb < 64 ->
  limbs (rshift_limbs l rb) /\ length (rshift_limbs l rb) = length l /\ lval (rshift_limbs l rb) = lval l / 2 ^ rb.
Proof.
  induction l as [|n l IH]; intros rb Hl Hrb.
  - cbn [rshift_limbs lval length]. rewrite Z.div_0_l by (apply Z.pow_nonzero; lia). repeat split. constructor.
  - apply limbs_cons_inv in Hl. destruct Hl as [[Hn0 Hn1] Hl]. cbn [rshift_limbs].
    destruct (IH rb Hl Hrb) as (Hr & Hlen & Hv).
    assert (Hp1 : 0 < 2 ^ rb) by (apply Z.pow_pos_nonneg; lia).
    assert (Hp2 : 0 < 2 ^ (64 - rb)) by (apply Z.pow_pos_nonneg; lia).
    set (hi := match l with [] => 0 | m :: _ => if rb =? 0 then 0 else shlw m (64 - rb) end).
    assert (Hq : 0 <= shrw n rb < 2 ^ (64 - rb)).
    { unfold shrw. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. rewrite <- BW_split by lia. lia. }
    assert (Hhi : hi mod 2 ^ (64 - rb) = 0 /\ 0 <= hi < BW /\
                  (n + BW * lval l) / 2 ^ rb = shrw n rb + hi + BW * (lval l / 2 ^ rb)).
    { assert (E0 : (n + BW * lval l) / 2 ^ rb = n / 2 ^ rb + 2 ^ (64 - rb) * lval l).
      { rewrite (BW_split rb) by lia.
        replace (n + 2 ^ rb * 2 ^ (64 - rb) * lval l) with (n + (2 ^ (64 - rb) * lval l) * 2 ^ rb) by ring.
        rewrite Z.div_add by lia. reflexivity. }
      subst hi. destruct l as [|m l'].
      - cbn [lval]. rewrite Z.mod_0_l by lia. rewrite Z.div_0_l by lia. unfold shrw, BW. split; [reflexivity|]. split; [lia|].
        rewrite Z.mul_0_r, Z.add_0_r. lia.
      - apply limbs_cons_inv in Hl. destruct Hl as [[Hm0 Hm1] Hl']. pose proof (lval_nonneg l' Hl') as HL.
        destruct (Z.eqb_spec rb 0) as [->|Hne].
        + rewrite Z.mod_0_l by lia. unfold shrw, BW. split; [reflexivity|]. split; [lia|].
          rewrite !Z.pow_0_r, !Z.div_1_r. lia.
        + destruct (shl_split m (64 - rb) Hm0 ltac:(lia)) as [_ Hmod].
          split; [exact Hmod|]. split; [apply shlw_limb|].
          rewrite E0. unfold shrw. cbn [lval].
          pose proof (rshift_step m (lval l') rb ltac:(lia) HL ltac:(lia)). lia. }
    destruct Hhi as (Hmod & Hhi & Hval).
    rewrite Z.lor_comm, (lor_disjoint hi (shrw n rb) (64 - rb)) by (try lia; exact Hmod).
    cbn [lval length]. rewrite Hv, Hval. repeat split; try lia.
    constructor; [|exact Hr]. unfold limb. split; [lia|].
    apply Z.mod_divide in Hmod; [|lia]. destruct Hmod as [k Hk]. rewrite (BW_split (64 - rb)) in * by lia.
    replace (64 - (64 - rb)) with rb in * by lia. rewrite Hk in *. assert (k < 2 ^ rb) by nia. nia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma firstn_S_nth : forall (d : list Z) t, (t < length d)%nat -> firstn (S t) d = firstn t d ++ [nth t d 0].
Proof.
  induction d as [|x d IH]; intros t H; cbn [length] in H; [lia|].
  destruct t as [|t]; [reflexivity|]. cbn [firstn nth app]. rewrite <- IH by lia. reflexivity.
Qed.

Lemma strip_top_spec : forall d top, (top <= length d)%nat ->
  (strip_top d top <= top)%nat /\
  lval (firstn (strip_top d top) d) = lval (firstn top d) /\
  (strip_top d top = 0%nat \/ nth (strip_top d top - 1) d 0 <> 0).
Proof.
  intros d. induction top as [|t IH]; intros H; cbn [strip_top].
  - repeat split; auto.
  - destruct (Z.eqb_spec (nth t d 0) 0) as [E|E].
    + destruct (IH ltac:(lia)) as (H1 & H2 & H3). repeat split; [lia| |exact H3].
      rewrite H2, firstn_S_nth by lia. rewrite lval_app, E. cbn [lval]. lia.
    + repeat split; [lia|]. right. replace (S t - 1)%nat with t by lia. exact E.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma add_words_c_length : forall a b c, length (fst (add_words_c a b c)) = Nat.min (length a) (length b).
Proof.
  induction a as [|x a IH]; intros [|y b] c; cbn [add_words_c fst length Nat.min]; try reflexivity.
  specialize (IH b ((x + y + c) / BW)). destruct (add_words_c a b ((x + y + c) / BW)) as [r c'].
  cbn [fst length] in *. rewrite IH. reflexivity.
Qed.

Lemma sub_words_c_length : forall a b c, length (fst (sub_words_c a b c)) = Nat.min (length a) (length b).
Proof.
  induction a as [|x a IH]; intros [|y b] c; cbn [sub_words_c fst length Nat.min]; try reflexivity.
  specialize (IH b (if x - y - c <? 0 then 1 else 0)).
  destruct (sub_words_c a b (if x - y - c <? 0 then 1 else 0)) as [r c'].
  cbn [fst length] in *. rewrite IH. reflexivity.
Qed.

Lemma mul_words_c_length : forall a w c, length (fst (mul_words_c a w c)) = length a.
Proof.
  induction a as [|x a IH]; intros w c; cbn [mul_words_c fst length]; try reflexivity.
  specialize (IH w ((x * w + c) / BW)). destruct (mul_words_c a w ((x * w + c) / BW)) as [r c'].
  cbn [fst length] in *. rewrite IH. reflexivity.
Qed.

Lemma add_words_length : forall a b, length (fst (add_words a b)) = Nat.min (length a) (length b).
Proof. intros. apply add_words_c_length. Qed.
Lemma sub_words_length : forall a b, length (fst (sub_words a b)) = Nat.min (length a) (length b).
Proof. intros. apply sub_words_c_length. Qed.
Lemma mul_words_length : forall a w, length (fst (mul_words a w)) = length a.
Proof. intros. apply mul_words_c_length. Qed.
