(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import BnBase BnWords BnWordsCorrect.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma num_bits_word_spec : forall l, 0 < l ->
  1 <= num_bits_word l /\ 2 ^ (num_bits_word l - 1) <= l < 2 ^ (num_bits_word l).
Proof.
  intros l Hl. unfold num_bits_word. destruct (Z.eqb_spec l 0); [lia|].
  pose proof (Z.log2_nonneg l). pose proof (Z.log2_spec l Hl) as [H1 H2].
  replace (Z.log2 l + 1 - 1) with (Z.log2 l) by lia. replace (Z.succ (Z.log2 l)) with (Z.log2 l + 1) in H2 by lia. lia.
Qed.

Lemma num_bits_word_le : forall l k, 0 <= k -> 0 <= l < 2 ^ k -> 0 <= num_bits_word l <= k.
Proof.
  intros l k Hk Hl. unfold num_bits_word. destruct (Z.eqb_spec l 0); [lia|].
  pose proof (Z.log2_nonneg l). assert (Z.log2 l < k) by (apply Z.log2_lt_pow2; lia). lia.
Qed.

Lemma num_bits_word_norm : forall d, 2 ^ 63 <= d < BW -> num_bits_word d = 64.
Proof.
  intros d Hd. destruct (num_bits_word_spec d ltac:(lia)) as [H1 [H2 H3]].
  pose proof (num_bits_word_le d 64 ltac:(lia) ltac:(unfold BW in *; lia)).
  destruct (Z.eq_dec (num_bits_word d) 64) as [E|E]; [exact E|exfalso].
  assert (2 ^ num_bits_word d <= 2 ^ 63) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma HW_half : HW = 2 * 2 ^ 31. Proof. reflexivity. Qed.
Lemma HW_lt_BW : HW < BW. Proof. reflexivity. Qed.

Lemma mul_bound : forall a b A C, 0 <= a < A -> 0 <= b < C -> 0 <= a * b < A * C.
Proof. intros. nia. Qed.

Lemma mul_lt_BW : forall a b, 0 <= a < HW -> 0 <= b < HW -> 0 <= a * b < BW.
Proof. intros a b Ha Hb. rewrite BW_HW. apply mul_bound; assumption. Qed.

Lemma divmod_BW : forall a b, 0 <= b < BW -> (a * BW + b) / BW = a /\ (a * BW + b) mod BW = b.
Proof.
  intros a b Hb. pose proof BW_pos. split.
  - rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia.
  - rewrite Z.add_comm, Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma mul_le_mono_nonneg : forall a b c, 0 <= c -> a <= b -> a * c <= b * c.
Proof. intros. nia. Qed.

Section Round.
Variables h l d dh dl : Z.
Hypothesis Hd : d = dh * HW + dl.
Hypothesis Hdh : 2 ^ 31 <= dh < HW.
Hypothesis Hdl : 0 <= dl < HW.
Hypothesis Hh : 0 <= h < d.
Hypothesis Hl : 0 <= l < BW.

Let U := h * HW + l / HW.

Lemma dw_l_hi : 0 <= l / HW < HW.
Proof.
  pose proof HW_pos. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. rewrite <- BW_HW. lia.
Qed.

Lemma dw_dpos : 0 < d /\ 0 < dh /\ d < BW.
Proof. pose proof HW_pos. rewrite BW_HW, Hd. repeat split; nia. Qed.

Lemma dw_U_bounds : 0 <= U /\ U < d * HW /\ 0 <= U / d < HW.
Proof.
  pose proof dw_l_hi. pose proof HW_pos. destruct dw_dpos as (Hdpos & _ & _). subst U.
  assert (HH1 : h * HW + l / HW < d * HW) by nia.
  assert (HH0 : 0 <= h * HW + l / HW) by nia.
  split; [exact HH0|]. split; [exact HH1|]. split; [apply Z.div_pos; lia|].
  apply Z.div_lt_upper_bound; [lia|]. lia.
Qed.

(* [comment removed for export] *)
Lemma dw_exit_iff : forall q, 0 <= q < HW -> q * dh <= h ->
  (negb ((h - q * dh) / HW =? 0) || (q * dl <=? ((h - q * dh) * HW) mod BW + l / HW) = true <-> q * d <= U).
Proof.
  intros q Hq Hqh. pose proof dw_l_hi as Hlh. pose proof HW_pos as HWp. subst U.
  set (t := h - q * dh). assert (Ht0 : 0 <= t) by (subst t; lia).
  assert (Eqd : q * d = q * dh * HW + q * dl) by (rewrite Hd; ring).
  assert (Hqdl : 0 <= q * dl < HW * HW) by nia.
  destruct (Z.eqb_spec (t / HW) 0) as [E|E]; cbn [negb orb].
  - assert (Ht : t < HW).
    { destruct (Z.lt_ge_cases t HW) as [|Hge]; [assumption|exfalso].
      assert (1 <= t / HW) by (apply Z.div_le_lower_bound; lia). lia. }
    rewrite Z.mod_small by (rewrite BW_HW; nia).
    rewrite Z.leb_le. rewrite Eqd. subst t. split; intros; nia.
  - split; [intros _|reflexivity].
    assert (Ht : HW <= t).
    { destruct (Z.lt_ge_cases t HW) as [Hlt|]; [exfalso|assumption]. apply E. apply Z.div_small. lia. }
    rewrite Eqd. subst t. nia.
Qed.

Lemma dw_corr_spec : forall fuel q, U / d <= q < HW -> q * dh <= h ->
  HW <= (h - q * dh) + (Z.of_nat fuel - 1) * dh ->
  dw_corr fuel h l dh dl q (q * dh) (q * dl) = (U / d, (U / d) * dh, (U / d) * dl).
Proof.
  pose proof dw_U_bounds as (HU0 & HU1 & HUd). pose proof HW_pos as HWp. pose proof HW_lt_BW as HWB.
  destruct dw_dpos as (Hdpos & Hdhpos & HdB).
  assert (Hqd : forall q, q * d <= U -> U / d <= q -> q = U / d).
  { intros q H1 H2. assert (q <= U / d) by (apply Z.div_le_lower_bound; lia). lia. }
  induction fuel as [|f IH]; intros q Hq Hqh Hfuel.
  - cbn [dw_corr]. assert (E : q = U / d).
    { apply Hqd; [|lia]. apply (dw_exit_iff q ltac:(lia) Hqh).
      assert (Ht : HW <= h - q * dh) by (change (Z.of_nat 0) with 0 in Hfuel; lia).
      destruct (Z.eqb_spec ((h - q * dh) / HW) 0) as [E|E]; [exfalso|reflexivity].
      assert (1 <= (h - q * dh) / HW) by (apply Z.div_le_lower_bound; lia). lia. }
    rewrite <- E. reflexivity.
  - cbn [dw_corr].
    assert (Hqdh0 : 0 <= q * dh) by nia.
    assert (Et : subw h (q * dh) = h - q * dh) by (unfold subw; apply Z.mod_small; lia).
    rewrite Et. pose proof (dw_exit_iff q ltac:(lia) Hqh) as Hex.
    destruct (negb ((h - q * dh) / HW =? 0) || (q * dl <=? ((h - q * dh) * HW) mod BW + l / HW)) eqn:Eb.
    + assert (E : q = U / d) by (apply Hqd; [apply Hex; reflexivity|lia]). rewrite <- E. reflexivity.
    + assert (Hgt : U < q * d).
      { destruct (Z.le_gt_cases (q * d) U) as [Hle|]; [|assumption]. apply Hex in Hle. congruence. }
      assert (Hq1 : U / d <= q - 1).
      { assert (U / d < q); [|lia]. apply Z.div_lt_upper_bound; lia. }
      assert (Hqpos : 1 <= q) by lia.
      assert (Hqdh : 0 <= (q - 1) * dh <= h).
      { split; [apply Z.mul_nonneg_nonneg; lia|]. pose proof (mul_le_mono_nonneg (q - 1) q dh ltac:(lia) ltac:(lia)). lia. }
      assert (Hqdl : 0 <= (q - 1) * dl < BW) by (apply mul_lt_BW; lia).
      assert (E1 : subw q 1 = q - 1) by (unfold subw; apply Z.mod_small; lia).
      assert (E2 : subw (q * dh) dh = (q - 1) * dh).
      { unfold subw. replace (q * dh - dh) with ((q - 1) * dh) by ring. apply Z.mod_small. lia. }
      assert (E3 : subw (q * dl) dl = (q - 1) * dl).
      { unfold subw. replace (q * dl - dl) with ((q - 1) * dl) by ring. apply Z.mod_small. lia. }
      rewrite E1, E2, E3. apply IH; [lia|lia|]. rewrite Nat2Z.inj_succ in Hfuel. lia.
Qed.

(* [comment removed for export] *)
Lemma dw_q0 :
  let q0 := if h / HW =? dh then HW - 1 else h / dh in
  U / d <= q0 < HW /\ q0 * dh <= h /\ mulw q0 dh = q0 * dh /\ mulw dl q0 = q0 * dl.
Proof.
  pose proof dw_U_bounds as (HU0 & HU1 & HUd). pose proof dw_l_hi as Hlh. pose proof HW_pos as HWp.
  destruct dw_dpos as (Hdpos & Hdhpos & HdB).
  cbv zeta. destruct (Z.eqb_spec (h / HW) dh) as [E|E].
  - assert (Hge : dh * HW <= h).
    { rewrite <- E. rewrite Z.mul_comm. apply Z.mul_div_le. lia. }
    assert (H1 : (HW - 1) * dh <= h) by nia.
    assert (H2 : 0 <= (HW - 1) * dl < BW) by (apply mul_lt_BW; lia).
    assert (H3 : 0 <= (HW - 1) * dh) by (apply Z.mul_nonneg_nonneg; lia).
    split; [lia|]. split; [exact H1|]. split.
    + unfold mulw. apply Z.mod_small. lia.
    + unfold mulw. rewrite Z.mul_comm. apply Z.mod_small. lia.
  - assert (Hlt : h < dh * HW).
    { assert (h / HW < dh + 1) by (apply Z.div_lt_upper_bound; [lia|]; nia).
      assert (Hlt : h / HW < dh) by lia.
      pose proof (Z.div_mod h HW ltac:(lia)). pose proof (Z.mod_pos_bound h HW ltac:(lia)). nia. }
    assert (Hq0 : 0 <= h / dh < HW).
    { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia. }
    assert (Hm : h / dh * dh <= h) by (rewrite Z.mul_comm; apply Z.mul_div_le; lia).
    assert (H2 : 0 <= h / dh * dl < BW) by (apply mul_lt_BW; lia).
    assert (H3 : 0 <= h / dh * dh) by (apply Z.mul_nonneg_nonneg; lia).
    split; [|split; [exact Hm|split]].
    + split; [|lia]. (* [comment removed for export] *)
      apply Z.div_le_lower_bound; [lia|].
      pose proof (Z.mul_div_le U d Hdpos) as HUm. set (qq := U / d) in *.
      assert (Hqq0 : 0 <= qq) by lia.
      assert (Hqq : dh * qq * HW <= d * qq).
      { rewrite Hd. assert (0 <= dl * qq) by (apply Z.mul_nonneg_nonneg; lia). lia. }
      assert (HUh : U < (h + 1) * HW) by (subst U; lia).
      assert (dh * qq < h + 1) by (apply Z.mul_lt_mono_pos_r with HW; lia). lia.
    + unfold mulw. apply Z.mod_small. lia.
    + unfold mulw. rewrite Z.mul_comm. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Lemma dw_round_spec :
  let q := U / d in
  let R := h * BW + l - q * d * HW in
  dw_round h l d dh dl = (q, R / BW, R mod BW) /\ 0 <= R < d * HW /\ 0 <= q < HW.
Proof.
  pose proof dw_U_bounds as (HU0 & HU1 & HUd). pose proof dw_l_hi as Hlh. pose proof HW_pos as HWp.
  destruct dw_dpos as (Hdpos & Hdhpos & HdB). pose proof BW_pos as BWp.
  cbv zeta. unfold dw_round. pose proof dw_q0 as Hq0. cbv zeta in Hq0.
  set (q0 := if h / HW =? dh then HW - 1 else h / dh) in *. destruct Hq0 as (Hq0a & Hq0b & Em1 & Em2).
  rewrite Em1, Em2. rewrite (dw_corr_spec DW_FUEL q0 Hq0a Hq0b)
    by (unfold DW_FUEL; change (Z.of_nat 4 - 1) with 3; rewrite HW_half in *; lia).
  set (q := U / d) in *.
  assert (HqU : q * d <= U) by (subst q; rewrite Z.mul_comm; apply Z.mul_div_le; lia).
  assert (HUq : U < q * d + d).
  { subst q. pose proof (Z.div_mod U d ltac:(lia)). pose proof (Z.mod_pos_bound U d Hdpos). lia. }
  assert (Hqdl : 0 <= q * dl < BW) by (apply mul_lt_BW; lia).
  set (t := q * dl / HW).
  assert (Etl : (q * dl * HW) mod BW = (q * dl) mod HW * HW).
  { rewrite BW_HW. apply Z.mul_mod_distr_r; lia. }
  rewrite Etl. set (tl2 := (q * dl) mod HW * HW).
  pose proof (Z.div_mod (q * dl) HW ltac:(lia)) as Edm. fold t in Edm.
  pose proof (Z.mod_pos_bound (q * dl) HW ltac:(lia)) as Hmb.
  assert (Ht : 0 <= t) by (subst t; apply Z.div_pos; lia).
  (* [comment removed for export] *)
  assert (EP : q * d * HW = (q * dh + t) * BW + tl2).
  { subst tl2. rewrite Hd, BW_HW.
    replace (q * (dh * HW + dl) * HW) with (q * dh * (HW * HW) + (q * dl) * HW) by ring. rewrite Edm at 1. ring. }
  pose proof (Z.div_mod l HW ltac:(lia)) as Eldm.
  pose proof (Z.mod_pos_bound l HW ltac:(lia)) as Hlmb.
  assert (EN : h * BW + l = U * HW + l mod HW) by (subst U; rewrite BW_HW; lia).
  assert (HN : q * d * HW <= h * BW + l).
  { pose proof (mul_le_mono_nonneg (q * d) U HW ltac:(lia) HqU). lia. }
  assert (Htl2 : 0 <= tl2 < BW).
  { subst tl2. rewrite BW_HW. split; [apply Z.mul_nonneg_nonneg; lia|]. apply Z.mul_lt_mono_pos_r; lia. }
  assert (Hth2 : q * dh + t <= h).
  { assert (Hx : (q * dh + t) * BW < (h + 1) * BW) by lia. apply Z.mul_lt_mono_pos_r in Hx; lia. }
  assert (Hqdh : 0 <= q * dh) by (apply Z.mul_nonneg_nonneg; lia).
  assert (Eth2 : addw (q * dh) t = q * dh + t) by (unfold addw; apply Z.mod_small; lia).
  rewrite Eth2.
  assert (HR : 0 <= h * BW + l - q * d * HW < d * HW).
  { split; [lia|]. pose proof (mul_le_mono_nonneg U (q * d + d - 1) HW ltac:(lia) ltac:(lia)). lia. }
  destruct (Z.ltb_spec l tl2) as [Hlt|Hge].
  - assert (Hth3 : q * dh + t + 1 <= h).
    { assert (Hx : (q * dh + t) * BW < h * BW) by lia. apply Z.mul_lt_mono_pos_r in Hx; lia. }
    assert (Eth3 : addw (q * dh + t) 1 = q * dh + t + 1) by (unfold addw; apply Z.mod_small; lia).
    rewrite Eth3. destruct (Z.ltb_spec h (q * dh + t + 1)); [lia|].
    assert (El : subw l tl2 = l - tl2 + BW).
    { unfold subw. rewrite <- (Z.mod_add (l - tl2) 1 BW) by lia. apply Z.mod_small. lia. }
    assert (Eh : subw h (q * dh + t + 1) = h - (q * dh + t + 1)) by (unfold subw; apply Z.mod_small; lia).
    rewrite El, Eh.
    assert (ER : h * BW + l - q * d * HW = (h - (q * dh + t + 1)) * BW + (l - tl2 + BW)) by (rewrite EP; ring).
    rewrite ER. split; [|split; [rewrite <- ER; exact HR|lia]].
    match goal with |- context [(?a * BW + ?b) / BW] => destruct (divmod_BW a b ltac:(lia)) as [Ed Em] end.
    rewrite Ed, Em. reflexivity.
  - destruct (Z.ltb_spec h (q * dh + t)); [lia|].
    assert (El : subw l tl2 = l - tl2) by (unfold subw; apply Z.mod_small; lia).
    assert (Eh : subw h (q * dh + t) = h - (q * dh + t)) by (unfold subw; apply Z.mod_small; lia).
    rewrite El, Eh.
    assert (ER : h * BW + l - q * d * HW = (h - (q * dh + t)) * BW + (l - tl2)) by (rewrite EP; ring).
    rewrite ER. split; [|split; [rewrite <- ER; exact HR|lia]].
    match goal with |- context [(?a * BW + ?b) / BW] => destruct (divmod_BW a b ltac:(lia)) as [Ed Em] end.
    rewrite Ed, Em. reflexivity.
Qed.

End Round.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem div_words_correct : forall h l d, 2 ^ 63 <= d < BW -> 0 <= h < d -> 0 <= l < BW ->
  div_words h l d = (h * BW + l) / d.
Proof.
  intros h l d Hd Hh Hl. pose proof HW_pos as HWp. pose proof BW_pos as BWp. pose proof HW_lt_BW as HWB.
  unfold div_words. destruct (Z.eqb_spec d 0) as [E|_]; [lia|].
  rewrite (num_bits_word_norm d Hd). change (64 - 64) with 0. rewrite Z.eqb_refl.
  destruct (Z.leb_spec d h) as [Hle|_]; [lia|].
  set (dh := d / HW). set (dl := d mod HW).
  assert (Ed : d = dh * HW + dl) by (subst dh dl; pose proof (Z.div_mod d HW ltac:(lia)); lia).
  assert (Hdl : 0 <= dl < HW) by (subst dl; apply Z.mod_pos_bound; lia).
  assert (Hdh : 2 ^ 31 <= dh < HW).
  { subst dh. split.
    - apply Z.div_le_lower_bound; [lia|]. rewrite HW_half. lia.
    - apply Z.div_lt_upper_bound; [lia|]. rewrite <- BW_HW. lia. }
  (* [comment removed for export] *)
  pose proof (dw_round_spec h l d dh dl Ed Hdh Hdl Hh Hl) as H1. cbv zeta in H1.
  set (q1 := (h * HW + l / HW) / d) in *. set (R1 := h * BW + l - q1 * d * HW) in *.
  destruct H1 as (E1 & HR1 & Hq1). rewrite E1.
  pose proof (Z.div_mod R1 BW ltac:(lia)) as ER1. pose proof (Z.mod_pos_bound R1 BW BWp) as Hl1.
  set (h1 := R1 / BW) in *. set (l1 := R1 mod BW) in *.
  assert (Hh1 : 0 <= h1 < HW).
  { subst h1. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
    assert (d * HW < BW * HW) by (apply Z.mul_lt_mono_pos_r; lia). lia. }
  assert (Eh1 : (h1 * HW) mod BW = h1 * HW).
  { apply Z.mod_small. rewrite BW_HW. split; [apply Z.mul_nonneg_nonneg; lia|]. apply Z.mul_lt_mono_pos_r; lia. }
  rewrite Eh1.
  pose proof (Z.div_mod l1 HW ltac:(lia)) as El1. pose proof (Z.mod_pos_bound l1 HW HWp) as Hl1m.
  assert (Hl1d : 0 <= l1 / HW < HW).
  { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. rewrite <- BW_HW. lia. }
  assert (El2 : ((l1 mod HW) * HW) mod BW = (l1 mod HW) * HW).
  { apply Z.mod_small. rewrite BW_HW. split; [apply Z.mul_nonneg_nonneg; lia|]. apply Z.mul_lt_mono_pos_r; lia. }
  rewrite El2.
  set (h2 := h1 * HW + l1 / HW). set (l2 := l1 mod HW * HW).
  (* [comment removed for export] *)
  assert (ER1' : R1 = h2 * HW + l1 mod HW) by (subst h2; rewrite ER1, BW_HW; lia).
  assert (Hh2 : 0 <= h2 < d).
  { split; [subst h2; assert (0 <= h1 * HW) by (apply Z.mul_nonneg_nonneg; lia); lia|].
    assert (Hx : h2 * HW < d * HW) by lia. apply Z.mul_lt_mono_pos_r in Hx; lia. }
  assert (Hl2 : 0 <= l2 < BW).
  { subst l2. rewrite BW_HW. split; [apply Z.mul_nonneg_nonneg; lia|]. apply Z.mul_lt_mono_pos_r; lia. }
  pose proof (dw_round_spec h2 l2 d dh dl Ed Hdh Hdl Hh2 Hl2) as H2. cbv zeta in H2.
  assert (EU2 : h2 * HW + l2 / HW = R1).
  { subst l2. rewrite Z.div_mul by lia. lia. }
  rewrite EU2 in H2. destruct H2 as (E2 & _ & Hq2). rewrite E2.
  assert (Eret : (q1 * HW) mod BW = q1 * HW).
  { apply Z.mod_small. rewrite BW_HW. split; [apply Z.mul_nonneg_nonneg; lia|]. apply Z.mul_lt_mono_pos_r; lia. }
  rewrite Eret.
  rewrite (lor_disjoint (q1 * HW) (R1 / d) 32);
    [|lia|rewrite <- HW_pow; exact Hq2|rewrite HW_pow; apply Z.mod_mul; lia].
  (* [comment removed for export] *)
  pose proof (Z.div_mod R1 d ltac:(lia)) as ERd. pose proof (Z.mod_pos_bound R1 d ltac:(lia)) as HRm.
  apply Z.div_unique with (R1 mod d); [left; lia|].
  assert (EN : h * BW + l = q1 * d * HW + R1) by (subst R1; ring).
  rewrite EN. rewrite ERd at 1. ring.
Qed.

(* [comment removed for export] *)
Lemma div_words_limb : forall h l d, 2 ^ 63 <= d < BW -> 0 <= h < d -> 0 <= l < BW -> limb (div_words h l d).
Proof.
  intros h l d Hd Hh Hl. rewrite div_words_correct by assumption. unfold limb. pose proof BW_pos.
  split; [apply Z.div_pos; nia|]. apply Z.div_lt_upper_bound; [lia|].
  assert (h * BW + l < (h + 1) * BW) by lia. assert ((h + 1) * BW <= d * BW) by (apply Z.mul_le_mono_nonneg_r; lia). lia.
Qed.
