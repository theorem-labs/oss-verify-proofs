(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnWordsCorrect BnKara.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma mul_bound_lt : forall a b A C, 0 <= a < A -> 0 <= b < C -> a * b < A * C.
Proof. intros. nia. Qed.

Lemma carry_up_spec : forall l, limbs l ->
  limbs (carry_up l) /\ length (carry_up l) = length l /\ lval (carry_up l) = (lval l + 1) mod Bp (length l).
Proof.
  induction l as [|x l IH]; intros Hl.
  - cbn [carry_up lval length]. rewrite Bp_0, Z.mod_1_r. repeat split. constructor.
  - apply limbs_cons_inv in Hl. destruct Hl as [[Hx0 Hx1] Hl]. destruct (IH Hl) as (H1 & H2 & H3).
    pose proof BW_pos as BWp. pose proof (Bp_pos (length l)) as Hbp. pose proof (lval_bound l Hl) as Hb.
    cbn [carry_up]. unfold addw. cbn [length]. rewrite Bp_S.
    destruct (Z.eq_dec x (BW - 1)) as [E|E].
    + subst x. replace (BW - 1 + 1) with BW by ring. rewrite Z.mod_same by lia. cbn [Z.eqb].
      cbn [lval length]. split; [constructor; [exact limb_0|exact H1]|]. split; [lia|].
      rewrite H3. cbn [lval]. replace (BW - 1 + BW * lval l + 1) with ((lval l + 1) * BW) by ring.
      rewrite (Z.mul_comm (lval l + 1) BW), Z.mul_mod_distr_l by lia. ring.
    + rewrite (Z.mod_small (x + 1) BW) by lia. destruct (Z.eqb_spec (x + 1) 0); [lia|].
      cbn [lval length]. split; [constructor; [unfold limb; lia|exact Hl]|]. split; [reflexivity|].
      cbn [lval]. replace (x + BW * lval l + 1) with (x + 1 + BW * lval l) by ring.
      symmetry. apply Z.mod_small. nia.
Qed.

Lemma add_carry_spec : forall l c, limbs l -> 0 <= c < BW -> lval l + c < Bp (length l) ->
  limbs (add_carry l c) /\ length (add_carry l c) = length l /\ lval (add_carry l c) = lval l + c.
Proof.
  intros [|x l] c Hl Hc Hfit.
  - cbn [add_carry lval length] in *. rewrite Bp_0 in Hfit. repeat split; [constructor|lia].
  - apply limbs_cons_inv in Hl. destruct Hl as [[Hx0 Hx1] Hl].
    pose proof BW_pos as BWp. pose proof (Bp_pos (length l)) as Hbp. pose proof (lval_bound l Hl) as Hb.
    cbn [add_carry]. unfold addw. rewrite (Z.mod_small c BW) by lia. cbn [lval length] in Hfit. rewrite Bp_S in Hfit.
    destruct (Z.lt_ge_cases (x + c) BW) as [Hno|Hov].
    + rewrite (Z.mod_small (x + c) BW) by lia. destruct (Z.ltb_spec (x + c) c); [lia|].
      cbn [lval length]. split; [constructor; [unfold limb; lia|exact Hl]|]. split; [reflexivity|lia].
    + assert (Em : (x + c) mod BW = x + c - BW).
      { rewrite <- (Z.mod_add _ (-1) BW) by lia. apply Z.mod_small. lia. }
      rewrite Em. destruct (Z.ltb_spec (x + c - BW) c); [|lia].
      destruct (carry_up_spec l Hl) as (H1 & H2 & H3).
      cbn [lval length]. split; [constructor; [unfold limb; lia|exact H1]|]. split; [lia|].
      rewrite H3. rewrite Z.mod_small by nia. ring.
Qed.

Lemma kara_combine_spec : forall n (neg : bool) r t,
  let n2 := (2 * n)%nat in
  limbs r -> length r = (2 * n2)%nat -> limbs t -> (2 * n2 <= length t)%nat ->
  let P0 := lval (slice r 0 n2) in
  let P2 := lval (slice r n2 n2) in
  let Tm := lval (slice t n2 n2) in
  let M := P0 + P2 + (if neg then - Tm else Tm) in
  0 <= M -> P0 + Bp n2 * P2 + Bp n * M < Bp (2 * n2) ->
  let '(r', t') := kara_combine n neg r t in
  limbs r' /\ length r' = length r /\ lval r' = P0 + Bp n2 * P2 + Bp n * M /\
  limbs t' /\ length t' = length t.
Proof.
  intros n neg r t n2 Hr Hrl Ht Htl P0 P2 Tm M HM Hfit. pose proof BW_pos as BWp.
  unfold kara_combine. fold n2.

  pose proof (add_words_spec (slice r 0 n2) (slice r n2 n2) (slice_limbs _ _ _ Hr) (slice_limbs _ _ _ Hr)
                ltac:(rewrite !slice_length by lia; reflexivity)) as H1.
  destruct (add_words (slice r 0 n2) (slice r n2 n2)) as [s1 c1]. destruct H1 as (Hs1 & Hs1l & Hc1 & Hv1).
  rewrite slice_length in Hs1l, Hv1 by lia. fold P0 P2 in Hv1.
  set (ta := splice t 0 s1).
  assert (Htal : length ta = length t) by (subst ta; apply splice_length; lia).
  assert (Hta : limbs ta) by (subst ta; apply splice_limbs; assumption).
  assert (Eta0 : slice ta 0 n2 = s1) by (subst ta; rewrite <- Hs1l; apply slice_splice_same; lia).
  assert (Etan : slice ta n2 n2 = slice t n2 n2) by (subst ta; apply slice_splice_above; lia).
  rewrite Eta0, Etan.
  pose proof (lval_bound (slice t n2 n2) (slice_limbs _ _ _ Ht)) as HTmb. rewrite slice_length in HTmb by lia. fold Tm in HTmb.
  pose proof (lval_bound s1 Hs1) as Hs1b. rewrite Hs1l in Hs1b.

  assert (H2 : let '(s2, c2) := (if neg
                  then let '(s, bw) := sub_words s1 (slice t n2 n2) in (s, c1 - bw)
                  else let '(s, cy) := add_words (slice t n2 n2) s1 in (s, c1 + cy)) in
               limbs s2 /\ length s2 = n2 /\ 0 <= c2 <= 2 /\ lval s2 + Bp n2 * c2 = M).
  { destruct neg.
    - pose proof (sub_words_spec s1 (slice t n2 n2) Hs1 (slice_limbs _ _ _ Ht)
                    ltac:(rewrite slice_length by lia; lia)) as Hx.
      destruct (sub_words s1 (slice t n2 n2)) as [s bw]. destruct Hx as (Hs & Hsl & Hbw & Hv).
      rewrite Hs1l in Hsl, Hv. fold Tm in Hv. pose proof (lval_bound s Hs) as Hsb. rewrite Hsl in Hsb.
      pose proof (Bp_pos n2). subst M. split; [exact Hs|]. split; [exact Hsl|]. split; [nia|]. nia.
    - pose proof (add_words_spec (slice t n2 n2) s1 (slice_limbs _ _ _ Ht) Hs1
                    ltac:(rewrite slice_length by lia; lia)) as Hx.
      destruct (add_words (slice t n2 n2) s1) as [s cy]. destruct Hx as (Hs & Hsl & Hcy & Hv).
      rewrite slice_length in Hsl, Hv by lia. fold Tm in Hv.
      subst M. split; [exact Hs|]. split; [exact Hsl|]. split; [lia|]. nia. }
  destruct (if neg then let '(s, bw) := sub_words s1 (slice t n2 n2) in (s, c1 - bw)
            else let '(s, cy) := add_words (slice t n2 n2) s1 in (s, c1 + cy)) as [s2 c2].
  destruct H2 as (Hs2 & Hs2l & Hc2 & Hv2).
  set (tb := splice ta n2 s2).
  assert (Htbl : length tb = length t) by (subst tb; rewrite splice_length; lia).
  assert (Htb : limbs tb) by (subst tb; apply splice_limbs; assumption).
  assert (Etb : slice tb n2 n2 = s2) by (subst tb; rewrite <- Hs2l; apply slice_splice_same; lia).
  rewrite Etb.

  pose proof (add_words_spec (slice r n n2) s2 (slice_limbs _ _ _ Hr) Hs2 ltac:(rewrite slice_length by lia; lia)) as H3.
  destruct (add_words (slice r n n2) s2) as [s3 c3]. destruct H3 as (Hs3 & Hs3l & Hc3 & Hv3).
  rewrite slice_length in Hs3l, Hv3 by lia.
  set (ra := splice r n s3).
  assert (Hral : length ra = length r) by (subst ra; apply splice_length; lia).
  assert (Hra : limbs ra) by (subst ra; apply splice_limbs; assumption).
  assert (Erav : lval ra = lval r + Bp n * (lval s3 - lval (slice r n n2))).
  { subst ra. rewrite lval_splice by lia. rewrite Hs3l. reflexivity. }

  assert (Erv : lval r = P0 + Bp n2 * P2).
  { subst P0 P2. rewrite (lval_split_le n2 r) by lia. unfold slice. cbn [skipn].
    rewrite (firstn_all2 (n:=n2) (skipn n2 r)) by (rewrite length_skipn; lia). reflexivity. }
  assert (EB : Bp (n + n2) = Bp n * Bp n2) by apply Bp_add.
  assert (EB2 : Bp (2 * n2) = Bp (n + n2) * Bp n) by (rewrite <- Bp_add; f_equal; lia).
  pose proof (Bp_pos n) as Hbn. pose proof (Bp_pos n2) as Hbn2.

  assert (Etot : lval ra + Bp (n + n2) * (c2 + c3) = P0 + Bp n2 * P2 + Bp n * M) by (rewrite Erav, Erv, EB; nia).
  destruct (Z.eqb_spec (c2 + c3) 0) as [Ec|Ec].
  - rewrite Ec, Z.mul_0_r, Z.add_0_r in Etot. repeat split; try assumption; lia.
  -
    pose proof (lval_split_le (n + n2) ra ltac:(lia)) as Esp.
    assert (Hhi : limbs (skipn (n + n2) ra)) by (apply limbs_skipn; exact Hra).
    assert (Hhil : length (skipn (n + n2) ra) = n) by (rewrite length_skipn; lia).
    pose proof (lval_nonneg _ (limbs_firstn (n + n2) ra Hra)) as Hlo0.
    pose proof (add_carry_spec (skipn (n + n2) ra) (c2 + c3) Hhi ltac:(unfold BW; lia)) as Hac.
    rewrite Hhil in Hac.
    assert (Hfit2 : lval (skipn (n + n2) ra) + (c2 + c3) < Bp n).
    { assert (Bp (n + n2) * (lval (skipn (n + n2) ra) + (c2 + c3)) < Bp (n + n2) * Bp n) by nia.
      apply Z.mul_lt_mono_pos_l in H; [exact H|]. apply Bp_pos. }
    destruct (Hac Hfit2) as (Ha1 & Ha2 & Ha3).
    split; [apply limbs_app; [apply limbs_firstn; exact Hra|exact Ha1]|].
    split; [rewrite length_app, length_firstn, Ha2; lia|].
    split; [|split; assumption].
    rewrite lval_app, firstn_length_le by lia. rewrite Ha3. nia.
Qed.

Lemma sub_part_words_fst : forall a b cl, limbs a -> limbs b ->
  (length a = cl /\ cl <= length b)%nat \/ (length b = cl /\ cl <= length a)%nat ->
  limbs (fst (sub_part_words a b cl)) /\ length (fst (sub_part_words a b cl)) = Nat.max (length a) (length b) /\
  (lval b <= lval a -> lval (fst (sub_part_words a b cl)) = lval a - lval b).
Proof.
  intros a b cl Ha Hb Hlen. pose proof (sub_part_words_spec a b cl Ha Hb Hlen) as H.
  destruct (sub_part_words a b cl) as [r c]. cbn [fst]. destruct H as (Hr & Hl & Hc & Hv).
  split; [exact Hr|]. split; [exact Hl|]. intros Hge.
  pose proof (lval_bound r Hr) as Hrb. pose proof (Bp_pos (length r)).
  assert (c = 0 \/ c = 1) as [->| ->] by lia; [lia|exfalso].
  pose proof (lval_bound a Ha). pose proof (lval_nonneg b Hb).
  assert (Bp (length a) <= Bp (length r)) by (apply Bp_mono; lia). lia.
Qed.

Ltac eval_conds :=
  repeat match goal with
         | |- context [Z.eqb ?a ?b] =>
             let v := eval vm_compute in (Z.eqb a b) in change (Z.eqb a b) with v
         end; cbn [orb andb].

Section Diffs.
Variables a_lo a_hi b_lo b_hi : list Z.
Variables n tna tnb : nat.
Hypothesis Hal : limbs a_lo. Hypothesis Hah : limbs a_hi.
Hypothesis Hbl : limbs b_lo. Hypothesis Hbh : limbs b_hi.
Hypothesis Hall : length a_lo = n. Hypothesis Hahl : length a_hi = tna.
Hypothesis Hbll : length b_lo = n. Hypothesis Hbhl : length b_hi = tnb.
Hypothesis Htna : (tna <= n)%nat. Hypothesis Htnb : (tnb <= n)%nat.

Let A0 := lval a_lo. Let A1 := lval a_hi. Let B0 := lval b_lo. Let B1 := lval b_hi.

Lemma kara_c1 : cmp_part_words a_lo a_hi tna = sgn3 A0 A1.
Proof. apply cmp_part_words_spec; try assumption. right. lia. Qed.
Lemma kara_c2 : cmp_part_words b_hi b_lo tnb = sgn3 B1 B0.
Proof. apply cmp_part_words_spec; try assumption. left. lia. Qed.

Lemma kd_ah_al : let r := fst (sub_part_words a_hi a_lo tna) in limbs r /\ length r = n /\ (A0 <= A1 -> lval r = A1 - A0).
Proof. destruct (sub_part_words_fst a_hi a_lo tna Hah Hal ltac:(left; lia)) as (H1 & H2 & H3). cbv zeta. repeat split; [exact H1|lia|exact H3]. Qed.
Lemma kd_al_ah : let r := fst (sub_part_words a_lo a_hi tna) in limbs r /\ length r = n /\ (A1 <= A0 -> lval r = A0 - A1).
Proof. destruct (sub_part_words_fst a_lo a_hi tna Hal Hah ltac:(right; lia)) as (H1 & H2 & H3). cbv zeta. repeat split; [exact H1|lia|exact H3]. Qed.
Lemma kd_bl_bh : let r := fst (sub_part_words b_lo b_hi tnb) in limbs r /\ length r = n /\ (B1 <= B0 -> lval r = B0 - B1).
Proof. destruct (sub_part_words_fst b_lo b_hi tnb Hbl Hbh ltac:(right; lia)) as (H1 & H2 & H3). cbv zeta. repeat split; [exact H1|lia|exact H3]. Qed.
Lemma kd_bh_bl : let r := fst (sub_part_words b_hi b_lo tnb) in limbs r /\ length r = n /\ (B0 <= B1 -> lval r = B1 - B0).
Proof. destruct (sub_part_words_fst b_hi b_lo tnb Hbh Hbl ltac:(left; lia)) as (H1 & H2 & H3). cbv zeta. repeat split; [exact H1|lia|exact H3]. Qed.

Definition diffs_ok (t0 t1 : list Z) (neg : bool) : Prop :=
  limbs t0 /\ length t0 = n /\ limbs t1 /\ length t1 = n /\
  (if neg then - (lval t0 * lval t1) else lval t0 * lval t1) = (A0 - A1) * (B1 - B0).

Lemma rec_diffs_spec :
  match rec_diffs a_lo a_hi b_lo b_hi tna tnb (cmp_part_words a_lo a_hi tna) (cmp_part_words b_hi b_lo tnb) with
  | Some (t0, t1, neg) => diffs_ok t0 t1 neg
  | None => (A0 - A1) * (B1 - B0) = 0
  end.
Proof.
  rewrite kara_c1, kara_c2. unfold rec_diffs, diffs_ok.
  destruct kd_ah_al as (P1 & P2 & P3). destruct kd_al_ah as (Q1 & Q2 & Q3).
  destruct kd_bl_bh as (R1 & R2 & R3). destruct kd_bh_bl as (S1 & S2 & S3).
  destruct (Z.lt_trichotomy A0 A1) as [Ha|[Ha|Ha]]; destruct (Z.lt_trichotomy B1 B0) as [Hb|[Hb|Hb]];
    rewrite ?(sgn3_lt _ _ Ha), ?(sgn3_gt _ _ Ha), ?(sgn3_lt _ _ Hb), ?(sgn3_gt _ _ Hb), ?Ha, ?Hb, ?sgn3_eq;
    eval_conds; try (repeat split; try assumption; rewrite ?P3, ?Q3, ?R3, ?S3 by lia; ring); try lia; try ring.
Qed.

Lemma part_diffs_spec :
  let '(t0, t1, neg) := part_diffs a_lo a_hi b_lo b_hi tna tnb (cmp_part_words a_lo a_hi tna) (cmp_part_words b_hi b_lo tnb) in
  diffs_ok t0 t1 neg.
Proof.
  rewrite kara_c1, kara_c2. unfold part_diffs, diffs_ok.
  destruct kd_ah_al as (P1 & P2 & P3). destruct kd_al_ah as (Q1 & Q2 & Q3).
  destruct kd_bl_bh as (R1 & R2 & R3). destruct kd_bh_bl as (S1 & S2 & S3).
  destruct (Z.lt_trichotomy A0 A1) as [Ha|[Ha|Ha]]; destruct (Z.lt_trichotomy B1 B0) as [Hb|[Hb|Hb]];
    rewrite ?(sgn3_lt _ _ Ha), ?(sgn3_gt _ _ Ha), ?(sgn3_lt _ _ Hb), ?(sgn3_gt _ _ Hb), ?Ha, ?Hb, ?sgn3_eq;
    eval_conds; repeat split; try assumption;
    rewrite ?P3, ?Q3, ?R3, ?S3 by lia; try ring; try lia.
Qed.

End Diffs.

Lemma kara_finish : forall n (neg : bool) r t A0 A1 B0 B1,
  let n2 := (2 * n)%nat in
  limbs r -> length r = (2 * n2)%nat -> limbs t -> (2 * n2 <= length t)%nat ->
  lval (slice r 0 n2) = A0 * B0 -> lval (slice r n2 n2) = A1 * B1 ->
  (if neg then - lval (slice t n2 n2) else lval (slice t n2 n2)) = (A0 - A1) * (B1 - B0) ->
  0 <= A0 < Bp n -> 0 <= A1 < Bp n -> 0 <= B0 < Bp n -> 0 <= B1 < Bp n ->
  let '(r', t') := kara_combine n neg r t in
  limbs r' /\ length r' = length r /\ lval r' = (A0 + Bp n * A1) * (B0 + Bp n * B1) /\
  limbs t' /\ length t' = length t.
Proof.
  intros n neg r t A0 A1 B0 B1 n2 Hr Hrl Ht Htl HP0 HP2 Hsgn HA0 HA1 HB0 HB1.
  pose proof (kara_combine_spec n neg r t Hr Hrl Ht Htl) as H. cbv zeta in H. fold n2 in H.
  rewrite HP0, HP2 in H.
  assert (EM : A0 * B0 + A1 * B1 + (if neg then - lval (slice t n2 n2) else lval (slice t n2 n2)) = A0 * B1 + A1 * B0).
  { rewrite Hsgn. ring. }
  rewrite EM in H.
  assert (EB : Bp n2 = Bp n * Bp n) by (subst n2; rewrite <- Bp_add; f_equal; lia).
  assert (EB2 : Bp (2 * n2) = Bp n2 * Bp n2) by (rewrite <- Bp_add; f_equal; lia).
  pose proof (Bp_pos n) as Hbn.
  assert (HM0 : 0 <= A0 * B1 + A1 * B0).
  { assert (0 <= A0 * B1) by (apply Z.mul_nonneg_nonneg; lia). assert (0 <= A1 * B0) by (apply Z.mul_nonneg_nonneg; lia). lia. }
  assert (Etgt : A0 * B0 + Bp n2 * (A1 * B1) + Bp n * (A0 * B1 + A1 * B0) = (A0 + Bp n * A1) * (B0 + Bp n * B1))
    by (rewrite EB; ring).
  assert (Hfit : A0 * B0 + Bp n2 * (A1 * B1) + Bp n * (A0 * B1 + A1 * B0) < Bp (2 * n2)).
  { rewrite Etgt, EB2, EB.
    assert (HA : 0 <= A0 + Bp n * A1 < Bp n * Bp n) by nia.
    assert (HB : 0 <= B0 + Bp n * B1 < Bp n * Bp n) by nia.
    apply (mul_bound_lt _ _ _ _ HA HB). }
  specialize (H HM0 Hfit). destruct (kara_combine n neg r t) as [r' t'].
  destruct H as (H1 & H2 & H3 & H4 & H5). rewrite Etgt in H3. repeat split; assumption.
Qed.

Lemma mul_comba8_spec : forall a b, limbs a -> limbs b -> length a = 8%nat -> length b = 8%nat ->
  limbs (mul_comba8 a b) /\ length (mul_comba8 a b) = 16%nat /\ lval (mul_comba8 a b) = lval a * lval b.
Proof.
  intros a b Ha Hb Hla Hlb. unfold mul_comba8. split; [apply to_limbs_limbs|]. split; [apply to_limbs_length|].
  apply lval_to_limbs_small. pose proof (lval_bound a Ha) as H1. pose proof (lval_bound b Hb) as H2.
  rewrite Hla in H1. rewrite Hlb in H2. replace 16%nat with (8 + 8)%nat by reflexivity. rewrite Bp_add.
  split; [apply Z.mul_nonneg_nonneg; lia|]. apply mul_bound_lt; assumption.
Qed.

Lemma slice_splice_same' : forall l off seg m, length seg = m -> (off + m <= length l)%nat ->
  slice (splice l off seg) off m = seg.
Proof. intros l off seg m H1 H2. subst m. apply slice_splice_same. exact H2. Qed.

Lemma splice_all : forall l seg, length seg = length l -> splice l 0 seg = seg.
Proof.
  intros l seg H. unfold splice. cbn [firstn app Nat.add]. rewrite skipn_all2 by lia. apply app_nil_r.
Qed.

Lemma mul_normal_fill : forall a b r n2 da db, limbs a -> limbs b -> limbs r ->
  (1 <= length a)%nat -> (1 <= length b)%nat ->
  length a = (n2 - da)%nat -> length b = (n2 - db)%nat -> (da <= n2)%nat -> (db <= n2)%nat -> length r = (2 * n2)%nat ->
  let r1 := splice r 0 (mul_normal a b) in
  let r2 := if (0 <? da + db)%nat then splice r1 (2 * n2 - da - db) (repeat 0 (da + db)) else r1 in
  limbs r2 /\ length r2 = length r /\ lval r2 = lval a * lval b.
Proof.
  intros a b r n2 da db Ha Hb Hr Hla1 Hlb1 Hla Hlb Hda Hdb Hrl. cbv zeta.
  destruct (mul_normal_spec a b Ha Hb) as (Hm & Hmv & Hml).
  assert (Hml' : length (mul_normal a b) = (2 * n2 - da - db)%nat).
  { rewrite Hml. destruct (Nat.eqb_spec (length a) 0); [lia|]. destruct (Nat.eqb_spec (length b) 0); [lia|]. cbn [orb]. lia. }
  set (P := mul_normal a b) in *.
  assert (Hr1l : length (splice r 0 P) = length r) by (apply splice_length; lia).
  assert (Hr1 : limbs (splice r 0 P)) by (apply splice_limbs; assumption).
  destruct (Nat.ltb_spec 0 (da + db)) as [Hpos|Hz].
  - assert (E : splice (splice r 0 P) (2 * n2 - da - db) (repeat 0 (da + db)) = P ++ repeat 0 (da + db)).
    { apply list_eq_nth.
      - rewrite splice_length by (rewrite repeat_length; lia). rewrite length_app, repeat_length. lia.
      - intros i Hi. rewrite nth_splice by (rewrite repeat_length; lia). rewrite repeat_length.
        destruct (Nat.leb_spec (2 * n2 - da - db) i) as [H1|H1]; cbn [andb].
        + destruct (Nat.ltb_spec i (2 * n2 - da - db + (da + db))) as [H2|H2].
          * rewrite app_nth2 by lia. f_equal. lia.
          * rewrite splice_length in Hi by (rewrite repeat_length; lia). lia.
        + rewrite app_nth1 by lia. rewrite nth_splice by lia.
          destruct (Nat.leb_spec 0 i); [|lia]. destruct (Nat.ltb_spec i (0 + length P)); [|lia].
          cbn [andb]. f_equal. lia. }
    rewrite E. split; [apply limbs_app; [exact Hm|apply limbs_repeat; exact limb_0]|].
    split; [rewrite length_app, repeat_length; lia|]. rewrite lval_app, lval_repeat0. lia.
  - assert (E : splice r 0 P = P) by (apply splice_all; lia). rewrite E. repeat split; [exact Hm|lia|exact Hmv].
Qed.

Lemma pow2_pos : forall k, (1 <= Nat.pow 2 k)%nat.
Proof. induction k as [|k IH]; cbn [Nat.pow]; lia. Qed.

Lemma scratch_rec_S : forall k, (16 <= Nat.pow 2 (S k))%nat -> scratch_rec (S k) = (2 * Nat.pow 2 (S k) + scratch_rec k)%nat.
Proof.
  intros k H. cbn [scratch_rec]. destruct (Nat.ltb_spec (Nat.pow 2 (S k)) 16); [lia|reflexivity].
Qed.

Definition mul_post (a b r t : list Z) (res : list Z * list Z) : Prop :=
  let '(r', t') := res in
  limbs r' /\ length r' = length r /\ lval r' = lval a * lval b /\ limbs t' /\ length t' = length t.

Theorem mul_recursive_spec : forall k a b da db r t,
  limbs a -> limbs b -> limbs r -> limbs t -> (1 <= k)%nat -> (da <= 1)%nat -> (db <= 1)%nat ->
  length a = (Nat.pow 2 k - da)%nat -> length b = (Nat.pow 2 k - db)%nat -> length r = (2 * Nat.pow 2 k)%nat ->
  (scratch_rec k <= length t)%nat ->
  mul_post a b r t (mul_recursive k a b da db r t).
Proof.
  induction k as [|k' IH]; intros a b da db r t Ha Hb Hr Ht Hk Hda Hdb Hla Hlb Hrl Hsc; [lia|].
  pose proof (pow2_pos k') as Hp. assert (Epow : Nat.pow 2 (S k') = (2 * Nat.pow 2 k')%nat) by (cbn [Nat.pow]; lia).
  cbn [mul_recursive]. set (n2 := Nat.pow 2 (S k')) in *. set (n := Nat.pow 2 k') in *.
  destruct ((n2 =? 8) && (da =? 0) && (db =? 0))%nat eqn:Ecomba.
  -
    apply andb_prop in Ecomba. destruct Ecomba as [E1 E3]. apply andb_prop in E1. destruct E1 as [E1 E2].
    apply Nat.eqb_eq in E1, E2, E3. subst da db. rewrite Nat.sub_0_r in Hla, Hlb. rewrite E1 in *.
    rewrite !firstn_all2 by lia.
    destruct (mul_comba8_spec a b Ha Hb Hla Hlb) as (H1 & H2 & H3).
    rewrite splice_all by lia. unfold mul_post. repeat split; try assumption; lia.
  - destruct (Nat.ltb_spec n2 16) as [Hsmall|Hbig].
    +
      rewrite !firstn_all2 by lia.
      pose proof (mul_normal_fill a b r n2 da db Ha Hb Hr ltac:(lia) ltac:(lia) Hla Hlb ltac:(lia) ltac:(lia) Hrl) as H.
      cbv zeta in H. destruct H as (H1 & H2 & H3). unfold mul_post. repeat split; assumption.
    +
      assert (Hn8 : (8 <= n)%nat) by lia. assert (Hk' : (1 <= k')%nat).
      { destruct k' as [|k'']; [cbn in n; lia|lia]. }
      rewrite scratch_rec_S in Hsc by (fold n2; lia). fold n2 in Hsc.
      set (tna := (n - da)%nat). set (tnb := (n - db)%nat).
      set (a_lo := firstn n a). set (a_hi := slice a n tna). set (b_lo := firstn n b). set (b_hi := slice b n tnb).
      assert (Hall : length a_lo = n) by (subst a_lo; apply firstn_length_le; lia).
      assert (Hbll : length b_lo = n) by (subst b_lo; apply firstn_length_le; lia).
      assert (Hahl : length a_hi = tna) by (subst a_hi; apply slice_length; lia).
      assert (Hbhl : length b_hi = tnb) by (subst b_hi; apply slice_length; lia).
      assert (Hal : limbs a_lo) by (subst a_lo; apply limbs_firstn; exact Ha).
      assert (Hbl : limbs b_lo) by (subst b_lo; apply limbs_firstn; exact Hb).
      assert (Hah : limbs a_hi) by (subst a_hi; apply slice_limbs; exact Ha).
      assert (Hbh : limbs b_hi) by (subst b_hi; apply slice_limbs; exact Hb).
      assert (Eav : lval a = lval a_lo + Bp n * lval a_hi).
      { rewrite (lval_split_le n a) by lia. subst a_lo a_hi. unfold slice. rewrite (firstn_all2 (n:=tna)) by (rewrite length_skipn; lia). reflexivity. }
      assert (Ebv : lval b = lval b_lo + Bp n * lval b_hi).
      { rewrite (lval_split_le n b) by lia. subst b_lo b_hi. unfold slice. rewrite (firstn_all2 (n:=tnb)) by (rewrite length_skipn; lia). reflexivity. }
      pose proof (lval_bound a_lo Hal) as HA0. rewrite Hall in HA0.
      pose proof (lval_bound b_lo Hbl) as HB0. rewrite Hbll in HB0.
      assert (HA1 : 0 <= lval a_hi < Bp n).
      { pose proof (lval_bound a_hi Hah) as Hx. rewrite Hahl in Hx. pose proof (Bp_mono tna n ltac:(lia)). lia. }
      assert (HB1 : 0 <= lval b_hi < Bp n).
      { pose proof (lval_bound b_hi Hbh) as Hx. rewrite Hbhl in Hx. pose proof (Bp_mono tnb n ltac:(lia)). lia. }
      pose proof (rec_diffs_spec a_lo a_hi b_lo b_hi n tna tnb Hal Hah Hbl Hbh Hall Hahl Hbll Hbhl ltac:(lia) ltac:(lia)) as Hdf.
      set (dif := rec_diffs a_lo a_hi b_lo b_hi tna tnb _ _) in *.

      set (td := match dif with Some (t0, t1, _) => splice (splice t 0 t0) n t1 | None => t end).
      set (neg := match dif with Some (_, _, ng) => ng | None => false end).
      set (zero := match dif with Some _ => false | None => true end).
      assert (Htd : limbs td /\ length td = length t /\
                    (if zero then (lval a_lo - lval a_hi) * (lval b_hi - lval b_lo) = 0
                     else limbs (slice td 0 n) /\ limbs (slice td n n) /\
                          (if neg then - (lval (slice td 0 n) * lval (slice td n n))
                           else lval (slice td 0 n) * lval (slice td n n)) = (lval a_lo - lval a_hi) * (lval b_hi - lval b_lo))).
      { subst td neg zero. destruct dif as [[[t0 t1] ng]|].
        - destruct Hdf as (D1 & D2 & D3 & D4 & D5).
          assert (L1 : length (splice t 0 t0) = length t) by (apply splice_length; lia).
          split; [apply splice_limbs; [apply splice_limbs|]; assumption|].
          split; [rewrite splice_length; lia|].
          assert (E0 : slice (splice (splice t 0 t0) n t1) 0 n = t0).
          { rewrite slice_splice_below by lia. apply slice_splice_same'; lia. }
          assert (E1 : slice (splice (splice t 0 t0) n t1) n n = t1).
          { apply slice_splice_same'; lia. }
          rewrite E0, E1. repeat split; assumption.
        - repeat split; assumption. }
      destruct Htd as (Htdl & Htdlen & Htdv).

      assert (Hmid : let '(r1, t1) :=
                (if ((n =? 8) && (da =? 0) && (db =? 0))%nat
                 then (splice (splice r 0 (mul_comba8 a_lo b_lo)) n2 (mul_comba8 a_hi b_hi),
                       splice td n2 (if zero then repeat 0 16%nat else mul_comba8 (slice td 0 8) (slice td 8 8)))
                 else let p := skipn (2 * n2) td in
                      let '(tm, p0) := if zero then (repeat 0 n2, p)
                                       else mul_recursive k' (slice td 0 n) (slice td n n) 0 0 (slice td n2 n2) p in
                      let '(rl, p1) := mul_recursive k' a_lo b_lo 0 0 (slice r 0 n2) p0 in
                      let '(rh, p2) := mul_recursive k' a_hi b_hi da db (slice r n2 n2) p1 in
                      (rl ++ rh, firstn n2 td ++ tm ++ p2)) in
              limbs r1 /\ length r1 = (2 * n2)%nat /\ limbs t1 /\ length t1 = length t /\
              lval (slice r1 0 n2) = lval a_lo * lval b_lo /\ lval (slice r1 n2 n2) = lval a_hi * lval b_hi /\
              (if neg then - lval (slice t1 n2 n2) else lval (slice t1 n2 n2)) = (lval a_lo - lval a_hi) * (lval b_hi - lval b_lo)).
      { destruct ((n =? 8) && (da =? 0) && (db =? 0))%nat eqn:Ec8.
        - apply andb_prop in Ec8. destruct Ec8 as [E1 E3]. apply andb_prop in E1. destruct E1 as [E1 E2].
          apply Nat.eqb_eq in E1, E2, E3. subst da db. subst tna tnb. rewrite Nat.sub_0_r in *.
          assert (En2 : n2 = 16%nat) by lia.
          destruct (mul_comba8_spec a_lo b_lo Hal Hbl ltac:(lia) ltac:(lia)) as (C1 & C2 & C3).
          destruct (mul_comba8_spec a_hi b_hi Hah Hbh ltac:(lia) ltac:(lia)) as (C4 & C5 & C6).
          set (tm := if zero then repeat 0 16%nat else mul_comba8 (slice td 0 8) (slice td 8 8)).
          assert (Htm : limbs tm /\ length tm = 16%nat /\
                        (if neg then - lval tm else lval tm) = (lval a_lo - lval a_hi) * (lval b_hi - lval b_lo)).
          { subst tm. destruct zero.
            - split; [apply limbs_repeat; exact limb_0|]. split; [apply repeat_length|].
              rewrite lval_repeat0, Htdv. destruct neg; reflexivity.
            - destruct Htdv as (T1 & T2 & T3). rewrite E1 in T1, T2, T3.
              destruct (mul_comba8_spec (slice td 0 8) (slice td 8 8) T1 T2
                          ltac:(apply slice_length; lia) ltac:(apply slice_length; lia)) as (C7 & C8 & C9).
              split; [exact C7|]. split; [exact C8|]. rewrite C9. exact T3. }
          destruct Htm as (M1 & M2 & M3).
          assert (L1 : length (splice r 0 (mul_comba8 a_lo b_lo)) = length r) by (apply splice_length; lia).
          split; [apply splice_limbs; [apply splice_limbs|]; assumption|].
          split; [rewrite splice_length; lia|].
          split; [apply splice_limbs; assumption|]. split; [rewrite splice_length; lia|].
          split; [|split].
          + rewrite slice_splice_below by lia. rewrite (slice_splice_same' r 0 _ n2) by lia. exact C3.
          + rewrite (slice_splice_same' _ n2 _ n2) by lia. exact C6.
          + rewrite (slice_splice_same' td n2 tm n2) by lia. exact M3.
        - cbv zeta.
          set (p := skipn (2 * n2) td).
          assert (Hp0 : limbs p /\ (scratch_rec k' <= length p)%nat /\ length p = (length t - 2 * n2)%nat).
          { subst p. split; [apply limbs_skipn; exact Htdl|]. rewrite length_skipn. lia. }
          destruct Hp0 as (Hpl & Hpsc & Hplen).

          assert (Hm : let '(tm, p0) := if zero then (repeat 0 n2, p)
                                        else mul_recursive k' (slice td 0 n) (slice td n n) 0 0 (slice td n2 n2) p in
                       limbs tm /\ length tm = n2 /\ limbs p0 /\ length p0 = length p /\
                       (if neg then - lval tm else lval tm) = (lval a_lo - lval a_hi) * (lval b_hi - lval b_lo)).
          { destruct zero.
            - split; [apply limbs_repeat; exact limb_0|]. split; [apply repeat_length|]. split; [exact Hpl|]. split; [reflexivity|].
              rewrite lval_repeat0, Htdv. destruct neg; reflexivity.
            - destruct Htdv as (T1 & T2 & T3).
              pose proof (IH (slice td 0 n) (slice td n n) 0%nat 0%nat (slice td n2 n2) p T1 T2 (slice_limbs _ _ _ Htdl) Hpl
                            Hk' ltac:(lia) ltac:(lia)
                            ltac:(rewrite slice_length by lia; fold n; lia) ltac:(rewrite slice_length by lia; fold n; lia)
                            ltac:(rewrite slice_length by lia; fold n; lia) Hpsc) as Hx.
              destruct (mul_recursive k' (slice td 0 n) (slice td n n) 0 0 (slice td n2 n2) p) as [tm p0].
              destruct Hx as (X1 & X2 & X3 & X4 & X5). rewrite slice_length in X2 by lia.
              repeat split; try assumption. rewrite X3. exact T3. }
          destruct (if zero then (repeat 0 n2, p)
                    else mul_recursive k' (slice td 0 n) (slice td n n) 0 0 (slice td n2 n2) p) as [tm p0].
          destruct Hm as (M1 & M2 & M3 & M4 & M5).
          pose proof (IH a_lo b_lo 0%nat 0%nat (slice r 0 n2) p0 Hal Hbl (slice_limbs _ _ _ Hr) M3 Hk' ltac:(lia) ltac:(lia)
                        ltac:(fold n; lia) ltac:(fold n; lia) ltac:(rewrite slice_length by lia; fold n; lia) ltac:(lia)) as Hx.
          destruct (mul_recursive k' a_lo b_lo 0 0 (slice r 0 n2) p0) as [rl p1].
          destruct Hx as (L1 & L2 & L3 & L4 & L5). rewrite slice_length in L2 by lia.
          pose proof (IH a_hi b_hi da db (slice r n2 n2) p1 Hah Hbh (slice_limbs _ _ _ Hr) L4 Hk' Hda Hdb
                        ltac:(fold n; lia) ltac:(fold n; lia) ltac:(rewrite slice_length by lia; fold n; lia) ltac:(lia)) as Hx.
          destruct (mul_recursive k' a_hi b_hi da db (slice r n2 n2) p1) as [rh p2].
          destruct Hx as (H1 & H2 & H3 & H4 & H5). rewrite slice_length in H2 by lia.
          split; [apply limbs_app; assumption|]. split; [rewrite length_app; lia|].
          split; [apply limbs_app; [apply limbs_firstn; exact Htdl|apply limbs_app; assumption]|].
          split; [rewrite !length_app, firstn_length_le by lia; lia|].
          assert (S1 : slice (rl ++ rh) 0 n2 = rl).
          { unfold slice. cbn [skipn]. rewrite firstn_app, L2, Nat.sub_diag. cbn [firstn]. rewrite app_nil_r. apply firstn_all2. lia. }
          assert (S2 : slice (rl ++ rh) n2 n2 = rh).
          { unfold slice. rewrite skipn_app, L2, Nat.sub_diag, skipn_all2 by lia. cbn [skipn app]. apply firstn_all2. lia. }
          assert (S3 : slice (firstn n2 td ++ tm ++ p2) n2 n2 = tm).
          { unfold slice. rewrite skipn_app, firstn_length_le, Nat.sub_diag, skipn_all2 by (rewrite ?firstn_length_le; lia).
            cbn [skipn app]. rewrite firstn_app, M2, Nat.sub_diag. cbn [firstn]. rewrite app_nil_r. apply firstn_all2. lia. }
          rewrite S1, S2, S3. repeat split; assumption. }
      destruct (if ((n =? 8) && (da =? 0) && (db =? 0))%nat
                then (splice (splice r 0 (mul_comba8 a_lo b_lo)) n2 (mul_comba8 a_hi b_hi),
                      splice td n2 (if zero then repeat 0 16%nat else mul_comba8 (slice td 0 8) (slice td 8 8)))
                else let p := skipn (2 * n2) td in
                     let '(tm, p0) := if zero then (repeat 0 n2, p)
                                      else mul_recursive k' (slice td 0 n) (slice td n n) 0 0 (slice td n2 n2) p in
                     let '(rl, p1) := mul_recursive k' a_lo b_lo 0 0 (slice r 0 n2) p0 in
                     let '(rh, p2) := mul_recursive k' a_hi b_hi da db (slice r n2 n2) p1 in
                     (rl ++ rh, firstn n2 td ++ tm ++ p2)) as [r1 t1].
      destruct Hmid as (R1 & R2 & T1 & T2 & V1 & V2 & V3).
      assert (En2 : n2 = (2 * n)%nat) by lia.
      pose proof (kara_finish n neg r1 t1 (lval a_lo) (lval a_hi) (lval b_lo) (lval b_hi)) as Hf. cbv zeta in Hf.
      rewrite <- En2 in Hf. specialize (Hf R1 R2 T1 ltac:(lia) V1 V2 V3 HA0 HA1 HB0 HB1).
      destruct (kara_combine n neg r1 t1) as [r' t']. destruct Hf as (F1 & F2 & F3 & F4 & F5).
      unfold mul_post. rewrite Eav, Ebv. repeat split; try assumption; lia.
Qed.

Lemma scratch_rec_le : forall k, (scratch_rec k <= 4 * Nat.pow 2 k)%nat.
Proof.
  induction k as [|k IH]; [cbn; lia|]. cbn [scratch_rec].
  destruct (Nat.ltb_spec (Nat.pow 2 (S k)) 16); [lia|]. cbn [Nat.pow] in *. lia.
Qed.

Lemma kara_find_spec : forall ki tna tnb,
  (1 <= Nat.max tna tnb)%nat -> (Nat.max tna tnb < 2 * Nat.pow 2 ki)%nat ->
  let '(kf, part) := kara_find ki tna tnb in
  let i := Nat.pow 2 kf in
  (kf <= ki)%nat /\ (i <= Nat.max tna tnb < 2 * i)%nat /\
  (if part then (i < tna \/ i < tnb)%nat else (tna <= i /\ tnb <= i /\ (i = tna \/ i = tnb))%nat).
Proof.
  induction ki as [|ki IH]; intros tna tnb H1 H2; cbn [kara_find].
  - cbn [Nat.pow] in *.
    destruct ((1 <? tna) || (1 <? tnb))%nat eqn:E1.
    + apply orb_prop in E1. cbn [Nat.pow]. destruct E1 as [E|E]; apply Nat.ltb_lt in E; lia.
    + apply orb_false_elim in E1. destruct E1 as [Ea Eb]. apply Nat.ltb_ge in Ea, Eb.
      destruct ((1 =? tna) || (1 =? tnb))%nat eqn:E2.
      * apply orb_prop in E2. cbn [Nat.pow]. destruct E2 as [E|E]; apply Nat.eqb_eq in E; lia.
      * apply orb_false_elim in E2. destruct E2 as [Ec Ed]. apply Nat.eqb_neq in Ec, Ed. lia.
  - set (i := Nat.pow 2 (S ki)) in *. assert (Ei : i = (2 * Nat.pow 2 ki)%nat) by (subst i; cbn [Nat.pow]; lia).
    destruct ((i <? tna) || (i <? tnb))%nat eqn:E1.
    + apply orb_prop in E1. fold i. destruct E1 as [E|E]; apply Nat.ltb_lt in E; lia.
    + apply orb_false_elim in E1. destruct E1 as [Ea Eb]. apply Nat.ltb_ge in Ea, Eb.
      destruct ((i =? tna) || (i =? tnb))%nat eqn:E2.
      * apply orb_prop in E2. fold i. destruct E2 as [E|E]; apply Nat.eqb_eq in E; lia.
      * apply orb_false_elim in E2. destruct E2 as [Ec Ed]. apply Nat.eqb_neq in Ec, Ed.
        specialize (IH tna tnb H1 ltac:(lia)). destruct (kara_find ki tna tnb) as [kf part].
        cbv zeta in *. destruct IH as (I1 & I2 & I3). split; [lia|]. split; assumption.
Qed.

Lemma zero_fill_small : forall l m, limbs l -> (m <= length l)%nat -> lval l < Bp m ->
  let l' := splice l m (repeat 0 (length l - m)) in
  limbs l' /\ length l' = length l /\ lval l' = lval l.
Proof.
  intros l m Hl Hm Hv. cbv zeta.
  split; [apply splice_limbs; [exact Hl|apply limbs_repeat; exact limb_0]|].
  split; [apply splice_length; rewrite repeat_length; lia|].
  rewrite lval_splice by (rewrite repeat_length; lia). rewrite lval_repeat0, repeat_length.
  pose proof (lval_split_le m l Hm) as E. unfold slice. rewrite (firstn_all2 (n:=length l - m)) by (rewrite length_skipn; lia).
  pose proof (lval_nonneg _ (limbs_firstn m l Hl)). pose proof (lval_nonneg _ (limbs_skipn m l Hl)) as Hs.
  pose proof (Bp_pos m). assert (lval (skipn m l) = 0) by nia. nia.
Qed.

Lemma mul_normal_into_zeros : forall a b m, limbs a -> limbs b -> (length a + length b <= m)%nat ->
  let l' := splice (repeat 0 m) 0 (mul_normal a b) in
  limbs l' /\ length l' = m /\ lval l' = lval a * lval b.
Proof.
  intros a b m Ha Hb Hm. cbv zeta. destruct (mul_normal_spec a b Ha Hb) as (H1 & H2 & H3).
  assert (Hl : (length (mul_normal a b) <= m)%nat).
  { rewrite H3. destruct ((length a =? 0) || (length b =? 0))%nat; lia. }
  split; [apply splice_limbs; [apply limbs_repeat; exact limb_0|exact H1]|].
  split; [rewrite splice_length; rewrite repeat_length; lia|].
  rewrite lval_splice by (rewrite repeat_length; lia). rewrite lval_repeat0. cbn [Nat.add].
  assert (E : slice (repeat 0 m) 0 (length (mul_normal a b)) = repeat 0 (length (mul_normal a b))).
  { apply list_eq_nth; [rewrite slice_length, repeat_length; rewrite ?repeat_length; lia|].
    intros i Hi. rewrite slice_length in Hi by (rewrite repeat_length; lia). rewrite nth_slice by lia.
    rewrite !nth_repeat. reflexivity. }
  rewrite E, lval_repeat0, Bp_0, H2. ring.
Qed.

Lemma slice_two_splices : forall X off P Z m, length P = m -> (off + m + length Z <= length X)%nat ->
  slice (splice (splice X off P) (off + m) Z) off (m + length Z) = P ++ Z.
Proof.
  intros X off P Z m HP HX.
  assert (L1 : length (splice X off P) = length X) by (apply splice_length; lia).
  apply list_eq_nth.
  - rewrite slice_length by (rewrite splice_length; lia). rewrite length_app. lia.
  - intros i Hi. rewrite slice_length in Hi by (rewrite splice_length; lia).
    rewrite nth_slice by lia. rewrite nth_splice by lia.
    destruct (Nat.leb_spec (off + m) (off + i)) as [H1|H1]; cbn [andb].
    + destruct (Nat.ltb_spec (off + i) (off + m + length Z)); [|lia].
      rewrite app_nth2 by lia. f_equal. lia.
    + rewrite nth_splice by lia. destruct (Nat.leb_spec off (off + i)); [|lia].
      destruct (Nat.ltb_spec (off + i) (off + length P)); [|lia]. cbn [andb].
      rewrite app_nth1 by lia. f_equal. lia.
Qed.

Lemma two_splices_all : forall X P Z m, length P = m -> (m + length Z = length X)%nat ->
  splice (splice X 0 P) m Z = P ++ Z.
Proof.
  intros X P Z m HP HX.
  pose proof (slice_two_splices X 0 P Z m HP ltac:(lia)) as H. cbn [Nat.add] in H.
  rewrite <- H. symmetry.
  replace (m + length Z)%nat with (length (splice (splice X 0 P) m Z)) by (rewrite !splice_length; rewrite ?splice_length; lia).
  apply slice_full.
Qed.

Theorem mul_part_recursive_spec : forall fuel k a b tna tnb r t,
  limbs a -> limbs b -> limbs r -> limbs t ->
  (3 <= k)%nat -> (k <= fuel)%nat ->
  (tna < Nat.pow 2 k)%nat -> (tnb < Nat.pow 2 k)%nat -> (tna <= tnb + 1)%nat -> (tnb <= tna + 1)%nat ->
  length a = (Nat.pow 2 k + tna)%nat -> length b = (Nat.pow 2 k + tnb)%nat ->
  length r = (4 * Nat.pow 2 k)%nat -> (8 * Nat.pow 2 k <= length t)%nat ->
  mul_post a b r t (mul_part_recursive fuel k a b tna tnb r t).
Proof.
  induction fuel as [|fuel' IH]; intros k a b tna tnb r t Ha Hb Hr Ht Hk3 Hkf Htna Htnb Hd1 Hd2 Hla Hlb Hrl Htl; [lia|].
  cbn [mul_part_recursive]. set (n := Nat.pow 2 k) in *. set (n2 := (2 * n)%nat) in *.
  assert (Hn8 : (8 <= n)%nat).
  { subst n. replace k with (3 + (k - 3))%nat by lia. rewrite Nat.pow_add_r. pose proof (pow2_pos (k - 3)). cbn [Nat.pow] in *. lia. }
  destruct (Nat.ltb_spec n 8) as [|_]; [lia|].
  set (a_lo := firstn n a). set (a_hi := slice a n tna). set (b_lo := firstn n b). set (b_hi := slice b n tnb).
  assert (Hall : length a_lo = n) by (subst a_lo; apply firstn_length_le; lia).
  assert (Hbll : length b_lo = n) by (subst b_lo; apply firstn_length_le; lia).
  assert (Hahl : length a_hi = tna) by (subst a_hi; apply slice_length; lia).
  assert (Hbhl : length b_hi = tnb) by (subst b_hi; apply slice_length; lia).
  assert (Hal : limbs a_lo) by (subst a_lo; apply limbs_firstn; exact Ha).
  assert (Hbl : limbs b_lo) by (subst b_lo; apply limbs_firstn; exact Hb).
  assert (Hah : limbs a_hi) by (subst a_hi; apply slice_limbs; exact Ha).
  assert (Hbh : limbs b_hi) by (subst b_hi; apply slice_limbs; exact Hb).
  assert (Eav : lval a = lval a_lo + Bp n * lval a_hi).
  { rewrite (lval_split_le n a) by lia. subst a_lo a_hi. unfold slice. rewrite (firstn_all2 (n:=tna)) by (rewrite length_skipn; lia). reflexivity. }
  assert (Ebv : lval b = lval b_lo + Bp n * lval b_hi).
  { rewrite (lval_split_le n b) by lia. subst b_lo b_hi. unfold slice. rewrite (firstn_all2 (n:=tnb)) by (rewrite length_skipn; lia). reflexivity. }
  pose proof (lval_bound a_lo Hal) as HA0. rewrite Hall in HA0.
  pose proof (lval_bound b_lo Hbl) as HB0. rewrite Hbll in HB0.
  pose proof (lval_bound a_hi Hah) as HA1'. rewrite Hahl in HA1'.
  pose proof (lval_bound b_hi Hbh) as HB1'. rewrite Hbhl in HB1'.
  assert (HA1 : 0 <= lval a_hi < Bp n) by (pose proof (Bp_mono tna n ltac:(lia)); lia).
  assert (HB1 : 0 <= lval b_hi < Bp n) by (pose proof (Bp_mono tnb n ltac:(lia)); lia).
  assert (Hhib : lval a_hi * lval b_hi < Bp (tna + tnb)) by (rewrite Bp_add; apply mul_bound_lt; assumption).
  pose proof (part_diffs_spec a_lo a_hi b_lo b_hi n tna tnb Hal Hah Hbl Hbh Hall Hahl Hbll Hbhl ltac:(lia) ltac:(lia)) as Hdf.
  destruct (part_diffs a_lo a_hi b_lo b_hi tna tnb _ _) as [[t0 t1] neg].
  destruct Hdf as (D1 & D2 & D3 & D4 & D5).
  set (td := splice (splice t 0 t0) n t1).
  assert (Ltd0 : length (splice t 0 t0) = length t) by (apply splice_length; lia).
  assert (Htdl : limbs td) by (subst td; apply splice_limbs; [apply splice_limbs|]; assumption).
  assert (Htdlen : length td = length t) by (subst td; rewrite splice_length; lia).
  assert (E0 : slice td 0 n = t0) by (subst td; rewrite slice_splice_below by lia; apply slice_splice_same'; lia).
  assert (E1 : slice td n n = t1) by (subst td; apply slice_splice_same'; lia).
  assert (Hmid : let '(r1, t1') :=
            (if (n =? 8)%nat
             then (splice (splice (splice r 0 (mul_comba8 a_lo b_lo)) n2 (mul_normal a_hi b_hi)) (n2 + tna + tnb) (repeat 0 (n2 - tna - tnb)),
                   splice td n2 (mul_comba8 (slice td 0 8) (slice td 8 8)))
             else let k' := (k - 1)%nat in
                  let p := skipn (2 * n2) td in
                  let '(tm, p0) := mul_recursive k (slice td 0 n) (slice td n n) 0 0 (slice td n2 n2) p in
                  let '(rl, p1) := mul_recursive k a_lo b_lo 0 0 (slice r 0 n2) p0 in
                  let i := Nat.pow 2 k' in
                  let mx := Nat.max tna tnb in
                  let rh := slice r n2 n2 in
                  let '(rh0, p2) :=
                    if (mx =? i)%nat
                    then let '(o, p2) := mul_recursive k' a_hi b_hi (i - tna) (i - tnb) (slice rh 0 (2 * i)) p1 in
                         (splice (splice rh 0 o) (2 * i) (repeat 0 (n2 - 2 * i)), p2)
                    else if (i <? mx)%nat
                         then let '(o, p2) := mul_part_recursive fuel' k' a_hi b_hi (tna - i) (tnb - i) (slice rh 0 (4 * i)) p1 in
                              (splice (splice rh 0 o) (tna + tnb) (repeat 0 (n2 - tna - tnb)), p2)
                         else let rh1 := repeat 0 n2 in
                              if ((tna <? 16) && (tnb <? 16))%nat then (splice rh1 0 (mul_normal a_hi b_hi), p1)
                              else let '(ki, part) := kara_find (k' - 1) tna tnb in
                                   let i0 := Nat.pow 2 ki in
                                   if part
                                   then let '(o, p2) := mul_part_recursive fuel' ki a_hi b_hi (tna - i0) (tnb - i0) (slice rh1 0 (4 * i0)) p1 in
                                        (splice rh1 0 o, p2)
                                   else let '(o, p2) := mul_recursive ki a_hi b_hi (i0 - tna) (i0 - tnb) (slice rh1 0 (2 * i0)) p1 in
                                        (splice rh1 0 o, p2) in
                  (rl ++ rh0, firstn n2 td ++ tm ++ p2)) in
          limbs r1 /\ length r1 = (2 * n2)%nat /\ limbs t1' /\ length t1' = length t /\
          lval (slice r1 0 n2) = lval a_lo * lval b_lo /\ lval (slice r1 n2 n2) = lval a_hi * lval b_hi /\
          (if neg then - lval (slice t1' n2 n2) else lval (slice t1' n2 n2)) = (lval a_lo - lval a_hi) * (lval b_hi - lval b_lo)).
  { destruct (Nat.eqb_spec n 8) as [E8|N8].
    -
      assert (En2 : n2 = 16%nat) by lia.
      destruct (mul_comba8_spec a_lo b_lo Hal Hbl ltac:(lia) ltac:(lia)) as (C1 & C2 & C3).
      assert (T0 : limbs (slice td 0 8)) by (apply slice_limbs; exact Htdl).
      assert (T1 : limbs (slice td 8 8)) by (apply slice_limbs; exact Htdl).
      destruct (mul_comba8_spec (slice td 0 8) (slice td 8 8) T0 T1 ltac:(apply slice_length; lia) ltac:(apply slice_length; lia)) as (C7 & C8 & C9).
      destruct (mul_normal_spec a_hi b_hi Hah Hbh) as (N1 & N2 & N3).
      assert (N3' : length (mul_normal a_hi b_hi) = (tna + tnb)%nat).
      { rewrite N3, Hahl, Hbhl. destruct (Nat.eqb_spec tna 0); destruct (Nat.eqb_spec tnb 0); cbn [orb]; lia. }
      set (P := mul_normal a_hi b_hi) in *. set (Zs := repeat 0 (n2 - tna - tnb)).
      assert (LZ : length Zs = (n2 - tna - tnb)%nat) by (subst Zs; apply repeat_length).
      assert (L1 : length (splice r 0 (mul_comba8 a_lo b_lo)) = length r) by (apply splice_length; lia).
      assert (L2 : length (splice (splice r 0 (mul_comba8 a_lo b_lo)) n2 P) = length r) by (rewrite splice_length; lia).
      split; [apply splice_limbs; [apply splice_limbs; [apply splice_limbs|]|apply limbs_repeat; exact limb_0]; assumption|].
      split; [rewrite splice_length; lia|].
      split; [apply splice_limbs; assumption|]. split; [rewrite splice_length; lia|].
      split; [|split].
      + rewrite slice_splice_below by lia. rewrite slice_splice_below by lia.
        rewrite (slice_splice_same' r 0 _ n2) by lia. exact C3.
      + replace (n2 + tna + tnb)%nat with (n2 + (tna + tnb))%nat by lia.
        replace n2 with ((tna + tnb) + length Zs)%nat at 4 by lia.
        rewrite slice_two_splices by lia. rewrite lval_app. subst Zs. rewrite lval_repeat0. lia.
      + rewrite (slice_splice_same' td n2 _ n2) by lia. rewrite C9.
        rewrite E8 in E0, E1. rewrite E0, E1. exact D5.
    -
      cbv zeta. set (k' := (k - 1)%nat).
      assert (Hk4 : (4 <= k)%nat).
      { destruct (Nat.eq_dec k 3) as [->|]; [cbn in n; lia|lia]. }
      assert (Epow : n = (2 * Nat.pow 2 k')%nat).
      { subst n k'. replace k with (S (k - 1)) at 1 by lia. cbn [Nat.pow]. lia. }
      set (i := Nat.pow 2 k') in *.
      set (p := skipn (2 * n2) td).
      assert (Hpl : limbs p) by (subst p; apply limbs_skipn; exact Htdl).
      assert (Hplen : length p = (length t - 2 * n2)%nat) by (subst p; rewrite length_skipn; lia).
      pose proof (scratch_rec_le k) as Hsck. fold n in Hsck.

      pose proof (mul_recursive_spec k (slice td 0 n) (slice td n n) 0 0 (slice td n2 n2) p
                    ltac:(rewrite E0; exact D1) ltac:(rewrite E1; exact D3) (slice_limbs _ _ _ Htdl) Hpl ltac:(lia) ltac:(lia) ltac:(lia)
                    ltac:(rewrite slice_length by lia; fold n; lia) ltac:(rewrite slice_length by lia; fold n; lia)
                    ltac:(rewrite slice_length by lia; fold n; lia) ltac:(lia)) as Hx.
      destruct (mul_recursive k (slice td 0 n) (slice td n n) 0 0 (slice td n2 n2) p) as [tm p0].
      destruct Hx as (M1 & M2 & M3 & M4 & M5). rewrite slice_length in M2 by lia. rewrite E0, E1 in M3.
      pose proof (mul_recursive_spec k a_lo b_lo 0 0 (slice r 0 n2) p0 Hal Hbl (slice_limbs _ _ _ Hr) M4 ltac:(lia) ltac:(lia) ltac:(lia)
                    ltac:(fold n; lia) ltac:(fold n; lia) ltac:(rewrite slice_length by lia; fold n; lia) ltac:(lia)) as Hx.
      destruct (mul_recursive k a_lo b_lo 0 0 (slice r 0 n2) p0) as [rl p1].
      destruct Hx as (L1 & L2 & L3 & L4 & L5). rewrite slice_length in L2 by lia.

      set (rh := slice r n2 n2).
      assert (Hrh : limbs rh) by (subst rh; apply slice_limbs; exact Hr).
      assert (Hrhl : length rh = n2) by (subst rh; apply slice_length; lia).
      assert (Hhigh : let '(rh0, p2) :=
                    (if (Nat.max tna tnb =? i)%nat
                     then let '(o, p2) := mul_recursive k' a_hi b_hi (i - tna) (i - tnb) (slice rh 0 (2 * i)) p1 in
                          (splice (splice rh 0 o) (2 * i) (repeat 0 (n2 - 2 * i)), p2)
                     else if (i <? Nat.max tna tnb)%nat
                          then let '(o, p2) := mul_part_recursive fuel' k' a_hi b_hi (tna - i) (tnb - i) (slice rh 0 (4 * i)) p1 in
                               (splice (splice rh 0 o) (tna + tnb) (repeat 0 (n2 - tna - tnb)), p2)
                          else let rh1 := repeat 0 n2 in
                               if ((tna <? 16) && (tnb <? 16))%nat then (splice rh1 0 (mul_normal a_hi b_hi), p1)
                               else let '(ki, part) := kara_find (k' - 1) tna tnb in
                                    let i0 := Nat.pow 2 ki in
                                    if part
                                    then let '(o, p2) := mul_part_recursive fuel' ki a_hi b_hi (tna - i0) (tnb - i0) (slice rh1 0 (4 * i0)) p1 in
                                         (splice rh1 0 o, p2)
                                    else let '(o, p2) := mul_recursive ki a_hi b_hi (i0 - tna) (i0 - tnb) (slice rh1 0 (2 * i0)) p1 in
                                         (splice rh1 0 o, p2)) in
                  limbs rh0 /\ length rh0 = n2 /\ lval rh0 = lval a_hi * lval b_hi /\ limbs p2 /\ length p2 = length p).
      { destruct (Nat.eqb_spec (Nat.max tna tnb) i) as [Ej0|Nj0].
        -
          pose proof (scratch_rec_le k') as Hsck'. fold i in Hsck'.
          pose proof (mul_recursive_spec k' a_hi b_hi (i - tna) (i - tnb) (slice rh 0 (2 * i)) p1 Hah Hbh (slice_limbs _ _ _ Hrh) L4
                        ltac:(lia) ltac:(lia) ltac:(lia) ltac:(fold i; lia) ltac:(fold i; lia)
                        ltac:(rewrite slice_length by lia; fold i; lia) ltac:(lia)) as Hx.
          destruct (mul_recursive k' a_hi b_hi (i - tna) (i - tnb) (slice rh 0 (2 * i)) p1) as [o p2].
          destruct Hx as (O1 & O2 & O3 & O4 & O5). rewrite slice_length in O2 by lia.
          rewrite two_splices_all by (rewrite ?repeat_length; lia).
          split; [apply limbs_app; [exact O1|apply limbs_repeat; exact limb_0]|].
          split; [rewrite length_app, repeat_length; lia|].
          split; [rewrite lval_app, lval_repeat0; lia|]. split; [assumption|lia].
        - destruct (Nat.ltb_spec i (Nat.max tna tnb)) as [Hjpos|Hjneg].
          +
            assert (E4i : (4 * i = n2)%nat) by lia.
            pose proof (IH k' a_hi b_hi (tna - i)%nat (tnb - i)%nat (slice rh 0 (4 * i)) p1 Hah Hbh (slice_limbs _ _ _ Hrh) L4
                          ltac:(lia) ltac:(lia) ltac:(fold i; lia) ltac:(fold i; lia) ltac:(lia) ltac:(lia)
                          ltac:(fold i; lia) ltac:(fold i; lia) ltac:(rewrite slice_length by lia; fold i; lia) ltac:(fold i; lia)) as Hx.
            destruct (mul_part_recursive fuel' k' a_hi b_hi (tna - i) (tnb - i) (slice rh 0 (4 * i)) p1) as [o p2].
            destruct Hx as (O1 & O2 & O3 & O4 & O5). rewrite slice_length in O2 by lia.
            assert (Ho : splice rh 0 o = o) by (apply splice_all; lia). rewrite Ho.
            pose proof (zero_fill_small o (tna + tnb) O1 ltac:(lia) ltac:(rewrite O3; exact Hhib)) as Hz. cbv zeta in Hz.
            replace (length o - (tna + tnb))%nat with (n2 - tna - tnb)%nat in Hz by lia.
            destruct Hz as (Z1 & Z2 & Z3). repeat split; try assumption; lia.
          +
            destruct ((tna <? 16) && (tnb <? 16))%nat eqn:Esm.
            * pose proof (mul_normal_into_zeros a_hi b_hi n2 Hah Hbh ltac:(lia)) as Hz. cbv zeta in Hz.
              destruct Hz as (Z1 & Z2 & Z3). repeat split; try assumption; lia.
            * assert (Hmx16 : (16 <= Nat.max tna tnb)%nat).
              { apply andb_false_elim in Esm. destruct Esm as [E|E]; apply Nat.ltb_ge in E; lia. }
              assert (Hk'1 : (1 <= k')%nat) by lia.
              assert (Ei' : i = (2 * Nat.pow 2 (k' - 1))%nat).
              { subst i. replace k' with (S (k' - 1)) at 1 by lia. cbn [Nat.pow]. lia. }
              pose proof (kara_find_spec (k' - 1) tna tnb ltac:(lia) ltac:(lia)) as Hfind.
              destruct (kara_find (k' - 1) tna tnb) as [ki part]. cbv zeta in Hfind. destruct Hfind as (F1 & F2 & F3).
              set (i0 := Nat.pow 2 ki) in *.
              assert (Hki : (4 <= ki)%nat).
              { destruct (Nat.le_gt_cases 4 ki) as [|Hlt]; [assumption|exfalso].
                assert (i0 <= 8)%nat; [|lia]. subst i0.
                assert (ki = 0 \/ ki = 1 \/ ki = 2 \/ ki = 3)%nat as [->|[->|[->| ->]]] by lia; cbn; lia. }
              set (rh1 := repeat 0 n2).
              assert (Hrh1 : limbs rh1) by (subst rh1; apply limbs_repeat; exact limb_0).
              assert (Hrh1l : length rh1 = n2) by (subst rh1; apply repeat_length).
              assert (Hi0n : (4 * i0 <= n2)%nat) by lia.
              destruct part; cbv zeta; fold rh1 i0.
              -- pose proof (IH ki a_hi b_hi (tna - i0)%nat (tnb - i0)%nat (slice rh1 0 (4 * i0)) p1 Hah Hbh (slice_limbs _ _ _ Hrh1) L4
                               ltac:(lia) ltac:(lia) ltac:(fold i0; lia) ltac:(fold i0; lia) ltac:(lia) ltac:(lia)
                               ltac:(fold i0; lia) ltac:(fold i0; lia) ltac:(rewrite slice_length by lia; fold i0; lia) ltac:(fold i0; lia)) as Hx.
                 destruct (mul_part_recursive fuel' ki a_hi b_hi (tna - i0) (tnb - i0) (slice rh1 0 (4 * i0)) p1) as [o p2].
                 destruct Hx as (O1 & O2 & O3 & O4 & O5). rewrite slice_length in O2 by lia.
                 split; [apply splice_limbs; assumption|]. split; [rewrite splice_length; lia|].
                 split; [|split; [assumption|lia]].
                 rewrite lval_splice by lia. subst rh1.
                 assert (Esl : lval (slice (repeat 0 n2) 0 (length o)) = 0).
                 { assert (E : slice (repeat 0 n2) 0 (length o) = repeat 0 (length o)).
                   { apply list_eq_nth; [rewrite slice_length, repeat_length; rewrite ?repeat_length; lia|].
                     intros x Hx. rewrite slice_length in Hx by (rewrite repeat_length; lia). rewrite nth_slice by lia.
                     rewrite !nth_repeat. reflexivity. }
                   rewrite E. apply lval_repeat0. }
                 rewrite Esl, lval_repeat0, Bp_0, O3. ring.
              -- pose proof (scratch_rec_le ki) as Hscki. fold i0 in Hscki.
                 pose proof (mul_recursive_spec ki a_hi b_hi (i0 - tna) (i0 - tnb) (slice rh1 0 (2 * i0)) p1 Hah Hbh (slice_limbs _ _ _ Hrh1) L4
                               ltac:(lia) ltac:(lia) ltac:(lia) ltac:(fold i0; lia) ltac:(fold i0; lia)
                               ltac:(rewrite slice_length by lia; fold i0; lia) ltac:(lia)) as Hx.
                 destruct (mul_recursive ki a_hi b_hi (i0 - tna) (i0 - tnb) (slice rh1 0 (2 * i0)) p1) as [o p2].
                 destruct Hx as (O1 & O2 & O3 & O4 & O5). rewrite slice_length in O2 by lia.
                 split; [apply splice_limbs; assumption|]. split; [rewrite splice_length; lia|].
                 split; [|split; [assumption|lia]].
                 rewrite lval_splice by lia. subst rh1.
                 assert (Esl : lval (slice (repeat 0 n2) 0 (length o)) = 0).
                 { assert (E : slice (repeat 0 n2) 0 (length o) = repeat 0 (length o)).
                   { apply list_eq_nth; [rewrite slice_length, repeat_length; rewrite ?repeat_length; lia|].
                     intros x Hx. rewrite slice_length in Hx by (rewrite repeat_length; lia). rewrite nth_slice by lia.
                     rewrite !nth_repeat. reflexivity. }
                   rewrite E. apply lval_repeat0. }
                 rewrite Esl, lval_repeat0, Bp_0, O3. ring. }
      destruct (if (Nat.max tna tnb =? i)%nat then _ else _) as [rh0 p2].
      destruct Hhigh as (H1 & H2 & H3 & H4 & H5).
      split; [apply limbs_app; assumption|]. split; [rewrite length_app; lia|].
      split; [apply limbs_app; [apply limbs_firstn; exact Htdl|apply limbs_app; assumption]|].
      split; [rewrite !length_app, firstn_length_le by lia; lia|].
      assert (S1 : slice (rl ++ rh0) 0 n2 = rl).
      { unfold slice. cbn [skipn]. rewrite firstn_app, L2, Nat.sub_diag. cbn [firstn]. rewrite app_nil_r. apply firstn_all2. lia. }
      assert (S2 : slice (rl ++ rh0) n2 n2 = rh0).
      { unfold slice. rewrite skipn_app, L2, Nat.sub_diag, skipn_all2 by lia. cbn [skipn app]. apply firstn_all2. lia. }
      assert (S3 : slice (firstn n2 td ++ tm ++ p2) n2 n2 = tm).
      { unfold slice. rewrite skipn_app, firstn_length_le, Nat.sub_diag, skipn_all2 by (rewrite ?firstn_length_le; lia).
        cbn [skipn app]. rewrite firstn_app, M2, Nat.sub_diag. cbn [firstn]. rewrite app_nil_r. apply firstn_all2. lia. }
      rewrite S1, S2, S3. repeat split; try assumption. rewrite M3. exact D5. }
  destruct (if (n =? 8)%nat then _ else _) as [r1 t1'].
  destruct Hmid as (R1 & R2 & T1 & T2 & V1 & V2 & V3).
  pose proof (kara_finish n neg r1 t1' (lval a_lo) (lval a_hi) (lval b_lo) (lval b_hi)) as Hf. cbv zeta in Hf.
  fold n2 in Hf. specialize (Hf R1 R2 T1 ltac:(lia) V1 V2 V3 HA0 HA1 HB0 HB1).
  destruct (kara_combine n neg r1 t1') as [r' t']. destruct Hf as (F1 & F2 & F3 & F4 & F5).
  unfold mul_post. rewrite Eav, Ebv. repeat split; try assumption; lia.
Qed.
