(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnKara BnWordsCorrect BnKaraCorrect BgWords.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Fixpoint sqsum (a : list Z) : Z :=
  match a with
  | [] => 0
  | x :: l => x * x + BW * BW * sqsum l
  end.

Fixpoint cross_upto (a : list Z) (k : nat) : Z :=
  match k with
  | O => 0
  | S k' => cross_upto a k' + nth k' a 0 * lval (skipn (S k') a) * Bp (2 * k' + 1)
  end.

Lemma cross_upto_cons : forall x l k, cross_upto (x :: l) (S k) = x * lval l * BW + BW * BW * cross_upto l k.
Proof.
  intros x l. induction k as [|k IH].
  - cbn [cross_upto nth skipn Nat.mul Nat.add]. rewrite Bp_1. lia.
  - change (cross_upto (x :: l) (S (S k))) with
      (cross_upto (x :: l) (S k) + nth (S k) (x :: l) 0 * lval (skipn (S (S k)) (x :: l)) * Bp (2 * S k + 1)).
    rewrite IH. cbn [nth skipn cross_upto].
    replace (2 * S k + 1)%nat with (S (S (2 * k + 1))) by lia. rewrite !Bp_S. ring.
Qed.

Lemma sq_decomp : forall a, sqsum a + 2 * cross_upto a (length a) = lval a * lval a.
Proof.
  induction a as [|x l IH]; [reflexivity|]. cbn [length sqsum lval]. rewrite cross_upto_cons. nia.
Qed.

Lemma cross_upto_last : forall a n, length a = S n -> cross_upto a (S n) = cross_upto a n.
Proof.
  intros a n H. cbn [cross_upto]. rewrite skipn_all2 by lia. cbn [lval]. lia.
Qed.

Lemma cross_upto_nonneg : forall a k, limbs a -> 0 <= cross_upto a k.
Proof.
  intros a k Ha. induction k as [|k IH]; cbn [cross_upto]; [lia|].
  pose proof (limbs_nth a k Ha) as [H0 _]. pose proof (lval_nonneg _ (limbs_skipn (S k) a Ha)). pose proof (Bp_pos (2 * k + 1)).
  assert (0 <= nth k a 0 * lval (skipn (S k) a) * Bp (2 * k + 1)) by (apply Z.mul_nonneg_nonneg; [apply Z.mul_nonneg_nonneg|]; lia). lia.
Qed.

Lemma sqr_words_spec : forall a, limbs a ->
  limbs (sqr_words a) /\ length (sqr_words a) = (2 * length a)%nat /\ lval (sqr_words a) = sqsum a.
Proof.
  induction a as [|x l IH]; intros Ha.
  - cbn. repeat split. constructor.
  - apply limbs_cons_inv in Ha. destruct Ha as [[Hx0 Hx1] Hl]. destruct (IH Hl) as (I1 & I2 & I3).
    cbn [sqr_words length sqsum lval]. split; [|split].
    + constructor; [apply limb_mod|]. constructor; [|exact I1]. unfold limb. split; [apply Z.div_pos; [nia|unfold BW; lia]|].
      apply Z.div_lt_upper_bound; [unfold BW; lia|]. nia.
    + lia.
    + rewrite I3. pose proof (Z.div_mod (x * x) BW ltac:(unfold BW; lia)). nia.
Qed.

Lemma firstn_splice_end : forall (r : list Z) off seg, (off + length seg <= length r)%nat ->
  firstn (off + length seg) (splice r off seg) = firstn off r ++ seg.
Proof.
  intros r off seg H. unfold splice. rewrite firstn_app, firstn_length_le by lia.
  rewrite (firstn_all2 (firstn off r)) by (rewrite firstn_length_le; lia).
  replace (off + length seg - off)%nat with (length seg) by lia.
  rewrite firstn_app, Nat.sub_diag, firstn_all. cbn [firstn]. rewrite app_nil_r. reflexivity.
Qed.

Lemma window_write : forall r off seg, (off + length seg <= length r)%nat ->
  lval (firstn (off + length seg) (splice r off seg)) = lval (firstn off r) + Bp off * lval seg.
Proof.
  intros r off seg H. rewrite firstn_splice_end by exact H. rewrite lval_app, firstn_length_le by lia. reflexivity.
Qed.

Lemma nth_splice_above : forall (r : list Z) off seg i, (off + length seg <= i)%nat -> (off + length seg <= length r)%nat ->
  nth i (splice r off seg) 0 = nth i r 0.
Proof.
  intros r off seg i Hi Hl. rewrite nth_splice_other by lia. reflexivity.
Qed.

Section SqrNormal.
Variable a : list Z.
Hypothesis Ha : limbs a.
Let n := length a.

Definition sqn_inv (k : nat) (r : list Z) : Prop :=
  limbs r /\ length r = (2 * n)%nat /\ lval (firstn (n + k) r) = cross_upto a k /\ nth (2 * n - 1) r 0 = 0.

Lemma sqr_normal_loop_spec : forall cnt k r, (1 <= k)%nat -> (k + cnt = n - 1)%nat -> sqn_inv k r ->
  sqn_inv (n - 1) (sqr_normal_loop a cnt k r).
Proof.
  induction cnt as [|c IH]; intros k r Hk Hcnt Hinv; cbn [sqr_normal_loop].
  - replace (n - 1)%nat with k by lia. exact Hinv.
  - destruct Hinv as (R1 & R2 & R3 & R4). fold n.
    set (j := (n - 1 - k)%nat). set (off := (1 + 2 * k)%nat).
    assert (Hj : (off + j = n + k)%nat) by (unfold off, j; lia).
    assert (Hsa : slice a (1 + k) j = skipn (S k) a).
    { unfold slice. apply firstn_all2. rewrite length_skipn. fold n. unfold j. lia. }
    assert (Hsal : length (skipn (S k) a) = j) by (rewrite length_skipn; fold n; unfold j; lia).
    pose proof (mul_add_words_spec (slice r off j) (skipn (S k) a) (nth k a 0) (slice_limbs _ _ _ R1) (limbs_skipn _ _ Ha)
                  ltac:(rewrite slice_length by lia; lia) (limbs_nth a k Ha)) as Hm.
    rewrite Hsa. destruct (mul_add_words (slice r off j) (skipn (S k) a) (nth k a 0)) as [seg cy].
    destruct Hm as (M1 & M2 & M3 & M4). rewrite Hsal in M2, M4.
    assert (Hsl : length (seg ++ [cy]) = (j + 1)%nat) by (rewrite length_app; cbn [length]; lia).
    apply IH; [lia|lia|].
    assert (Hfit : (off + length (seg ++ [cy]) <= length r)%nat) by (rewrite Hsl; lia).
    split; [apply splice_limbs; [exact R1|apply limbs_app; [exact M1|constructor; [exact M3|constructor]]]|].
    split; [rewrite splice_length by exact Hfit; exact R2|]. split.
    + replace (n + S k)%nat with (off + length (seg ++ [cy]))%nat by (rewrite Hsl; lia).
      rewrite window_write by exact Hfit. rewrite lval_app, M2. cbn [lval]. rewrite Z.mul_0_r, Z.add_0_r.
      cbn [cross_upto]. rewrite <- R3. rewrite <- Hj. rewrite firstn_add, lval_app, firstn_length_le by lia.
      fold (slice r off j). replace (2 * k + 1)%nat with off by (unfold off; lia). nia.
    + rewrite nth_splice_above by (rewrite ?Hsl; lia). exact R4.
Qed.

Lemma sqr_normal_spec : forall r, (1 <= n)%nat -> limbs r -> length r = (2 * n)%nat ->
  let '(r', tmp) := sqr_normal a r in
  limbs r' /\ length r' = (2 * n)%nat /\ lval r' = lval a * lval a /\ tmp = sqr_words a.
Proof.
  intros r Hn Hr Hrl. unfold sqr_normal. fold n.
  set (r0 := upd (upd r 0 0) (2 * n - 1) 0).
  assert (L0 : length (upd r 0 0) = length r) by (apply upd_length; lia).
  assert (Hr0 : limbs r0 /\ length r0 = (2 * n)%nat /\ nth 0 r0 0 = 0 /\ nth (2 * n - 1) r0 0 = 0).
  { unfold r0. split; [apply upd_limbs; [apply upd_limbs; [exact Hr|exact limb_0]|exact limb_0]|].
    split; [rewrite upd_length by lia; lia|]. split; [|apply nth_upd_same; lia].
    destruct (Nat.eq_dec (2 * n - 1) 0) as [E|E]; [rewrite E; apply nth_upd_same; lia|].
    rewrite nth_upd_other by lia. apply nth_upd_same. lia. }
  destruct Hr0 as (Z1 & Z2 & Z3 & Z4).

  set (r1 := if (1 <? n)%nat then let '(seg, cy) := mul_words (slice a 1 (n - 1)) (nth 0 a 0) in splice r0 1 (seg ++ [cy]) else r0).
  assert (Hinv1 : (1 < n)%nat -> sqn_inv 1 r1).
  { intros Hn1. unfold r1. destruct (Nat.ltb_spec 1 n); [|lia].
    assert (Hsa : slice a 1 (n - 1) = skipn 1 a) by (unfold slice; apply firstn_all2; rewrite length_skipn; fold n; lia).
    rewrite Hsa. pose proof (mul_words_spec (skipn 1 a) (nth 0 a 0) (limbs_skipn _ _ Ha) (limbs_nth a 0 Ha)) as Hm.
    destruct (mul_words (skipn 1 a) (nth 0 a 0)) as [seg cy]. destruct Hm as (M1 & M2 & M3 & M4).
    rewrite length_skipn in M2, M4. fold n in M2, M4.
    assert (Hsl : length (seg ++ [cy]) = n) by (rewrite length_app; cbn [length]; lia).
    assert (Hfit : (1 + length (seg ++ [cy]) <= length r0)%nat) by (rewrite Hsl; lia).
    split; [apply splice_limbs; [exact Z1|apply limbs_app; [exact M1|constructor; [exact M3|constructor]]]|].
    split; [rewrite splice_length by exact Hfit; exact Z2|]. split.
    - replace (n + 1)%nat with (1 + length (seg ++ [cy]))%nat by (rewrite Hsl; lia).
      rewrite window_write by exact Hfit. rewrite lval_app, M2. cbn [lval]. rewrite Z.mul_0_r, Z.add_0_r.
      assert (E1 : lval (firstn 1 r0) = 0).
      { destruct r0 as [|y t]; [reflexivity|]. cbn [firstn lval]. cbn [nth] in Z3. lia. }
      rewrite E1. cbn [cross_upto Nat.mul Nat.add]. rewrite Bp_1. nia.
    - rewrite nth_splice_above by (rewrite ?Hsl; lia). exact Z4. }

  set (r2 := sqr_normal_loop a (n - 2) 1 r1).
  assert (Hinv2 : limbs r2 /\ length r2 = (2 * n)%nat /\ lval r2 = cross_upto a n).
  { destruct (Nat.eq_dec n 1) as [E1|E1].
    - unfold r2, r1. rewrite E1. cbn [Nat.sub Nat.ltb Nat.leb sqr_normal_loop]. split; [exact Z1|]. split; [rewrite Z2, E1; reflexivity|].
      rewrite E1 in Z2, Z4. cbn [Nat.mul Nat.add Nat.sub] in Z2, Z4.
      destruct r0 as [|y0 [|y1 [|y2 t]]]; cbn [length] in Z2; try lia. cbn [nth] in Z3, Z4. subst y0 y1.
      cbn [lval cross_upto]. rewrite (skipn_all2 a) by (fold n; lia). cbn [lval]. lia.
    - destruct (sqr_normal_loop_spec (n - 2) 1 r1 ltac:(lia) ltac:(lia) (Hinv1 ltac:(lia))) as (I1 & I2 & I3 & I4). fold r2 in I1, I2, I3, I4.
      split; [exact I1|]. split; [exact I2|].
      rewrite <- (cross_upto_last a (n - 1)) in I3 by (fold n; lia). replace (S (n - 1)) with n in I3 by lia.
      rewrite <- I3. replace (n + (n - 1))%nat with (2 * n - 1)%nat by lia.
      pose proof (lval_split_le (2 * n - 1) r2 ltac:(lia)) as Hsp. rewrite Hsp.
      assert (Hsk : lval (skipn (2 * n - 1) r2) = 0).
      { assert (Hlk : length (skipn (2 * n - 1) r2) = 1%nat) by (rewrite length_skipn; lia).
        destruct (skipn (2 * n - 1) r2) as [|y [|z t]] eqn:Es; cbn in Hlk; try lia.
        assert (Hy : nth (2 * n - 1) r2 0 = y).
        { rewrite <- (firstn_skipn (2 * n - 1) r2), Es. rewrite app_nth2 by (rewrite firstn_length_le by lia; lia).
          rewrite firstn_length_le by lia. rewrite Nat.sub_diag. reflexivity. }
        rewrite I4 in Hy. subst y. reflexivity. }
      rewrite Hsk. lia. }
  destruct Hinv2 as (I1 & I2 & I3).
  pose proof (sq_decomp a) as Hdec. fold n in Hdec.
  destruct (sqr_words_spec a Ha) as (S1 & S2 & S3). fold n in S2.
  pose proof (lval_bound a Ha) as Hab. fold n in Hab.
  assert (Hsq : lval a * lval a < Bp (2 * n)).
  { replace (2 * n)%nat with (n + n)%nat by lia. rewrite Bp_add. apply mul_bound_lt; assumption. }
  pose proof (cross_upto_nonneg a n Ha) as Hc0.
  assert (Hss0 : 0 <= sqsum a) by (rewrite <- S3; apply lval_nonneg; exact S1).

  pose proof (add_words_spec r2 r2 I1 I1 eq_refl) as Hd. destruct (add_words r2 r2) as [r3 c3]. cbn [fst].
  destruct Hd as (D1 & D2 & D3 & D4). rewrite I2 in D2, D4. rewrite I3 in D4.
  assert (Ec3 : c3 = 0).
  { pose proof (lval_bound r3 D1) as Hb3. rewrite D2 in Hb3. pose proof (Bp_pos (2 * n)). nia. }
  subst c3. rewrite Z.mul_0_r, Z.add_0_r in D4.

  pose proof (add_words_spec r3 (sqr_words a) D1 S1 ltac:(lia)) as He. destruct (add_words r3 (sqr_words a)) as [r4 c4]. cbn [fst].
  destruct He as (E1 & E2 & E3 & E4). rewrite D2 in E2, E4. rewrite D4, S3 in E4.
  assert (Ec4 : c4 = 0).
  { pose proof (lval_bound r4 E1) as Hb4. rewrite E2 in Hb4. pose proof (Bp_pos (2 * n)). nia. }
  subst c4. rewrite Z.mul_0_r, Z.add_0_r in E4.
  split; [exact E1|]. split; [exact E2|]. split; [lia|reflexivity].
Qed.

End SqrNormal.

Lemma sqr_comba_spec : forall a m, limbs a -> length a = m ->
  limbs (to_limbs (2 * m) (lval a * lval a)) /\ length (to_limbs (2 * m) (lval a * lval a)) = (2 * m)%nat /\
  lval (to_limbs (2 * m) (lval a * lval a)) = lval a * lval a.
Proof.
  intros a m Ha Hl. split; [apply to_limbs_limbs|]. split; [apply to_limbs_length|].
  apply lval_to_limbs_small. pose proof (lval_bound a Ha) as H1. rewrite Hl in H1.
  replace (2 * m)%nat with (m + m)%nat by lia. rewrite Bp_add.
  split; [apply Z.mul_nonneg_nonneg; lia|]. apply mul_bound_lt; assumption.
Qed.

Fixpoint sqr_scratch (k : nat) : nat :=
  match k with
  | O => 2
  | S k' => (2 * Nat.pow 2 k + sqr_scratch k')%nat
  end.

Lemma sqr_scratch_le : forall k, (sqr_scratch k + 2 <= 4 * Nat.pow 2 k)%nat.
Proof.
  induction k as [|k IH]; [cbn; lia|]. cbn [sqr_scratch]. assert (E : Nat.pow 2 (S k) = (2 * Nat.pow 2 k)%nat) by (cbn [Nat.pow]; lia).
  rewrite E. lia.
Qed.

Lemma sqr_scratch_ge : forall k, (2 * Nat.pow 2 k <= sqr_scratch k)%nat.
Proof. destruct k as [|k]; [cbn; lia|]. cbn [sqr_scratch]. lia. Qed.

Definition sqr_post (a r t : list Z) (res : list Z * list Z) : Prop :=
  let '(r', t') := res in
  limbs r' /\ length r' = length r /\ lval r' = lval a * lval a /\ limbs t' /\ length t' = length t.

Theorem sqr_recursive_spec : forall k a r t,
  limbs a -> limbs r -> limbs t -> length a = Nat.pow 2 k -> length r = (2 * Nat.pow 2 k)%nat ->
  (sqr_scratch k <= length t)%nat ->
  sqr_post a r t (sqr_recursive k a r t).
Proof.
  induction k as [|k' IH]; intros a r t Ha Hr Ht Hla Hrl Hsc.
  -
    cbn [sqr_recursive Nat.pow Nat.eqb Nat.ltb Nat.leb]. cbn [Nat.pow] in Hla, Hrl. cbn [sqr_scratch] in Hsc.
    rewrite firstn_all2 by lia. rewrite (firstn_all2 r) by lia.
    pose proof (sqr_normal_spec a Ha r ltac:(lia) Hr ltac:(lia)) as Hn. destruct (sqr_normal a r) as [ro tmp].
    destruct Hn as (N1 & N2 & N3 & N4). destruct (sqr_words_spec a Ha) as (S1 & S2 & S3).
    unfold sqr_post. rewrite N4. split; [apply splice_limbs; assumption|]. split; [apply splice_length; lia|].
    split; [rewrite splice_all by lia; exact N3|]. split; [apply splice_limbs; assumption|apply splice_length; lia].
  - pose proof (pow2_pos k') as Hp. assert (Epow : Nat.pow 2 (S k') = (2 * Nat.pow 2 k')%nat) by (cbn [Nat.pow]; lia).
    cbn [sqr_recursive]. set (n2 := Nat.pow 2 (S k')) in *. set (n := Nat.pow 2 k') in *.
    cbn [sqr_scratch] in Hsc. fold n2 in Hsc.
    destruct (Nat.eqb_spec n2 4) as [E4|N4].
    { rewrite firstn_all2 by lia. destruct (sqr_comba_spec a 4 Ha ltac:(lia)) as (C1 & C2 & C3). change (2 * 4)%nat with 8%nat in *.
      unfold sqr_post, sqr_comba4. split; [apply splice_limbs; assumption|]. split; [apply splice_length; lia|].
      split; [rewrite splice_all by lia; exact C3|]. split; [exact Ht|reflexivity]. }
    destruct (Nat.eqb_spec n2 8) as [E8|N8].
    { rewrite firstn_all2 by lia. destruct (sqr_comba_spec a 8 Ha ltac:(lia)) as (C1 & C2 & C3). change (2 * 8)%nat with 16%nat in *.
      unfold sqr_post, sqr_comba8. split; [apply splice_limbs; assumption|]. split; [apply splice_length; lia|].
      split; [rewrite splice_all by lia; exact C3|]. split; [exact Ht|reflexivity]. }
    destruct (Nat.ltb_spec n2 16) as [Hlt|Hge].
    { rewrite firstn_all2 by lia. rewrite (firstn_all2 r) by lia.
      pose proof (sqr_normal_spec a Ha r ltac:(lia) Hr ltac:(lia)) as Hn. destruct (sqr_normal a r) as [ro tmp].
      destruct Hn as (N1 & N2 & N3 & N4'). destruct (sqr_words_spec a Ha) as (S1 & S2 & S3).
      unfold sqr_post. rewrite N4'. split; [apply splice_limbs; assumption|]. split; [apply splice_length; lia|].
      split; [rewrite splice_all by lia; exact N3|]. split; [apply splice_limbs; assumption|apply splice_length; lia]. }

    set (a_lo := firstn n a). set (a_hi := slice a n n).
    assert (Hal : limbs a_lo) by (apply limbs_firstn; exact Ha). assert (Hah : limbs a_hi) by (apply slice_limbs; exact Ha).
    assert (Lal : length a_lo = n) by (apply firstn_length_le; lia). assert (Lah : length a_hi = n) by (apply slice_length; lia).
    assert (Eav : lval a = lval a_lo + Bp n * lval a_hi).
    { pose proof (lval_split_le n a ltac:(lia)) as E. rewrite E. unfold a_lo, a_hi, slice. rewrite (firstn_all2 (skipn n a)) by (rewrite length_skipn; lia). reflexivity. }
    pose proof (lval_bound a_lo Hal) as B0. rewrite Lal in B0. pose proof (lval_bound a_hi Hah) as B1. rewrite Lah in B1.
    rewrite (cmp_words_spec a_lo a_hi Hal Hah ltac:(lia)).
    pose proof (sqr_scratch_ge k') as Hsg. fold n in Hsg.

    set (td := if 0 <? sgn3 (lval a_lo) (lval a_hi) then splice t 0 (fst (sub_words a_lo a_hi))
               else if sgn3 (lval a_lo) (lval a_hi) <? 0 then splice t 0 (fst (sub_words a_hi a_lo)) else t).
    assert (Htd : limbs td /\ length td = length t /\
                  (sgn3 (lval a_lo) (lval a_hi) <> 0 -> limbs (slice td 0 n) /\
                     lval (slice td 0 n) * lval (slice td 0 n) = (lval a_lo - lval a_hi) * (lval a_lo - lval a_hi))).
    { unfold td. destruct (Z.ltb_spec 0 (sgn3 (lval a_lo) (lval a_hi))) as [Hs|Hs].
      - assert (Hgt : lval a_hi < lval a_lo).
        { apply sgn3_pos_iff. destruct (sgn3_range (lval a_lo) (lval a_hi)) as [Eq|[Eq|Eq]]; lia. }
        pose proof (sub_words_spec a_lo a_hi Hal Hah ltac:(lia)) as Hsw. destruct (sub_words a_lo a_hi) as [d bw]. cbn [fst].
        destruct Hsw as (W1 & W2 & W3 & W4).
        assert (Hdl : length d = n) by lia.
        split; [apply splice_limbs; assumption|]. split; [apply splice_length; lia|]. intros _.
        rewrite (slice_splice_same' t 0 d n) by lia. split; [exact W1|].
        rewrite Lal in W4. pose proof (lval_bound d W1) as Hdb. rewrite Hdl in Hdb. pose proof (Bp_pos n).
        assert (Ebw : bw = 0) by nia. subst bw. assert (Ed : lval d = lval a_lo - lval a_hi) by lia. rewrite Ed. reflexivity.
      - destruct (Z.ltb_spec (sgn3 (lval a_lo) (lval a_hi)) 0) as [Hs2|Hs2].
        + pose proof (sub_words_spec a_hi a_lo Hah Hal ltac:(lia)) as Hsw. destruct (sub_words a_hi a_lo) as [d bw]. cbn [fst].
          destruct Hsw as (W1 & W2 & W3 & W4).
          assert (Hdl : length d = n) by lia.
          split; [apply splice_limbs; assumption|]. split; [apply splice_length; lia|]. intros _.
          rewrite (slice_splice_same' t 0 d n) by lia. split; [exact W1|].
          assert (Hlt' : lval a_lo < lval a_hi).
          { apply sgn3_neg_iff. destruct (sgn3_range (lval a_lo) (lval a_hi)) as [Eq|[Eq|Eq]]; lia. }
          rewrite Lah in W4. pose proof (lval_bound d W1) as Hdb. rewrite Hdl in Hdb. pose proof (Bp_pos n).
          assert (Ebw : bw = 0) by nia. subst bw. assert (Ed : lval d = lval a_hi - lval a_lo) by lia. rewrite Ed. ring.
        + split; [exact Ht|]. split; [reflexivity|]. intros Hne. lia. }
    destruct Htd as (Htdl & Htdlen & Htdv).
    set (p := skipn (2 * n2) td).
    assert (Hpl : limbs p) by (apply limbs_skipn; exact Htdl).
    assert (Hplen : length p = (length t - 2 * n2)%nat) by (unfold p; rewrite length_skipn; lia).

    assert (Hm : let '(tm, p0) := if sgn3 (lval a_lo) (lval a_hi) =? 0 then (repeat 0 n2, p)
                                  else sqr_recursive k' (slice td 0 n) (slice td n2 n2) p in
                 limbs tm /\ length tm = n2 /\ limbs p0 /\ length p0 = length p /\
                 lval tm = (lval a_lo - lval a_hi) * (lval a_lo - lval a_hi)).
    { destruct (Z.eqb_spec (sgn3 (lval a_lo) (lval a_hi)) 0) as [Ez|Ez].
      - apply (proj1 (sgn3_0_iff _ _)) in Ez. split; [apply limbs_repeat; exact limb_0|]. split; [apply repeat_length|]. split; [exact Hpl|]. split; [reflexivity|].
        rewrite lval_repeat0, Ez. ring.
      - destruct (Htdv Ez) as (T1 & T2).
        pose proof (IH (slice td 0 n) (slice td n2 n2) p T1 (slice_limbs _ _ _ Htdl) Hpl
                      ltac:(rewrite slice_length by lia; reflexivity) ltac:(rewrite slice_length by lia; fold n; lia) ltac:(lia)) as Hx.
        destruct (sqr_recursive k' (slice td 0 n) (slice td n2 n2) p) as [tm p0].
        destruct Hx as (X1 & X2 & X3 & X4 & X5). rewrite slice_length in X2 by lia.
        repeat split; try assumption. rewrite X3. exact T2. }
    destruct (if sgn3 (lval a_lo) (lval a_hi) =? 0 then (repeat 0 n2, p)
              else sqr_recursive k' (slice td 0 n) (slice td n2 n2) p) as [tm p0].
    destruct Hm as (M1 & M2 & M3 & M4 & M5).

    pose proof (IH a_lo (slice r 0 n2) p0 Hal (slice_limbs _ _ _ Hr) M3 Lal ltac:(rewrite slice_length by lia; fold n; lia) ltac:(lia)) as Hl.
    destruct (sqr_recursive k' a_lo (slice r 0 n2) p0) as [rl p1]. destruct Hl as (L1 & L2 & L3 & L4 & L5). rewrite slice_length in L2 by lia.
    pose proof (IH a_hi (slice r n2 n2) p1 Hah (slice_limbs _ _ _ Hr) L4 Lah ltac:(rewrite slice_length by lia; fold n; lia) ltac:(lia)) as Hh.
    destruct (sqr_recursive k' a_hi (slice r n2 n2) p1) as [rh p2]. destruct Hh as (H1 & H2 & H3 & H4 & H5). rewrite slice_length in H2 by lia.

    set (r1 := rl ++ rh). set (t1 := firstn n2 td ++ tm ++ p2).
    assert (Hr1 : limbs r1 /\ length r1 = (2 * n2)%nat) by (unfold r1; split; [apply limbs_app; assumption|rewrite length_app; lia]).
    assert (Ht1 : limbs t1 /\ length t1 = length t).
    { unfold t1. split; [apply limbs_app; [apply limbs_firstn; exact Htdl|apply limbs_app; assumption]|].
      rewrite !length_app, firstn_length_le by lia. lia. }
    assert (Es0 : slice r1 0 n2 = rl) by (unfold r1, slice; cbn [skipn]; rewrite firstn_app, firstn_all2, L2, Nat.sub_diag by lia; cbn [firstn]; apply app_nil_r).
    assert (Es1 : slice r1 n2 n2 = rh).
    { unfold r1, slice. rewrite skipn_app, skipn_all2, L2, Nat.sub_diag by lia. cbn [skipn app]. apply firstn_all2. lia. }
    assert (Est : slice t1 n2 n2 = tm).
    { unfold t1, slice. rewrite skipn_app, skipn_all2, firstn_length_le, Nat.sub_diag by (rewrite ?firstn_length_le; lia). cbn [skipn app].
      rewrite firstn_app, firstn_all2, M2, Nat.sub_diag by lia. cbn [firstn]. apply app_nil_r. }
    pose proof (kara_finish n true r1 t1 (lval a_lo) (lval a_hi) (lval a_lo) (lval a_hi)) as Hk. cbv zeta in Hk.
    replace (2 * n)%nat with n2 in Hk by lia.
    specialize (Hk (proj1 Hr1) (proj2 Hr1) (proj1 Ht1) ltac:(destruct Ht1; lia)
                   ltac:(rewrite Es0; exact L3) ltac:(rewrite Es1; exact H3) ltac:(rewrite Est, M5; ring) B0 B1 B0 B1).
    fold r1 t1. destruct (kara_combine n true r1 t1) as [r' t'].
    destruct Hk as (K1 & K2 & K3 & K4 & K5). unfold sqr_post.
    split; [exact K1|]. split; [rewrite K2; destruct Hr1; lia|]. split; [rewrite K3, Eav; reflexivity|].
    split; [exact K4|rewrite K5; destruct Ht1; assumption].
Qed.
