(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnWordsCorrect BnKara BnKaraCorrect.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma add_carry_test : forall x c, 0 <= x < BW -> (addw x c <? c mod BW) = (addw x c <? x).
Proof.
  intros x c Hx. unfold addw. pose proof BW_pos as HB.
  pose proof (Z.mod_pos_bound c BW HB) as Hc.
  assert (E : (x + c) mod BW = (x + c mod BW) mod BW) by (rewrite Z.add_mod_idemp_r by lia; reflexivity).
  rewrite E. destruct (Z.lt_ge_cases (x + c mod BW) BW) as [H|H].
  - rewrite Z.mod_small by lia. destruct (Z.ltb_spec (x + c mod BW) (c mod BW)); destruct (Z.ltb_spec (x + c mod BW) x); lia.
  - assert (E2 : (x + c mod BW) mod BW = x + c mod BW - BW).
    { rewrite <- (Z.mod_add _ (-1) BW) by lia. apply Z.mod_small. lia. }
    rewrite E2. destruct (Z.ltb_spec (x + c mod BW - BW) (c mod BW)); destruct (Z.ltb_spec (x + c mod BW - BW) x); lia.
Qed.

Definition cu_fit (l : list Z) : Prop := lval l + 1 < Bp (length l).

Lemma cu_fit_cons : forall l, limbs l -> cu_fit l -> exists x l', l = x :: l' /\ 0 <= x < BW /\ limbs l' /\
  (addw x 1 = 0 -> cu_fit l').
Proof.
  intros [|x l'] Hl Hf.
  - unfold cu_fit in Hf. cbn in Hf. lia.
  - apply limbs_cons_inv in Hl. destruct Hl as [Hx Hl]. exists x, l'. split; [reflexivity|]. split; [exact Hx|]. split; [exact Hl|].
    intros E. unfold cu_fit in *. cbn [lval length] in Hf. rewrite Bp_S in Hf. unfold addw in E. unfold limb in Hx.
    pose proof BW_pos. assert (x = BW - 1).
    { destruct (Z.eq_dec x (BW - 1)); [assumption|]. rewrite Z.mod_small in E by lia. lia. }
    subst x. nia.
Qed.

Lemma add_carry_fit : forall x l' c, 0 <= x < BW -> limbs l' -> 0 <= c < BW -> lval (x :: l') + c < Bp (S (length l')) ->
  (addw x c <? x) = true -> cu_fit l'.
Proof.
  intros x l' c Hx Hl Hc Hf Ht. apply Z.ltb_lt in Ht. unfold addw in Ht. unfold cu_fit.
  cbn [lval] in Hf. rewrite Bp_S in Hf. pose proof BW_pos.
  destruct (Z.lt_ge_cases (x + c) BW) as [H1|H1]; [rewrite Z.mod_small in Ht by lia; lia|].
  pose proof (lval_nonneg l' Hl). nia.
Qed.

Definition kc3_ok (RES : list Z * list Z) (n : nat) (r t : list Z) (c12 : Z) : Prop :=
  let n2 := (2 * n)%nat in
  let '(s3, c3) := add_words (slice r n n2) (slice t n2 n2) in
  let r' := splice r n s3 in
  let c := c12 + c3 in
  RES = ((if c =? 0 then r' else firstn (n + n2) r' ++ add_carry (skipn (n + n2) r') c), t) /\
  0 <= c <= 3 /\ (c <> 0 -> lval (skipn (n + n2) r') + c < Bp n).

Definition kc2_ok (RES : list Z * list Z) (n : nat) (neg : bool) (r t : list Z) (c1 : Z) : Prop :=
  let n2 := (2 * n)%nat in
  let '(s2, c2) := if neg then let '(s, bw) := sub_words (slice t 0 n2) (slice t n2 n2) in (s, c1 - bw)
                   else let '(s, cy) := add_words (slice t n2 n2) (slice t 0 n2) in (s, c1 + cy) in
  kc3_ok RES n r (splice t n2 s2) c2.

Definition kc_ok (RES : list Z * list Z) (n : nat) (neg : bool) (r t : list Z) : Prop :=
  let n2 := (2 * n)%nat in
  let '(s1, c1) := add_words (slice r 0 n2) (slice r n2 n2) in
  kc2_ok RES n neg r (splice t 0 s1) c1.

Lemma kc_ok_intro : forall n (neg : bool) r t,
  let n2 := (2 * n)%nat in
  limbs r -> length r = (2 * n2)%nat -> limbs t -> (2 * n2 <= length t)%nat ->
  let P0 := lval (slice r 0 n2) in
  let P2 := lval (slice r n2 n2) in
  let Tm := lval (slice t n2 n2) in
  let M := P0 + P2 + (if neg then - Tm else Tm) in
  0 <= M -> P0 + Bp n2 * P2 + Bp n * M < Bp (2 * n2) ->
  kc_ok (kara_combine n neg r t) n neg r t.
Proof.
  intros n neg r t n2 Hr Hrl Ht Htl P0 P2 Tm M HM Hfit. pose proof BW_pos as BWp.
  unfold kc_ok, kara_combine. fold n2.
  pose proof (add_words_spec (slice r 0 n2) (slice r n2 n2) (slice_limbs _ _ _ Hr) (slice_limbs _ _ _ Hr)
                ltac:(rewrite !slice_length by lia; reflexivity)) as H1.
  destruct (add_words (slice r 0 n2) (slice r n2 n2)) as [s1 c1]. destruct H1 as (Hs1 & Hs1l & Hc1 & Hv1).
  rewrite slice_length in Hs1l, Hv1 by lia. fold P0 P2 in Hv1.
  unfold kc2_ok. fold n2.
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
  unfold kc3_ok. fold n2.
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
  split; [reflexivity|]. split; [lia|]. intros Ec.
  pose proof (lval_split_le (n + n2) ra ltac:(lia)) as Esp.
  pose proof (lval_nonneg _ (limbs_firstn (n + n2) ra Hra)) as Hlo0.
  assert (Bp (n + n2) * (lval (skipn (n + n2) ra) + (c2 + c3)) < Bp (n + n2) * Bp n) by nia.
  apply Z.mul_lt_mono_pos_l in H; [exact H|]. apply Bp_pos.
Qed.

Definition gen3_ok (RES : list Z * list Z) (k' n : nat) (neg : bool) (a b : list Z) (da db : nat) (R T : list Z) : Prop :=
  let '(rh, p2) := mul_recursive k' (slice a n (n - da)) (slice b n (n - db)) da db (slice R (2 * n) (2 * n)) (skipn (4 * n) T) in
  kc_ok RES n neg (splice R (2 * n) rh) (splice T (4 * n) p2).

Definition gen2_ok (RES : list Z * list Z) (k' n : nat) (neg : bool) (a b : list Z) (da db : nat) (R T : list Z) : Prop :=
  let '(rl, p1) := mul_recursive k' (firstn n a) (firstn n b) 0 0 (slice R 0 (2 * n)) (skipn (4 * n) T) in
  gen3_ok RES k' n neg a b da db (splice R 0 rl) (splice T (4 * n) p1).

Definition comba_ok (RES : list Z * list Z) (n : nat) (neg : bool) (a b : list Z) (da db : nat) (R T : list Z) : Prop :=
  kc_ok RES n neg
        (splice (splice R 0 (mul_comba8 (firstn n a) (firstn n b))) (2 * n) (mul_comba8 (slice a n (n - da)) (slice b n (n - db)))) T.

Definition join_ok (RES : list Z * list Z) (k' n : nat) (neg : bool) (a b : list Z) (da db : nat) (R T : list Z) : Prop :=
  if ((n =? 8) && (da =? 0) && (db =? 0))%nat
  then comba_ok RES n neg a b da db R (splice T (2 * n) (mul_comba8 (slice T 0 n) (slice T n n)))
  else let '(tm, p0) := mul_recursive k' (slice T 0 n) (slice T n n) 0 0 (slice T (2 * n) (2 * n)) (skipn (4 * n) T) in
       gen2_ok RES k' n neg a b da db R (splice T (2 * n) (tm ++ p0)).

Definition zero_ok (RES : list Z * list Z) (k' n : nat) (a b : list Z) (da db : nat) (R T : list Z) : Prop :=
  if ((n =? 8) && (da =? 0) && (db =? 0))%nat
  then comba_ok RES n false a b da db R (splice T (2 * n) (repeat 0 (2 * n)))
  else gen2_ok RES k' n false a b da db R (splice T (2 * n) (repeat 0 (2 * n))).

Section RecDiffsLit.
  Variables (al ah bl bh : list Z) (tna tnb : nat).
  Lemma rec_diffs_m1_m1 : rec_diffs al ah bl bh tna tnb (-1) (-1) = Some (fst (sub_part_words ah al tna), fst (sub_part_words bl bh tnb), false).
  Proof. reflexivity. Qed.
  Lemma rec_diffs_m1_p1 : rec_diffs al ah bl bh tna tnb (-1) 1 = Some (fst (sub_part_words ah al tna), fst (sub_part_words bh bl tnb), true).
  Proof. reflexivity. Qed.
  Lemma rec_diffs_p1_m1 : rec_diffs al ah bl bh tna tnb 1 (-1) = Some (fst (sub_part_words al ah tna), fst (sub_part_words bl bh tnb), true).
  Proof. reflexivity. Qed.
  Lemma rec_diffs_p1_p1 : rec_diffs al ah bl bh tna tnb 1 1 = Some (fst (sub_part_words al ah tna), fst (sub_part_words bh bl tnb), false).
  Proof. reflexivity. Qed.
  Lemma rec_diffs_m1_0 : rec_diffs al ah bl bh tna tnb (-1) 0 = None. Proof. reflexivity. Qed.
  Lemma rec_diffs_0_m1 : rec_diffs al ah bl bh tna tnb 0 (-1) = None. Proof. reflexivity. Qed.
  Lemma rec_diffs_0_0 : rec_diffs al ah bl bh tna tnb 0 0 = None. Proof. reflexivity. Qed.
  Lemma rec_diffs_0_p1 : rec_diffs al ah bl bh tna tnb 0 1 = None. Proof. reflexivity. Qed.
  Lemma rec_diffs_p1_0 : rec_diffs al ah bl bh tna tnb 1 0 = None. Proof. reflexivity. Qed.
End RecDiffsLit.

Lemma kc_ok_finish : forall n (neg : bool) r t A0 A1 B0 B1,
  let n2 := (2 * n)%nat in
  limbs r -> length r = (2 * n2)%nat -> limbs t -> (2 * n2 <= length t)%nat ->
  lval (slice r 0 n2) = A0 * B0 -> lval (slice r n2 n2) = A1 * B1 ->
  (if neg then - lval (slice t n2 n2) else lval (slice t n2 n2)) = (A0 - A1) * (B1 - B0) ->
  0 <= A0 < Bp n -> 0 <= A1 < Bp n -> 0 <= B0 < Bp n -> 0 <= B1 < Bp n ->
  kc_ok (kara_combine n neg r t) n neg r t.
Proof.
  intros n neg r t A0 A1 B0 B1 n2 Hr Hrl Ht Htl HP0 HP2 Hsgn HA0 HA1 HB0 HB1.
  apply kc_ok_intro; try assumption; fold n2; rewrite HP0, HP2.
  - assert (EM : A0 * B0 + A1 * B1 + (if neg then - lval (slice t n2 n2) else lval (slice t n2 n2)) = A0 * B1 + A1 * B0)
      by (rewrite Hsgn; ring).
    rewrite EM. assert (0 <= A0 * B1) by (apply Z.mul_nonneg_nonneg; lia). assert (0 <= A1 * B0) by (apply Z.mul_nonneg_nonneg; lia). lia.
  - assert (EM : A0 * B0 + A1 * B1 + (if neg then - lval (slice t n2 n2) else lval (slice t n2 n2)) = A0 * B1 + A1 * B0)
      by (rewrite Hsgn; ring).
    rewrite EM.
    assert (EB : Bp n2 = Bp n * Bp n) by (subst n2; rewrite <- Bp_add; f_equal; lia).
    assert (EB2 : Bp (2 * n2) = Bp n2 * Bp n2) by (rewrite <- Bp_add; f_equal; lia).
    pose proof (Bp_pos n) as Hbn.
    assert (Etgt : A0 * B0 + Bp n2 * (A1 * B1) + Bp n * (A0 * B1 + A1 * B0) = (A0 + Bp n * A1) * (B0 + Bp n * B1))
      by (rewrite EB; ring).
    rewrite Etgt, EB2, EB.
    assert (HA : 0 <= A0 + Bp n * A1 < Bp n * Bp n) by nia.
    assert (HB : 0 <= B0 + Bp n * B1 < Bp n * Bp n) by nia.
    apply (mul_bound_lt _ _ _ _ HA HB).
Qed.

Lemma splice_tail : forall l off seg, (off + length seg = length l)%nat -> splice l off seg = firstn off l ++ seg.
Proof. intros l off seg H. unfold splice. rewrite H, skipn_all. rewrite app_nil_r. reflexivity. Qed.

Lemma skipn_app_len : forall (A B : list Z) k, length A = k -> skipn k (A ++ B) = B.
Proof. intros A B k <-. rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity. Qed.

Lemma firstn_app_len : forall (A B : list Z) k, length A = k -> firstn k (A ++ B) = A.
Proof. intros A B k <-. rewrite firstn_app, firstn_all, Nat.sub_diag. cbn [firstn]. apply app_nil_r. Qed.

Lemma gen2_ok_intro : forall k' a b da db r (F tm p0 : list Z) (neg : bool),
  let n := Nat.pow 2 k' in
  let a_lo := firstn n a in let a_hi := slice a n (n - da) in let b_lo := firstn n b in let b_hi := slice b n (n - db) in
  limbs a -> limbs b -> limbs r -> (1 <= k')%nat -> (8 <= n)%nat -> (da <= 1)%nat -> (db <= 1)%nat ->
  length a = (2 * n - da)%nat -> length b = (2 * n - db)%nat -> length r = (2 * (2 * n))%nat ->
  limbs F -> length F = (2 * n)%nat -> limbs tm -> length tm = (2 * n)%nat -> limbs p0 -> (scratch_rec k' <= length p0)%nat ->
  (if neg then - lval tm else lval tm) = (lval a_lo - lval a_hi) * (lval b_hi - lval b_lo) ->
  gen2_ok (let '(r1, t1) := (let '(rl, p1) := mul_recursive k' a_lo b_lo 0 0 (slice r 0 (2 * n)) p0 in
                             let '(rh, p2) := mul_recursive k' a_hi b_hi da db (slice r (2 * n) (2 * n)) p1 in
                             (rl ++ rh, F ++ tm ++ p2)) in
           kara_combine n neg r1 t1)
          k' n neg a b da db r (F ++ tm ++ p0).
Proof.
  intros k' a b da db r F tm p0 neg n a_lo a_hi b_lo b_hi Ha Hb Hr Hk' Hn8 Hda Hdb Hla Hlb Hrl HF HFl Htm Html Hp0 Hp0s Hsgn.
  assert (Hall : length a_lo = n) by (subst a_lo; apply firstn_length_le; lia).
  assert (Hbll : length b_lo = n) by (subst b_lo; apply firstn_length_le; lia).
  assert (Hahl : length a_hi = (n - da)%nat) by (subst a_hi; apply slice_length; lia).
  assert (Hbhl : length b_hi = (n - db)%nat) by (subst b_hi; apply slice_length; lia).
  assert (Hal : limbs a_lo) by (subst a_lo; apply limbs_firstn; exact Ha).
  assert (Hbl : limbs b_lo) by (subst b_lo; apply limbs_firstn; exact Hb).
  assert (Hah : limbs a_hi) by (subst a_hi; apply slice_limbs; exact Ha).
  assert (Hbh : limbs b_hi) by (subst b_hi; apply slice_limbs; exact Hb).
  pose proof (lval_bound a_lo Hal) as HA0. rewrite Hall in HA0.
  pose proof (lval_bound b_lo Hbl) as HB0. rewrite Hbll in HB0.
  assert (HA1 : 0 <= lval a_hi < Bp n).
  { pose proof (lval_bound a_hi Hah) as Hx. rewrite Hahl in Hx. pose proof (Bp_mono (n - da) n ltac:(lia)). lia. }
  assert (HB1 : 0 <= lval b_hi < Bp n).
  { pose proof (lval_bound b_hi Hbh) as Hx. rewrite Hbhl in Hx. pose proof (Bp_mono (n - db) n ltac:(lia)). lia. }
  unfold gen2_ok. fold a_lo b_lo.
  assert (E0 : skipn (4 * n) (F ++ tm ++ p0) = p0).
  { rewrite app_assoc. apply skipn_app_len. rewrite length_app. lia. }
  rewrite E0.
  pose proof (mul_recursive_spec k' a_lo b_lo 0 0 (slice r 0 (2 * n)) p0 Hal Hbl (slice_limbs _ _ _ Hr) Hp0 Hk' ltac:(lia) ltac:(lia)
                ltac:(fold n; lia) ltac:(fold n; lia) ltac:(rewrite slice_length by lia; fold n; lia) Hp0s) as Hx.
  destruct (mul_recursive k' a_lo b_lo 0 0 (slice r 0 (2 * n)) p0) as [rl p1].
  destruct Hx as (L1 & L2 & L3 & L4 & L5). rewrite slice_length in L2 by lia.
  unfold gen3_ok. fold a_hi b_hi.
  assert (E1 : slice (splice r 0 rl) (2 * n) (2 * n) = slice r (2 * n) (2 * n)) by (apply slice_splice_above; lia).
  assert (E2 : skipn (4 * n) (splice (F ++ tm ++ p0) (4 * n) p1) = p1).
  { rewrite splice_tail by (rewrite !length_app; lia). apply skipn_app_len. rewrite length_firstn, !length_app. lia. }
  rewrite E1, E2.
  pose proof (mul_recursive_spec k' a_hi b_hi da db (slice r (2 * n) (2 * n)) p1 Hah Hbh (slice_limbs _ _ _ Hr) L4 Hk' Hda Hdb
                ltac:(fold n; lia) ltac:(fold n; lia) ltac:(rewrite slice_length by lia; fold n; lia) ltac:(lia)) as Hx.
  destruct (mul_recursive k' a_hi b_hi da db (slice r (2 * n) (2 * n)) p1) as [rh p2].
  destruct Hx as (H1 & H2 & H3 & H4 & H5). rewrite slice_length in H2 by lia.
  assert (ER : splice (splice r 0 rl) (2 * n) rh = rl ++ rh) by (apply two_splices_all; lia).
  assert (ET : splice (splice (F ++ tm ++ p0) (4 * n) p1) (4 * n) p2 = F ++ tm ++ p2).
  { rewrite (splice_tail (F ++ tm ++ p0)) by (rewrite !length_app; lia).
    assert (EF : firstn (4 * n) (F ++ tm ++ p0) = F ++ tm) by (rewrite app_assoc; apply firstn_app_len; rewrite length_app; lia).
    rewrite EF. rewrite splice_tail by (rewrite !length_app; lia).
    rewrite firstn_app_len by (rewrite length_app; lia). rewrite <- app_assoc. reflexivity. }
  rewrite ER, ET.
  assert (S1 : slice (rl ++ rh) 0 (2 * n) = rl).
  { unfold slice. cbn [skipn]. apply firstn_app_len. exact L2. }
  assert (S2 : slice (rl ++ rh) (2 * n) (2 * n) = rh).
  { unfold slice. rewrite skipn_app_len by exact L2. apply firstn_all2. lia. }
  assert (S3 : slice (F ++ tm ++ p2) (2 * n) (2 * n) = tm).
  { unfold slice. rewrite skipn_app_len by exact HFl. apply firstn_app_len. exact Html. }
  apply (kc_ok_finish n neg (rl ++ rh) (F ++ tm ++ p2) (lval a_lo) (lval a_hi) (lval b_lo) (lval b_hi)); try assumption.
  - apply limbs_app; assumption.
  - rewrite length_app. lia.
  - apply limbs_app; [exact HF | apply limbs_app; assumption].
  - rewrite !length_app. lia.
  - rewrite S1. exact L3.
  - rewrite S2. exact H3.
  - rewrite S3. exact Hsgn.
Qed.

Lemma rec_staged : forall k' a b da db R T,
  limbs a -> limbs b -> limbs R -> limbs T -> (da <= 1)%nat -> (db <= 1)%nat ->
  length a = (Nat.pow 2 (S k') - da)%nat -> length b = (Nat.pow 2 (S k') - db)%nat -> length R = (2 * Nat.pow 2 (S k'))%nat ->
  (scratch_rec (S k') <= length T)%nat -> (16 <= Nat.pow 2 (S k'))%nat ->
  let n := Nat.pow 2 k' in
  match rec_diffs (firstn n a) (slice a n (n - da)) (firstn n b) (slice b n (n - db)) (n - da) (n - db)
          (cmp_part_words (firstn n a) (slice a n (n - da)) (n - da)) (cmp_part_words (slice b n (n - db)) (firstn n b) (n - db)) with
  | Some (t0, t1, neg) => join_ok (mul_recursive (S k') a b da db R T) k' n neg a b da db R (splice (splice T 0 t0) n t1)
  | None => zero_ok (mul_recursive (S k') a b da db R T) k' n a b da db R T
  end.
Proof.
  intros k' a b da db r t Ha Hb Hr Ht Hda Hdb Hla Hlb Hrl Hsc Hbig n.
  pose proof (pow2_pos k') as Hp. assert (Epow : Nat.pow 2 (S k') = (2 * n)%nat) by (subst n; cbn [Nat.pow]; lia).
  assert (Hn8 : (8 <= n)%nat) by lia.
  assert (Hk' : (1 <= k')%nat) by (destruct k' as [|k'']; [cbn in n; lia | lia]).
  rewrite scratch_rec_S in Hsc by exact Hbig. rewrite Epow in Hla, Hlb, Hrl, Hsc.
  set (tna := (n - da)%nat). set (tnb := (n - db)%nat).
  set (a_lo := firstn n a). set (a_hi := slice a n tna). set (b_lo := firstn n b). set (b_hi := slice b n tnb).

  assert (EM : mul_recursive (S k') a b da db r t =
    (let dif := rec_diffs a_lo a_hi b_lo b_hi tna tnb (cmp_part_words a_lo a_hi tna) (cmp_part_words b_hi b_lo tnb) in
     let td := match dif with Some (t0, t1, _) => splice (splice t 0 t0) n t1 | None => t end in
     let neg := match dif with Some (_, _, ng) => ng | None => false end in
     let zero := match dif with Some _ => false | None => true end in
     let '(r1, t1) :=
       if ((n =? 8) && (da =? 0) && (db =? 0))%nat
       then (splice (splice r 0 (mul_comba8 a_lo b_lo)) (2 * n) (mul_comba8 a_hi b_hi),
             splice td (2 * n) (if zero then repeat 0 16%nat else mul_comba8 (slice td 0 8) (slice td 8 8)))
       else let p := skipn (2 * (2 * n)) td in
            let '(tm, p0) := if zero then (repeat 0 (2 * n), p)
                             else mul_recursive k' (slice td 0 n) (slice td n n) 0 0 (slice td (2 * n) (2 * n)) p in
            let '(rl, p1) := mul_recursive k' a_lo b_lo 0 0 (slice r 0 (2 * n)) p0 in
            let '(rh, p2) := mul_recursive k' a_hi b_hi da db (slice r (2 * n) (2 * n)) p1 in
            (rl ++ rh, firstn (2 * n) td ++ tm ++ p2) in
     kara_combine n neg r1 t1)).
  { cbn [mul_recursive]. fold n. rewrite Epow.
    destruct (Nat.eqb_spec (2 * n) 8) as [E|_]; [lia|]. cbn [andb].
    destruct (Nat.ltb_spec (2 * n) 16) as [E|_]; [lia|]. reflexivity. }

  assert (Hall : length a_lo = n) by (subst a_lo; apply firstn_length_le; lia).
  assert (Hbll : length b_lo = n) by (subst b_lo; apply firstn_length_le; lia).
  assert (Hahl : length a_hi = tna) by (subst a_hi; apply slice_length; lia).
  assert (Hbhl : length b_hi = tnb) by (subst b_hi; apply slice_length; lia).
  assert (Hal : limbs a_lo) by (subst a_lo; apply limbs_firstn; exact Ha).
  assert (Hbl : limbs b_lo) by (subst b_lo; apply limbs_firstn; exact Hb).
  assert (Hah : limbs a_hi) by (subst a_hi; apply slice_limbs; exact Ha).
  assert (Hbh : limbs b_hi) by (subst b_hi; apply slice_limbs; exact Hb).
  pose proof (lval_bound a_lo Hal) as HA0. rewrite Hall in HA0.
  pose proof (lval_bound b_lo Hbl) as HB0. rewrite Hbll in HB0.
  assert (HA1 : 0 <= lval a_hi < Bp n).
  { pose proof (lval_bound a_hi Hah) as Hx. rewrite Hahl in Hx. pose proof (Bp_mono tna n ltac:(lia)). lia. }
  assert (HB1 : 0 <= lval b_hi < Bp n).
  { pose proof (lval_bound b_hi Hbh) as Hx. rewrite Hbhl in Hx. pose proof (Bp_mono tnb n ltac:(lia)). lia. }
  pose proof (rec_diffs_spec a_lo a_hi b_lo b_hi n tna tnb Hal Hah Hbl Hbh Hall Hahl Hbll Hbhl ltac:(lia) ltac:(lia)) as Hdf.
  rewrite EM. clear EM.
  destruct (rec_diffs a_lo a_hi b_lo b_hi tna tnb (cmp_part_words a_lo a_hi tna) (cmp_part_words b_hi b_lo tnb)) as [[[t0 t1] ng]|].
  -
    cbv zeta. destruct Hdf as (D1 & D2 & D3 & D4 & D5).
    set (td := splice (splice t 0 t0) n t1).
    assert (L1 : length (splice t 0 t0) = length t) by (apply splice_length; lia).
    assert (Htdl : limbs td) by (subst td; apply splice_limbs; [apply splice_limbs|]; assumption).
    assert (Htdlen : length td = length t) by (subst td; rewrite splice_length; lia).
    assert (E0 : slice td 0 n = t0) by (subst td; rewrite slice_splice_below by lia; apply slice_splice_same'; lia).
    assert (E1 : slice td n n = t1) by (subst td; apply slice_splice_same'; lia).
    unfold join_ok. destruct ((n =? 8) && (da =? 0) && (db =? 0))%nat eqn:Ec8.
    + apply andb_prop in Ec8. destruct Ec8 as [Ec8 E3]. apply andb_prop in Ec8. destruct Ec8 as [En E2].
      apply Nat.eqb_eq in En, E2, E3. subst da db.
      assert (Etna : tna = n) by (subst tna; lia). assert (Etnb : tnb = n) by (subst tnb; lia).
      unfold comba_ok. fold tna tnb. fold a_lo a_hi b_lo b_hi.
      replace (slice td 0 8) with (slice td 0 n) by (rewrite En; reflexivity).
      replace (slice td 8 8) with (slice td n n) by (rewrite En; reflexivity).
      rewrite E0, E1.
      destruct (mul_comba8_spec a_lo b_lo Hal Hbl ltac:(lia) ltac:(lia)) as (C1 & C2 & C3).
      destruct (mul_comba8_spec a_hi b_hi Hah Hbh ltac:(lia) ltac:(lia)) as (C4 & C5 & C6).
      destruct (mul_comba8_spec t0 t1 D1 D3 ltac:(lia) ltac:(lia)) as (C7 & C8 & C9).
      assert (L2 : length (splice r 0 (mul_comba8 a_lo b_lo)) = length r) by (apply splice_length; lia).
      apply (kc_ok_finish n ng _ _ (lval a_lo) (lval a_hi) (lval b_lo) (lval b_hi)); try assumption.
      * apply splice_limbs; [apply splice_limbs|]; assumption.
      * rewrite splice_length; lia.
      * apply splice_limbs; assumption.
      * rewrite splice_length; lia.
      * rewrite slice_splice_below by lia. rewrite (slice_splice_same' r 0 _ (2 * n)) by lia. exact C3.
      * rewrite (slice_splice_same' _ (2 * n) _ (2 * n)) by lia. exact C6.
      * rewrite (slice_splice_same' td (2 * n) _ (2 * n)) by lia. rewrite C9. exact D5.
    + replace (2 * (2 * n))%nat with (4 * n)%nat by lia.
      pose proof (mul_recursive_spec k' (slice td 0 n) (slice td n n) 0 0 (slice td (2 * n) (2 * n)) (skipn (4 * n) td)
                    ltac:(rewrite E0; exact D1) ltac:(rewrite E1; exact D3) (slice_limbs _ _ _ Htdl) (limbs_skipn _ _ Htdl)
                    Hk' ltac:(lia) ltac:(lia)
                    ltac:(rewrite slice_length by lia; fold n; lia) ltac:(rewrite slice_length by lia; fold n; lia)
                    ltac:(rewrite slice_length by lia; fold n; lia) ltac:(rewrite length_skipn; lia)) as Hx.
      destruct (mul_recursive k' (slice td 0 n) (slice td n n) 0 0 (slice td (2 * n) (2 * n)) (skipn (4 * n) td)) as [tm p0].
      destruct Hx as (X1 & X2 & X3 & X4 & X5). rewrite slice_length in X2 by lia. rewrite length_skipn in X5.
      rewrite splice_tail by (rewrite length_app; lia).
      apply gen2_ok_intro; try assumption; try lia.
      * apply limbs_firstn. exact Htdl.
      * apply firstn_length_le. lia.
      * rewrite X3, E0, E1. exact D5.
  -
    cbv zeta. unfold zero_ok. destruct ((n =? 8) && (da =? 0) && (db =? 0))%nat eqn:Ec8.
    + apply andb_prop in Ec8. destruct Ec8 as [Ec8 E3]. apply andb_prop in Ec8. destruct Ec8 as [En E2].
      apply Nat.eqb_eq in En, E2, E3. subst da db.
      assert (Etna : tna = n) by (subst tna; lia). assert (Etnb : tnb = n) by (subst tnb; lia).
      unfold comba_ok. fold tna tnb. fold a_lo a_hi b_lo b_hi.
      replace 16%nat with (2 * n)%nat by lia.
      destruct (mul_comba8_spec a_lo b_lo Hal Hbl ltac:(lia) ltac:(lia)) as (C1 & C2 & C3).
      destruct (mul_comba8_spec a_hi b_hi Hah Hbh ltac:(lia) ltac:(lia)) as (C4 & C5 & C6).
      assert (L2 : length (splice r 0 (mul_comba8 a_lo b_lo)) = length r) by (apply splice_length; lia).
      apply (kc_ok_finish n false _ _ (lval a_lo) (lval a_hi) (lval b_lo) (lval b_hi)); try assumption.
      * apply splice_limbs; [apply splice_limbs|]; assumption.
      * rewrite splice_length; lia.
      * apply splice_limbs; [assumption | apply limbs_repeat; exact limb_0].
      * rewrite splice_length; rewrite ?repeat_length; lia.
      * rewrite slice_splice_below by lia. rewrite (slice_splice_same' r 0 _ (2 * n)) by lia. exact C3.
      * rewrite (slice_splice_same' _ (2 * n) _ (2 * n)) by lia. exact C6.
      * rewrite (slice_splice_same' t (2 * n) _ (2 * n)) by (rewrite ?repeat_length; lia). rewrite lval_repeat0. symmetry. exact Hdf.
    + replace (2 * (2 * n))%nat with (4 * n)%nat by lia.
      assert (ES : splice t (2 * n) (repeat 0 (2 * n)) = firstn (2 * n) t ++ repeat 0 (2 * n) ++ skipn (4 * n) t).
      { unfold splice. rewrite repeat_length. replace (2 * n + 2 * n)%nat with (4 * n)%nat by lia. reflexivity. }
      rewrite ES.
      apply gen2_ok_intro; try assumption; try lia.
      * apply limbs_firstn. exact Ht.
      * apply firstn_length_le. lia.
      * apply limbs_repeat. exact limb_0.
      * apply repeat_length.
      * apply limbs_skipn. exact Ht.
      * rewrite length_skipn. lia.
      * rewrite lval_repeat0. symmetry. exact Hdf.
Qed.

Lemma mul_recursive_comba : forall k a b r t, Nat.pow 2 k = 8%nat ->
  mul_recursive k a b 0 0 r t = (splice r 0 (mul_comba8 (firstn 8 a) (firstn 8 b)), t).
Proof. intros k a b r t E. destruct k as [|k0]; cbn [mul_recursive]; rewrite E; reflexivity. Qed.

Lemma mul_recursive_small : forall k a b da db r t, (Nat.pow 2 k < 16)%nat ->
  ((Nat.pow 2 k =? 8) && (da =? 0) && (db =? 0))%nat = false ->
  mul_recursive k a b da db r t =
  (let n2 := Nat.pow 2 k in
   let r1 := splice r 0 (mul_normal (firstn (n2 - da) a) (firstn (n2 - db) b)) in
   let r2 := if (0 <? da + db)%nat then splice r1 (2 * n2 - da - db) (repeat 0 (da + db)) else r1 in
   (r2, t)).
Proof.
  intros k a b da db r t Hs Hc. apply Nat.ltb_lt in Hs.
  destruct k as [|k0]; cbn [mul_recursive]; rewrite Hc, Hs; reflexivity.
Qed.
