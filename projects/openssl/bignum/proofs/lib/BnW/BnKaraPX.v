(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnWordsCorrect BnKara BnKaraCorrect.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnKaraX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Stages.
  Variables (RES : list Z * list Z) (fuel' k n : nat) (neg : bool) (a b : list Z) (tna tnb : nat).
  Notation a_lo := (firstn n a).
  Notation a_hi := (slice a n tna).
  Notation b_lo := (firstn n b).
  Notation b_hi := (slice b n tnb).
  Notation k' := (k - 1)%nat.
  Notation i := (Nat.pow 2 (k - 1)).

  Definition pcomba_ok (R T : list Z) : Prop :=
    let T1 := splice T (2 * n) (mul_comba8 (slice T 0 n) (slice T n n)) in
    let R1 := splice R 0 (mul_comba8 a_lo b_lo) in
    let R2 := splice R1 (2 * n) (mul_normal a_hi b_hi) in
    let R3 := splice R2 (2 * n + tna + tnb) (repeat 0 (2 * n - tna - tnb)) in
    kc_ok RES n neg R3 T1.

  Definition pj0_ok (R T : list Z) : Prop :=
    let '(o, p2) := mul_recursive k' a_hi b_hi (i - tna) (i - tnb) (slice R (2 * n) (2 * i)) (skipn (4 * n) T) in
    let R2 := splice R (2 * n) o in
    let R3 := splice R2 (2 * n + 2 * i) (repeat 0 (2 * n - 2 * i)) in
    kc_ok RES n neg R3 (splice T (4 * n) p2).

  Definition pjpos_ok (R T : list Z) : Prop :=
    let '(o, p2) := mul_part_recursive fuel' k' a_hi b_hi (tna - i) (tnb - i) (slice R (2 * n) (4 * i)) (skipn (4 * n) T) in
    let R2 := splice R (2 * n) o in
    let R3 := splice R2 (2 * n + tna + tnb) (repeat 0 (2 * n - tna - tnb)) in
    kc_ok RES n neg R3 (splice T (4 * n) p2).

  Definition pfpart_ok (kf : nat) (R T : list Z) : Prop :=
    let ii := Nat.pow 2 kf in
    let '(o, p2) := mul_part_recursive fuel' kf a_hi b_hi (tna - ii) (tnb - ii) (slice R (2 * n) (4 * ii)) (skipn (4 * n) T) in
    kc_ok RES n neg (splice R (2 * n) o) (splice T (4 * n) p2).
  Definition pfrec_ok (kf : nat) (R T : list Z) : Prop :=
    let ii := Nat.pow 2 kf in
    let '(o, p2) := mul_recursive kf a_hi b_hi (ii - tna) (ii - tnb) (slice R (2 * n) (2 * ii)) (skipn (4 * n) T) in
    kc_ok RES n neg (splice R (2 * n) o) (splice T (4 * n) p2).

  Definition pfind_ok (ki : nat) (R T : list Z) : Prop :=
    let '(kf, part) := kara_find ki tna tnb in
    if part then pfpart_ok kf R T else pfrec_ok kf R T.

  Definition pjneg_ok (R T : list Z) : Prop :=
    let R2 := splice R (2 * n) (repeat 0 (2 * n)) in
    if ((tna <? 16) && (tnb <? 16))%nat then kc_ok RES n neg (splice R2 (2 * n) (mul_normal a_hi b_hi)) T
    else pfind_ok (k' - 1) R2 T.

  Definition pgen3_ok (R T : list Z) : Prop :=
    let mx := Nat.max tna tnb in
    if (mx =? i)%nat then pj0_ok R T else if (i <? mx)%nat then pjpos_ok R T else pjneg_ok R T.

  Definition pgen2_ok (R T : list Z) : Prop :=
    let '(rl, p1) := mul_recursive k a_lo b_lo 0 0 (slice R 0 (2 * n)) (skipn (4 * n) T) in
    pgen3_ok (splice R 0 rl) (splice T (4 * n) p1).

  Definition pjoin_ok (R T : list Z) : Prop :=
    if (n =? 8)%nat then pcomba_ok R T
    else let '(tm, p0) := mul_recursive k (slice T 0 n) (slice T n n) 0 0 (slice T (2 * n) (2 * n)) (skipn (4 * n) T) in
         pgen2_ok R (splice T (2 * n) (tm ++ p0)).
End Stages.

Section PartDiffsLit.
  Variables (al ah bl bh : list Z) (tna tnb : nat).
  Notation ah_al := (fst (sub_part_words ah al tna)).
  Notation al_ah := (fst (sub_part_words al ah tna)).
  Notation bl_bh := (fst (sub_part_words bl bh tnb)).
  Notation bh_bl := (fst (sub_part_words bh bl tnb)).
  Lemma part_diffs_m1_m1 : part_diffs al ah bl bh tna tnb (-1) (-1) = (ah_al, bl_bh, false). Proof. reflexivity. Qed.
  Lemma part_diffs_m1_0 : part_diffs al ah bl bh tna tnb (-1) 0 = (ah_al, bh_bl, true). Proof. reflexivity. Qed.
  Lemma part_diffs_m1_p1 : part_diffs al ah bl bh tna tnb (-1) 1 = (ah_al, bh_bl, true). Proof. reflexivity. Qed.
  Lemma part_diffs_0_m1 : part_diffs al ah bl bh tna tnb 0 (-1) = (al_ah, bl_bh, true). Proof. reflexivity. Qed.
  Lemma part_diffs_0_0 : part_diffs al ah bl bh tna tnb 0 0 = (al_ah, bl_bh, true). Proof. reflexivity. Qed.
  Lemma part_diffs_0_p1 : part_diffs al ah bl bh tna tnb 0 1 = (al_ah, bl_bh, true). Proof. reflexivity. Qed.
  Lemma part_diffs_p1_m1 : part_diffs al ah bl bh tna tnb 1 (-1) = (al_ah, bl_bh, true). Proof. reflexivity. Qed.
  Lemma part_diffs_p1_0 : part_diffs al ah bl bh tna tnb 1 0 = (al_ah, bh_bl, false). Proof. reflexivity. Qed.
  Lemma part_diffs_p1_p1 : part_diffs al ah bl bh tna tnb 1 1 = (al_ah, bh_bl, false). Proof. reflexivity. Qed.
End PartDiffsLit.

Lemma kara_find_lt : forall ki tna tnb, (Nat.pow 2 ki < tna \/ Nat.pow 2 ki < tnb)%nat -> kara_find ki tna tnb = (ki, true).
Proof.
  intros ki tna tnb H. assert (E : ((Nat.pow 2 ki <? tna) || (Nat.pow 2 ki <? tnb))%nat = true).
  { apply orb_true_iff. destruct H as [H|H]; [left|right]; apply Nat.ltb_lt; exact H. }
  destruct ki; cbn [kara_find]; rewrite E; reflexivity.
Qed.
Lemma kara_find_eq : forall ki tna tnb, (tna <= Nat.pow 2 ki)%nat -> (tnb <= Nat.pow 2 ki)%nat ->
  (Nat.pow 2 ki = tna \/ Nat.pow 2 ki = tnb)%nat -> kara_find ki tna tnb = (ki, false).
Proof.
  intros ki tna tnb Ha Hb H.
  assert (E1 : ((Nat.pow 2 ki <? tna) || (Nat.pow 2 ki <? tnb))%nat = false).
  { apply orb_false_iff. split; apply Nat.ltb_ge; assumption. }
  assert (E2 : ((Nat.pow 2 ki =? tna) || (Nat.pow 2 ki =? tnb))%nat = true).
  { apply orb_true_iff. destruct H as [H|H]; [left|right]; apply Nat.eqb_eq; exact H. }
  destruct ki; cbn [kara_find]; rewrite E1, E2; reflexivity.
Qed.
Lemma kara_find_S : forall ki tna tnb, (tna < Nat.pow 2 (S ki))%nat -> (tnb < Nat.pow 2 (S ki))%nat ->
  kara_find (S ki) tna tnb = kara_find ki tna tnb.
Proof.
  intros ki tna tnb Ha Hb.
  assert (E1 : ((Nat.pow 2 (S ki) <? tna) || (Nat.pow 2 (S ki) <? tnb))%nat = false).
  { apply orb_false_iff. split; apply Nat.ltb_ge; lia. }
  assert (E2 : ((Nat.pow 2 (S ki) =? tna) || (Nat.pow 2 (S ki) =? tnb))%nat = false).
  { apply orb_false_iff. split; apply Nat.eqb_neq; lia. }
  cbn [kara_find]. rewrite E1, E2. reflexivity.
Qed.

Lemma splice_0_app : forall (X A : list Z) m, length A = m -> splice X 0 A = A ++ skipn m X.
Proof. intros X A m <-. unfold splice. cbn [firstn app Nat.add]. reflexivity. Qed.

Lemma slice_app_r : forall (A B : list Z) m o len, length A = m -> slice (A ++ B) (m + o) len = slice B o len.
Proof.
  intros A B m o len <-. unfold slice. rewrite skipn_app. rewrite skipn_all2 by lia. cbn [app].
  replace (length A + o - length A)%nat with o by lia. reflexivity.
Qed.

Lemma slice_app_r0 : forall (A B : list Z) m len, length A = m -> slice (A ++ B) m len = slice B 0 len.
Proof. intros A B m len H. rewrite <- (slice_app_r A B m 0 len H). f_equal. lia. Qed.

Lemma splice_app_r : forall (A B Zs : list Z) m off, length A = m -> splice (A ++ B) (m + off) Zs = A ++ splice B off Zs.
Proof.
  intros A B Zs m off <-. unfold splice.
  rewrite firstn_app. rewrite (firstn_all2 (n := length A + off) A) by lia.
  replace (length A + off - length A)%nat with off by lia.
  rewrite skipn_app. rewrite (skipn_all2 (n := length A + off + length Zs) A) by lia. cbn [app].
  replace (length A + off + length Zs - length A)%nat with (off + length Zs)%nat by lia.
  rewrite <- app_assoc. reflexivity.
Qed.

Lemma splice_app_r0 : forall (A B Zs : list Z) m, length A = m -> splice (A ++ B) m Zs = A ++ splice B 0 Zs.
Proof. intros A B Zs m H. rewrite <- (splice_app_r A B Zs m 0 H). f_equal. lia. Qed.

Lemma slice_repeat0 : forall m len, (len <= m)%nat -> slice (repeat 0 m) 0 len = repeat 0 len.
Proof.
  intros m len H. apply list_eq_nth; [rewrite slice_length, repeat_length; rewrite ?repeat_length; lia|].
  intros x Hx. rewrite slice_length in Hx by (rewrite repeat_length; lia). rewrite nth_slice by lia.
  rewrite !nth_repeat. reflexivity.
Qed.

Lemma kc_ok_leaf : forall n (neg : bool) (rl rh0 F tm p2 : list Z) A0 A1 B0 B1,
  limbs rl -> length rl = (2 * n)%nat -> limbs rh0 -> length rh0 = (2 * n)%nat ->
  limbs F -> length F = (2 * n)%nat -> limbs tm -> length tm = (2 * n)%nat -> limbs p2 ->
  lval rl = A0 * B0 -> lval rh0 = A1 * B1 -> (if neg then - lval tm else lval tm) = (A0 - A1) * (B1 - B0) ->
  0 <= A0 < Bp n -> 0 <= A1 < Bp n -> 0 <= B0 < Bp n -> 0 <= B1 < Bp n ->
  kc_ok (kara_combine n neg (rl ++ rh0) (F ++ tm ++ p2)) n neg (rl ++ rh0) (F ++ tm ++ p2).
Proof.
  intros n neg rl rh0 F tm p2 A0 A1 B0 B1 L1 L2 H1 H2 HF HFl Htm Html Hp2 V1 V2 V3 HA0 HA1 HB0 HB1.
  assert (S1 : slice (rl ++ rh0) 0 (2 * n) = rl) by (unfold slice; cbn [skipn]; apply firstn_app_len; exact L2).
  assert (S2 : slice (rl ++ rh0) (2 * n) (2 * n) = rh0) by (unfold slice; rewrite skipn_app_len by exact L2; apply firstn_all2; lia).
  assert (S3 : slice (F ++ tm ++ p2) (2 * n) (2 * n) = tm) by (unfold slice; rewrite skipn_app_len by exact HFl; apply firstn_app_len; exact Html).
  apply (kc_ok_finish n neg (rl ++ rh0) (F ++ tm ++ p2) A0 A1 B0 B1); try assumption.
  - apply limbs_app; assumption.
  - rewrite length_app. lia.
  - apply limbs_app; [exact HF | apply limbs_app; assumption].
  - rewrite !length_app. lia.
  - rewrite S1. exact V1.
  - rewrite S2. exact V2.
  - rewrite S3. exact V3.
Qed.

Lemma scratch_skip : forall (F tm p : list Z) n, length F = (2 * n)%nat -> length tm = (2 * n)%nat -> skipn (4 * n) (F ++ tm ++ p) = p.
Proof. intros F tm p n HF Htm. rewrite app_assoc. apply skipn_app_len. rewrite length_app. lia. Qed.

Lemma scratch_put : forall (F tm p p' : list Z) n, length F = (2 * n)%nat -> length tm = (2 * n)%nat -> length p' = length p ->
  splice (F ++ tm ++ p) (4 * n) p' = F ++ tm ++ p'.
Proof.
  intros F tm p p' n HF Htm Hp. rewrite splice_tail by (rewrite !length_app; lia).
  rewrite app_assoc, firstn_app_len by (rewrite length_app; lia). rewrite <- app_assoc. reflexivity.
Qed.

Lemma pgen3_intro : forall fuel' k a b tna tnb (rl rh F tm p1 : list Z) (neg : bool),
  let n := Nat.pow 2 k in
  let a_lo := firstn n a in let a_hi := slice a n tna in let b_lo := firstn n b in let b_hi := slice b n tnb in
  limbs a -> limbs b -> (4 <= k)%nat -> (k <= S fuel')%nat ->
  (tna < n)%nat -> (tnb < n)%nat -> (tna <= tnb + 1)%nat -> (tnb <= tna + 1)%nat ->
  length a = (n + tna)%nat -> length b = (n + tnb)%nat ->
  limbs rl -> length rl = (2 * n)%nat -> limbs rh -> length rh = (2 * n)%nat ->
  limbs F -> length F = (2 * n)%nat -> limbs tm -> length tm = (2 * n)%nat -> limbs p1 -> (4 * n <= length p1)%nat ->
  lval rl = lval a_lo * lval b_lo ->
  (if neg then - lval tm else lval tm) = (lval a_lo - lval a_hi) * (lval b_hi - lval b_lo) ->
  pgen3_ok
    (let '(r1, t1') :=
       (let '(rh0, p2) :=
          (let i := Nat.pow 2 (k - 1) in
           if (Nat.max tna tnb =? i)%nat
           then let '(o, p2) := mul_recursive (k - 1) a_hi b_hi (i - tna) (i - tnb) (slice rh 0 (2 * i)) p1 in
                (splice (splice rh 0 o) (2 * i) (repeat 0 (2 * n - 2 * i)), p2)
           else if (i <? Nat.max tna tnb)%nat
                then let '(o, p2) := mul_part_recursive fuel' (k - 1) a_hi b_hi (tna - i) (tnb - i) (slice rh 0 (4 * i)) p1 in
                     (splice (splice rh 0 o) (tna + tnb) (repeat 0 (2 * n - tna - tnb)), p2)
                else let rh1 := repeat 0 (2 * n) in
                     if ((tna <? 16) && (tnb <? 16))%nat then (splice rh1 0 (mul_normal a_hi b_hi), p1)
                     else let '(ki, part) := kara_find (k - 1 - 1) tna tnb in
                          let i0 := Nat.pow 2 ki in
                          if part
                          then let '(o, p2) := mul_part_recursive fuel' ki a_hi b_hi (tna - i0) (tnb - i0) (slice rh1 0 (4 * i0)) p1 in
                               (splice rh1 0 o, p2)
                          else let '(o, p2) := mul_recursive ki a_hi b_hi (i0 - tna) (i0 - tnb) (slice rh1 0 (2 * i0)) p1 in
                               (splice rh1 0 o, p2)) in
        (rl ++ rh0, F ++ tm ++ p2)) in
     kara_combine n neg r1 t1')
    fuel' k n neg a b tna tnb (rl ++ rh) (F ++ tm ++ p1).
Proof.
  intros fuel' k a b tna tnb rl rh F tm p1 neg n a_lo a_hi b_lo b_hi Ha Hb Hk4 Hkf Htna Htnb Hd1 Hd2 Hla Hlb
         Hrl Hrll Hrh Hrhl HF HFl Htm Html Hp1 Hp1l V1 V3.
  assert (Hn8 : (16 <= n)%nat).
  { subst n. replace k with (4 + (k - 4))%nat by lia. rewrite Nat.pow_add_r. pose proof (pow2_pos (k - 4)). cbn [Nat.pow] in *. lia. }
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
  pose proof (lval_bound a_hi Hah) as HA1'. rewrite Hahl in HA1'.
  pose proof (lval_bound b_hi Hbh) as HB1'. rewrite Hbhl in HB1'.
  assert (HA1 : 0 <= lval a_hi < Bp n) by (pose proof (Bp_mono tna n ltac:(lia)); lia).
  assert (HB1 : 0 <= lval b_hi < Bp n) by (pose proof (Bp_mono tnb n ltac:(lia)); lia).
  assert (Hhib : lval a_hi * lval b_hi < Bp (tna + tnb)) by (rewrite Bp_add; apply mul_bound_lt; assumption).
  set (k' := (k - 1)%nat).
  assert (Epow : n = (2 * Nat.pow 2 k')%nat).
  { subst n k'. replace k with (S (k - 1)) at 1 by lia. cbn [Nat.pow]. lia. }
  cbv zeta. fold k'. set (i := Nat.pow 2 k') in *.
  unfold pgen3_ok. fold k' i. fold a_hi b_hi.
  assert (ESK : skipn (4 * n) (F ++ tm ++ p1) = p1) by (apply scratch_skip; assumption).
  destruct (Nat.eqb_spec (Nat.max tna tnb) i) as [Ej0|Nj0].
  -
    unfold pj0_ok. fold k' i a_hi b_hi.
    rewrite (slice_app_r0 rl rh (2 * n) (2 * i) Hrll), ESK.
    pose proof (scratch_rec_le k') as Hsck'. fold i in Hsck'.
    pose proof (mul_recursive_spec k' a_hi b_hi (i - tna) (i - tnb) (slice rh 0 (2 * i)) p1 Hah Hbh (slice_limbs _ _ _ Hrh) Hp1
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(fold i; lia) ltac:(fold i; lia)
                  ltac:(rewrite slice_length by lia; fold i; lia) ltac:(lia)) as Hx.
    destruct (mul_recursive k' a_hi b_hi (i - tna) (i - tnb) (slice rh 0 (2 * i)) p1) as [o p2].
    destruct Hx as (O1 & O2 & O3 & O4 & O5). rewrite slice_length in O2 by lia.
    rewrite (splice_app_r0 rl rh o (2 * n) Hrll).
    rewrite (splice_app_r rl (splice rh 0 o) (repeat 0 (2 * n - 2 * i)) (2 * n) (2 * i) Hrll).
    rewrite (scratch_put F tm p1 p2 n HFl Html O5).
    rewrite two_splices_all by (rewrite ?repeat_length; lia).
    apply (kc_ok_leaf n neg rl (o ++ repeat 0 (2 * n - 2 * i)) F tm p2 (lval a_lo) (lval a_hi) (lval b_lo) (lval b_hi)); try assumption.
    + apply limbs_app; [exact O1 | apply limbs_repeat; exact limb_0].
    + rewrite length_app, repeat_length. lia.
    + rewrite lval_app, lval_repeat0. lia.
  - destruct (Nat.ltb_spec i (Nat.max tna tnb)) as [Hjpos|Hjneg].
    +
      unfold pjpos_ok. fold k' i a_hi b_hi.
      rewrite (slice_app_r0 rl rh (2 * n) (4 * i) Hrll), ESK.
      pose proof (mul_part_recursive_spec fuel' k' a_hi b_hi (tna - i)%nat (tnb - i)%nat (slice rh 0 (4 * i)) p1 Hah Hbh (slice_limbs _ _ _ Hrh) Hp1
                    ltac:(lia) ltac:(lia) ltac:(fold i; lia) ltac:(fold i; lia) ltac:(lia) ltac:(lia)
                    ltac:(fold i; lia) ltac:(fold i; lia) ltac:(rewrite slice_length by lia; fold i; lia) ltac:(fold i; lia)) as Hx.
      destruct (mul_part_recursive fuel' k' a_hi b_hi (tna - i) (tnb - i) (slice rh 0 (4 * i)) p1) as [o p2].
      destruct Hx as (O1 & O2 & O3 & O4 & O5). rewrite slice_length in O2 by lia.
      rewrite (splice_app_r0 rl rh o (2 * n) Hrll).
      replace (2 * n + tna + tnb)%nat with (2 * n + (tna + tnb))%nat by lia.
      rewrite (splice_app_r rl (splice rh 0 o) (repeat 0 (2 * n - tna - tnb)) (2 * n) (tna + tnb) Hrll).
      rewrite (scratch_put F tm p1 p2 n HFl Html O5).
      assert (Ho : splice rh 0 o = o) by (apply splice_all; lia). rewrite Ho.
      pose proof (zero_fill_small o (tna + tnb) O1 ltac:(lia) ltac:(rewrite O3; exact Hhib)) as Hz. cbv zeta in Hz.
      replace (length o - (tna + tnb))%nat with (2 * n - tna - tnb)%nat in Hz by lia.
      destruct Hz as (Z1 & Z2 & Z3).
      apply (kc_ok_leaf n neg rl _ F tm p2 (lval a_lo) (lval a_hi) (lval b_lo) (lval b_hi)); try assumption; lia.
    +
      unfold pjneg_ok. fold k' i a_hi b_hi.
      rewrite (splice_app_r0 rl rh (repeat 0 (2 * n)) (2 * n) Hrll).
      rewrite (splice_all rh (repeat 0 (2 * n))) by (rewrite repeat_length; lia).
      set (rh1 := repeat 0 (2 * n)).
      assert (Hrh1 : limbs rh1) by (subst rh1; apply limbs_repeat; exact limb_0).
      assert (Hrh1l : length rh1 = (2 * n)%nat) by (subst rh1; apply repeat_length).
      destruct ((tna <? 16) && (tnb <? 16))%nat eqn:Esm.
      * rewrite (splice_app_r0 rl rh1 (mul_normal a_hi b_hi) (2 * n) Hrll).
        pose proof (mul_normal_into_zeros a_hi b_hi (2 * n) Hah Hbh ltac:(lia)) as Hz. cbv zeta in Hz. fold rh1 in Hz.
        destruct Hz as (Z1 & Z2 & Z3).
        apply (kc_ok_leaf n neg rl _ F tm p1 (lval a_lo) (lval a_hi) (lval b_lo) (lval b_hi)); try assumption.
      * assert (Hmx16 : (16 <= Nat.max tna tnb)%nat).
        { apply andb_false_elim in Esm. destruct Esm as [E|E]; apply Nat.ltb_ge in E; lia. }
        assert (Hk'1 : (1 <= k')%nat) by lia.
        assert (Ei' : i = (2 * Nat.pow 2 (k' - 1))%nat).
        { subst i. replace k' with (S (k' - 1)) at 1 by lia. cbn [Nat.pow]. lia. }
        unfold pfind_ok. fold a_hi b_hi.
        pose proof (kara_find_spec (k' - 1) tna tnb ltac:(lia) ltac:(lia)) as Hfind.
        destruct (kara_find (k' - 1) tna tnb) as [ki part]. cbv zeta in Hfind. destruct Hfind as (F1 & F2 & F3).
        cbv zeta. set (i0 := Nat.pow 2 ki) in *.
        assert (Hki : (4 <= ki)%nat).
        { destruct (Nat.le_gt_cases 4 ki) as [|Hlt]; [assumption|exfalso].
          assert (i0 <= 8)%nat; [|lia]. subst i0.
          assert (ki = 0 \/ ki = 1 \/ ki = 2 \/ ki = 3)%nat as [->|[->|[->| ->]]] by lia; cbn; lia. }
        assert (Hi0n : (4 * i0 <= 2 * n)%nat) by lia.
        destruct part.
        -- unfold pfpart_ok. cbv zeta. fold i0 a_hi b_hi.
           rewrite (slice_app_r0 rl rh1 (2 * n) (4 * i0) Hrll), ESK.
           pose proof (mul_part_recursive_spec fuel' ki a_hi b_hi (tna - i0)%nat (tnb - i0)%nat (slice rh1 0 (4 * i0)) p1 Hah Hbh (slice_limbs _ _ _ Hrh1) Hp1
                         ltac:(lia) ltac:(lia) ltac:(fold i0; lia) ltac:(fold i0; lia) ltac:(lia) ltac:(lia)
                         ltac:(fold i0; lia) ltac:(fold i0; lia) ltac:(rewrite slice_length by lia; fold i0; lia) ltac:(fold i0; lia)) as Hx.
           destruct (mul_part_recursive fuel' ki a_hi b_hi (tna - i0) (tnb - i0) (slice rh1 0 (4 * i0)) p1) as [o p2].
           destruct Hx as (O1 & O2 & O3 & O4 & O5). rewrite slice_length in O2 by lia.
           rewrite (splice_app_r0 rl rh1 o (2 * n) Hrll).
           rewrite (scratch_put F tm p1 p2 n HFl Html O5).
           apply (kc_ok_leaf n neg rl (splice rh1 0 o) F tm p2 (lval a_lo) (lval a_hi) (lval b_lo) (lval b_hi)); try assumption.
           ++ apply splice_limbs; assumption.
           ++ rewrite splice_length; lia.
           ++ rewrite lval_splice by lia. subst rh1. rewrite slice_repeat0 by lia. rewrite !lval_repeat0, Bp_0, O3. ring.
        -- unfold pfrec_ok. cbv zeta. fold i0 a_hi b_hi.
           rewrite (slice_app_r0 rl rh1 (2 * n) (2 * i0) Hrll), ESK.
           pose proof (scratch_rec_le ki) as Hscki. fold i0 in Hscki.
           pose proof (mul_recursive_spec ki a_hi b_hi (i0 - tna) (i0 - tnb) (slice rh1 0 (2 * i0)) p1 Hah Hbh (slice_limbs _ _ _ Hrh1) Hp1
                         ltac:(lia) ltac:(lia) ltac:(lia) ltac:(fold i0; lia) ltac:(fold i0; lia)
                         ltac:(rewrite slice_length by lia; fold i0; lia) ltac:(lia)) as Hx.
           destruct (mul_recursive ki a_hi b_hi (i0 - tna) (i0 - tnb) (slice rh1 0 (2 * i0)) p1) as [o p2].
           destruct Hx as (O1 & O2 & O3 & O4 & O5). rewrite slice_length in O2 by lia.
           rewrite (splice_app_r0 rl rh1 o (2 * n) Hrll).
           rewrite (scratch_put F tm p1 p2 n HFl Html O5).
           apply (kc_ok_leaf n neg rl (splice rh1 0 o) F tm p2 (lval a_lo) (lval a_hi) (lval b_lo) (lval b_hi)); try assumption.
           ++ apply splice_limbs; assumption.
           ++ rewrite splice_length; lia.
           ++ rewrite lval_splice by lia. subst rh1. rewrite slice_repeat0 by lia. rewrite !lval_repeat0, Bp_0, O3. ring.
Qed.

Lemma part_staged : forall fuel' k a b tna tnb r t,
  limbs a -> limbs b -> limbs r -> limbs t ->
  (3 <= k)%nat -> (k <= S fuel')%nat ->
  (tna < Nat.pow 2 k)%nat -> (tnb < Nat.pow 2 k)%nat -> (tna <= tnb + 1)%nat -> (tnb <= tna + 1)%nat ->
  length a = (Nat.pow 2 k + tna)%nat -> length b = (Nat.pow 2 k + tnb)%nat ->
  length r = (4 * Nat.pow 2 k)%nat -> (8 * Nat.pow 2 k <= length t)%nat ->
  let n := Nat.pow 2 k in
  let '(t0, t1, neg) := part_diffs (firstn n a) (slice a n tna) (firstn n b) (slice b n tnb) tna tnb
                          (cmp_part_words (firstn n a) (slice a n tna) tna) (cmp_part_words (slice b n tnb) (firstn n b) tnb) in
  pjoin_ok (mul_part_recursive (S fuel') k a b tna tnb r t) fuel' k n neg a b tna tnb r (splice (splice t 0 t0) n t1).
Proof.
  intros fuel' k a b tna tnb r t Ha Hb Hr Ht Hk3 Hkf Htna Htnb Hd1 Hd2 Hla Hlb Hrl Htl n.
  cbn [mul_part_recursive]. fold n.
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
  pose proof (lval_bound a_lo Hal) as HA0. rewrite Hall in HA0.
  pose proof (lval_bound b_lo Hbl) as HB0. rewrite Hbll in HB0.
  pose proof (lval_bound a_hi Hah) as HA1'. rewrite Hahl in HA1'.
  pose proof (lval_bound b_hi Hbh) as HB1'. rewrite Hbhl in HB1'.
  assert (HA1 : 0 <= lval a_hi < Bp n) by (pose proof (Bp_mono tna n ltac:(lia)); lia).
  assert (HB1 : 0 <= lval b_hi < Bp n) by (pose proof (Bp_mono tnb n ltac:(lia)); lia).
  pose proof (part_diffs_spec a_lo a_hi b_lo b_hi n tna tnb Hal Hah Hbl Hbh Hall Hahl Hbll Hbhl ltac:(lia) ltac:(lia)) as Hdf.
  destruct (part_diffs a_lo a_hi b_lo b_hi tna tnb (cmp_part_words a_lo a_hi tna) (cmp_part_words b_hi b_lo tnb)) as [[t0 t1] neg].
  destruct Hdf as (D1 & D2 & D3 & D4 & D5).
  set (td := splice (splice t 0 t0) n t1).
  assert (Ltd0 : length (splice t 0 t0) = length t) by (apply splice_length; lia).
  assert (Htdl : limbs td) by (subst td; apply splice_limbs; [apply splice_limbs|]; assumption).
  assert (Htdlen : length td = length t) by (subst td; rewrite splice_length; lia).
  assert (E0 : slice td 0 n = t0) by (subst td; rewrite slice_splice_below by lia; apply slice_splice_same'; lia).
  assert (E1 : slice td n n = t1) by (subst td; apply slice_splice_same'; lia).
  unfold pjoin_ok. destruct (Nat.eqb_spec n 8) as [E8|N8].
  -
    unfold pcomba_ok. cbv zeta. fold a_lo a_hi b_lo b_hi.
    replace (slice td 0 8) with (slice td 0 n) by (rewrite E8; reflexivity).
    replace (slice td 8 8) with (slice td n n) by (rewrite E8; reflexivity).
    rewrite E0, E1.
    destruct (mul_comba8_spec a_lo b_lo Hal Hbl ltac:(lia) ltac:(lia)) as (C1 & C2 & C3).
    destruct (mul_comba8_spec t0 t1 D1 D3 ltac:(lia) ltac:(lia)) as (C7 & C8 & C9).
    destruct (mul_normal_spec a_hi b_hi Hah Hbh) as (N1 & N2 & N3).
    assert (N3' : length (mul_normal a_hi b_hi) = (tna + tnb)%nat).
    { rewrite N3, Hahl, Hbhl. destruct (Nat.eqb_spec tna 0); destruct (Nat.eqb_spec tnb 0); cbn [orb]; lia. }
    set (P := mul_normal a_hi b_hi) in *. set (Zs := repeat 0 (2 * n - tna - tnb)).
    assert (LZ : length Zs = (2 * n - tna - tnb)%nat) by (subst Zs; apply repeat_length).
    assert (L1 : length (splice r 0 (mul_comba8 a_lo b_lo)) = length r) by (apply splice_length; lia).
    assert (L2 : length (splice (splice r 0 (mul_comba8 a_lo b_lo)) (2 * n) P) = length r) by (rewrite splice_length; lia).
    apply (kc_ok_finish n neg _ _ (lval a_lo) (lval a_hi) (lval b_lo) (lval b_hi)); try assumption.
    + apply splice_limbs; [apply splice_limbs; [apply splice_limbs|]|subst Zs; apply limbs_repeat; exact limb_0]; assumption.
    + rewrite splice_length; lia.
    + apply splice_limbs; assumption.
    + rewrite splice_length; lia.
    + rewrite slice_splice_below by lia. rewrite slice_splice_below by lia.
      rewrite (slice_splice_same' r 0 _ (2 * n)) by lia. exact C3.
    + replace (2 * n + tna + tnb)%nat with (2 * n + (tna + tnb))%nat by lia.
      replace (2 * n)%nat with ((tna + tnb) + length Zs)%nat at 4 by lia.
      rewrite slice_two_splices by lia. rewrite lval_app. subst Zs. rewrite lval_repeat0. lia.
    + rewrite (slice_splice_same' td (2 * n) _ (2 * n)) by lia. rewrite C9. exact D5.
  -
    assert (Hk4 : (4 <= k)%nat).
    { destruct (Nat.eq_dec k 3) as [->|]; [cbn in n; lia|lia]. }
    replace (2 * (2 * n))%nat with (4 * n)%nat by lia.
    pose proof (scratch_rec_le k) as Hsck. fold n in Hsck.
    pose proof (mul_recursive_spec k (slice td 0 n) (slice td n n) 0 0 (slice td (2 * n) (2 * n)) (skipn (4 * n) td)
                  ltac:(rewrite E0; exact D1) ltac:(rewrite E1; exact D3) (slice_limbs _ _ _ Htdl) (limbs_skipn _ _ Htdl) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(rewrite slice_length by lia; fold n; lia) ltac:(rewrite slice_length by lia; fold n; lia)
                  ltac:(rewrite slice_length by lia; fold n; lia) ltac:(rewrite length_skipn; lia)) as Hx.
    destruct (mul_recursive k (slice td 0 n) (slice td n n) 0 0 (slice td (2 * n) (2 * n)) (skipn (4 * n) td)) as [tm p0].
    destruct Hx as (M1 & M2 & M3 & M4 & M5). rewrite slice_length in M2 by lia. rewrite E0, E1 in M3. rewrite length_skipn in M5.
    rewrite (splice_tail td (2 * n) (tm ++ p0)) by (rewrite length_app; lia).
    assert (HFl : length (firstn (2 * n) td) = (2 * n)%nat) by (apply firstn_length_le; lia).
    unfold pgen2_ok. fold a_lo b_lo.
    rewrite (scratch_skip (firstn (2 * n) td) tm p0 n HFl M2).
    pose proof (mul_recursive_spec k a_lo b_lo 0 0 (slice r 0 (2 * n)) p0 Hal Hbl (slice_limbs _ _ _ Hr) M4 ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(fold n; lia) ltac:(fold n; lia) ltac:(rewrite slice_length by lia; fold n; lia) ltac:(lia)) as Hx.
    destruct (mul_recursive k a_lo b_lo 0 0 (slice r 0 (2 * n)) p0) as [rl p1].
    destruct Hx as (L1 & L2 & L3 & L4 & L5). rewrite slice_length in L2 by lia.
    rewrite (splice_0_app r rl (2 * n) L2).
    rewrite (scratch_put (firstn (2 * n) td) tm p0 p1 n HFl M2 L5).
    assert (Erh : slice r (2 * n) (2 * n) = skipn (2 * n) r) by (unfold slice; apply firstn_all2; rewrite length_skipn; lia).
    rewrite Erh.
    apply (pgen3_intro fuel' k a b tna tnb rl (skipn (2 * n) r) (firstn (2 * n) td) tm p1 neg); try assumption; try (fold n; lia).
    + apply limbs_skipn. exact Hr.
    + rewrite length_skipn. fold n. lia.
    + apply limbs_firstn. exact Htdl.
    + fold n a_lo a_hi b_lo b_hi. rewrite M3. exact D5.
Qed.
