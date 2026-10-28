(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Spec Require Import SoftFloat.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Spec Require Import FmtFp.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10 Require Import F_frexpl_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.F10 Require Import FmtFp_split.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Lemma land15_bound : forall a, 0 <= Z.land a 32767 <= 32767.
Proof.
  intros a. change 32767 with (Z.ones 15). rewrite Z.land_ones by lia.
  pose proof (Z.mod_pos_bound a (2^15) ltac:(lia)). change (Z.ones 15) with (2^15 - 1). lia.
Qed.

Lemma frexpl_e_range : forall x x' e', frexpl FREXPL_FUEL x 0 = Some (x', e') -> -16501 <= e' <= 16384.
Proof.
  intros x x' e' H. change FREXPL_FUEL with 2%nat in H. rewrite frexpl_unfold in H. cbv zeta in H.
  pose proof (land15_bound (Z.shiftr (hi64 x) 48)) as U1.
  destruct (Z.eqb_spec (Z.land (Z.shiftr (hi64 x) 48) 32767) 0) as [E0|E0].
  - destruct (negb _).
    + rewrite frexpl_unfold in H. cbv zeta in H.
      set (x2 := f128_mul x (f128_of_d D_0x1p120)) in H.
      pose proof (land15_bound (Z.shiftr (hi64 x2) 48)) as U2.
      destruct (Z.eqb_spec (Z.land (Z.shiftr (hi64 x2) 48) 32767) 0) as [E2|E2].
      * destruct (negb _); [discriminate H|]. inversion H; subst. lia.
      * destruct (Z.eqb_spec (Z.land (Z.shiftr (hi64 x2) 48) 32767) 32767); inversion H; subst; lia.
    + inversion H; subst. lia.
  - destruct (Z.eqb_spec (Z.land (Z.shiftr (hi64 x) 48) 32767) 32767); inversion H; subst; lia.
Qed.

Lemma lxor_signbit_range : forall y, 0 <= y < 2^128 -> 0 <= Z.lxor y F128_SIGNBIT < 2^128.
Proof.
  intros y Hy. unfold F128_SIGNBIT. change 0x80000000000000000000000000000000 with (2^127).
  split. { apply Z.lxor_nonneg. lia. }
  destruct (Z.eq_dec (Z.lxor y (2^127)) 0) as [->|NZ]; [lia|].
  apply Z.log2_lt_pow2. { pose proof (Z.lxor_nonneg y (2^127)). lia. }
  eapply Z.le_lt_trans. { apply Z.log2_lxor; lia. }
  apply Z.max_lub_lt.
  - destruct (Z.eq_dec y 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia.
  - rewrite Z.log2_pow2 by lia. lia.
Qed.

Lemma fmt_fp_dig_step : forall k big z y,
  fmt_fp_dig (S k) (big, z, y) =
   (let zv := f128_to_u32 y in
    let y' := f128_mul (f128_of_i32 1000000000) (f128_sub y (f128_of_u32 zv)) in
    if negb (f128_le y' F128_ZERO =? 0) then fmt_fp_dig k (zupd big z zv, z + 1, y')
    else Some (zupd big z zv, z + 1, y')).
Proof. reflexivity. Qed.

Lemma fmt_fp_dig_z : forall k big z y big' z' y',
  fmt_fp_dig k (big, z, y) = Some (big', z', y') -> z < z' /\ length big' = length big.
Proof.
  induction k as [|k IH]; intros big z y big' z' y' H; [discriminate H|].
  rewrite fmt_fp_dig_step in H. cbv zeta in H.
  destruct (negb _).
  - apply IH in H. rewrite zupd_length in H. lia.
  - set (v := f128_to_u32 y) in H. clearbody v. set (y2 := f128_mul _ _) in H. clearbody y2.
    injection H as <- <- <-. rewrite zupd_length. lia.
Qed.

Lemma fmt_fp_strip_step : forall k big a z,
  fmt_fp_strip (S k) big a z = (if (a <? z) && (znth big (z - 1) =? 0) then fmt_fp_strip k big a (z - 1) else Some z).
Proof. reflexivity. Qed.
Lemma fmt_fp_strip_res : forall k big a z z', fmt_fp_strip k big a z = Some z' -> (a <= z)%Z -> a <= z' <= z.
Proof.
  induction k as [|k IH]; intros big a z z' H Haz; [discriminate H|].
  rewrite fmt_fp_strip_step in H. destruct (Z.ltb_spec0 a z); cbn [andb] in H.
  - destruct (znth big (z - 1) =? 0). { apply IH in H; lia. } inversion H; lia.
  - inversion H; lia.
Qed.

Lemma fmt_fp_up_inner_step : forall sh k a big d c,
  fmt_fp_up_inner sh (S k) a (big, d, c) =
   (if a <=? d then
      let x := Z.shiftl (znth big d) sh + c in
      fmt_fp_up_inner sh k a (zupd big d (x mod 1000000000), d - 1, u32 (x / 1000000000))
    else Some (big, d, c)).
Proof. reflexivity. Qed.
Lemma fmt_fp_up_inner_res : forall sh k a big d c big' d' c',
  fmt_fp_up_inner sh k a (big, d, c) = Some (big', d', c') -> (a - 1 <= d)%Z -> d' = a - 1 /\ length big' = length big.
Proof.
  induction k as [|k IH]; intros a big d c big' d' c' H Hd; [discriminate H|].
  rewrite fmt_fp_up_inner_step in H. destruct (Z.leb_spec0 a d).
  - cbv zeta in H. apply IH in H; [|lia]. rewrite zupd_length in H. exact H.
  - inversion H; subst. lia.
Qed.

Lemma fmt_fp_up_step : forall k big a z e2,
  fmt_fp_up (S k) (big, a, z, e2) =
    (if 0 <? e2 then match fmt_fp_up_body (big, a, z, e2) with Some s => fmt_fp_up k s | None => None end
     else Some (big, a, z, e2)).
Proof. reflexivity. Qed.

Lemma fmt_fp_up_nonneg : forall k big a z e2 big' a' z' e2',
  fmt_fp_up k (big, a, z, e2) = Some (big', a', z', e2') -> (0 <= e2)%Z -> e2' = 0%Z.
Proof.
  induction k as [|k IH]; intros big a z e2 big' a' z' e2' H He; [discriminate H|].
  rewrite fmt_fp_up_step in H. destruct (Z.ltb_spec0 0 e2).
  - unfold fmt_fp_up_body in H.
    destruct (fmt_fp_up_inner _ _ _ _) as [[[b1 d1] c1]|]; [|discriminate H].
    destruct (negb (c1 =? 0)).
    + destruct (fmt_fp_strip _ _ _ _) as [z1|]; [|discriminate H]. apply IH in H; lia.
    + destruct (fmt_fp_strip _ _ _ _) as [z1|]; [|discriminate H]. apply IH in H; lia.
  - inversion H; subst. lia.
Qed.

Lemma znth_over : forall l i, (length l <= Z.to_nat i)%nat -> znth l i = 0%Z.
Proof.
  intros l i H. unfold znth. destruct (i <? 0); [reflexivity|]. apply nth_overflow. exact H.
Qed.

Lemma fmt_fp_dn_step : forall k p t r big a z e2,
  fmt_fp_dn (S k) p t r (big, a, z, e2) =
    (if e2 <? 0 then match fmt_fp_dn_body p t r (big, a, z, e2) with Some s => fmt_fp_dn k p t r s | None => None end
     else Some (big, a, z, e2)).
Proof. reflexivity. Qed.

Lemma fmt_fp_dn_inner_step : forall sh k z big d c,
  fmt_fp_dn_inner sh (S k) z (big, d, c) =
   (if d <? z then
      fmt_fp_dn_inner sh k z (zupd big d (u32 (Z.shiftr (znth big d) sh + c)), d + 1,
                              u32 (Z.shiftr 1000000000 sh * Z.land (znth big d) (Z.shiftl 1 sh - 1)))
    else Some (big, d, c)).
Proof. reflexivity. Qed.

Lemma fmt_fp_dn_inner_res : forall sh k z big d c big' d' c',
  fmt_fp_dn_inner sh k z (big, d, c) = Some (big', d', c') -> (d <= z)%Z ->
  d' = z /\ length big' = length big /\ ((0 <= c)%Z -> (0 <= c')%Z)
  /\ (forall i, (i < d \/ z <= i)%Z -> znth big' i = znth big i).
Proof.
  induction k as [|k IH]; intros z big d c big' d' c' H Hd; [discriminate H|].
  rewrite fmt_fp_dn_inner_step in H. destruct (Z.ltb_spec0 d z).
  - apply IH in H; [|lia]. rewrite zupd_length in H. destruct H as (H1 & H2 & H3 & H4).
    split; [exact H1|]. split; [exact H2|]. split.
    + intros _. apply H3. unfold u32. apply Z.mod_pos_bound. lia.
    + intros i Hi. rewrite H4 by lia. apply znth_zupd_neq. lia.
  - inversion H; subst. repeat split; auto; lia.
Qed.

Fixpoint fmt_fp_dn_iter (n : nat) (p t r : Z) (s : list Z * Z * Z * Z) {struct n} : option (list Z * Z * Z * Z) :=
  match n with
  | O => Some s
  | S n' => let '(big, a, z, e2) := s in
            if e2 <? 0 then match fmt_fp_dn_body p t r s with Some s' => fmt_fp_dn_iter n' p t r s' | None => None end
            else None
  end.

Definition dn_ok (s : list Z * Z * Z * Z) : Prop :=
  let '(big, a, z, e2) := s in (a <= z <= 127)%Z /\ (a = z -> znth big a <> 0%Z).

Definition dn_good (p t r : Z) (s : list Z * Z * Z * Z) : Prop :=
  forall n big a z e2, fmt_fp_dn_iter n p t r s = Some (big, a, z, e2) -> (e2 < 0)%Z -> dn_ok (big, a, z, e2).

Lemma dn_good_now : forall p t r big a z e2, dn_good p t r (big, a, z, e2) -> (e2 < 0)%Z -> dn_ok (big, a, z, e2).
Proof. intros p t r big a z e2 G He. exact (G O big a z e2 eq_refl He). Qed.

Lemma dn_good_next : forall p t r big a z e2 s', dn_good p t r (big, a, z, e2) -> (e2 < 0)%Z ->
  fmt_fp_dn_body p t r (big, a, z, e2) = Some s' -> dn_good p t r s'.
Proof.
  intros p t r big a z e2 s' G He HB n big1 a1 z1 e21 Hn He1.
  apply (G (S n) big1 a1 z1 e21); [|exact He1]. cbn [fmt_fp_dn_iter].
  rewrite (proj2 (Z.ltb_lt e2 0) He). rewrite HB. exact Hn.
Qed.

Lemma fmt_fp_dn_iter_end : forall k n p t r s s1 s2,
  fmt_fp_dn_iter n p t r s = Some s1 -> fmt_fp_dn k p t r s1 = Some s2 -> fmt_fp_dn (n + k) p t r s = Some s2.
Proof.
  induction n as [|n IH]; intros p t r s s1 s2 Hn Hk.
  - cbn in Hn. inversion Hn; subst. exact Hk.
  - cbn [fmt_fp_dn_iter] in Hn. destruct s as [[[big a] z] e2].
    destruct (e2 <? 0) eqn:E; [|discriminate Hn].
    destruct (fmt_fp_dn_body p t r (big, a, z, e2)) as [s'|] eqn:HB; [|discriminate Hn].
    cbn [Nat.add]. rewrite fmt_fp_dn_step, E, HB. eapply IH; eauto.
Qed.

Lemma fmt_fp_dn_more : forall k k' p t r s s2,
  fmt_fp_dn k p t r s = Some s2 -> fmt_fp_dn (k + k') p t r s = Some s2.
Proof.
  induction k as [|k IH]; intros k' p t r s s2 H; [discriminate H|].
  cbn [Nat.add]. destruct s as [[[big a] z] e2]. rewrite fmt_fp_dn_step in H |- *.
  destruct (e2 <? 0); [|exact H].
  destruct (fmt_fp_dn_body p t r (big, a, z, e2)) as [s'|]; [|discriminate H]. apply IH. exact H.
Qed.

Definition dn_a1 (bigI : list Z) (a : Z) : Z := if znth bigI a =? 0 then a + 1 else a.
Definition dn_bz (bigI : list Z) (z cI : Z) : list Z * Z := if negb (cI =? 0) then (zupd bigI z cI, z + 1) else (bigI, z).
Definition dn_zf (t r need a1 z1 : Z) : Z :=
  let b := if Z.lor t 32 =? CHR_f then r else a1 in if need <? z1 - b then b + need else z1.

Lemma fmt_fp_dn_body_some : forall p t r big a z e2 s1,
  fmt_fp_dn_body p t r (big, a, z, e2) = Some s1 ->
  exists bigI dI cI, fmt_fp_dn_inner (Z.min 9 (- e2)) BIG_FUEL z (big, a, 0) = Some (bigI, dI, cI) /\
    s1 = (fst (dn_bz bigI z cI), dn_a1 bigI a,
          dn_zf t r (1 + u32 (p + LDBL_MANT_DIG / 3 + 8) / 9) (dn_a1 bigI a) (snd (dn_bz bigI z cI)),
          (e2 + Z.min 9 (- e2))%Z).
Proof.
  intros p t r big a z e2 s1 H. unfold fmt_fp_dn_body in H.
  destruct (fmt_fp_dn_inner (Z.min 9 (- e2)) BIG_FUEL z (big, a, 0)) as [[[bigI dI] cI]|] eqn:HI; [|discriminate H].
  exists bigI, dI, cI. split; [reflexivity|].
  unfold dn_bz, dn_a1, dn_zf. cbv beta iota zeta in H.
  destruct (negb (cI =? 0)); cbv beta iota zeta in H; cbv beta iota zeta; injection H as E; subst s1; reflexivity.
Qed.

Definition zero_from (big : list Z) (z : Z) : Prop := forall i, (z <= i)%Z -> znth big i = 0%Z.

Lemma zero_from_zrepeat : forall n z, (0 <= z)%Z -> zero_from (zrepeat 0 n) z.
Proof.
  intros n z Hz i Hi. unfold znth, zrepeat. destruct (i <? 0); [reflexivity|].
  destruct (nth_in_or_default (Z.to_nat i) (repeat 0%Z (Z.to_nat n)) 0%Z) as [H|H]; [|exact H].
  apply repeat_spec in H. exact H.
Qed.

Lemma fmt_fp_dig_zero : forall k big z y big' z' y',
  fmt_fp_dig k (big, z, y) = Some (big', z', y') -> (0 <= z)%Z -> zero_from big z -> zero_from big' z'.
Proof.
  induction k as [|k IH]; intros big z y big' z' y' H Hz ZF; [discriminate H|].
  rewrite fmt_fp_dig_step in H. cbv zeta in H.
  set (v := f128_to_u32 y) in H. clearbody v. set (y2 := f128_mul _ _) in H. clearbody y2.
  assert (ZF' : zero_from (zupd big z v) (z + 1)).
  { intros i Hi. rewrite znth_zupd_neq by lia. apply ZF. lia. }
  destruct (negb _).
  - eapply IH; [exact H | lia | exact ZF'].
  - injection H as <- <- <-. exact ZF'.
Qed.

Lemma fmt_fp_strip_zeros : forall k big a z z', fmt_fp_strip k big a z = Some z' ->
  forall i, (z' <= i < z)%Z -> znth big i = 0%Z.
Proof.
  induction k as [|k IH]; intros big a z z' H i Hi; [discriminate H|].
  rewrite fmt_fp_strip_step in H. destruct (Z.ltb_spec0 a z); cbn [andb] in H.
  - destruct (Z.eqb_spec (znth big (z - 1)) 0).
    + destruct (Z.eq_dec i (z - 1)) as [->|Hne]; [assumption|]. eapply IH; [exact H|]. lia.
    + injection H as <-. lia.
  - injection H as <-. lia.
Qed.

Lemma fmt_fp_up_inner_same : forall sh k a big d c big' d' c',
  fmt_fp_up_inner sh k a (big, d, c) = Some (big', d', c') ->
  (forall i, (d < i)%Z -> znth big' i = znth big i) /\ (c' <> c -> (a <= d)%Z).
Proof.
  induction k as [|k IH]; intros a big d c big' d' c' H; [discriminate H|].
  rewrite fmt_fp_up_inner_step in H. destruct (Z.leb_spec0 a d).
  - cbv zeta in H. apply IH in H. destruct H as [H _]. split; [|lia].
    intros i Hi. rewrite H by lia. apply znth_zupd_neq. lia.
  - injection H as <- <- <-. split; [reflexivity | intros X; exfalso; exact (X eq_refl)].
Qed.

Lemma fmt_fp_up_zero : forall k big a z e2 big' a' z' e2',
  fmt_fp_up k (big, a, z, e2) = Some (big', a', z', e2') -> zero_from big z -> zero_from big' z'.
Proof.
  induction k as [|k IH]; intros big a z e2 big' a' z' e2' H ZF; [discriminate H|].
  rewrite fmt_fp_up_step in H. destruct (0 <? e2).
  - unfold fmt_fp_up_body in H.
    destruct (fmt_fp_up_inner (Z.min 29 e2) BIG_FUEL a (big, z - 1, 0)) as [[[b1 d1] c1]|] eqn:HI; [|discriminate H].
    pose proof (fmt_fp_up_inner_same _ _ _ _ _ _ _ _ _ HI) as [SAME Hc1].
    assert (ZF1 : zero_from b1 z) by (intros i Hi; rewrite SAME by lia; apply ZF; lia).
    destruct (Z.eqb_spec c1 0); cbn [negb] in H.
    + destruct (fmt_fp_strip BIG_FUEL b1 a z) as [z1|] eqn:HS; [|discriminate H].
      eapply IH; [exact H|]. intros i Hi. destruct (Z.lt_ge_cases i z); [|apply ZF1; lia].
      eapply fmt_fp_strip_zeros; [exact HS | lia].
    + destruct (fmt_fp_strip BIG_FUEL (zupd b1 (a - 1) c1) (a - 1) z) as [z1|] eqn:HS; [|discriminate H].
      eapply IH; [exact H|]. intros i Hi. destruct (Z.lt_ge_cases i z).
      * eapply fmt_fp_strip_zeros; [exact HS | lia].
      * rewrite znth_zupd_neq by lia. apply ZF1. lia.
  - injection H as <- <- <- <-. exact ZF.
Qed.

Definition dig_words_fact (yv fl : Z) : Prop :=
  forall y1 fr e0 y e2 b' z' y',
    fst (fst (ffp_sign yv fl)) = y1 ->
    frexpl FREXPL_FUEL y1 0 = Some (fr, e0) ->
    (let y2 := f128_mul fr (f128_of_i32 2) in
     let ynz := negb (f128_le y2 F128_ZERO =? 0) in
     y = (if ynz then f128_mul y2 (f128_of_d D_0x1p28) else y2) /\ e2 = (if ynz then e0 - 1 - 28 else e0)%Z) ->
    fmt_fp_dig DIG_FUEL (zrepeat 0 128, (if e2 <? 0 then 0 else 122)%Z, y) = Some (b', z', y') ->
    (z' <= (if e2 <? 0 then 0 else 122) + 6)%Z.

Definition e2_range_fact (yv fl : Z) : Prop :=
  forall y1 fr e0,
    fst (fst (ffp_sign yv fl)) = y1 ->
    frexpl FREXPL_FUEL y1 0 = Some (fr, e0) ->
    (let y2 := f128_mul fr (f128_of_i32 2) in
     let ynz := negb (f128_le y2 F128_ZERO =? 0) in
     let e2 := if ynz then e0 - 1 - 28 else e0 in
     -1102 <= e2 <= 1024)%Z.

Definition dn_phase_fact (yv fl p t : Z) : Prop :=
  forall y1 fr e0 y e2 b' z' y' s,
    fst (fst (ffp_sign yv fl)) = y1 ->
    frexpl FREXPL_FUEL y1 0 = Some (fr, e0) ->
    (let y2 := f128_mul fr (f128_of_i32 2) in
     let ynz := negb (f128_le y2 F128_ZERO =? 0) in
     y = (if ynz then f128_mul y2 (f128_of_d D_0x1p28) else y2) /\ e2 = (if ynz then e0 - 1 - 28 else e0)%Z) ->
    fmt_fp_dig DIG_FUEL (zrepeat 0 128, (if e2 <? 0 then 0 else 122)%Z, y) = Some (b', z', y') ->
    fmt_fp_up UP_FUEL (b', (if e2 <? 0 then 0 else 122)%Z, z', e2) = Some s ->
    dn_good (if p <? 0 then 6 else p)%Z t (if e2 <? 0 then 0 else 122)%Z s.
