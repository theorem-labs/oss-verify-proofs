(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Spec Require Import Prelim.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Spec Require Import SoftFloat.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Spec Require Import FmtFp.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.F9 Require Import FmtFp_split.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Notation "'let?' x ':=' e 'in' k" :=
  (match e with Some x => k | None => None end)
  (at level 200, x pattern, e at level 100, k at level 200, only parsing).

Definition ffp_Rd (j r : Z) : Z := r + 1 + (Z.quot (j + 9 * LDBL_MAX_EXP) 9 - LDBL_MAX_EXP).
Definition ffp_Ri (j : Z) : option (Z * Z) :=
  let j := j + 9 * LDBL_MAX_EXP in
  let j := Z.rem j 9 in
  fmt_fp_powi TEN_FUEL (10, j + 1).

Definition ffp_R6 (big : list Z) (a r d i x e round small : Z) : option (list Z * Z * Z * Z) :=
  let big := zupd big d (znth big d - x) in
  if negb (f128_le (f128_add round small) round =? 0) then
    let big := zupd big d (u32 (znth big d + i)) in
    let? (big, d, a) := fmt_fp_carry BIG_FUEL (big, d, a) in
    let? (i, e) := fmt_fp_cnt TEN_FUEL (znth big a) (10, 9 * (r - a)) in
    Some (big, a, d, e)
  else Some (big, a, d, e).

Definition ffp_flip (prefix pl round small : Z) : Z * Z :=
  if negb (pl =? 0) && (znth PREFIX_STR prefix =? CHR_minus) then
    let m1 := f128_of_i32 (-1) in
    let round := f128_mul round m1 in
    let small := f128_mul small m1 in
    (round, small)
  else (round, small).
Definition ffp_R5 (prefix pl : Z) (big : list Z) (a r d i x e round small : Z) : option (list Z * Z * Z * Z) :=
  let '(round, small) := ffp_flip prefix pl round small in
  ffp_R6 big a r d i x e round small.

Definition ffp_smallD (z d i x : Z) : Z :=
  if x <? Z.quot i 2 then D_0_5
  else if (x =? Z.quot i 2) && (d + 1 =? z) then D_1_0
  else D_1_5.

Definition ffp_small (z d i x : Z) : Z :=
  if x <? Z.quot i 2 then f128_of_d D_0_5
  else if (x =? Z.quot i 2) && (d + 1 =? z) then f128_of_d D_1_0
  else f128_of_d D_1_5.
Lemma ffp_small_D : forall z d i x, ffp_small z d i x = f128_of_d (ffp_smallD z d i x).
Proof. intros. unfold ffp_small, ffp_smallD. destruct (x <? Z.quot i 2); [reflexivity|]. destruct (_ && _); reflexivity. Qed.

Definition ffp_R4 (prefix pl : Z) (big : list Z) (a r z d i x e round : Z) : option (list Z * Z * Z * Z) :=
  ffp_R5 prefix pl big a r d i x e round (ffp_small z d i x).

Definition ffp_odd (big : list Z) (a d i : Z) : bool :=
  negb (Z.land (znth big d / i) 1 =? 0)
  || ((i =? 1000000000) && (a <? d) && negb (Z.land (znth big (d - 1)) 1 =? 0)).

Definition ffp_R3 (prefix pl : Z) (big : list Z) (a r z d i x e : Z) : option (list Z * Z * Z * Z) :=
  let round := f128_div (f128_of_i32 2) K_LDBL_EPSILON in
  let round := if ffp_odd big a d i then f128_add round (f128_of_i32 2) else round in
  ffp_R4 prefix pl big a r z d i x e round.

Definition ffp_R2 (prefix pl : Z) (big : list Z) (a r z e d i : Z) : option (list Z * Z * Z * Z) :=
  let x := (znth big d) mod i in
  let? (big, a, d, e) :=
    if negb (x =? 0) || negb (d + 1 =? z) then ffp_R3 prefix pl big a r z d i x e
    else Some (big, a, d, e) in
  let z := if d + 1 <? z then d + 1 else z in
  Some (big, a, z, e).

Lemma ffp_R_eq : forall t p prefix pl big a r z e j,
  ffp_R t p prefix pl big a r z e j =
    (if j <? 9 * (z - r - 1) then
       let? (i, j') := ffp_Ri j in ffp_R2 prefix pl big a r z e (ffp_Rd j r) i
     else Some (big, a, z, e)).
Proof. intros. reflexivity. Qed.

Lemma fmt_fp_powi_step : forall k i j,
  fmt_fp_powi (S k) (i, j) = (if j <? 9 then fmt_fp_powi k (i * 10, j + 1) else Some (i, j)).
Proof. reflexivity. Qed.

Lemma fmt_fp_powi_res : forall k m jj i' j',
  (0 <= m)%Z -> (jj <= 9)%Z -> (Z.to_nat (9 - jj) < k)%nat ->
  fmt_fp_powi k (10 ^ m, jj) = Some (i', j') -> i' = 10 ^ (m + 9 - jj) /\ j' = 9.
Proof.
  induction k as [|k IH]; intros m jj i' j' Hm Hj Hk H; [cbn in Hk; lia|].
  rewrite fmt_fp_powi_step in H. destruct (Z.ltb_spec0 jj 9).
  - replace (10 ^ m * 10) with (10 ^ (m + 1)) in H by (rewrite Z.pow_add_r by lia; change (10 ^ 1) with 10; lia).
    apply IH in H; [|lia|lia|lia]. destruct H as [-> ->]. split; [f_equal; lia|reflexivity].
  - injection H as <- <-. split; [f_equal; lia|lia].
Qed.

Lemma ffp_Ri_res : forall j i j', (-9 * LDBL_MAX_EXP <= j)%Z -> ffp_Ri j = Some (i, j') ->
  exists n, (1 <= n <= 9)%Z /\ i = 10 ^ n /\ n = 9 - Z.rem (j + 9 * LDBL_MAX_EXP) 9.
Proof.
  intros j i j' Hj H. unfold ffp_Ri in H.
  pose proof (Z.rem_bound_pos (j + 9 * LDBL_MAX_EXP) 9 ltac:(lia) ltac:(lia)) as R.
  set (jr := Z.rem (j + 9 * LDBL_MAX_EXP) 9) in *.
  change 10 with (10 ^ 1) in H. apply fmt_fp_powi_res in H; [|lia|lia|unfold TEN_FUEL; lia].
  destruct H as [-> _]. exists (1 + 9 - (jr + 1)). split; [lia|]. split; [reflexivity|lia].
Qed.

Lemma fmt_fp_carry_step : forall k big d a,
  fmt_fp_carry (S k) (big, d, a) =
    (if 999999999 <? znth big d then fmt_fp_carry k (fmt_fp_carry_body (big, d, a)) else Some (big, d, a)).
Proof. reflexivity. Qed.

Lemma fmt_fp_carry_body_eq : forall big d a,
  fmt_fp_carry_body (big, d, a) =
    (let big1 := zupd big d 0 in
     let a1 := if d - 1 <? a then a - 1 else a in
     let big2 := if d - 1 <? a then zupd big1 (a - 1) 0 else big1 in
     (zupd big2 (d - 1) (u32 (znth big2 (d - 1) + 1)), d - 1, a1)).
Proof. intros. unfold fmt_fp_carry_body. destruct (d - 1 <? a); reflexivity. Qed.

Lemma fmt_fp_carry_res : forall k big d a big' d' a',
  fmt_fp_carry k (big, d, a) = Some (big', d', a') -> (a <= d)%Z ->
  (a' <= a)%Z /\ (a' <= d' <= d)%Z /\ length big' = length big
  /\ (forall i, (i < a' \/ d < i)%Z -> (0 <= i)%Z -> znth big' i = znth big i).
Proof.
  induction k as [|k IH]; intros big d a big' d' a' H Had; [discriminate H|].
  rewrite fmt_fp_carry_step in H. destruct (999999999 <? znth big d).
  - rewrite fmt_fp_carry_body_eq in H. cbv zeta in H.
    apply IH in H; [|destruct (Z.ltb_spec0 (d - 1) a); lia].
    destruct H as (H1 & H2 & H3 & H4).
    destruct (Z.ltb_spec0 (d - 1) a).
    + rewrite !zupd_length in H3. split; [lia|]. split; [lia|]. split; [exact H3|].
      intros i Hi Hi0. rewrite H4 by lia. rewrite !znth_zupd_neq by lia. reflexivity.
    + rewrite !zupd_length in H3. split; [lia|]. split; [lia|]. split; [exact H3|].
      intros i Hi Hi0. rewrite H4 by lia. rewrite !znth_zupd_neq by lia. reflexivity.
  - injection H as <- <- <-. split; [lia|]. split; [lia|]. split; [reflexivity|]. intros; reflexivity.
Qed.

Lemma fmt_fp_carry_wb : forall k big d a big' d' a' z,
  fmt_fp_carry k (big, d, a) = Some (big', d', a') ->
  (a <= d < z)%Z -> (z <= 128)%Z -> length big = 128%nat -> (0 <= a')%Z ->
  (forall i, (a <= i < z)%Z -> i <> d -> 0 <= znth big i < 1000000000) ->
  (0 <= znth big d)%Z ->
  forall i, (a' <= i < z)%Z -> 0 <= znth big' i < 1000000000.
Proof.
  induction k as [|k IH]; intros big d a big' d' a' z H Hd Hz LB Ha' WB Hd0; [discriminate H|].
  rewrite fmt_fp_carry_step in H. destruct (Z.ltb_spec0 999999999 (znth big d)) as [Hgt|Hle].
  - rewrite fmt_fp_carry_body_eq in H. cbv zeta in H.
    pose proof (fmt_fp_carry_res _ _ _ _ _ _ _ H ltac:(destruct (Z.ltb_spec0 (d - 1) a); lia)) as (Q1 & Q2 & Q3 & Q4).
    assert (Hd1 : (0 <= d)%Z).
    { unfold znth in Hgt. destruct (Z.ltb_spec0 d 0); [cbn in Hgt; lia|lia]. }
    destruct (Z.ltb_spec0 (d - 1) a).
    + eapply (IH _ _ _ _ _ _ z H); [lia | lia | rewrite !zupd_length; exact LB | lia | |].
      * intros i Hi Hne. rewrite znth_zupd_neq by lia.
        destruct (Z.eq_dec i d) as [->|Hned].
        -- rewrite znth_zupd_neq by lia. rewrite znth_zupd_eq by (unfold zlength; rewrite zupd_length || idtac; lia). lia.
        -- rewrite znth_zupd_neq by lia. rewrite znth_zupd_neq by lia. apply WB; lia.
      * rewrite znth_zupd_eq by (unfold zlength; rewrite !zupd_length; lia). unfold u32. apply Z.mod_pos_bound. lia.
    + eapply (IH _ _ _ _ _ _ z H); [lia | lia | rewrite !zupd_length; exact LB | lia | |].
      * intros i Hi Hne. rewrite znth_zupd_neq by lia.
        destruct (Z.eq_dec i d) as [->|Hned].
        -- rewrite znth_zupd_eq by (unfold zlength; lia). lia.
        -- rewrite znth_zupd_neq by lia. apply WB; lia.
      * rewrite znth_zupd_eq by (unfold zlength; rewrite !zupd_length; lia). unfold u32. apply Z.mod_pos_bound. lia.
  - injection H as <- <- <-. intros i Hi. destruct (Z.eq_dec i d) as [->|Hne]; [lia|]. apply WB; lia.
Qed.
