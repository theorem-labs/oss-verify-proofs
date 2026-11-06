(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel BzLemmasHb.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma lor_lt_pow2 : forall a b k, 0 <= a < 2 ^ k -> 0 <= b < 2 ^ k -> 0 <= Z.lor a b < 2 ^ k.
Proof.
  intros a b k Ha Hb.
  assert (0 <= k) by (destruct (Z.neg_nonneg_cases k) as [K|K]; [rewrite Z.pow_neg_r in Ha by lia; lia| lia]).
  split; [apply Z.lor_nonneg; lia|].
  destruct (Z.eq_dec a 0) as [->|]; [rewrite Z.lor_0_l; lia|].
  destruct (Z.eq_dec b 0) as [->|]; [rewrite Z.lor_0_r; lia|].
  assert (0 < Z.lor a b) by (pose proof (proj2 (Z.lor_nonneg a b) ltac:(lia)); destruct (Z.eq_dec (Z.lor a b) 0) as [E|]; [apply Z.lor_eq_0_iff in E; lia|lia]).
  apply Z.log2_lt_pow2; [lia|]. rewrite Z.log2_lor by lia.
  apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia.
Qed.

Lemma land15_range : forall x, 0 <= Z.land x 15 < 16.
Proof. intros. change 15 with (Z.ones 4). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. Qed.
Lemma get_ll4_range : forall ll4 i, 0 <= get_ll4 ll4 i < 16.
Proof. intros. unfold get_ll4. apply land15_range. Qed.
Lemma get_ll_range : forall ll16 ll4 i, 0 <= ll16 i < 2 ^ 16 -> 0 <= get_ll ll16 ll4 i < 2 ^ 20.
Proof.
  intros. unfold get_ll. pose proof (get_ll4_range ll4 i).
  apply lor_lt_pow2; [lia|]. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 20) with (16 * 2 ^ 16). lia.
Qed.

Lemma lo8_mod : forall x, lo8 x = x mod 256.
Proof. intros. unfold lo8. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.
(* [comment removed for export] *)
Lemma lo8_small : forall x, 0 <= x < 256 -> lo8 x = x.
Proof. intros. rewrite lo8_mod. apply Z.mod_small. lia. Qed.
(* [comment removed for export] *)
Lemma lo8_lor_shiftl8 : forall x m, 0 <= m -> lo8 (Z.lor x (Z.shiftl m 8)) = lo8 x.
Proof.
  intros x m Hm. unfold lo8. change 255 with (Z.ones 8).
  apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec, Z.lor_spec, Z.testbit_ones by lia.
  destruct (Z.ltb_spec n 8).
  - rewrite Z.shiftl_spec_low by lia. now rewrite orb_false_r.
  - destruct (Z.leb_spec 0 n); cbn; [|lia]. now rewrite !andb_false_r.
Qed.
(* [comment removed for export] *)
Lemma lor_shiftl8_lt : forall x m, 0 <= x < 2 ^ 32 -> 0 <= m < 2 ^ 24 -> 0 <= Z.lor x (Z.shiftl m 8) < 2 ^ 32.
Proof.
  intros. apply lor_lt_pow2; [lia|]. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 32) with (2 ^ 24 * 2 ^ 8). nia.
Qed.

(* [comment removed for export] *)
Lemma land_65535 : forall v, Z.land v 65535 = v mod 2 ^ 16.
Proof. intros. change 65535 with (Z.ones 16). apply Z.land_ones. lia. Qed.
Lemma shiftr16_range : forall v, 0 <= v < 2 ^ 20 -> 0 <= Z.shiftr v 16 < 16.
Proof.
  intros. rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|].
  apply Z.div_lt_upper_bound; [lia|]. change (2 ^ 16 * 16) with (2 ^ 20). lia.
Qed.
Lemma lor_low_high : forall v, 0 <= v -> Z.lor (Z.land v 65535) (Z.shiftl (Z.shiftr v 16) 16) = v.
Proof.
  intros v Hv. change 65535 with (Z.ones 16).
  apply Z.bits_inj'. intros n Hn. rewrite Z.lor_spec, Z.land_spec, Z.testbit_ones, Z.shiftl_spec by lia.
  destruct (Z.ltb_spec n 16).
  - rewrite (Z.testbit_neg_r _ (n - 16)) by lia. destruct (Z.leb_spec 0 n); [|lia]. cbn. now rewrite andb_true_r, orb_false_r.
  - rewrite Z.shiftr_spec by lia. replace (n - 16 + 16) with n by lia.
    destruct (Z.leb_spec 0 n); [|lia]. cbn. rewrite andb_false_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma land1_mod : forall i, Z.land i 1 = i mod 2.
Proof. intros. change 1 with (Z.ones 1) at 1. rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma shiftr1_div : forall i, Z.shiftr i 1 = i / 2.
Proof. intros. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.
Lemma shl2_land4 : forall i, 0 <= i -> Z.land (Z.shiftl i 2) 4 = if Z.land i 1 =? 0 then 0 else 4.
Proof.
  intros i Hi. rewrite land1_mod.
  assert (E : forall n, 0 <= n -> Z.testbit (Z.land (Z.shiftl i 2) 4) n = (n =? 2) && Z.testbit i 0).
  { intros n Hn. rewrite Z.land_spec, Z.shiftl_spec by lia. change 4 with (2 ^ 2). rewrite Z.pow2_bits_eqb by lia.
    destruct (Z.eqb_spec 2 n), (Z.eqb_spec n 2); try lia.
    subst n. rewrite Z.sub_diag. apply andb_comm. }
  pose proof (Z.bit0_mod i) as B0.
  apply Z.bits_inj'. intros n Hn. rewrite E by lia.
  destruct (Z.testbit i 0); cbn [Z.b2z] in B0; rewrite <- B0; cbn [Z.eqb Pos.eqb].
  - change 4 with (2 ^ 2). rewrite Z.pow2_bits_eqb by lia. rewrite andb_true_r. apply Z.eqb_sym.
  - rewrite Z.bits_0. apply andb_false_r.
Qed.

(* [comment removed for export] *)
Definition nib_even_ok (B nb : Z) : bool :=
  let B' := Z.lor (Z.land B 240) nb in
  (Z.land (Z.shiftr B' 0) 15 =? nb) && (Z.land (Z.shiftr B' 4) 15 =? Z.land (Z.shiftr B 4) 15) && (0 <=? B') && (B' <? 256).
Definition nib_odd_ok (B nb : Z) : bool :=
  let B' := Z.lor (Z.land B 15) (Z.shiftl nb 4) in
  (Z.land (Z.shiftr B' 4) 15 =? nb) && (Z.land (Z.shiftr B' 0) 15 =? Z.land (Z.shiftr B 0) 15) && (0 <=? B') && (B' <? 256).
Definition zall (P : Z -> bool) (n : nat) : bool := forallb P (map Z.of_nat (seq 0 n)).
Lemma zall_spec : forall P n, zall P n = true -> forall z, 0 <= z < Z.of_nat n -> P z = true.
Proof.
  intros P n H z Hz. unfold zall in H. rewrite forallb_forall in H. apply H.
  apply in_map_iff. exists (Z.to_nat z). split; [lia|]. apply in_seq. lia.
Qed.
Lemma nib_check : zall (fun B => zall (fun nb => nib_even_ok B nb && nib_odd_ok B nb) 16) 256 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma nib_facts : forall B nb, 0 <= B < 256 -> 0 <= nb < 16 ->
  nib_even_ok B nb = true /\ nib_odd_ok B nb = true.
Proof.
  intros B nb HB Hnb.
  pose proof (zall_spec _ _ nib_check B ltac:(cbn; lia)) as H1. cbn beta in H1.
  pose proof (zall_spec _ _ H1 nb ltac:(cbn; lia)) as H2. cbn beta in H2.
  apply andb_prop in H2. exact H2.
Qed.

(* [comment removed for export] *)
Lemma set_ll4_apply : forall ll4 i n a,
  set_ll4 ll4 i n a =
  if Z.land i 1 =? 0 then zfupd ll4 (Z.shiftr i 1) (Z.lor (Z.land (ll4 (Z.shiftr i 1)) 240) n) a
  else zfupd ll4 (Z.shiftr i 1) (Z.lor (Z.land (ll4 (Z.shiftr i 1)) 15) (Z.shiftl n 4)) a.
Proof. intros. unfold set_ll4. destruct (Z.land i 1 =? 0); reflexivity. Qed.

Lemma set_ll_fst : forall ll16 ll4 i v, fst (set_ll ll16 ll4 i v) = zfupd ll16 i (Z.land v 65535).
Proof. reflexivity. Qed.
Lemma set_ll_snd : forall ll16 ll4 i v, snd (set_ll ll16 ll4 i v) = set_ll4 ll4 i (Z.shiftr v 16).
Proof. reflexivity. Qed.

Ltac nib_unpack EV OD :=
  unfold nib_even_ok in EV; unfold nib_odd_ok in OD;
  apply andb_prop in EV; destruct EV as [EV ?EV4]; apply andb_prop in EV; destruct EV as [EV ?EV3];
  apply andb_prop in EV; destruct EV as [?EV1 ?EV2];
  apply andb_prop in OD; destruct OD as [OD ?OD4]; apply andb_prop in OD; destruct OD as [OD ?OD3];
  apply andb_prop in OD; destruct OD as [?OD1 ?OD2];
  apply Z.eqb_eq in EV1; apply Z.eqb_eq in EV2; apply Z.eqb_eq in OD1; apply Z.eqb_eq in OD2;
  apply Z.leb_le in EV3; apply Z.ltb_lt in EV4; apply Z.leb_le in OD3; apply Z.ltb_lt in OD4.

Lemma get_set_ll_same : forall ll16 ll4 i v,
  0 <= i -> 0 <= v < 2 ^ 20 -> 0 <= ll4 (Z.shiftr i 1) < 256 ->
  let p := set_ll ll16 ll4 i v in get_ll (fst p) (snd p) i = v.
Proof.
  intros ll16 ll4 i v Hi Hv HB. cbn zeta. rewrite set_ll_fst, set_ll_snd. unfold get_ll, get_ll4.
  rewrite set_ll4_apply, zfupd_same, shl2_land4 by lia.
  pose proof (shiftr16_range v Hv) as Hn.
  destruct (nib_facts (ll4 (Z.shiftr i 1)) (Z.shiftr v 16) HB Hn) as [EV OD]. nib_unpack EV OD.
  destruct (Z.land i 1 =? 0); rewrite zfupd_same; [rewrite EV1|rewrite OD1]; apply lor_low_high; lia.
Qed.

Lemma get_set_ll_other : forall ll16 ll4 i v k,
  0 <= i -> 0 <= k -> k <> i -> 0 <= v < 2 ^ 20 -> 0 <= ll4 (Z.shiftr i 1) < 256 ->
  let p := set_ll ll16 ll4 i v in get_ll (fst p) (snd p) k = get_ll ll16 ll4 k.
Proof.
  intros ll16 ll4 i v k Hi Hk Hki Hv HB. cbn zeta. rewrite set_ll_fst, set_ll_snd. unfold get_ll, get_ll4.
  rewrite zfupd_other by lia. rewrite set_ll4_apply.
  pose proof (shiftr16_range v Hv) as Hn.
  destruct (Z.eq_dec (Z.shiftr k 1) (Z.shiftr i 1)) as [E|NE].
  - (* [comment removed for export] *)
    destruct (nib_facts (ll4 (Z.shiftr i 1)) (Z.shiftr v 16) HB Hn) as [EV OD]. nib_unpack EV OD.
    rewrite !shl2_land4, !land1_mod by lia. rewrite !shiftr1_div in *.
    assert (k mod 2 <> i mod 2) by (intro; apply Hki; rewrite (Z.div_mod k 2), (Z.div_mod i 2) by lia; lia).
    pose proof (Z.mod_pos_bound k 2 ltac:(lia)). pose proof (Z.mod_pos_bound i 2 ltac:(lia)).
    rewrite E.
    destruct (Z.eqb_spec (i mod 2) 0); destruct (Z.eqb_spec (k mod 2) 0); try lia; rewrite zfupd_same.
    + now rewrite EV2.
    + now rewrite OD2.
  - destruct (Z.land i 1 =? 0); rewrite zfupd_other by lia; reflexivity.
Qed.

Lemma set_ll_byte_range : forall ll16 ll4 i v a,
  0 <= i -> 0 <= v < 2 ^ 20 -> (forall a', 0 <= ll4 a' < 256) -> 0 <= snd (set_ll ll16 ll4 i v) a < 256.
Proof.
  intros ll16 ll4 i v a Hi Hv HB. rewrite set_ll_snd, set_ll4_apply.
  pose proof (shiftr16_range v Hv) as Hn.
  destruct (nib_facts (ll4 (Z.shiftr i 1)) (Z.shiftr v 16) (HB _) Hn) as [EV OD]. nib_unpack EV OD.
  destruct (Z.land i 1 =? 0); rewrite zfupd_eq; destruct (a =? Z.shiftr i 1); auto; lia.
Qed.

(* [comment removed for export] *)
Lemma set_ll_snd_other : forall ll16 ll4 i v a, a <> Z.shiftr i 1 -> snd (set_ll ll16 ll4 i v) a = ll4 a.
Proof. intros. rewrite set_ll_snd, set_ll4_apply. destruct (Z.land i 1 =? 0); rewrite zfupd_other by lia; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma psum_0 : forall unz, psum unz 0 = 0. Proof. reflexivity. Qed.
Lemma psum_succ : forall unz k, 0 <= k -> psum unz (k + 1) = psum unz k + unz k.
Proof.
  intros. unfold psum. replace (Z.to_nat (k + 1)) with (S (Z.to_nat k)) by lia.
  rewrite zsum_S. f_equal. f_equal. lia.
Qed.
Lemma psum_mono : forall unz a b, 0 <= a <= b -> (forall q, a <= q < b -> 0 <= unz q) -> psum unz a <= psum unz b.
Proof.
  intros unz a b Hab Hpos. unfold psum. replace (Z.to_nat b) with (Z.to_nat a + Z.to_nat (b - a))%nat by lia.
  rewrite zsum_app. pose proof (zsum_bounds unz (0 + Z.of_nat (Z.to_nat a)) (Z.to_nat (b - a)) 0 (psum unz b + Z.abs (psum unz a) + 1)) as B.
  assert (0 <= zsum unz (0 + Z.of_nat (Z.to_nat a)) (Z.to_nat (b - a))).
  { clear B. assert (G : forall m, (m <= Z.to_nat (b - a))%nat -> 0 <= zsum unz (0 + Z.of_nat (Z.to_nat a)) m).
    { induction m; intros; cbn [zsum]; [lia|]. specialize (IHm ltac:(lia)). specialize (Hpos (0 + Z.of_nat (Z.to_nat a) + Z.of_nat m) ltac:(lia)). lia. }
    apply G. lia. }
  lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Fast.
  Variables (sym unz cf0 tt0 : Z -> Z) (nblock : nat).
  Let n : Z := Z.of_nat nblock.
  Hypothesis Hsym : forall k, 0 <= k < n -> 0 <= sym k < 256.
  Hypothesis Hhist : hist_ok unz sym nblock.
  (* [comment removed for export] *)
  Hypothesis Hcf : forall b, 0 <= b <= 256 -> cf0 b = psum unz b.
  Hypothesis Hcf256 : cf0 256 <= n.
  Hypothesis Htt0 : forall k, 0 <= k < n -> lo8 (tt0 k) = sym k.
  Hypothesis Htt0r : forall k, 0 <= tt0 k < 2 ^ 32.
  Hypothesis Hnmax : n <= 900000.

  (* [comment removed for export] *)
  Definition tval (k : Z) : Z := cf0 (sym k) + occ sym (Z.to_nat k) (sym k).

  Lemma unz_nonneg : forall b, 0 <= b < 256 -> 0 <= unz b.
  Proof. intros. rewrite (Hhist b H). apply occ_bounds. Qed.

  Lemma cf_mono : forall a b, 0 <= a <= b -> b <= 256 -> cf0 a <= cf0 b.
  Proof. intros. rewrite !Hcf by lia. apply psum_mono; [lia|]. intros. apply unz_nonneg. lia. Qed.

  Lemma cf_step : forall b, 0 <= b < 256 -> cf0 (b + 1) = cf0 b + occ sym nblock b.
  Proof. intros. rewrite !Hcf, psum_succ by lia. rewrite (Hhist b H). reflexivity. Qed.

  Lemma cf_nonneg : forall b, 0 <= b <= 256 -> 0 <= cf0 b.
  Proof. intros. rewrite Hcf by lia. pose proof (psum_mono unz 0 b ltac:(lia) ltac:(intros; apply unz_nonneg; lia)). rewrite psum_0 in *. lia. Qed.

  Lemma occ_strict : forall k, 0 <= k < n -> occ sym (Z.to_nat k) (sym k) + 1 <= occ sym nblock (sym k).
  Proof.
    intros k Hk. unfold occ. replace nblock with (Z.to_nat k + (nblock - Z.to_nat k))%nat at 1 by lia.
    rewrite zcount_app.
    pose proof (zcount_true1 (fun q => sym q =? sym k) (0 + Z.of_nat (Z.to_nat k)) (nblock - Z.to_nat k) k ltac:(lia) ltac:(apply Z.eqb_refl)). lia.
  Qed.

  Lemma tval_range : forall k, 0 <= k < n -> 0 <= tval k /\ tval k + 1 <= cf0 (sym k + 1) /\ tval k < n.
  Proof.
    intros k Hk. unfold tval. pose proof (Hsym k Hk). pose proof (occ_strict k Hk).
    pose proof (cf_step (sym k) ltac:(lia)). pose proof (cf_nonneg (sym k) ltac:(lia)).
    pose proof (occ_bounds sym (Z.to_nat k) (sym k)). pose proof (cf_mono (sym k + 1) 256 ltac:(lia) ltac:(lia)). lia.
  Qed.

  Lemma tval_inj : forall k1 k2, 0 <= k1 < n -> 0 <= k2 < n -> tval k1 = tval k2 -> k1 = k2.
  Proof.
    intros k1 k2 H1 H2 E.
    destruct (Z.lt_trichotomy k1 k2) as [L|[->|L]]; [exfalso| reflexivity | exfalso].
    - pose proof (Hsym k1 H1). pose proof (Hsym k2 H2).
      destruct (Z.lt_trichotomy (sym k1) (sym k2)) as [SY|[SY|SY]].
      + pose proof (tval_range k1 H1). pose proof (cf_mono (sym k1 + 1) (sym k2) ltac:(lia) ltac:(lia)).
        unfold tval in *. pose proof (occ_bounds sym (Z.to_nat k2) (sym k2)). lia.
      + unfold tval in E. rewrite SY in E.
        pose proof (occ_le_mono sym (Z.to_nat (k1 + 1)) (Z.to_nat k2) (sym k2) ltac:(lia)).
        replace (Z.to_nat (k1 + 1)) with (S (Z.to_nat k1)) in H3 by lia. rewrite occ_S in H3.
        replace (Z.of_nat (Z.to_nat k1)) with k1 in H3 by lia. rewrite SY, Z.eqb_refl in H3. lia.
      + pose proof (tval_range k2 H2). pose proof (cf_mono (sym k2 + 1) (sym k1) ltac:(lia) ltac:(lia)).
        unfold tval in *. pose proof (occ_bounds sym (Z.to_nat k1) (sym k1)). lia.
    - pose proof (Hsym k1 H1). pose proof (Hsym k2 H2).
      destruct (Z.lt_trichotomy (sym k1) (sym k2)) as [SY|[SY|SY]].
      + pose proof (tval_range k1 H1). pose proof (cf_mono (sym k1 + 1) (sym k2) ltac:(lia) ltac:(lia)).
        unfold tval in *. pose proof (occ_bounds sym (Z.to_nat k2) (sym k2)). lia.
      + unfold tval in E. rewrite SY in E.
        pose proof (occ_le_mono sym (Z.to_nat (k2 + 1)) (Z.to_nat k1) (sym k2) ltac:(lia)).
        replace (Z.to_nat (k2 + 1)) with (S (Z.to_nat k2)) in H3 by lia. rewrite occ_S in H3.
        replace (Z.of_nat (Z.to_nat k2)) with k2 in H3 by lia. rewrite Z.eqb_refl in H3. lia.
      + pose proof (tval_range k2 H2). pose proof (cf_mono (sym k2 + 1) (sym k1) ltac:(lia) ltac:(lia)).
        unfold tval in *. pose proof (occ_bounds sym (Z.to_nat k1) (sym k1)). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma tinv_inv : forall m, (m <= nblock)%nat ->
    let r := tinv 0 m tt0 cf0 in
    (forall b, 0 <= b < 256 -> snd r b = cf0 b + occ sym m b) /\
    (forall b, ~ (0 <= b < 256) -> snd r b = cf0 b) /\
    (forall k, 0 <= k < n -> lo8 (fst r k) = sym k) /\
    (forall k, ~ (0 <= k < n) -> fst r k = tt0 k) /\
    (forall k, 0 <= fst r k < 2 ^ 32).
  Proof.
    induction m as [|m IH]; intros Hm; cbn zeta.
    - cbn [tinv fst snd]. split; [intros; rewrite occ_0; lia|]. split; [intros; reflexivity|].
      split; [exact Htt0|]. split; [intros; reflexivity| exact Htt0r].
    - rewrite tinv_snoc. cbn zeta. cps_destruct (IH ltac:(lia)) as (A1 & A2 & A3 & A4 & A5).
      set (r := tinv 0 m tt0 cf0) in *. cbn [fst snd]. rewrite Z.add_0_l.
      assert (U : lo8 (fst r (Z.of_nat m)) = sym (Z.of_nat m)) by (apply A3; lia).
      rewrite U. pose proof (Hsym (Z.of_nat m) ltac:(lia)) as SB.
      assert (IDX : snd r (sym (Z.of_nat m)) = tval (Z.of_nat m)).
      { rewrite A1 by lia. unfold tval. now rewrite Nat2Z.id. }
      pose proof (tval_range (Z.of_nat m) ltac:(lia)) as TR. rewrite IDX.
      split; [|split; [|split; [|split]]].
      + intros b Hb. rewrite zfupd_eq, occ_S. destruct (Z.eqb_spec b (sym (Z.of_nat m))), (Z.eqb_spec (sym (Z.of_nat m)) b); try lia.
        * subst b. unfold tval. rewrite Nat2Z.id. lia.
        * rewrite A1 by lia. lia.
      + intros b Hb. rewrite zfupd_other by lia. apply A2. lia.
      + intros k Hk. rewrite zfupd_eq. destruct (Z.eqb_spec k (tval (Z.of_nat m))).
        * rewrite lo8_lor_shiftl8 by lia. subst k. apply A3. lia.
        * apply A3. lia.
      + intros k Hk. rewrite zfupd_other by lia. apply A4. lia.
      + intros k. rewrite zfupd_eq. destruct (k =? tval (Z.of_nat m)); [|apply A5].
        apply lor_shiftl8_lt; [apply A5|]. unfold n in *. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem tinv_step_facts : forall m, (m < nblock)%nat ->
    let r := tinv 0 m tt0 cf0 in
    let i := Z.of_nat m in
    let uc := lo8 (fst r i) in
    let idx := snd r uc in
    uc = sym i /\ 0 <= uc < 256 /\ idx = tval i /\ 0 <= idx < n /\
    0 <= fst r idx < 2 ^ 32 /\ 0 <= Z.lor (fst r idx) (Z.shiftl i 8) < 2 ^ 32 /\ 0 <= idx + 1 <= n.
  Proof.
    intros m Hm. cbn zeta. cps_destruct (tinv_inv m ltac:(lia)) as (A1 & A2 & A3 & A4 & A5).
    set (r := tinv 0 m tt0 cf0) in *.
    assert (U : lo8 (fst r (Z.of_nat m)) = sym (Z.of_nat m)) by (apply A3; lia). rewrite U.
    pose proof (Hsym (Z.of_nat m) ltac:(lia)).
    assert (IDX : snd r (sym (Z.of_nat m)) = tval (Z.of_nat m)) by (rewrite A1 by lia; unfold tval; now rewrite Nat2Z.id).
    rewrite IDX. pose proof (tval_range (Z.of_nat m) ltac:(lia)).
    repeat split; try lia; try apply A5.
    all: pose proof (lor_shiftl8_lt (fst r (tval (Z.of_nat m))) (Z.of_nat m) (A5 _) ltac:(unfold n in *; lia)); lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
End Fast.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint find_in (x : Z) (l : list Z) (pos : nat) : option nat :=
  match l with
  | [] => None
  | y :: r => if x =? y then Some pos else find_in x r (S pos)
  end.
Fixpoint find_dup (l : list Z) (pos : nat) : option (nat * nat) :=
  match l with
  | [] => None
  | x :: r => match find_in x r (S pos) with
              | Some j => Some (pos, j)
              | None => find_dup r (S pos)
              end
  end.

Lemma find_in_some : forall x l pos j, find_in x l pos = Some j ->
  (pos <= j)%nat /\ (j < pos + length l)%nat /\ nth_error l (j - pos) = Some x.
Proof.
  induction l as [|y r IH]; intros pos j H; cbn in H; [discriminate|].
  destruct (Z.eqb_spec x y).
  - inversion H; subst. rewrite Nat.sub_diag. cbn. split; [lia|]. split; [lia|]. now f_equal.
  - cps_destruct (IH _ _ H) as (A & B & C). split; [lia|]. split; [cbn; lia|].
    replace (j - pos)%nat with (S (j - S pos)) by lia. cbn. exact C.
Qed.
Lemma find_in_none : forall x l pos, find_in x l pos = None -> ~ In x l.
Proof.
  induction l as [|y r IH]; intros pos H; cbn in H; [tauto|].
  destruct (Z.eqb_spec x y); [discriminate|]. intros [E|I]; [subst; tauto|]. exact (IH _ H I).
Qed.
Lemma find_dup_some : forall l pos i j, find_dup l pos = Some (i, j) ->
  (pos <= i)%nat /\ (i < j)%nat /\ (j < pos + length l)%nat /\
  exists x, nth_error l (i - pos) = Some x /\ nth_error l (j - pos) = Some x.
Proof.
  induction l as [|y r IH]; intros pos i j H; cbn in H; [discriminate|].
  destruct (find_in y r (S pos)) as [j'|] eqn:F.
  - injection H as E1 E2; subst i; subst j'. cps_destruct (find_in_some _ _ _ _ F) as (A & B & C).
    split; [lia|]. split; [lia|]. split; [cbn; lia|]. exists y. rewrite Nat.sub_diag. cbn. split; [reflexivity|].
    replace (j - pos)%nat with (S (j - S pos)) by lia. cbn. exact C.
  - cps_destruct (IH _ _ _ H) as (A & B & C & x & D & E). split; [lia|]. split; [lia|]. split; [cbn; lia|].
    exists x. replace (i - pos)%nat with (S (i - S pos)) by lia. replace (j - pos)%nat with (S (j - S pos)) by lia. cbn. auto.
Qed.
Lemma find_dup_none : forall l pos, find_dup l pos = None -> NoDup l.
Proof.
  induction l as [|y r IH]; intros pos H; cbn in H; [constructor|].
  destruct (find_in y r (S pos)) eqn:F; [discriminate|].
  constructor; [exact (find_in_none _ _ _ F)| exact (IH _ H)].
Qed.

Definition zseq (lo : Z) (cnt : nat) : list Z := map (fun i => lo + Z.of_nat i) (seq 0 cnt).
Lemma in_zseq : forall lo cnt x, In x (zseq lo cnt) <-> lo <= x < lo + Z.of_nat cnt.
Proof.
  intros. unfold zseq. rewrite in_map_iff. split.
  - intros [i [<- Hi]]. rewrite in_seq in Hi. lia.
  - intros H. exists (Z.to_nat (x - lo)). rewrite in_seq. lia.
Qed.
Lemma zseq_length : forall lo cnt, length (zseq lo cnt) = cnt.
Proof. intros. unfold zseq. now rewrite length_map, length_seq. Qed.

Section Orbit.
  Variables (T : Z -> Z) (N : nat) (o : Z).
  Hypothesis HT : forall x, 0 <= x < Z.of_nat N -> 0 <= T x < Z.of_nat N.
  Hypothesis Hinj : forall x y, 0 <= x < Z.of_nat N -> 0 <= y < Z.of_nat N -> T x = T y -> x = y.
  Hypothesis Ho : 0 <= o < Z.of_nat N.

  Lemma iter_range : forall k, 0 <= iter T k o < Z.of_nat N.
  Proof. induction k; cbn [iter]; [lia|]. apply HT. exact IHk. Qed.

  Lemma iter_cancel : forall m a b, iter T (m + a) o = iter T (m + b) o -> iter T a o = iter T b o.
  Proof.
    induction m; intros a b E; cbn [iter Nat.add] in E; [exact E|].
    apply IHm. apply Hinj; [apply iter_range|apply iter_range|exact E].
  Qed.

  (* [comment removed for export] *)
  Lemma orbit_returns : exists c, (1 <= c <= N)%nat /\ iter T c o = o.
  Proof.
    set (l := map (fun k => iter T k o) (seq 0 (S N))).
    destruct (find_dup l 0) as [[i j]|] eqn:F.
    - cps_destruct (find_dup_some _ _ _ _ F) as (A & B & C & x & D & E).
      unfold l in C, D, E. rewrite length_map, length_seq in C.
      rewrite nth_error_map, nth_error_seq in D, E. rewrite Nat.sub_0_r in D, E.
      destruct (Nat.ltb_spec i (S N)); [|discriminate]. destruct (Nat.ltb_spec j (S N)); [|discriminate].
      cbn in D, E. inversion D. inversion E. exists (j - i)%nat. split; [lia|].
      change (iter T (j - i) o = iter T 0 o). apply (iter_cancel i). rewrite Nat.add_0_r. replace (i + (j - i))%nat with j by lia. congruence.
    - exfalso. pose proof (find_dup_none _ _ F) as ND.
      assert (INCL : incl l (zseq 0 N)).
      { intros x Hx. unfold l in Hx. rewrite in_map_iff in Hx. destruct Hx as [k [<- _]]. rewrite in_zseq. pose proof (iter_range k). lia. }
      pose proof (NoDup_incl_length ND INCL) as LEN. unfold l in LEN. rewrite length_map, length_seq, zseq_length in LEN. lia.
  Qed.

  Lemma first_ret_spec : forall fuel k0,
    (1 <= k0)%nat ->
    (forall k, (1 <= k < k0)%nat -> iter T k o <> o) ->
    (exists c, (k0 <= c < k0 + fuel)%nat /\ iter T c o = o) ->
    let c := first_ret T o k0 fuel in
    (k0 <= c < k0 + fuel)%nat /\ iter T c o = o /\ (forall k, (1 <= k < c)%nat -> iter T k o <> o).
  Proof.
    induction fuel as [|f IH]; intros k0 Hk0 Hbefore [c [Hc E]]; cbn zeta; [lia|].
    cbn [first_ret]. destruct (Z.eqb_spec (iter T k0 o) o) as [E0|NE].
    - split; [lia|]. split; [exact E0| exact Hbefore].
    - cps_destruct (IH (S k0) ltac:(lia)) as (A & B & C).
      + intros k Hk. destruct (Nat.eq_dec k k0) as [->|]; [exact NE|]. apply Hbefore. lia.
      + exists c. split; [|exact E]. destruct (Nat.eq_dec c k0) as [->|]; [congruence|lia].
      + split; [lia|]. split; [exact B| exact C].
  Qed.

  (* [comment removed for export] *)
  Lemma cyc_spec :
    (1 <= cyc T N o <= N)%nat /\ iter T (cyc T N o) o = o /\
    (forall k, (1 <= k < cyc T N o)%nat -> iter T k o <> o).
  Proof.
    unfold cyc. destruct orbit_returns as [c [Hc E]].
    cps_destruct (first_ret_spec N 1 ltac:(lia) ltac:(intros; lia) ltac:(exists c; split; [lia|exact E])) as (A & B & C).
    split; [lia|]. split; [exact B| exact C].
  Qed.

  Lemma orbit_distinct : forall a b, (a < b)%nat -> (b < cyc T N o)%nat -> iter T a o <> iter T b o.
  Proof.
    intros a b Hab Hb E. cps_destruct cyc_spec as (C1 & C2 & C3).
    apply (C3 (b - a)%nat ltac:(lia)). change (iter T (b - a) o = iter T 0 o). symmetry.
    apply (iter_cancel a). rewrite Nat.add_0_r. replace (a + (b - a))%nat with b by lia. exact E.
  Qed.

  (* [comment removed for export] *)
  Fixpoint aprL (L0 : Z -> Z) (k : nat) : Z -> Z :=
    match k with
    | O => L0
    | S k' => zfupd (aprL L0 k') (iter T (S k') o) (iter T k' o)
    end.

  Lemma aprL_other : forall L0 k x, (forall m, (1 <= m <= k)%nat -> x <> iter T m o) -> aprL L0 k x = L0 x.
  Proof.
    induction k; intros x Hx; cbn [aprL]; [reflexivity|].
    rewrite zfupd_other by (apply Hx; lia). apply IHk. intros m Hm. apply Hx. lia.
  Qed.

  Lemma apr_iter_spec : forall L0 k,
    (forall x, 0 <= x < Z.of_nat N -> L0 x = T x) ->
    (k <= cyc T N o)%nat ->
    apr_iter k (L0, o, L0 o) = (aprL L0 k, iter T k o, iter T (S k) o).
  Proof.
    intros L0 k HL0. induction k as [|k IH]; intros Hk.
    - cbn. rewrite (HL0 o) by lia. all: try reflexivity.
    - rewrite apr_iter_S, IH by lia. unfold apr_step. cbn [aprL]. f_equal.
      (* [comment removed for export] *)
      rewrite aprL_other.
      + rewrite HL0 by (apply iter_range). reflexivity.
      + intros m Hm. cps_destruct cyc_spec as (C1 & C2 & C3).
        destruct (Nat.eq_dec (S k) (cyc T N o)) as [E|NE].
        * (* [comment removed for export] *)
          rewrite E, C2. change o with (iter T 0 o). intros X. apply (orbit_distinct 0 m); first [lia | exact X].
        * intros X. apply (orbit_distinct m (S k)); first [lia | symmetry; exact X].
  Qed.

  (* [comment removed for export] *)
  Lemma apr_i_range : forall L0 k, (forall x, 0 <= x < Z.of_nat N -> L0 x = T x) -> (k <= cyc T N o)%nat ->
    let '(L, i, j) := apr_iter k (L0, o, L0 o) in
    i = iter T k o /\ j = iter T (S k) o /\ 0 <= i < Z.of_nat N /\ 0 <= j < Z.of_nat N /\ L = aprL L0 k.
  Proof.
    intros L0 k HL0 Hk. rewrite apr_iter_spec by auto. pose proof (iter_range k). pose proof (iter_range (S k)).
    repeat split; auto; lia.
  Qed.

  Lemma apr_continue : forall k, (1 <= k < cyc T N o)%nat -> iter T k o <> o.
  Proof. intros. cps_destruct cyc_spec as (C1 & C2 & C3). apply C3. lia. Qed.
  Lemma apr_stop : iter T (cyc T N o) o = o.
  Proof. cps_destruct cyc_spec as (C1 & C2 & C3). exact C2. Qed.
  Lemma cyc_range : (1 <= cyc T N o <= N)%nat.
  Proof. destruct cyc_spec as (C1 & _). exact C1. Qed.
End Orbit.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Small.
  Variables (sym unz cf0 ll16_0 ll4_0 : Z -> Z) (nblock : nat).
  Let n : Z := Z.of_nat nblock.
  Hypothesis Hsym : forall k, 0 <= k < n -> 0 <= sym k < 256.
  Hypothesis Hhist : hist_ok unz sym nblock.
  Hypothesis Hcf : forall b, 0 <= b <= 256 -> cf0 b = psum unz b.      (* [comment removed for export] *)
  Hypothesis Hcf256 : cf0 256 <= n.
  Hypothesis Hnmax : n <= 900000.
  Hypothesis Hll16 : forall k, 0 <= k < n -> lo8 (ll16_0 k) = sym k.
  Hypothesis Hll16r : forall k, 0 <= ll16_0 k < 2 ^ 16.
  Hypothesis Hll4r : forall a, 0 <= ll4_0 a < 256.

  Let T : Z -> Z := tval sym cf0.

  Lemma T_range : forall k, 0 <= k < n -> 0 <= T k < n.
  Proof. intros. cps_destruct (tval_range sym unz cf0 nblock Hsym Hhist Hcf Hcf256 k H) as (A & B & C). unfold T. lia. Qed.
  Lemma T_inj : forall x y, 0 <= x < n -> 0 <= y < n -> T x = T y -> x = y.
  Proof. intros. eapply (tval_inj sym unz cf0 nblock); eauto. Qed.

  (* [comment removed for export] *)
  Lemma tvec_inv : forall m, (m <= nblock)%nat ->
    let '(ll16, ll4, cfc) := tvec 0 m ll16_0 ll4_0 cf0 in
    (forall b, 0 <= b < 256 -> cfc b = cf0 b + occ sym m b) /\
    (forall b, ~ (0 <= b < 256) -> cfc b = cf0 b) /\
    (forall k, 0 <= k < Z.of_nat m -> get_ll ll16 ll4 k = T k) /\
    (forall k, ~ (0 <= k < Z.of_nat m) -> ll16 k = ll16_0 k) /\
    (forall k, 0 <= ll16 k < 2 ^ 16) /\
    (forall a, 0 <= ll4 a < 256) /\
    (forall a, ~ (0 <= 2 * a < Z.of_nat m) -> ll4 a = ll4_0 a).
  Proof.
    induction m as [|m IH]; intros Hm.
    - cbn [tvec]. split; [intros; rewrite occ_0; lia|]. split; [intros; reflexivity|].
      split; [intros; lia|]. split; [intros; reflexivity|]. split; [exact Hll16r|]. split; [exact Hll4r| intros; reflexivity].
    - rewrite tvec_snoc. specialize (IH ltac:(lia)).
      destruct (tvec 0 m ll16_0 ll4_0 cf0) as [[ll16 ll4] cfc]. cbn zeta. rewrite Z.add_0_l.
      cps_destruct IH as (A1 & A2 & A3 & A4 & A5 & A6 & A7).
      rewrite set_ll_fst.
      assert (U : lo8 (ll16 (Z.of_nat m)) = sym (Z.of_nat m)) by (rewrite A4 by lia; apply Hll16; lia).
      rewrite U. pose proof (Hsym (Z.of_nat m) ltac:(lia)) as SB.
      assert (V : cfc (sym (Z.of_nat m)) = T (Z.of_nat m)) by (rewrite A1 by lia; unfold T, tval; now rewrite Nat2Z.id).
      rewrite V. pose proof (T_range (Z.of_nat m) ltac:(lia)) as TR.
      assert (TV : 0 <= T (Z.of_nat m) < 2 ^ 20) by lia.
      split; [|split; [|split; [|split; [|split; [|split]]]]].
      + intros b Hb. rewrite zfupd_eq. rewrite occ_S.
        destruct (Z.eqb_spec b (sym (Z.of_nat m))), (Z.eqb_spec (sym (Z.of_nat m)) b); try lia.
        * subst b. unfold T, tval. rewrite Nat2Z.id. lia.
        * rewrite A1 by lia. lia.
      + intros b Hb. rewrite zfupd_other by lia. apply A2. lia.
      + intros k Hk. destruct (Z.eq_dec k (Z.of_nat m)) as [->|NE].
        * rewrite <- (set_ll_fst ll16 ll4). apply get_set_ll_same; auto; lia.
        * rewrite <- (set_ll_fst ll16 ll4).
          rewrite (get_set_ll_other ll16 ll4 (Z.of_nat m) (T (Z.of_nat m)) k) by (auto; lia). apply A3. lia.
      + intros k Hk. rewrite zfupd_other by lia. apply A4. lia.
      + intros k. rewrite zfupd_eq. destruct (k =? Z.of_nat m); [|apply A5].
        rewrite land_65535. pose proof (Z.mod_pos_bound (T (Z.of_nat m)) (2 ^ 16) ltac:(lia)). lia.
      + intros a. apply set_ll_byte_range; auto; lia.
      + intros a Ha. rewrite set_ll_snd_other; [apply A7; lia|]. rewrite shiftr1_div. intros E. subst a.
        pose proof (Z.div_mod (Z.of_nat m) 2 ltac:(lia)). pose proof (Z.mod_pos_bound (Z.of_nat m) 2 ltac:(lia)). lia.
  Qed.

  (* [comment removed for export] *)
  Theorem tvec_step_facts : forall m, (m < nblock)%nat ->
    let '(ll16, ll4, cfc) := tvec 0 m ll16_0 ll4_0 cf0 in
    let i := Z.of_nat m in let uc := lo8 (ll16 i) in let v := cfc uc in
    uc = sym i /\ 0 <= uc < 256 /\ v = T i /\ 0 <= v < n /\ 0 <= v + 1 <= n /\
    0 <= Z.shiftr v 16 < 16 /\ 0 <= Z.land v 65535 < 2 ^ 16 /\
    0 <= ll4 (Z.shiftr i 1) < 256 /\ 0 <= Z.shiftr i 1 /\ 2 * Z.shiftr i 1 <= i.
  Proof.
    intros m Hm. pose proof (tvec_inv m ltac:(lia)) as IV.
    destruct (tvec 0 m ll16_0 ll4_0 cf0) as [[ll16 ll4] cfc]. cbn zeta.
    cps_destruct IV as (A1 & A2 & A3 & A4 & A5 & A6 & A7).
    assert (U : lo8 (ll16 (Z.of_nat m)) = sym (Z.of_nat m)) by (rewrite A4 by lia; apply Hll16; lia).
    rewrite U. pose proof (Hsym (Z.of_nat m) ltac:(lia)) as SB.
    assert (V : cfc (sym (Z.of_nat m)) = T (Z.of_nat m)) by (rewrite A1 by lia; unfold T, tval; now rewrite Nat2Z.id).
    rewrite V. pose proof (T_range (Z.of_nat m) ltac:(lia)) as TR.
    pose proof (shiftr16_range (T (Z.of_nat m)) ltac:(lia)).
    rewrite land_65535. pose proof (Z.mod_pos_bound (T (Z.of_nat m)) (2 ^ 16) ltac:(lia)).
    rewrite shiftr1_div. pose proof (Z.div_mod (Z.of_nat m) 2 ltac:(lia)). pose proof (Z.mod_pos_bound (Z.of_nat m) 2 ltac:(lia)).
    pose proof (Z.div_pos (Z.of_nat m) 2 ltac:(lia) ltac:(lia)).
    repeat split; auto; try lia; apply A6.
  Qed.

  (* [comment removed for export] *)
  Variable o : Z.                                 (* [comment removed for export] *)
  Hypothesis Ho : 0 <= o < n.

  Definition ll16_T : Z -> Z := fst (fst (tvec 0 nblock ll16_0 ll4_0 cf0)).
  Definition ll4_T : Z -> Z := snd (fst (tvec 0 nblock ll16_0 ll4_0 cf0)).
  Definition pr_start : (Z -> Z) * (Z -> Z) * Z * Z := (ll16_T, ll4_T, o, get_ll ll16_T ll4_T o).
  Definition apr_start : (Z -> Z) * Z * Z := (get_ll ll16_T ll4_T, o, get_ll ll16_T ll4_T o).
  Definition cycle : nat := cyc T nblock o.

  Lemma llT_facts :
    (forall k, 0 <= k < n -> get_ll ll16_T ll4_T k = T k) /\
    (forall k, 0 <= ll16_T k < 2 ^ 16) /\ (forall a, 0 <= ll4_T a < 256).
  Proof.
    unfold ll16_T, ll4_T. pose proof (tvec_inv nblock ltac:(lia)) as IV.
    destruct (tvec 0 nblock ll16_0 ll4_0 cf0) as [[ll16 ll4] cfc]. cbn [fst snd].
    cps_destruct IV as (A1 & A2 & A3 & A4 & A5 & A6 & A7). auto.
  Qed.

  (* [comment removed for export] *)
  Lemma pr_sim : forall k, (k <= cycle)%nat ->
    let '(a, b, i, j) := pr_iter k pr_start in
    let '(L, i', j') := apr_iter k apr_start in
    i = i' /\ j = j' /\ (forall x, 0 <= x < n -> get_ll a b x = L x) /\
    (forall x, 0 <= a x < 2 ^ 16) /\ (forall y, 0 <= b y < 256) /\
    i = iter T k o /\ j = iter T (S k) o /\ 0 <= i < n /\ 0 <= j < n.
  Proof.
    cps_destruct llT_facts as (F1 & F2 & F3).
    induction k as [|k IH]; intros Hk.
    - cbn [pr_iter apr_iter pr_start apr_start iter]. pose proof (T_range o Ho).
      rewrite (F1 o Ho). repeat split; auto; try lia.
      all: first [pose proof (F2 x); lia | pose proof (F3 y); lia].
    - specialize (IH ltac:(lia)). rewrite pr_iter_S, apr_iter_S.
      pose proof (apr_i_range T nblock o T_range T_inj Ho (get_ll ll16_T ll4_T) (S k) F1 ltac:(unfold cycle in Hk; lia)) as AR.
      unfold apr_start in *. rewrite apr_iter_S in AR.
      destruct (pr_iter k pr_start) as [[[a b] i] j]. destruct (apr_iter k _) as [[L i'] j'].
      cps_destruct IH as (E1 & E2 & R & Ra & Rb & Hi & Hj & Bi & Bj). subst i' j'.
      cbn [apr_step pr_step] in *. cps_destruct AR as (AR1 & AR2 & AR3 & AR4 & _).
      assert (TV : 0 <= i < 2 ^ 20) by lia.
      split; [reflexivity|]. split; [apply R; lia|]. split.
      { intros x Hx. rewrite zfupd_eq. destruct (Z.eqb_spec x j).
        - subst x. apply get_set_ll_same; auto; lia.
        - rewrite (get_set_ll_other a b j i x); auto; try lia. }
      split. { intros x. rewrite set_ll_fst, zfupd_eq. destruct (x =? j); [|apply Ra]. rewrite land_65535. pose proof (Z.mod_pos_bound i (2 ^ 16) ltac:(lia)). lia. }
      split. { intros y. apply set_ll_byte_range; auto; lia. }
      rewrite (R j) by lia. repeat split; try lia; congruence.
  Qed.

  (* [comment removed for export] *)
  Theorem ptr_rev_facts :
    (1 <= cycle <= nblock)%nat /\
    (forall s, (s < cycle)%nat ->
       let '(a, b, i, j) := pr_iter s pr_start in
       0 <= i < n /\ 0 <= j < n /\ 0 <= get_ll a b j < n /\ 0 <= b (Z.shiftr j 1) < 256 /\
       (forall y, 0 <= b y < 256) /\ (forall x, 0 <= a x < 2 ^ 16) /\
       let '(a', b', i', j') := pr_step (a, b, i, j) in
       i' = j /\ (i' = o <-> S s = cycle)) .
  Proof.
    pose proof (cyc_range T nblock o T_range T_inj Ho) as CR. fold cycle in CR.
    split; [exact CR|]. intros s Hs.
    pose proof (pr_sim s ltac:(lia)) as P0. pose proof (pr_sim (S s) ltac:(lia)) as P1.
    rewrite pr_iter_S, apr_iter_S in P1.
    destruct (pr_iter s pr_start) as [[[a b] i] j]. destruct (apr_iter s apr_start) as [[L i0] j0].
    cps_destruct P0 as (E1 & E2 & R & Ra & Rb & Hi & Hj & Bi & Bj). subst i0 j0.
    cbn [pr_step apr_step] in P1 |- *.
    cps_destruct P1 as (_ & E4 & _ & _ & _ & Hi' & Hj' & Bi' & Bj').
    repeat split; try lia; try apply Rb; try apply Ra.
    - intros E. rewrite Hi' in E. destruct (Nat.eq_dec (S s) cycle) as [|NE]; [assumption|].
      exfalso. apply (apr_continue T nblock o T_range T_inj Ho (S s)); [fold cycle; lia| exact E].
    - intros E. rewrite Hi'. rewrite E. apply (apr_stop T nblock o T_range T_inj Ho).
  Qed.
End Small.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint iif_state (cftab : Z -> Z) (indx : Z) (t : nat) : Z * Z :=
  match t with
  | O => (0, 256)
  | S t' => let '(nb, na) := iif_state cftab indx t' in
            let mid := Z.shiftr (nb + na) 1 in
            if cftab mid <=? indx then (mid, na) else (nb, mid)
  end.

Lemma iif_state_inv : forall cftab indx t, (t <= 8)%nat ->
  let '(nb, na) := iif_state cftab indx t in
  0 <= nb /\ na <= 256 /\ na - nb = 2 ^ (8 - Z.of_nat t) /\ (exists q, nb = q * (na - nb)).
Proof.
  induction t as [|t IH]; intros Ht.
  - cbn. split; [lia|]. split; [lia|]. split; [reflexivity| exists 0; lia].
  - cbn [iif_state]. specialize (IH ltac:(lia)). destruct (iif_state cftab indx t) as [nb na].
    cps_destruct IH as (A & B & C & [q D]).
    assert (P : 2 ^ (8 - Z.of_nat t) = 2 * 2 ^ (8 - Z.of_nat (S t))).
    { replace (8 - Z.of_nat t) with (Z.succ (8 - Z.of_nat (S t))) by lia. rewrite Z.pow_succ_r; lia. }
    set (h := 2 ^ (8 - Z.of_nat (S t))) in *.
    assert (Hh : 0 < h) by (unfold h; apply Z.pow_pos_nonneg; lia).
    assert (M : Z.shiftr (nb + na) 1 = nb + h).
    { rewrite Z.shiftr_div_pow2, Z.pow_1_r by lia. replace na with (nb + 2 * h) by lia.
      replace (nb + (nb + 2 * h)) with ((nb + h) * 2) by lia. now rewrite Z.div_mul by lia. }
    rewrite M. destruct (cftab (nb + h) <=? indx).
    + split; [lia|]. split; [lia|]. split; [lia|]. exists (2 * q + 1). lia.
    + split; [lia|]. split; [lia|]. split; [lia|]. exists (2 * q). lia.
Qed.

(* [comment removed for export] *)
Lemma iif_state_diff : forall cftab indx t, (t <= 8)%nat ->
  let '(nb, na) := iif_state cftab indx t in na - nb = 2 ^ (8 - Z.of_nat t) /\ 0 <= nb /\ na <= 256.
Proof.
  intros. pose proof (iif_state_inv cftab indx t H) as I. destruct (iif_state cftab indx t) as [nb na]. cps_destruct I as (A & B & C & _). auto.
Qed.

Lemma pow2_eq_1 : forall e, 0 <= e -> 2 ^ e = 1 -> e = 0.
Proof.
  intros e He E. destruct (Z.eq_dec e 0) as [->|NE]; [reflexivity|].
  assert (2 ^ 1 <= 2 ^ e) by (apply Z.pow_le_mono_r; lia). rewrite Z.pow_1_r in H. lia.
Qed.

(* [comment removed for export] *)
Theorem iif_step_facts : forall cftab indx t, (t <= 7)%nat ->
  let '(nb, na) := iif_state cftab indx t in
  let mid := Z.shiftr (nb + na) 1 in
  0 <= nb /\ nb < mid /\ mid < na /\ na <= 256 /\ 1 <= mid <= 255 /\ 0 <= nb + na <= 512 /\
  let '(nb', na') := iif_state cftab indx (S t) in
  ((nb', na') = (if cftab mid <=? indx then (mid, na) else (nb, mid))) /\
  0 <= nb' /\ na' <= 256 /\ 1 <= na' - nb' /\ (na' - nb' = 1 <-> t = 7%nat).
Proof.
  intros cftab indx t Ht.
  pose proof (iif_state_diff cftab indx t ltac:(lia)) as D0.
  pose proof (iif_state_diff cftab indx (S t) ltac:(lia)) as D1.
  cbn [iif_state] in D1 |- *.
  destruct (iif_state cftab indx t) as [nb na]. cps_destruct D0 as (A & B & C).
  set (h := 2 ^ (8 - Z.of_nat (S t))) in *.
  assert (P : 2 ^ (8 - Z.of_nat t) = 2 * h).
  { unfold h. replace (8 - Z.of_nat t) with (Z.succ (8 - Z.of_nat (S t))) by lia. rewrite Z.pow_succ_r; lia. }
  assert (Hh : 1 <= h) by (unfold h; pose proof (Z.pow_le_mono_r 2 0 (8 - Z.of_nat (S t)) ltac:(lia) ltac:(lia)); rewrite Z.pow_0_r in *; lia).
  assert (M : Z.shiftr (nb + na) 1 = nb + h).
  { rewrite Z.shiftr_div_pow2, Z.pow_1_r by lia. replace (nb + na) with ((nb + h) * 2) by lia. now rewrite Z.div_mul by lia. }
  rewrite M in *.
  assert (HX : h = 1 <-> t = 7%nat).
  { unfold h. split.
    - intros E. apply pow2_eq_1 in E; lia.
    - intros ->. reflexivity. }
  destruct (cftab (nb + h) <=? indx); cps_destruct D1 as (A1 & B1 & C1); cbn zeta;
    (repeat split; try lia); try tauto.
  all: intros E; first [apply HX; lia | apply HX in E; lia].
Qed.

(* [comment removed for export] *)
Lemma iif_loop_state : forall cftab indx t, (t <= 7)%nat ->
  let '(nb, na) := iif_state cftab indx t in
  iif_loop cftab indx nb na (8 - t) = iif_state cftab indx 8.
Proof.
  intros cftab indx t. remember (8 - t)%nat as f. revert t Heqf.
  induction f as [|f IH]; intros t Hf Ht; [lia|].
  pose proof (iif_step_facts cftab indx t Ht) as SF.
  cbn [iif_loop]. 
  destruct (iif_state cftab indx t) as [nb na] eqn:E0.
  cps_destruct SF as (A & B & C & D & E & F & SF).
  destruct (iif_state cftab indx (S t)) as [nb' na'] eqn:E1.
  cps_destruct SF as (EQ & G & H & I & J).
  destruct (cftab (Z.shiftr (nb + na) 1) <=? indx); injection EQ as -> ->.
  - destruct (Z.eqb_spec (na - Z.shiftr (nb + na) 1) 1) as [X|X].
    + apply J in X. subst t. replace f with 0%nat by lia. rewrite <- E1. reflexivity.
    + destruct (Nat.eq_dec t 7) as [->|NE]; [exfalso; apply X; now apply J|].
      pose proof (IH (S t) ltac:(lia) ltac:(lia)) as R. rewrite E1 in R. exact R.
  - destruct (Z.eqb_spec (Z.shiftr (nb + na) 1 - nb) 1) as [X|X].
    + apply J in X. subst t. replace f with 0%nat by lia. rewrite <- E1. reflexivity.
    + destruct (Nat.eq_dec t 7) as [->|NE]; [exfalso; apply X; now apply J|].
      pose proof (IH (S t) ltac:(lia) ltac:(lia)) as R. rewrite E1 in R. exact R.
Qed.

Theorem index_into_f_spec : forall indx cftab,
  index_into_f indx cftab = fst (iif_state cftab indx 8) /\ 0 <= index_into_f indx cftab <= 255.
Proof.
  intros. unfold index_into_f.
  pose proof (iif_loop_state cftab indx 0 ltac:(lia)) as L.
  change (let '(nb, na) := (0, 256) in iif_loop cftab indx nb na 8 = iif_state cftab indx 8) in L.
  lazy beta iota zeta in L. rewrite L.
  pose proof (iif_state_diff cftab indx 8 ltac:(lia)) as D. destruct (iif_state cftab indx 8) as [nb na].
  cbn [fst]. rewrite Z.sub_diag, Z.pow_0_r in D. split; [reflexivity| lia].
Qed.
