(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzArrD. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCSortM. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCPermF BzCRebuildF.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
Lemma lor_step : forall s b, 0 <= s < 65536 -> 0 <= b < 256 ->
  Z.lor (Z.shiftr s 8) (Z.shiftl b 8) = s / 256 + 256 * b.
Proof.
  intros s b Hs Hb. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
  assert (L : 0 <= s / 256 < 256) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  set (a := s / 256) in *. clearbody a.
  assert (LAND : Z.land a (256 * b) = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases n 8) as [Ln|Gn].
    + rewrite (Z.mul_comm 256 b). change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits by lia.
      rewrite (Z.testbit_neg_r b (n - 8)) by lia. apply Bool.andb_false_r.
    + rewrite (Z.bits_above_log2 a n); [reflexivity| lia|].
      destruct (Z.eq_dec a 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; [lia|].
      eapply Z.lt_le_trans; [apply (proj2 L)|]. change 256 with (2 ^ 8). apply Z.pow_le_mono_r; lia. }
  rewrite (Z.mul_comm b 256). rewrite <- Z.lxor_lor by exact LAND. symmetry. apply Z.add_nocarry_lxor. exact LAND.
Qed.

Lemma cntP_lt_between : forall P n k m, (n <= k)%nat -> (k < m)%nat -> P (Z.of_nat k) = true -> cntP P n < cntP P m.
Proof.
  intros P n k m H1 H2 HP. pose proof (cntP_mono_n P n k H1). pose proof (cntP_lt_at P k m H2 HP). lia.
Qed.

Section M1.
  Variables (a2 : zarr) (nb qoff : Z).
  Hypothesis BB : forall i, 0 <= rd8 a2 i < 256.
  Hypothesis NB : 1 <= nb <= 4294967296.
  Hypothesis QO : nb <= qoff.

  (* [comment removed for export] *)
  Definition nxt (i : Z) : Z := if i =? nb - 1 then 0 else i + 1.
  Definition key (i : Z) : Z := 256 * rd8 a2 i + rd8 a2 (nxt i).
  Lemma key_range : forall i, 0 <= key i < 65536.
  Proof. intros i. unfold key. pose proof (BB i). pose proof (BB (nxt i)). lia. Qed.

  Definition ClM (v : Z) : Z := cntP (fun i => key i <? v) (Z.to_nat nb).
  Definition EqM (v : Z) (k : nat) : Z := cntP (fun i => key i =? v) k.
  (* [comment removed for export] *)
  Definition EqA (v : Z) (k : nat) : Z := EqM v (Z.to_nat nb) - EqM v k.

  Lemma ClM_0 : ClM 0 = 0.
  Proof.
    unfold ClM. rewrite (cntP_ext _ (fun _ => false)); [induction (Z.to_nat nb); cbn; lia|].
    intros i Hi. pose proof (key_range i). apply Z.ltb_ge. lia.
  Qed.
  Lemma ClM_top : forall v, 65536 <= v -> ClM v = nb.
  Proof.
    intros v Hv. unfold ClM. rewrite (cntP_ext _ (fun _ => true)).
    - assert (G : forall n, cntP (fun _ => true) n = Z.of_nat n) by (induction n; cbn; lia). rewrite G. lia.
    - intros i Hi. pose proof (key_range i). apply Z.ltb_lt. lia.
  Qed.
  Lemma ClM_step : forall v, ClM (v + 1) = ClM v + EqM v (Z.to_nat nb).
  Proof.
    intros v. unfold ClM, EqM. rewrite <- cntP_or.
    - apply cntP_ext. intros i Hi. destruct (Z.ltb_spec (key i) (v + 1)), (Z.ltb_spec (key i) v), (Z.eqb_spec (key i) v); cbn; auto; lia.
    - intros i Hi A B. apply Z.ltb_lt in A. apply Z.eqb_eq in B. lia.
  Qed.
  Lemma ClM_mono : forall v v', v <= v' -> ClM v <= ClM v'.
  Proof. intros v v' H. unfold ClM. apply cntP_impl. intros i _ A. apply Z.ltb_lt in A. apply Z.ltb_lt. lia. Qed.
  Lemma ClM_range : forall v, 0 <= ClM v <= nb.
  Proof. intros v. unfold ClM. pose proof (cntP_nonneg (fun i => key i <? v) (Z.to_nat nb)). pose proof (cntP_le (fun i => key i <? v) (Z.to_nat nb)). lia. Qed.
  Lemma EqM_mono : forall v k k', (k <= k')%nat -> EqM v k <= EqM v k'.
  Proof. intros. unfold EqM. apply cntP_mono_n. assumption. Qed.
  Lemma EqM_nonneg : forall v k, 0 <= EqM v k.
  Proof. intros. unfold EqM. apply cntP_nonneg. Qed.
  Lemma EqM_S : forall v k, EqM v (S k) = EqM v k + (if key (Z.of_nat k) =? v then 1 else 0).
  Proof. intros. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition KpM (i : Z) : Z := ClM (key i + 1) - EqA (key i) (Z.to_nat (i + 1)) - 1.

  Lemma KpM_bucket : forall i, 0 <= i < nb -> ClM (key i) <= KpM i < ClM (key i + 1).
  Proof.
    intros i Hi. unfold KpM, EqA. pose proof (ClM_step (key i)).
    assert (1 <= EqM (key i) (Z.to_nat (i + 1))).
    { unfold EqM. apply (cntP_pos _ _ i); [lia| apply Z.eqb_refl]. }
    pose proof (EqM_mono (key i) (Z.to_nat (i + 1)) (Z.to_nat nb) ltac:(lia)).
    pose proof (EqM_nonneg (key i) (Z.to_nat (i+1))). lia.
  Qed.
  Lemma KpM_range : forall i, 0 <= i < nb -> 0 <= KpM i < nb.
  Proof. intros i Hi. pose proof (KpM_bucket i Hi). pose proof (ClM_range (key i)). pose proof (ClM_range (key i + 1)). lia. Qed.
  Lemma KpM_inj : forall i1 i2, 0 <= i1 < nb -> 0 <= i2 < nb -> KpM i1 = KpM i2 -> i1 = i2.
  Proof.
    intros i1 i2 H1 H2 HK.
    destruct (Z.lt_trichotomy (key i1) (key i2)) as [LT|[EQ|GT]].
    - pose proof (KpM_bucket i1 H1). pose proof (KpM_bucket i2 H2). pose proof (ClM_mono (key i1 + 1) (key i2) ltac:(lia)). lia.
    - destruct (Z.lt_trichotomy i1 i2) as [L|[E|G]]; [|exact E|]; exfalso; unfold KpM, EqA in HK; rewrite EQ in HK.
      + assert (EqM (key i2) (Z.to_nat (i1 + 1)) < EqM (key i2) (Z.to_nat (i2 + 1))); [|lia].
        unfold EqM. apply (cntP_lt_between _ _ (Z.to_nat i2)); [lia|lia|]. rewrite Z2Nat.id by lia. apply Z.eqb_refl.
      + assert (EqM (key i2) (Z.to_nat (i2 + 1)) < EqM (key i2) (Z.to_nat (i1 + 1))); [|lia].
        unfold EqM. apply (cntP_lt_between _ _ (Z.to_nat i1)); [lia|lia|]. rewrite Z2Nat.id by lia. rewrite <- EQ. apply Z.eqb_refl.
    - pose proof (KpM_bucket i1 H1). pose proof (KpM_bucket i2 H2). pose proof (ClM_mono (key i2 + 1) (key i1) ltac:(lia)). lia.
  Qed.
  Lemma KpM_onto : forall x, 0 <= x < nb -> exists i, 0 <= i < nb /\ KpM i = x.
  Proof. apply inj_onto; [apply KpM_range | apply KpM_inj]. Qed.

  (* [comment removed for export] *)
  Lemma ms_ftab_zero_get : forall n ft i v, zget (ms_ftab_zero n ft i) v = if (i - Z.of_nat n <? v) && (v <=? i) then 0 else zget ft v.
  Proof.
    induction n as [|n IH]; intros ft i v; cbn [ms_ftab_zero].
    - change (Z.of_nat 0) with 0. destruct (Z.ltb_spec (i - 0) v), (Z.leb_spec v i); cbn [andb]; try reflexivity; lia.
    - rewrite IH, zget_zset. replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia.
      destruct (Z.ltb_spec (i - 1 - Z.of_nat n) v), (Z.leb_spec v (i - 1)), (Z.eqb_spec v i), (Z.ltb_spec (i - (Z.of_nat n + 1)) v), (Z.leb_spec v i); cbn [andb]; try reflexivity; lia.
  Qed.

  Lemma rd8_qwr : forall a i v k, k < qoff -> 0 <= i -> rd8 (qwr a qoff i v) k = rd8 a k.
  Proof. intros a i v k Hk Hi. unfold rd8, qwr, wr16. rewrite !zget_zset_other by lia. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma ms_radix1_spec : forall n a ft i j,
    (forall k, 0 <= k < nb -> rd8 a k = rd8 a2 k) -> -1 <= i < nb -> Z.of_nat n = i + 1 ->
    0 <= j < 65536 -> j / 256 = rd8 a2 (nxt i) ->
    let r := ms_radix1 n a ft qoff i j in
    (forall k, 0 <= k < nb -> rd8 (fst (fst r)) k = rd8 a2 k) /\
    (forall v, zget (snd (fst r)) v = zget ft v + EqM v (Z.to_nat (i + 1))).
  Proof.
    induction n as [|n IH]; intros a ft i j HA Hi Hn Hj HJ; cbn zeta.
    - cbn [ms_radix1 fst snd]. split; [exact HA|]. intros v. unfold EqM. replace (Z.to_nat (i + 1)) with 0%nat by lia. cbn. lia.
    - cbn [ms_radix1]. set (a' := qwr a qoff i 0).
      assert (HA' : forall k, 0 <= k < nb -> rd8 a' k = rd8 a2 k) by (intros k Hk; subst a'; rewrite rd8_qwr by lia; apply HA; lia).
      rewrite HA' by lia. rewrite lor_step by (try apply BB; lia). rewrite HJ.
      assert (KEY : rd8 a2 (nxt i) + 256 * rd8 a2 i = key i) by (unfold key; lia).
      rewrite KEY.
      destruct (IH a' (zincr ft (key i)) (i - 1) (key i) HA' ltac:(lia) ltac:(lia) (key_range i)) as [R1 R2].
      { unfold key. pose proof (BB i). pose proof (BB (nxt i)). unfold nxt at 2.
        replace (if i - 1 =? nb - 1 then 0 else i - 1 + 1) with i by (destruct (Z.eqb_spec (i - 1) (nb - 1)); lia).
        rewrite Z.mul_comm, Z.div_add_l by lia. rewrite Z.div_small by lia. lia. }
      split; [exact R1|]. intros v. rewrite R2, zget_zincr. replace (i - 1 + 1) with i by lia.
      replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. rewrite EqM_S. rewrite Z2Nat.id by lia.
      destruct (Z.eqb_spec v (key i)) as [->|NE]; [rewrite Z.eqb_refl; lia|].
      destruct (Z.eqb_spec (key i) v); [congruence| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma of_nat_65537 : Z.of_nat 65537%nat = 65537. Proof. vm_compute; reflexivity. Qed.
  Lemma of_nat_65536 : Z.of_nat 65536%nat = 65536. Proof. vm_compute; reflexivity. Qed.
  Definition mft1 (ft : zarr) : zarr := ms_ftab_zero 65537%nat ft 65536.
  Lemma mft1_get : forall ft v, 0 <= v <= 65536 -> zget (mft1 ft) v = 0.
  Proof. intros ft v Hv. unfold mft1. rewrite ms_ftab_zero_get, of_nat_65537. destruct (Z.ltb_spec (65536 - 65537) v), (Z.leb_spec v 65536); cbn [andb]; try reflexivity; lia. Qed.

  Lemma radix1_ft : forall a ft, (forall k, 0 <= k < nb -> rd8 a k = rd8 a2 k) ->
    let r := ms_radix1 (Z.to_nat nb) a (mft1 ft) qoff (nb - 1) (Z.shiftl (rd8 a 0) 8) in
    (forall k, 0 <= k < nb -> rd8 (fst (fst r)) k = rd8 a2 k) /\
    (forall v, 0 <= v <= 65536 -> zget (snd (fst r)) v = EqM v (Z.to_nat nb)).
  Proof.
    intros a ft HA. cbn zeta.
    pose proof (BB 0) as B0. rewrite HA in * by lia.
    destruct (ms_radix1_spec (Z.to_nat nb) a (mft1 ft) (nb - 1) (Z.shiftl (rd8 a2 0) 8) HA ltac:(lia) ltac:(lia)) as [R1 R2].
    - rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256. lia.
    - rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256. unfold nxt. rewrite Z.eqb_refl. rewrite Z.div_mul by lia. reflexivity.
    - split; [exact R1|]. intros v Hv. rewrite R2, mft1_get by lia. replace (nb - 1 + 1) with nb by lia. lia.
  Qed.

  Lemma ms_accum_get : forall n ft i,
    1 <= i -> (forall v, 0 <= v < i -> zget ft v = ClM (v + 1)) -> (forall v, i <= v < i + Z.of_nat n -> zget ft v = EqM v (Z.to_nat nb)) ->
    (forall v, 0 <= v < i + Z.of_nat n -> zget (ms_accum n ft i) v = ClM (v + 1)) /\
    (forall v, i + Z.of_nat n <= v -> zget (ms_accum n ft i) v = zget ft v).
  Proof.
    induction n as [|n IH]; intros ft i Hi LO HIx.
    - cbn [ms_accum]. split; intros; [apply LO; lia|reflexivity].
    - cbn [ms_accum].
      destruct (IH (zset ft i (zget ft i + zget ft (i - 1))) (i + 1) ltac:(lia)) as [A B].
      + intros v Hv. rewrite zget_zset. destruct (Z.eqb_spec v i) as [->|NE].
        * rewrite HIx, LO by lia. replace (i - 1 + 1) with i by lia. rewrite ClM_step. lia.
        * apply LO. lia.
      + intros v Hv. rewrite zget_zset_other by lia. apply HIx. lia.
      + split; intros v Hv; [apply A; lia|]. rewrite B by lia. apply zget_zset_other. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma ms_radix2_spec : forall n a1 a ft i s,
    (forall k, 0 <= k < nb -> rd8 a k = rd8 a2 k) -> -1 <= i < nb -> Z.of_nat n = i + 1 ->
    0 <= s < 65536 -> s / 256 = rd8 a2 (nxt i) ->
    (forall v, 0 <= v <= 65536 -> zget ft v = ClM (v + 1) - EqA v (Z.to_nat (i + 1))) ->
    let r := ms_radix2 n a1 a ft i s in
    (forall v, 0 <= v <= 65536 -> zget (snd (fst r)) v = ClM v) /\
    (forall i', 0 <= i' <= i -> rd32 (fst (fst r)) (KpM i') = i') /\
    (forall x, (forall i', 0 <= i' <= i -> KpM i' <> x) -> rd32 (fst (fst r)) x = rd32 a1 x).
  Proof.
    induction n as [|n IH]; intros a1 a ft i s HA Hi Hn Hs HS HF; cbn zeta.
    - cbn [ms_radix2 fst snd]. split; [|split; [intros; lia| intros; reflexivity]].
      intros v Hv. rewrite HF by lia. unfold EqA. replace (Z.to_nat (i + 1)) with 0%nat by lia. unfold EqM at 2. cbn [cntP].
      fold (EqM v (Z.to_nat nb)). rewrite ClM_step. lia.
    - cbn [ms_radix2]. rewrite HA by lia. rewrite lor_step by (try apply BB; lia). rewrite HS.
      assert (KEY : rd8 a2 (nxt i) + 256 * rd8 a2 i = key i) by (unfold key; lia). rewrite KEY.
      pose proof (key_range i) as KR.
      assert (HW : zget ft (key i) - 1 = KpM i). { rewrite HF by lia. unfold KpM. lia. }
      rewrite HW.
      cps_destruct (IH (wr32 a1 (KpM i) i) a (zset ft (key i) (KpM i)) (i - 1) (key i) HA ltac:(lia) ltac:(lia) KR) as (R1 & R2 & R3).
      { unfold key. pose proof (BB i). pose proof (BB (nxt i)). unfold nxt at 2.
        replace (if i - 1 =? nb - 1 then 0 else i - 1 + 1) with i by (destruct (Z.eqb_spec (i - 1) (nb - 1)); lia).
        rewrite Z.mul_comm, Z.div_add_l by lia. rewrite Z.div_small by lia. lia. }
      { intros v Hv. rewrite zget_zset. replace (i - 1 + 1) with i by lia.
        assert (EA : EqA v (Z.to_nat i) = EqA v (Z.to_nat (i + 1)) + (if key i =? v then 1 else 0)).
        { unfold EqA. replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. rewrite EqM_S. rewrite Z2Nat.id by lia. lia. }
        destruct (Z.eqb_spec v (key i)) as [->|NE].
        - unfold KpM. rewrite EA, Z.eqb_refl. lia.
        - rewrite HF by lia. rewrite EA. destruct (Z.eqb_spec (key i) v); [congruence|lia]. }
      split; [exact R1|]. split.
      + intros i' Hi'. destruct (Z.eq_dec i' i) as [->|NE].
        * rewrite R3. { apply rd32_wr32_same. lia. } intros i'' Hi'' X. apply KpM_inj in X; lia.
        * apply R2. lia.
      + intros x Hx. rewrite R3 by (intros; apply Hx; lia). apply rd32_wr32_other.
        intros X. apply (Hx i); [lia|]. symmetry. exact X.
  Qed.

  (* [comment removed for export] *)
  Theorem ms_radix_perm : forall a1 a ft,
    (forall k, 0 <= k < nb -> rd8 a k = rd8 a2 k) ->
    (forall v, 0 <= v <= 65536 -> zget ft v = ClM (v + 1)) ->
    let r := ms_radix2 (Z.to_nat nb) a1 a ft (nb - 1) (Z.shiftl (rd8 a 0) 8) in
    (forall v, 0 <= v <= 65536 -> zget (snd (fst r)) v = ClM v) /\
    (forall i, 0 <= i < nb -> rd32 (fst (fst r)) (KpM i) = i) /\
    fm_perm (fst (fst r)) nb /\
    (forall x, (x < 0 \/ nb <= x) -> rd32 (fst (fst r)) x = rd32 a1 x).
  Proof.
    intros a1 a ft HA HF. cbn zeta. pose proof (BB 0) as B0. rewrite HA in * by lia.
    cps_destruct (ms_radix2_spec (Z.to_nat nb) a1 a ft (nb - 1) (Z.shiftl (rd8 a2 0) 8) HA ltac:(lia) ltac:(lia)) as (R1 & R2 & R3).
    - rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256. lia.
    - rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256. unfold nxt. rewrite Z.eqb_refl. rewrite Z.div_mul by lia. reflexivity.
    - intros v Hv. rewrite HF by lia. unfold EqA. replace (nb - 1 + 1) with nb by lia. lia.
    - split; [exact R1|]. split; [intros i Hi; apply R2; lia|]. split.
      + split.
        * intros x Hx. cps_destruct (KpM_onto x Hx) as (i & Hi & <-). rewrite R2 by lia. lia.
        * intros x y Hx Hy E. cps_destruct (KpM_onto x Hx) as (i & Hi & <-). cps_destruct (KpM_onto y Hy) as (i' & Hi' & <-).
          rewrite !R2 in E by lia. subst i'. reflexivity.
      + intros x Hx. apply R3. intros i' Hi'. pose proof (KpM_range i' ltac:(lia)). lia.
  Qed.

  (* [comment removed for export] *)
  Theorem ms_accum_ft : forall ft2,
    (forall v, 0 <= v <= 65536 -> zget ft2 v = EqM v (Z.to_nat nb)) ->
    forall v, 0 <= v <= 65536 -> zget (ms_accum 65536%nat ft2 1) v = ClM (v + 1).
  Proof.
    intros ft2 H v Hv.
    (* [comment removed for export] *)
    destruct (ms_accum_get 65536%nat ft2 1 ltac:(lia)) as [A _].
    - intros v0 Hv0. replace v0 with 0 by lia. rewrite H by lia. rewrite ClM_step, ClM_0. reflexivity.
    - intros v0 Hv0. rewrite of_nat_65536 in Hv0. apply H. lia.
    - apply A. rewrite of_nat_65536. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma ms_overshoot_low : forall n a i, 0 <= i -> nb + Z.of_nat n <= qoff ->
    (forall k, 0 <= k < nb -> rd8 (ms_overshoot n a qoff nb i) k = rd8 a k).
  Proof.
    induction n as [|n IH]; intros a i Hi Hq k Hk; cbn [ms_overshoot]; [reflexivity|].
    rewrite IH by lia. rewrite rd8_qwr by lia. unfold rd8, wr8. apply zget_zset_other. lia.
  Qed.
End M1.
