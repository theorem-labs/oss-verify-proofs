(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzArrD BzCSortF BzCLemmasFs BzCFactsFs.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
Fixpoint cntP (P : Z -> bool) (n : nat) : Z :=
  match n with
  | O => 0
  | S n' => cntP P n' + (if P (Z.of_nat n') then 1 else 0)
  end.

Lemma cntP_nonneg : forall P n, 0 <= cntP P n.
Proof. induction n; cbn; [lia|]. destruct (P (Z.of_nat n)); lia. Qed.

Lemma cntP_le : forall P n, cntP P n <= Z.of_nat n.
Proof. induction n; cbn; [lia|]. destruct (P (Z.of_nat n)); lia. Qed.

Lemma cntP_mono_n : forall P n m, (n <= m)%nat -> cntP P n <= cntP P m.
Proof.
  intros P n m H. induction H as [|m H IH]; [lia|]. cbn. destruct (P (Z.of_nat m)); lia.
Qed.

Lemma cntP_impl : forall P Q n, (forall i, 0 <= i < Z.of_nat n -> P i = true -> Q i = true) -> cntP P n <= cntP Q n.
Proof.
  induction n as [|n IH]; intros H; cbn; [lia|].
  assert (cntP P n <= cntP Q n) by (apply IH; intros; apply H; [lia|assumption]).
  destruct (P (Z.of_nat n)) eqn:EP.
  - rewrite (H (Z.of_nat n)); [lia|lia|exact EP].
  - destruct (Q (Z.of_nat n)); lia.
Qed.

Lemma cntP_or : forall P Q n, (forall i, 0 <= i < Z.of_nat n -> P i = true -> Q i = true -> False) ->
  cntP (fun i => P i || Q i) n = cntP P n + cntP Q n.
Proof.
  induction n as [|n IH]; intros H; cbn; [lia|].
  rewrite IH by (intros; eapply H; eauto; lia).
  destruct (P (Z.of_nat n)) eqn:EP, (Q (Z.of_nat n)) eqn:EQ; cbn; try lia.
  exfalso. eapply H; eauto; lia.
Qed.

Lemma cntP_ext : forall P Q n, (forall i, 0 <= i < Z.of_nat n -> P i = Q i) -> cntP P n = cntP Q n.
Proof.
  induction n as [|n IH]; intros H; cbn; [lia|]. rewrite IH by (intros; apply H; lia). rewrite H by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma cntP_pos : forall P n i, 0 <= i < Z.of_nat n -> P i = true -> 1 <= cntP P n.
Proof.
  induction n as [|n IH]; intros i Hi HP; cbn; [lia|].
  pose proof (cntP_nonneg P n).
  destruct (Z.eq_dec i (Z.of_nat n)) as [->|NE].
  - rewrite HP. lia.
  - assert (1 <= cntP P n) by (apply (IH i); [lia|exact HP]). destruct (P (Z.of_nat n)); lia.
Qed.

(* [comment removed for export] *)
Lemma cntP_lt_at : forall P n m, (n < m)%nat -> P (Z.of_nat n) = true -> cntP P n < cntP P m.
Proof.
  intros P n m H HP. induction H as [|m H IH].
  - cbn. rewrite HP. lia.
  - cbn. destruct (P (Z.of_nat m)); lia.
Qed.

Section S1.
  Variables (ec : zarr) (nb : Z).
  Hypothesis ECB : zbok ec.
  Hypothesis NB : 0 <= nb.

  Let e8 (i : Z) : Z := rd8 ec i.
  (* [comment removed for export] *)
  Definition Cl (j : Z) : Z := cntP (fun i => e8 i <? j) (Z.to_nat nb).
  Definition Eq (j : Z) (k : nat) : Z := cntP (fun i => e8 i =? j) k.

  Lemma e8_range : forall i, 0 <= e8 i < 256.
  Proof. intros i. unfold e8, rd8. apply ECB. Qed.

  Lemma Cl_0 : Cl 0 = 0.
  Proof.
    unfold Cl. rewrite (cntP_ext _ (fun _ => false)).
    - induction (Z.to_nat nb); cbn; lia.
    - intros i Hi. pose proof (e8_range i). apply Z.ltb_ge. lia.
  Qed.

  (* [comment removed for export] *)

  Lemma Cl_step : forall j, Cl (j + 1) = Cl j + Eq j (Z.to_nat nb).
  Proof.
    intros j. unfold Cl, Eq. rewrite <- cntP_or.
    - apply cntP_ext. intros i Hi.
      destruct (Z.ltb_spec (e8 i) (j + 1)), (Z.ltb_spec (e8 i) j), (Z.eqb_spec (e8 i) j); cbn; auto; lia.
    - intros i Hi A B. apply Z.ltb_lt in A. apply Z.eqb_eq in B. lia.
  Qed.

  Lemma Cl_mono : forall j j', j <= j' -> Cl j <= Cl j'.
  Proof.
    intros j j' H. unfold Cl. apply cntP_impl. intros i _ A. apply Z.ltb_lt in A. apply Z.ltb_lt. lia.
  Qed.

  Lemma Cl_range : forall j, 0 <= Cl j <= nb.
  Proof. intros j. unfold Cl. pose proof (cntP_nonneg (fun i => e8 i <? j) (Z.to_nat nb)). pose proof (cntP_le (fun i => e8 i <? j) (Z.to_nat nb)). lia. Qed.

  Lemma Eq_range : forall j k, (k <= Z.to_nat nb)%nat -> 0 <= Eq j k <= Eq j (Z.to_nat nb).
  Proof. intros j k Hk. unfold Eq. pose proof (cntP_nonneg (fun i => e8 i =? j) k). pose proof (cntP_mono_n (fun i => e8 i =? j) k _ Hk). lia. Qed.

  (* [comment removed for export] *)
  Lemma ft1_get : forall j, zget (fp_ft1) j = 0.
  Proof. intros j. unfold fp_ft1. rewrite fs_ftab_zero_get. destruct (_ && _); [reflexivity| apply zget_znew]. Qed.

  Lemma fs_count_get : forall n ft i j, 0 <= i ->
    zget (fs_count n ft ec i) j = zget ft j + (cntP (fun i' => e8 i' =? j) (Z.to_nat i + n) - cntP (fun i' => e8 i' =? j) (Z.to_nat i)).
  Proof.
    induction n as [|n IH]; intros ft i j Hi.
    - cbn [fs_count]. rewrite Nat.add_0_r. lia.
    - rewrite fs_count_S, IH by lia. rewrite zget_zincr. unfold e8, rd8.
      replace (Z.to_nat (i + 1) + n)%nat with (Z.to_nat i + S n)%nat by lia.
      replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
      replace (Z.to_nat i + S n)%nat with (S (Z.to_nat i + n))%nat by lia.
      cbn [cntP]. rewrite Z2Nat.id by lia.
      destruct (Z.eqb_spec j (zget ec i)) as [E|NE].
      + rewrite <- E, Z.eqb_refl. lia.
      + destruct (Z.eqb_spec (zget ec i) j); lia.
  Qed.

  Lemma ft2_get : forall j, zget (fp_ft2 ec nb) j = Eq j (Z.to_nat nb).
  Proof.
    intros j. unfold fp_ft2. rewrite fs_count_get by lia. rewrite ft1_get. unfold Eq.
    change (Z.to_nat 0) with 0%nat. cbn [cntP Nat.add]. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma fs_accum_get : forall n ft i,
    1 <= i -> (forall j, 0 <= j < i -> zget ft j = Cl (j + 1)) -> (forall j, i <= j -> zget ft j = Eq j (Z.to_nat nb)) ->
    (forall j, 0 <= j < i + Z.of_nat n -> zget (fs_accum n ft i) j = Cl (j + 1)) /\
    (forall j, i + Z.of_nat n <= j -> zget (fs_accum n ft i) j = Eq j (Z.to_nat nb)).
  Proof.
    induction n as [|n IH]; intros ft i Hi LO HIx.
    - cbn [fs_accum]. split; intros; [apply LO|apply HIx]; lia.
    - rewrite fs_accum_S.
      destruct (IH (zset ft i (zget ft i + zget ft (i - 1))) (i + 1) ltac:(lia)) as [A B].
      + intros j Hj. rewrite zget_zset. destruct (Z.eqb_spec j i) as [->|NE].
        * rewrite HIx, LO by lia. replace (i - 1 + 1) with i by lia. rewrite Cl_step. lia.
        * apply LO. lia.
      + intros j Hj. rewrite zget_zset_other by lia. apply HIx. lia.
      + split; intros j Hj; [apply A|apply B]; lia.
  Qed.

  Lemma ft3_get : forall j, 0 <= j <= 256 -> zget (fp_ft3 ec nb) j = Cl (j + 1).
  Proof.
    intros j Hj. unfold fp_ft3.
    destruct (fs_accum_get 256 (fp_ft2 ec nb) 1 ltac:(lia)) as [A _].
    - intros j0 Hj0. rewrite ft2_get. replace j0 with 0 by lia. rewrite Cl_step, Cl_0. reflexivity.
    - intros j0 Hj0. apply ft2_get.
    - apply A. lia.
  Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition Kp (i : Z) : Z := Cl (e8 i + 1) - Eq (e8 i) (Z.to_nat i) - 1.

  Lemma Eq_S : forall j k, Eq j (S k) = Eq j k + (if e8 (Z.of_nat k) =? j then 1 else 0).
  Proof. intros. unfold Eq. reflexivity. Qed.

  Lemma Eq_lt_nb : forall i, 0 <= i < nb -> Eq (e8 i) (Z.to_nat i) < Eq (e8 i) (Z.to_nat nb).
  Proof.
    intros i Hi. unfold Eq. apply cntP_lt_at; [lia|]. rewrite Z2Nat.id by lia. apply Z.eqb_refl.
  Qed.

  Lemma Kp_bucket : forall i, 0 <= i < nb -> Cl (e8 i) <= Kp i < Cl (e8 i + 1).
  Proof.
    intros i Hi. unfold Kp. pose proof (Eq_lt_nb i Hi). pose proof (Cl_step (e8 i)).
    pose proof (Eq_range (e8 i) (Z.to_nat i) ltac:(lia)). lia.
  Qed.

  Lemma Kp_range : forall i, 0 <= i < nb -> 0 <= Kp i < nb.
  Proof.
    intros i Hi. pose proof (Kp_bucket i Hi). pose proof (Cl_range (e8 i)). pose proof (Cl_range (e8 i + 1)). lia.
  Qed.

  Lemma Kp_inj : forall i1 i2, 0 <= i1 < nb -> 0 <= i2 < nb -> Kp i1 = Kp i2 -> i1 = i2.
  Proof.
    intros i1 i2 H1 H2 HK.
    destruct (Z.lt_trichotomy (e8 i1) (e8 i2)) as [LT|[EQ|GT]].
    - pose proof (Kp_bucket i1 H1). pose proof (Kp_bucket i2 H2). pose proof (Cl_mono (e8 i1 + 1) (e8 i2) ltac:(lia)). lia.
    - destruct (Z.lt_trichotomy i1 i2) as [L|[E|G]]; [|exact E|]; exfalso; unfold Kp in HK; rewrite EQ in HK.
      + assert (Eq (e8 i2) (Z.to_nat i1) < Eq (e8 i2) (Z.to_nat i2)); [|lia].
        unfold Eq. apply cntP_lt_at; [lia|]. rewrite Z2Nat.id by lia. rewrite <- EQ. apply Z.eqb_refl.
      + assert (Eq (e8 i2) (Z.to_nat i2) < Eq (e8 i2) (Z.to_nat i1)); [|lia].
        unfold Eq. apply cntP_lt_at; [lia|]. rewrite Z2Nat.id by lia. apply Z.eqb_refl.
    - pose proof (Kp_bucket i1 H1). pose proof (Kp_bucket i2 H2). pose proof (Cl_mono (e8 i2 + 1) (e8 i1) ltac:(lia)). lia.
  Qed.

  (* [comment removed for export] *)
  Variable fm : zarr.
  Hypothesis NB32 : nb <= 4294967296.

  Lemma dist_inv : forall k, (k <= Z.to_nat nb)%nat ->
    (forall j, 0 <= j < 256 -> zget (fst (fp_dist fm ec nb k)) j = Cl (j + 1) - Eq j k) /\
    (forall i, 0 <= i < Z.of_nat k -> rd32 (snd (fp_dist fm ec nb k)) (Kp i) = i) /\
    (forall x, (forall i, 0 <= i < Z.of_nat k -> Kp i <> x) -> rd32 (snd (fp_dist fm ec nb k)) x = rd32 fm x).
  Proof.
    induction k as [|k IH]; intros Hk.
    - cbn [fp_dist fs_distrib fst snd]. split; [|split].
      + intros j Hj. rewrite ft3_get by lia. unfold Eq; cbn [cntP]. lia.
      + intros; lia.
      + intros; reflexivity.
    - cps_destruct (IH ltac:(lia)) as (A & B & C).
      replace (S k) with (Z.to_nat (Z.of_nat k + 1)) by lia. rewrite fp_dist_step by lia.
      rewrite Nat2Z.id. destruct (fp_dist fm ec nb k) as [ft fm'] eqn:EQD. cbn [fst snd] in *.
      pose proof (e8_range (Z.of_nat k)) as R8.
      assert (HW : zget ft (rd8 ec (Z.of_nat k)) - 1 = Kp (Z.of_nat k)).
      { rewrite A by (unfold e8 in R8; lia). unfold Kp, e8. rewrite Nat2Z.id. lia. }
      rewrite HW. split; [|split].
      + intros j Hj. rewrite zget_zset. replace (Z.to_nat (Z.of_nat k + 1)) with (S k) by lia. rewrite Eq_S.
        fold (e8 (Z.of_nat k)). destruct (Z.eqb_spec j (e8 (Z.of_nat k))) as [->|NE].
        * rewrite Z.eqb_refl. unfold Kp. rewrite Nat2Z.id. lia.
        * rewrite A by lia. destruct (Z.eqb_spec (e8 (Z.of_nat k)) j); lia.
      + intros i Hi. destruct (Z.eq_dec i (Z.of_nat k)) as [->|NE].
        * apply rd32_wr32_same. lia.
        * rewrite rd32_wr32_other. { apply B. lia. }
          intros X. apply NE. apply Kp_inj; [lia|lia|exact X].
      + intros x Hx. rewrite rd32_wr32_other. { apply C. intros i Hi. apply Hx. lia. }
        intros X. apply (Hx (Z.of_nat k)); [lia|]. symmetry; exact X.
  Qed.

  (* [comment removed for export] *)
  Definition zseq (n : Z) : list Z := map Z.of_nat (seq 0 (Z.to_nat n)).

  Lemma in_zseq : forall n x, In x (zseq n) <-> 0 <= x < n.
  Proof.
    intros n x. unfold zseq. rewrite in_map_iff. split.
    - cps_intros (k & <- & Hk). apply in_seq in Hk. lia.
    - intros Hx. exists (Z.to_nat x). split; [lia|]. apply in_seq. lia.
  Qed.

  Lemma NoDup_map_on : forall (A B : Type) (f : A -> B) (l : list A),
    NoDup l -> (forall a b, In a l -> In b l -> f a = f b -> a = b) -> NoDup (map f l).
  Proof.
    intros A B f l ND INJ. induction ND as [|a l Ha ND IH]; cbn; constructor.
    - intros Hin. apply in_map_iff in Hin. cps_destruct Hin as (b & Hfb & Hb).
      assert (b = a) by (apply INJ; cbn; auto). subst b. exact (Ha Hb).
    - apply IH. intros x y Hx Hy. apply INJ; cbn; auto.
  Qed.

  Lemma zseq_NoDup : forall n, NoDup (zseq n).
  Proof.
    intros n. unfold zseq. apply NoDup_map_on; [apply seq_NoDup|]. intros a b _ _ H. apply Nat2Z.inj; exact H.
  Qed.

  (* [comment removed for export] *)

  Lemma inj_onto : forall (f : Z -> Z) (n : Z),
    (forall i, 0 <= i < n -> 0 <= f i < n) ->
    (forall i j, 0 <= i < n -> 0 <= j < n -> f i = f j -> i = j) ->
    forall x, 0 <= x < n -> exists i, 0 <= i < n /\ f i = x.
  Proof.
    intros f n RNG INJ x Hx.
    assert (INC : incl (zseq n) (map f (zseq n))).
    { apply NoDup_length_incl.
      - apply NoDup_map_on; [apply zseq_NoDup|]. intros a b Ha Hb. apply in_zseq in Ha. apply in_zseq in Hb. apply INJ; assumption.
      - rewrite length_map. lia.
      - intros y Hy. apply in_map_iff in Hy. cps_destruct Hy as (i & <- & Hi). apply in_zseq in Hi. apply in_zseq. apply RNG; exact Hi. }
    pose proof (INC x ltac:(apply in_zseq; exact Hx)) as Hin.
    apply in_map_iff in Hin. cps_destruct Hin as (i & Hfi & Hi). apply in_zseq in Hi. exists i. split; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma Kp_onto : forall x, 0 <= x < nb -> exists i, 0 <= i < nb /\ Kp i = x.
  Proof. apply inj_onto; [apply Kp_range | apply Kp_inj]. Qed.

  Theorem fsf_distrib_ok : fsf_distrib fm ec nb.
  Proof.
    intros i Hi. cps_destruct (dist_inv (Z.to_nat i) ltac:(lia)) as (A & _ & _).
    pose proof (e8_range i) as R8. unfold e8 in R8.
    rewrite A by lia.
    pose proof (Kp_range i Hi). unfold Kp, e8 in *. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem fp_ft4_count : forall b, 0 <= b < 256 -> zget (fp_ft4 fm ec nb) b = Cl b.
  Proof.
    intros b Hb. unfold fp_ft4. cps_destruct (dist_inv (Z.to_nat nb) ltac:(lia)) as (A & _ & _).
    rewrite A by lia. rewrite Cl_step. lia.
  Qed.

  Theorem fsf_ft4_ok : fsf_ft4 fm ec nb.
  Proof. intros b Hb. rewrite fp_ft4_count by lia. apply Cl_range. Qed.

  Definition fm_perm (f : zarr) (n : Z) : Prop :=
    (forall x, 0 <= x < n -> 0 <= rd32 f x < n) /\
    (forall x y, 0 <= x < n -> 0 <= y < n -> rd32 f x = rd32 f y -> x = y).

  (* [comment removed for export] *)
  Theorem fp_fm1_Kp : forall i, 0 <= i < nb -> rd32 (fp_fm1 fm ec nb) (Kp i) = i.
  Proof.
    intros i Hi. unfold fp_fm1. cps_destruct (dist_inv (Z.to_nat nb) ltac:(lia)) as (_ & B & _). apply B. lia.
  Qed.

  Theorem fp_fm1_perm : fm_perm (fp_fm1 fm ec nb) nb.
  Proof.
    split.
    - intros x Hx. cps_destruct (Kp_onto x Hx) as (i & Hi & <-). rewrite fp_fm1_Kp by lia. lia.
    - intros x y Hx Hy H. cps_destruct (Kp_onto x Hx) as (i & Hi & <-). cps_destruct (Kp_onto y Hy) as (i' & Hi' & <-).
      rewrite !fp_fm1_Kp in H by lia. subst i'. reflexivity.
  Qed.

  Theorem fsf_fm1_ok : fsf_fm1 fm ec nb.
  Proof. intros x Hx. apply (proj1 fp_fm1_perm). exact Hx. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
End S1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma fm_perm_onto : forall fm nb, fm_perm fm nb -> forall v, 0 <= v < nb -> exists x, 0 <= x < nb /\ rd32 fm x = v.
Proof. intros fm nb [R I]. apply inj_onto; assumption. Qed.

Lemma fm_perm_ext : forall fm fm' nb, fm_perm fm nb -> (forall x, 0 <= x < nb -> rd32 fm' x = rd32 fm x) -> fm_perm fm' nb.
Proof.
  intros fm fm' nb [R I] E. split.
  - intros x Hx. rewrite E by lia. apply R; lia.
  - intros x y Hx Hy H. rewrite !E in H by lia. apply I; assumption.
Qed.

Lemma fm_perm_fswap : forall fm nb a b, fm_perm fm nb -> nb <= 4294967296 -> 0 <= a < nb -> 0 <= b < nb -> fm_perm (fswap fm a b) nb.
Proof.
  intros fm nb a b [R I] NB Ha Hb.
  assert (G : forall x, rd32 (fswap fm a b) x = if x =? b then rd32 fm a else if x =? a then rd32 fm b else rd32 fm x).
  { intros x. unfold fswap. destruct (Z.eqb_spec x b) as [->|NB1].
    - apply rd32_wr32_same. pose proof (R a Ha). lia.
    - rewrite rd32_wr32_other by lia. destruct (Z.eqb_spec x a) as [->|NA].
      + apply rd32_wr32_same. pose proof (R b Hb). lia.
      + apply rd32_wr32_other. lia. }
  split.
  - intros x Hx. rewrite G. destruct (x =? b); [apply R; lia|]. destruct (x =? a); apply R; lia.
  - intros x y Hx Hy H. rewrite !G in H.
    destruct (Z.eqb_spec x b), (Z.eqb_spec y b), (Z.eqb_spec x a), (Z.eqb_spec y a); subst;
      try reflexivity; first [apply I in H; lia | idtac].
Qed.
