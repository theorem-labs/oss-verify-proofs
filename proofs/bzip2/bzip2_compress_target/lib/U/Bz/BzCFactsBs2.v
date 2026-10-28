(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzArrD BzCState. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCSortM BzCBlock. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCPermF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCPermM BzCLemmasMs BzCFactsBs BzCSortPost BzCSewF BzCSewH.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {BZP : BzParams}.


(* [comment removed for export] *)

Section J.
  Variable e : est.
  Hypothesis BB : zbok (e_arr2 e).
  Hypothesis NB : 34 <= e_nblock e <= 1000000.

  Lemma E_ft0 : bp_ft0 e = mft1 (bp_ft e). Proof. unfold bp_ft0, mft1. reflexivity. Qed.
  Lemma E_j0 : bp_j0 e = Z.shiftl (rd8 (bp_a2 e) 0) 8. Proof. reflexivity. Qed.
  Lemma E_r1 : bp_r1 e = ms_radix1 (Z.to_nat (bp_n e)) (bp_a2 e) (bp_ft0 e) (bp_qoff e) (bp_n e - 1) (bp_j0 e). Proof. unfold bp_r1. reflexivity. Qed.
  Lemma E_a2r : bp_a2r e = fst (fst (bp_r1 e)). Proof. reflexivity. Qed.
  Lemma E_ft1 : bp_ft1 e = snd (fst (bp_r1 e)). Proof. reflexivity. Qed.
  Lemma E_a2o : bp_a2o e = ms_overshoot 34 (bp_a2r e) (bp_qoff e) (bp_n e) 0. Proof. unfold bp_a2o. reflexivity. Qed.
  Lemma E_ft3 : bp_ft3 e = ms_accum 65536 (bp_ft1 e) 1. Proof. unfold bp_ft3. reflexivity. Qed.
  Lemma E_s0 : bp_s0 e = Z.shiftl (rd8 (bp_a2o e) 0) 8. Proof. reflexivity. Qed.
  Lemma E_r4 : bp_r4 e = ms_radix2 (Z.to_nat (bp_n e)) (bp_a1 e) (bp_a2o e) (bp_ft3 e) (bp_n e - 1) (bp_s0 e). Proof. unfold bp_r4. reflexivity. Qed.
  Lemma E_a1r : bp_a1r e = fst (fst (bp_r4 e)). Proof. reflexivity. Qed.
  Lemma E_ft4 : bp_ft4 e = snd (fst (bp_r4 e)). Proof. reflexivity. Qed.

  Lemma BBr : forall i, 0 <= rd8 (bp_a2 e) i < 256. Proof. intros i. unfold rd8, bp_a2. apply BB. Qed.
  Lemma NBp : 34 <= bp_n e <= 1000000. Proof. exact NB. Qed.
  Lemma QO : bp_n e + 34 <= bp_qoff e. Proof. unfold bp_qoff, BZ_N_OVERSHOOT. destruct (_ =? 0); lia. Qed.

  Lemma pt_radix1 : (forall k, 0 <= k < bp_n e -> rd8 (bp_a2r e) k = rd8 (bp_a2 e) k) /\
                    (forall v, 0 <= v <= 65536 -> zget (bp_ft1 e) v = EqM (bp_a2 e) (bp_n e) v (Z.to_nat (bp_n e))).
  Proof.
    pose proof NBp as NB'. pose proof QO as QO'.
    pose proof (radix1_ft (bp_a2 e) (bp_n e) (bp_qoff e) BBr ltac:(lia) ltac:(lia) (bp_a2 e) (bp_ft e) ltac:(intros; reflexivity)) as R.
    cbv zeta in R. rewrite <- E_ft0, <- E_j0, <- E_r1, <- E_a2r, <- E_ft1 in R. exact R.
  Qed.
  Lemma pt_a2o : forall k, 0 <= k < bp_n e -> rd8 (bp_a2o e) k = rd8 (bp_a2 e) k.
  Proof.
    pose proof NBp as NB'. pose proof QO as QO'.
    intros k Hk. rewrite E_a2o. rewrite (ms_overshoot_low (bp_n e) (bp_qoff e) ltac:(lia) 34 (bp_a2r e) 0 ltac:(lia) ltac:(cbn; lia) k Hk).
    apply (proj1 pt_radix1). exact Hk.
  Qed.
  Lemma pt_a2o_zbok : zbok (bp_a2o e).
  Proof. rewrite E_a2o. apply zbok_overshoot. rewrite E_a2r, E_r1. apply zbok_radix1. unfold bp_a2. exact BB. Qed.
  Lemma pt_ft3 : forall v, 0 <= v <= 65536 -> zget (bp_ft3 e) v = ClM (bp_a2 e) (bp_n e) (v + 1).
  Proof.
    pose proof NBp as NB'.
    pose proof (ms_accum_ft (bp_a2 e) (bp_n e) BBr ltac:(lia) (bp_ft1 e) (proj2 pt_radix1)) as R. rewrite <- E_ft3 in R. exact R.
  Qed.
  Lemma pt_ft4 : forall v, 0 <= v <= 65536 -> zget (bp_ft4 e) v = ClM (bp_a2 e) (bp_n e) v.
  Proof.
    pose proof NBp as NB'.
    pose proof (ms_radix_perm (bp_a2 e) (bp_n e) BBr ltac:(lia) (bp_a1 e) (bp_a2o e) (bp_ft3 e) pt_a2o pt_ft3) as R. cbv zeta in R.
    rewrite <- E_s0, <- E_r4, <- E_ft4 in R. exact (proj1 R).
  Qed.

  Theorem bsA_accum_ok : bsA_accum e.
  Proof. pose proof NBp as NB'. intros v Hv. rewrite pt_ft3 by exact Hv. exact (ClM_range (bp_a2 e) (bp_n e) ltac:(lia) (v + 1)). Qed.

  Theorem bsA_mono_ok : bsA_mono e.
  Proof.
    pose proof NBp as NB'. intros b Hb. rewrite !pt_ft4 by lia.
    pose proof (ClM_range (bp_a2 e) (bp_n e) ltac:(lia) (b * 256)).
    pose proof (ClM_range (bp_a2 e) (bp_n e) ltac:(lia) ((b + 1) * 256)).
    pose proof (ClM_mono (bp_a2 e) (bp_n e) (b * 256) ((b + 1) * 256) ltac:(lia)). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma s0_facts : 0 <= bp_s0 e < 65536 /\ bp_s0 e / 256 = rd8 (bp_a2 e) (nxt (bp_n e) (bp_n e - 1)).
  Proof.
    pose proof NBp as NB'. rewrite E_s0. rewrite shl8. pose proof (zbok_rd8 (bp_a2o e) 0 pt_a2o_zbok). rewrite pt_a2o by lia.
    pose proof (BBr 0). unfold nxt. rewrite Z.eqb_refl. split; [lia|]. rewrite Z.mul_comm, Z.div_mul by lia. reflexivity.
  Qed.

  Lemma EqA_all : forall v, EqA (bp_a2 e) (bp_n e) v (Z.to_nat (bp_n e)) = 0.
  Proof. intros v. unfold EqA. lia. Qed.
  Lemma EqA_step : forall v i, 0 <= i -> EqA (bp_a2 e) (bp_n e) v (Z.to_nat i) = EqA (bp_a2 e) (bp_n e) v (Z.to_nat (i + 1)) + (if key (bp_a2 e) (bp_n e) i =? v then 1 else 0).
  Proof. intros v i Hi. unfold EqA. replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. rewrite EqM_S. rewrite Z2Nat.id by lia. lia. Qed.

  Lemma radix2_inv : forall k, Z.of_nat k <= bp_n e ->
    let r := ms_radix2 k (bp_a1 e) (bp_a2o e) (bp_ft3 e) (bp_n e - 1) (bp_s0 e) in
    (forall v, 0 <= v <= 65536 -> zget (snd (fst r)) v = ClM (bp_a2 e) (bp_n e) (v + 1) - EqA (bp_a2 e) (bp_n e) v (Z.to_nat (bp_n e - Z.of_nat k))) /\
    0 <= snd r < 65536 /\ snd r / 256 = rd8 (bp_a2 e) (nxt (bp_n e) (bp_n e - 1 - Z.of_nat k)).
  Proof.
    pose proof NBp as NB'.
    induction k as [|k IH]; intros Hk; cbv zeta.
    - cbn [ms_radix2 fst snd]. destruct s0_facts as [S1 S2]. rewrite !Z.sub_0_r. split; [| split; [exact S1| exact S2]].
      intros v Hv. rewrite pt_ft3 by exact Hv. rewrite EqA_all. lia.
    - replace (S k) with (k + 1)%nat by lia. rewrite ms_radix2_app.
      cps_destruct (IH ltac:(lia)) as (F & SR & SD).
      destruct (ms_radix2 k (bp_a1 e) (bp_a2o e) (bp_ft3 e) (bp_n e - 1) (bp_s0 e)) as [[a1k ftk] sk]. cbn [fst snd] in F, SR, SD.
      change (ms_radix2 1) with (ms_radix2 (S 0)). rewrite (ms_radix2_step 0 a1k (bp_a2o e) ftk (bp_n e - 1 - Z.of_nat k) sk SR pt_a2o_zbok).
      cbv zeta. cbn [ms_radix2 fst snd].
      set (i' := bp_n e - 1 - Z.of_nat k) in *.
      assert (Hi' : 0 <= i' < bp_n e) by lia.
      assert (KEY : sk / 256 + 256 * zget (bp_a2o e) i' = key (bp_a2 e) (bp_n e) i').
      { rewrite SD. unfold key. change (zget (bp_a2o e) i') with (rd8 (bp_a2o e) i'). rewrite pt_a2o by exact Hi'. lia. }
      rewrite KEY. pose proof (key_range (bp_a2 e) (bp_n e) BBr i') as KR.
      split; [| split].
      + intros v Hv. rewrite zget_zset.
        replace (bp_n e - Z.of_nat (k + 1)) with i' by lia.
        destruct (Z.eqb_spec v (key (bp_a2 e) (bp_n e) i')) as [->|NE].
        * rewrite F by lia. replace (bp_n e - Z.of_nat k) with (i' + 1) by lia.
          rewrite (EqA_step (key (bp_a2 e) (bp_n e) i') i') by lia. rewrite Z.eqb_refl. lia.
        * rewrite F by lia. replace (bp_n e - Z.of_nat k) with (i' + 1) by lia.
          rewrite (EqA_step v i') by lia. destruct (Z.eqb_spec (key (bp_a2 e) (bp_n e) i') v); [congruence| lia].
      + exact KR.
      + replace (bp_n e - 1 - Z.of_nat (k + 1)) with (i' - 1) by lia. unfold key. unfold nxt at 2.
        destruct (Z.eqb_spec (i' - 1) (bp_n e - 1)); [lia|]. replace (i' - 1 + 1) with i' by lia.
        pose proof (BBr i'). pose proof (BBr (nxt (bp_n e) i')). rewrite Z.mul_comm, Z.div_add_l by lia. rewrite Z.div_small by lia. lia.
  Qed.

  Theorem bsA_radix2_ok : bsA_radix2 e.
  Proof.
    pose proof NBp as NB'. unfold bsA_radix2, r2ok. intros k Hk.
    pose proof (radix2_inv k ltac:(lia)) as R. cbv zeta in R.
    destruct (ms_radix2 k (bp_a1 e) (bp_a2o e) (bp_ft3 e) (bp_n e - 1) (bp_s0 e)) as [[a1k ftk] sk]. cbn [fst snd] in R. cps_destruct R as (F & SR & SD).
    set (i' := bp_n e - 1 - Z.of_nat k) in *. assert (Hi' : 0 <= i' < bp_n e) by lia.
    assert (KEY : sk / 256 + 256 * zget (bp_a2o e) i' = key (bp_a2 e) (bp_n e) i').
    { rewrite SD. unfold key. change (zget (bp_a2o e) i') with (rd8 (bp_a2o e) i'). rewrite pt_a2o by exact Hi'. lia. }
    rewrite KEY. pose proof (key_range (bp_a2 e) (bp_n e) BBr i') as KR. rewrite F by lia.
    replace (bp_n e - Z.of_nat k) with (i' + 1) by lia. unfold EqA.
    pose proof (ClM_step (bp_a2 e) (bp_n e) ltac:(lia) (key (bp_a2 e) (bp_n e) i')) as CS.
    assert (1 <= EqM (bp_a2 e) (bp_n e) (key (bp_a2 e) (bp_n e) i') (Z.to_nat (i' + 1))).
    { replace (Z.to_nat (i' + 1)) with (S (Z.to_nat i')) by lia. rewrite EqM_S. rewrite Z2Nat.id by lia. rewrite Z.eqb_refl.
      pose proof (EqM_nonneg (bp_a2 e) (bp_n e) (key (bp_a2 e) (bp_n e) i') (Z.to_nat i')). lia. }
    pose proof (EqM_mono (bp_a2 e) (bp_n e) (key (bp_a2 e) (bp_n e) i') (Z.to_nat (i' + 1)) (Z.to_nat (bp_n e)) ltac:(lia)).
    pose proof (ClM_range (bp_a2 e) (bp_n e) ltac:(lia) (key (bp_a2 e) (bp_n e) i')).
    pose proof (ClM_range (bp_a2 e) (bp_n e) ltac:(lia) (key (bp_a2 e) (bp_n e) i' + 1)). lia.
  Qed.
End J.

Theorem bs_facts_intro : forall e, zbok (e_arr2 e) -> 34 <= e_nblock e <= 1000000 -> bs_facts e.
Proof.
  intros e BB NB. split; [| split].
  - apply bsA_accum_ok; assumption.
  - apply bsA_radix2_ok; assumption.
  - apply bsA_mono_ok; assumption.
Qed.

End ACeilS1.
