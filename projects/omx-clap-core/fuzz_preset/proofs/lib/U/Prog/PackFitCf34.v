From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0g YO0s YO0d YO0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM0b.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import AllocPack AllocPackRoom SlotAgree
  AllocPackGSF AllocPackFit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import AgreeLim.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import PackFit PackOwn.
Import ListNotations.
Local Open Scope Z_scope.

(* U twin of Prog/PackFitCf.v (c-frame-gi, db362d2b84), with the ubsan build's modules: fuzz_preset's caps fit the agreement's sanitizer budget: the cut-free pack room LIVE2c of CS_of (beta2_x x) plus
   NONHEAP_CF stays under LIM_AG, for every payload of at most pf_MAX bytes and every call with at most pf_BMAX live
   bytes. *)

Definition LWk (k : Z) : Z := METAS_PER_AREA * MWf k + 3 * PGSZ * znth k pk_BETA.

Definition pfc_R : Z := 5190667776000.

Lemma pfc_ratio_tab : forallb (fun k => (pv k =? 0) || (LWk k <=? pfc_R * pv k)) (zseq 0 49) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pfc_LW_nonneg_tab : forallb (fun k => 0 <=? LWk k) (zseq 0 49) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pfc_const : 3 * pfc_R * (2 * pf_MAX + pf_E) + 271 * zsumZ LWk (zseq 0 49) +
  (METAS_PER_AREA * MW0 + 3 * PGSZ * pk_G0) + METAS_PER_AREA * pk_D * (pf_BMAX + 84 * PGSZ) <=
  METAS_PER_AREA * pk_D * (LIM_AG - NONHEAP_CF).
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

Theorem pack_own_fit_cf : forall x bytes, Z.of_nat (length x) <= pf_MAX -> 0 <= bytes <= pf_BMAX ->
  LIVE2c (CS_of (beta2_x x)) bytes + NONHEAP_CF <= LIM_AG.
Proof.
  intros x bytes Hn Hb. destruct (beta2_x_own x) as (H0 & Hz & Hs).
  set (beta := beta2_x x) in *.
  assert (Hc : forall k, 0 <= k < 49 -> 0 <= znth k (CS_of beta)) by (intros k Hk; rewrite CS_of_nth by exact Hk; pose proof (H0 k); lia).
  pose proof (LIVE2c_lin (CS_of beta) bytes (CS_of_len beta) Hc) as HL.
  assert (E : zsumZ (fun k => (METAS_PER_AREA * MWf k + 3 * PGSZ * znth k pk_BETA) * znth k (CS_of beta)) (zseq 0 49) =
     3 * zsumZ (fun k => LWk k * beta k) (zseq 0 49) + 271 * zsumZ LWk (zseq 0 49)).
  { rewrite <- !zsumZ_mul_l, <- zsumZ_add. apply zsumZ_ext. intros k Hk. apply In_zseq in Hk.
    rewrite CS_of_nth by lia. unfold LWk. ring. }
  assert (R : zsumZ (fun k => LWk k * beta k) (zseq 0 49) <= pfc_R * zsumZ (fun k => pv k * beta k) (zseq 0 49)).
  { rewrite <- zsumZ_mul_l. apply zsumZ_le. intros k Hk. apply In_zseq in Hk. cbv beta.
    pose proof (H0 k) as B.
    pose proof pfc_ratio_tab as T. rewrite forallb_forall in T. specialize (T k (proj2 (In_zseq 0 49 k) ltac:(lia))).
    destruct (Z.eq_dec (pv k) 0) as [P|P].
    - assert (k = 0).
      { destruct (Z.eq_dec k 0) as [|K]; [assumption|]. exfalso. revert P. unfold pv.
        assert (Tp : forallb (fun k => (k =? 0) || negb (znth k pv_tab =? 0)) (zseq 0 49) = true) by (vm_compute; reflexivity).
        rewrite forallb_forall in Tp. specialize (Tp k (proj2 (In_zseq 0 49 k) ltac:(lia))).
        apply orb_true_iff in Tp as [Tp|Tp]; [apply Z.eqb_eq in Tp; lia|]. apply negb_true_iff, Z.eqb_neq in Tp. exact Tp. }
      subst k. rewrite Hz. lia.
    - apply orb_true_iff in T as [T|T]; [apply Z.eqb_eq in T; contradiction|]. apply Z.leb_le in T.
      assert (LWk k * beta k <= (pfc_R * pv k) * beta k) by (apply Z.mul_le_mono_nonneg_r; lia). lia. }
  pose proof pfc_const as C.
  assert (Hpv : 0 <= zsumZ (fun k => pv k * beta k) (zseq 0 49)).
  { apply zsumZ_nonneg. intros k _. pose proof (pv_nonneg k). pose proof (H0 k). nia. }
  rewrite E in HL. rewrite LIM_AG_eq in *.
  unfold NONHEAP_CF, pfc_R, pf_MAX, pf_E, pf_BMAX, METAS_PER_AREA, pk_D, PGSZ in *. lia.
Qed.

(* The plain run (budget SRC_LIM_MIN = 2^34) with the run's byte bound 256 |x| + 16448. *)
Lemma pfc_const_plain : 3 * pfc_R * (2 * pf_MAX + pf_E) + 271 * zsumZ LWk (zseq 0 49) +
  (METAS_PER_AREA * MW0 + 3 * PGSZ * pk_G0) + METAS_PER_AREA * pk_D * (256 * pf_MAX + 16448 + 84 * PGSZ) <=
  METAS_PER_AREA * pk_D * (SRC_LIM_MIN - NONHEAP_CF).
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

Theorem pack_own_fit_cf_plain : forall x bytes, Z.of_nat (length x) <= pf_MAX ->
  0 <= bytes <= 256 * Z.of_nat (length x) + 16448 ->
  LIVE2c (CS_of (beta2_x x)) bytes + NONHEAP_CF <= SRC_LIM_MIN.
Proof.
  intros x bytes Hn Hb. destruct (beta2_x_own x) as (H0 & Hz & Hs).
  set (beta := beta2_x x) in *.
  assert (Hc : forall k, 0 <= k < 49 -> 0 <= znth k (CS_of beta)) by (intros k Hk; rewrite CS_of_nth by exact Hk; pose proof (H0 k); lia).
  pose proof (LIVE2c_lin (CS_of beta) bytes (CS_of_len beta) Hc) as HL.
  assert (E : zsumZ (fun k => (METAS_PER_AREA * MWf k + 3 * PGSZ * znth k pk_BETA) * znth k (CS_of beta)) (zseq 0 49) =
     3 * zsumZ (fun k => LWk k * beta k) (zseq 0 49) + 271 * zsumZ LWk (zseq 0 49)).
  { rewrite <- !zsumZ_mul_l, <- zsumZ_add. apply zsumZ_ext. intros k Hk. apply In_zseq in Hk.
    rewrite CS_of_nth by lia. unfold LWk. ring. }
  assert (R : zsumZ (fun k => LWk k * beta k) (zseq 0 49) <= pfc_R * zsumZ (fun k => pv k * beta k) (zseq 0 49)).
  { rewrite <- zsumZ_mul_l. apply zsumZ_le. intros k Hk. apply In_zseq in Hk. cbv beta.
    pose proof (H0 k) as B.
    pose proof pfc_ratio_tab as T. rewrite forallb_forall in T. specialize (T k (proj2 (In_zseq 0 49 k) ltac:(lia))).
    destruct (Z.eq_dec (pv k) 0) as [P|P].
    - assert (k = 0).
      { destruct (Z.eq_dec k 0) as [|K]; [assumption|]. exfalso. revert P. unfold pv.
        assert (Tp : forallb (fun k => (k =? 0) || negb (znth k pv_tab =? 0)) (zseq 0 49) = true) by (vm_compute; reflexivity).
        rewrite forallb_forall in Tp. specialize (Tp k (proj2 (In_zseq 0 49 k) ltac:(lia))).
        apply orb_true_iff in Tp as [Tp|Tp]; [apply Z.eqb_eq in Tp; lia|]. apply negb_true_iff, Z.eqb_neq in Tp. exact Tp. }
      subst k. rewrite Hz. lia.
    - apply orb_true_iff in T as [T|T]; [apply Z.eqb_eq in T; contradiction|]. apply Z.leb_le in T.
      assert (LWk k * beta k <= (pfc_R * pv k) * beta k) by (apply Z.mul_le_mono_nonneg_r; lia). lia. }
  pose proof pfc_const_plain as C.
  assert (Hpv : 0 <= zsumZ (fun k => pv k * beta k) (zseq 0 49)).
  { apply zsumZ_nonneg. intros k _. pose proof (pv_nonneg k). pose proof (H0 k). nia. }
  rewrite E in HL.
  unfold SRC_LIM_MIN, NONHEAP_CF, pfc_R, pf_MAX, pf_E, METAS_PER_AREA, pk_D, PGSZ in *. lia.
Qed.

(* The plain run (budget 2^34) for every byte count up to BBMAX. *)
Definition BBMAX : Z := 3794103235.
Lemma pfc_const_BB : 3 * pfc_R * (2 * pf_MAX + pf_E) + 271 * zsumZ LWk (zseq 0 49) +
  (METAS_PER_AREA * MW0 + 3 * PGSZ * pk_G0) + METAS_PER_AREA * pk_D * (BBMAX + 84 * PGSZ) <=
  METAS_PER_AREA * pk_D * (SRC_LIM_MIN - NONHEAP_CF).
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

Theorem pack_fit_cf_plain_BB : forall x, Z.of_nat (length x) <= pf_MAX -> forall bytes, 0 <= bytes <= BBMAX ->
  LIVE2c (CS_of (beta2_x x)) bytes + NONHEAP_CF <= 2 ^ 34.
Proof.
  intros x Hn bytes Hb. destruct (beta2_x_own x) as (H0 & Hz & Hs).
  set (beta := beta2_x x) in *.
  assert (Hc : forall k, 0 <= k < 49 -> 0 <= znth k (CS_of beta)) by (intros k Hk; rewrite CS_of_nth by exact Hk; pose proof (H0 k); lia).
  pose proof (LIVE2c_lin (CS_of beta) bytes (CS_of_len beta) Hc) as HL.
  assert (E : zsumZ (fun k => (METAS_PER_AREA * MWf k + 3 * PGSZ * znth k pk_BETA) * znth k (CS_of beta)) (zseq 0 49) =
     3 * zsumZ (fun k => LWk k * beta k) (zseq 0 49) + 271 * zsumZ LWk (zseq 0 49)).
  { rewrite <- !zsumZ_mul_l, <- zsumZ_add. apply zsumZ_ext. intros k Hk. apply In_zseq in Hk.
    rewrite CS_of_nth by lia. unfold LWk. ring. }
  assert (R : zsumZ (fun k => LWk k * beta k) (zseq 0 49) <= pfc_R * zsumZ (fun k => pv k * beta k) (zseq 0 49)).
  { rewrite <- zsumZ_mul_l. apply zsumZ_le. intros k Hk. apply In_zseq in Hk. cbv beta.
    pose proof (H0 k) as B.
    pose proof pfc_ratio_tab as T. rewrite forallb_forall in T. specialize (T k (proj2 (In_zseq 0 49 k) ltac:(lia))).
    destruct (Z.eq_dec (pv k) 0) as [P|P].
    - assert (k = 0).
      { destruct (Z.eq_dec k 0) as [|K]; [assumption|]. exfalso. revert P. unfold pv.
        assert (Tp : forallb (fun k => (k =? 0) || negb (znth k pv_tab =? 0)) (zseq 0 49) = true) by (vm_compute; reflexivity).
        rewrite forallb_forall in Tp. specialize (Tp k (proj2 (In_zseq 0 49 k) ltac:(lia))).
        apply orb_true_iff in Tp as [Tp|Tp]; [apply Z.eqb_eq in Tp; lia|]. apply negb_true_iff, Z.eqb_neq in Tp. exact Tp. }
      subst k. rewrite Hz. lia.
    - apply orb_true_iff in T as [T|T]; [apply Z.eqb_eq in T; contradiction|]. apply Z.leb_le in T.
      assert (LWk k * beta k <= (pfc_R * pv k) * beta k) by (apply Z.mul_le_mono_nonneg_r; lia). lia. }
  pose proof pfc_const_BB as C.
  assert (Hpv : 0 <= zsumZ (fun k => pv k * beta k) (zseq 0 49)).
  { apply zsumZ_nonneg. intros k _. pose proof (pv_nonneg k). pose proof (H0 k). nia. }
  rewrite E in HL.
  unfold SRC_LIM_MIN, BBMAX, NONHEAP_CF, pfc_R, pf_MAX, pf_E, METAS_PER_AREA, pk_D, PGSZ in *. lia.
Qed.
