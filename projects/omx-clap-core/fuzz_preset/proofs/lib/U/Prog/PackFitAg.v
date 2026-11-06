From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0g YO0s YO0d YO0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import AllocPack AllocPackRoom SlotAgree
  AllocPackGSF AllocPackFit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import AgreeLim.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import PackFit PackOwn.
Import ListNotations.
Local Open Scope Z_scope.

(* fuzz_preset's caps fit the agreement's sanitizer budget: the cut-free pack room LIVE2c of CS_of (beta2_x x) plus
   NONHEAP_CF stays under LIM_AG, for every payload of at most pf_MAX bytes and every call with at most BB_AG live
   bytes. *)

Definition BB_AG : Z := 2 ^ 36.

Definition LWk (k : Z) : Z := METAS_PER_AREA * MWf k + 3 * PGSZ * znth k pk_BETA.

Definition pfa_R : Z := 5190667776000.

Lemma pfa_ratio_tab : forallb (fun k => (pv k =? 0) || (LWk k <=? pfa_R * pv k)) (zseq 0 49) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pfa_const : 3 * pfa_R * (2 * pf_MAX + pf_E) + 271 * zsumZ LWk (zseq 0 49) +
  (METAS_PER_AREA * MW0 + 3 * PGSZ * pk_G0) + METAS_PER_AREA * pk_D * (BB_AG + 84 * PGSZ) <=
  METAS_PER_AREA * pk_D * (LIM_AG - NONHEAP_CF).
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

Theorem pack_own_fit_ag : forall x bytes, Z.of_nat (length x) <= pf_MAX -> 0 <= bytes <= BB_AG ->
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
  assert (R : zsumZ (fun k => LWk k * beta k) (zseq 0 49) <= pfa_R * zsumZ (fun k => pv k * beta k) (zseq 0 49)).
  { rewrite <- zsumZ_mul_l. apply zsumZ_le. intros k Hk. apply In_zseq in Hk. cbv beta.
    pose proof (H0 k) as B.
    pose proof pfa_ratio_tab as T. rewrite forallb_forall in T. specialize (T k (proj2 (In_zseq 0 49 k) ltac:(lia))).
    destruct (Z.eq_dec (pv k) 0) as [P|P].
    - assert (k = 0).
      { destruct (Z.eq_dec k 0) as [|K]; [assumption|]. exfalso. revert P. unfold pv.
        assert (Tp : forallb (fun k => (k =? 0) || negb (znth k pv_tab =? 0)) (zseq 0 49) = true) by (vm_compute; reflexivity).
        rewrite forallb_forall in Tp. specialize (Tp k (proj2 (In_zseq 0 49 k) ltac:(lia))).
        apply orb_true_iff in Tp as [Tp|Tp]; [apply Z.eqb_eq in Tp; lia|]. apply negb_true_iff, Z.eqb_neq in Tp. exact Tp. }
      subst k. rewrite Hz. lia.
    - apply orb_true_iff in T as [T|T]; [apply Z.eqb_eq in T; contradiction|]. apply Z.leb_le in T.
      assert (LWk k * beta k <= (pfa_R * pv k) * beta k) by (apply Z.mul_le_mono_nonneg_r; lia). lia. }
  pose proof pfa_const as C.
  assert (Hpv : 0 <= zsumZ (fun k => pv k * beta k) (zseq 0 49)).
  { apply zsumZ_nonneg. intros k _. pose proof (pv_nonneg k). pose proof (H0 k). nia. }
  rewrite E in HL. rewrite LIM_AG_eq in *.
  unfold NONHEAP_CF, pfa_R, pf_MAX, pf_E, BB_AG, METAS_PER_AREA, pk_D, PGSZ in *. lia.
Qed.
