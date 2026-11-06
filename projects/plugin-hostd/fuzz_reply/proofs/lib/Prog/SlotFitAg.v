From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0g YO0d YO03 YO0q PlaceCap
  PlaceCapW YM0b.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import AllocPack AllocPackRoom AllocPack3 AllocPack3Room
  AllocPackGSF AllocPackFit SlotPack AgreeRoom AllocPack3Cf AllocPack3Ag.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import SlotParse SlotCaps3 SlotRI3.
Import ListNotations.
Local Open Scope Z_scope.

Definition fit_W (k : Z) : Z := METAS_PER_AREA * MWf k + 3 * PGSZ * znth k pk_BETA.

Definition fit_Wl : list Z := map fit_W (zseq 0 49).

Definition FIT_R : Z := 108941910647.

Definition FIT_S : Z := 17187646423453696.

Definition FIT_MC : Z := 457319554302431232.

Lemma fit_Wl_at k : 0 <= k < 49 -> znth k fit_Wl = fit_W k.
Proof. intros Hk. unfold fit_Wl. apply znth_map_zseq. exact Hk. Qed.

Lemma fit_tab : forallb (fun k => znth k fit_Wl <=? FIT_R * band_lo k) (zseq 1 48) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma fit_sum : zsumZ (fun k => znth k fit_Wl) (zseq 1 48) = FIT_S.
Proof. vm_compute. reflexivity. Qed.

Lemma fit_mc : zsumZ (fun k => fit_W k * (if k <? 48 then MC_ONE else 0)) (zseq 0 49) = FIT_MC.
Proof. vm_compute. reflexivity. Qed.

Lemma fit_Wl_nonneg k : 0 <= znth k fit_Wl.
Proof. apply tab_nonneg. vm_compute. reflexivity. Qed.

Lemma fit_W0 : znth 0 fit_Wl = 774003793920.
Proof. vm_compute. reflexivity. Qed.

Lemma pk3cm_reply_len pl : length (pk3_cm (CS_reply pl) MC_reply) = 49%nat.
Proof. unfold pk3_cm, zseq. rewrite !length_map, length_seq. reflexivity. Qed.

Lemma pk3cm_reply_at pl k : 0 <= k < 49 ->
  znth k (pk3_cm (CS_reply pl) MC_reply) = znth k (CS_reply pl) + (if k <? 48 then MC_ONE else 0).
Proof.
  intros Hk. unfold pk3_cm. rewrite (pk3_map_zseq _ k Hk). cbv beta. rewrite (MC_reply_at k Hk). reflexivity.
Qed.

Lemma pk3cm_reply_nonneg pl k : 0 <= k < 49 -> 0 <= znth k (pk3_cm (CS_reply pl) MC_reply).
Proof.
  intros Hk. rewrite (pk3cm_reply_at pl k Hk). pose proof (CS_reply_nonneg pl k Hk).
  destruct (k <? 48); unfold MC_ONE; lia.
Qed.

Lemma fit_split pl :
  zsumZ (fun k => fit_W k * znth k (pk3_cm (CS_reply pl) MC_reply)) (zseq 0 49) =
  zsumZ (fun k => znth k fit_Wl * znth k (CS_reply pl)) (zseq 0 49) + FIT_MC.
Proof.
  rewrite <- fit_mc, <- zsumZ_add. apply zsumZ_ext. intros k Hk. apply In_zseq in Hk. cbv beta.
  rewrite (pk3cm_reply_at pl k ltac:(lia)), (fit_Wl_at k ltac:(lia)). ring.
Qed.

Theorem live3c_lin_reply pl bytes :
  METAS_PER_AREA * pk_D * LIVE3c (CS_reply pl) MC_reply bytes <=
  774003793920 * CAPS0 + CBASE * FIT_S + FIT_R * (4 * BTEXT + 2 ^ 20) + FIT_MC +
  METAS_PER_AREA * MW0 + 3 * PGSZ * pk_G0 + METAS_PER_AREA * pk_D * (bytes + 84 * PGSZ).
Proof.
  unfold LIVE3c.
  pose proof (LIVE2c_lin (pk3_cm (CS_reply pl) MC_reply) bytes (pk3cm_reply_len pl) (pk3cm_reply_nonneg pl)) as H.
  change (fun k => (METAS_PER_AREA * MWf k + 3 * PGSZ * znth k pk_BETA) * znth k (pk3_cm (CS_reply pl) MC_reply))
    with (fun k => fit_W k * znth k (pk3_cm (CS_reply pl) MC_reply)) in H.
  rewrite fit_split in H.
  pose proof (lin_bound fit_Wl FIT_R FIT_S pl fit_tab ltac:(unfold FIT_R; lia) fit_Wl_nonneg fit_sum) as H2.
  rewrite fit_W0 in H2. unfold METAS_PER_AREA, pk_D, PGSZ in *. lia.
Qed.

Lemma fit_const : 774003793920 * CAPS0 + CBASE * FIT_S + FIT_R * (4 * BTEXT + 2 ^ 20) + FIT_MC +
  METAS_PER_AREA * MW0 + 3 * PGSZ * pk_G0 + METAS_PER_AREA * pk_D * (CF_MAX + 84 * PGSZ) <=
  METAS_PER_AREA * pk_D * (SRC_LIM_MIN - NONHEAP_CF).
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

Theorem live3c_fit pl bytes : bytes <= CF_MAX -> LIVE3c (CS_reply pl) MC_reply bytes + NONHEAP_CF <= SRC_LIM_MIN.
Proof.
  intros Hb. pose proof (live3c_lin_reply pl bytes) as H. pose proof fit_const as C.
  unfold METAS_PER_AREA, pk_D, PGSZ in *. lia.
Qed.

Lemma slots_const : SLOTS2 GALLB3 GMAPB3 + 5 + KRES <= slot_capW (RQ2 GALLB3 NMAX + PGSZ).
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

Lemma RQ2_mono H H' n n' : H <= H' -> n <= n' -> RQ2 H n <= RQ2 H' n'.
Proof.
  intros HH Hn. unfold RQ2, AREA2.
  pose proof (page_round_mono (n + IB + UNIT) (n' + IB + UNIT) ltac:(lia)).
  pose proof (Z.div_le_mono H H' METAS_PER_AREA ltac:(unfold METAS_PER_AREA; lia) HH). unfold PGSZ. lia.
Qed.

Theorem slots_fit pl n : 0 <= n <= NMAX ->
  SLOTS2 (GALL3 (CS_reply pl) MC_reply) (GMAP3 (CS_reply pl) MC_reply) + 5 + KRES <=
    slot_capW (RQ2 (GALL3 (CS_reply pl) MC_reply) n + PGSZ).
Proof.
  intros Hn. pose proof (CS_reply_GALL3 pl) as HG. pose proof (CS_reply_GMAP3 pl) as HM.
  pose proof slots_const as C.
  assert (A1 : SLOTS2 (GALL3 (CS_reply pl) MC_reply) (GMAP3 (CS_reply pl) MC_reply) <= SLOTS2 GALLB3 GMAPB3).
  { unfold SLOTS2, NA2. pose proof (Z.div_le_mono _ _ METAS_PER_AREA ltac:(unfold METAS_PER_AREA; lia) HG). lia. }
  assert (R1 : 0 < RQ2 (GALL3 (CS_reply pl) MC_reply) n + PGSZ) by (unfold RQ2, MMAX, PGSZ; lia).
  pose proof (RQ2_mono _ _ _ _ HG (proj2 Hn)) as R2.
  assert (R3 : 0 < RQ2 (GALL3 (CS_reply pl) MC_reply) n + PGSZ <= RQ2 GALLB3 NMAX + PGSZ) by lia.
  pose proof (slot_capW_anti _ _ R3) as W. lia.
Qed.

Theorem RMH_ag pl b n : p3_cap b = CS_reply pl -> p3_mcap b = MC_reply -> 0 <= n <= NMAX ->
  p3_bytes b + n <= CF_MAX -> RM_ag b n.
Proof.
  intros HC HM Hn Hb. unfold RM_ag. rewrite HC, HM. split; [exact (live3c_fit pl _ Hb) | exact (slots_fit pl n Hn)].
Qed.
