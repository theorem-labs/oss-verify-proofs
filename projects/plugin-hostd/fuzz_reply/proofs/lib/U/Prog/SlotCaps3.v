From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0g YO0d YO03 PlaceCap.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import AllocPack AllocPackRoom AllocPack3 AllocPack3Room
  SlotPack.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import SlotParse.
Import ListNotations.
Local Open Scope Z_scope.

Definition CAPS0 : Z := 67109022.

Definition CBASE : Z := 1669.

Definition cs_band (pl : list byte) (c : Z) : Z := if c =? 0 then CAPS0 else CBASE + x_c c pl.

Definition CS_reply (pl : list byte) : list Z := map (cs_band pl) (zseq 0 49).

Definition MC_ONE : Z := 27.

Definition MC_reply : list Z := repeat MC_ONE 49.

Definition GALLB3 : Z := 2674469.

Definition GMAPB3 : Z := 134167.

Definition BMAX : Z := 2 ^ 44.

Definition NMAX : Z := 2 ^ 29 + 2 ^ 13.

Lemma znth_map_zseq (f : Z -> Z) n c : 0 <= c < n -> znth c (map f (zseq 0 n)) = f c.
Proof.
  intros Hc. unfold znth.
  assert (L : (Z.to_nat c < length (zseq 0 n))%nat) by (unfold zseq; rewrite length_map, length_seq; lia).
  rewrite (nth_indep (map f (zseq 0 n)) 0 (f 0)) by (rewrite length_map; exact L).
  rewrite map_nth. f_equal. unfold zseq in *. rewrite length_map in L.
  rewrite (nth_indep (map (fun k : nat => 0 + Z.of_nat k) (seq 0 (Z.to_nat n))) 0
    ((fun k : nat => 0 + Z.of_nat k) 0%nat)) by (rewrite length_map; exact L).
  rewrite (map_nth (fun k : nat => 0 + Z.of_nat k)). rewrite length_seq in L. rewrite seq_nth by exact L.
  cbv beta. rewrite Nat.add_0_l, Z2Nat.id by lia. lia.
Qed.

Lemma CS_reply_len pl : length (CS_reply pl) = 49%nat.
Proof. unfold CS_reply, zseq. rewrite !length_map, length_seq. reflexivity. Qed.

Lemma CS_reply_at pl c : 0 <= c < 49 -> znth c (CS_reply pl) = cs_band pl c.
Proof. intros Hc. unfold CS_reply. apply znth_map_zseq. exact Hc. Qed.

Lemma cs_band_ge pl c : PCAP0 <= cs_band pl c.
Proof.
  unfold cs_band, PCAP0, CAPS0, CBASE. pose proof (x_nonneg c pl). destruct (c =? 0); lia.
Qed.

Theorem CS_reply_ok : CS_ok CS_reply.
Proof.
  intros pl. split; [apply CS_reply_len|]. intros k Hk. rewrite CS_reply_at by exact Hk. apply cs_band_ge.
Qed.

Lemma CS_reply_nonneg pl k : 0 <= k < 49 -> 0 <= znth k (CS_reply pl).
Proof. intros Hk. rewrite CS_reply_at by exact Hk. pose proof (cs_band_ge pl k). unfold PCAP0 in *. lia. Qed.

Lemma MC_reply_len : length MC_reply = 49%nat.
Proof. apply repeat_length. Qed.

Lemma MC_reply_at k : 0 <= k < 49 -> znth k MC_reply = MC_ONE.
Proof.
  intros Hk. unfold znth, MC_reply. rewrite (nth_indep (repeat MC_ONE 49) 0 MC_ONE) by (rewrite repeat_length; lia).
  apply nth_repeat.
Qed.

Lemma MC_reply_nonneg k : 0 <= znth k MC_reply.
Proof.
  unfold znth, MC_reply. destruct (Nat.lt_ge_cases (Z.to_nat k) 49) as [L|L].
  - rewrite (nth_indep (repeat MC_ONE 49) 0 MC_ONE) by (rewrite repeat_length; exact L).
    rewrite nth_repeat. unfold MC_ONE. lia.
  - rewrite nth_overflow by (rewrite repeat_length; exact L). lia.
Qed.

Lemma zseq_049 : zseq 0 49 = 0 :: zseq 1 48.
Proof. reflexivity. Qed.

Lemma beta3_tab : forallb (fun k => znth k pk3_BETA <=? 512239 * band_lo k) (zseq 1 48) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma mu3_tab : forallb (fun k => znth k pk3_MU <=? 65930 * band_lo k) (zseq 1 48) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma beta3_sum : zsumZ (fun k => znth k pk3_BETA) (zseq 1 48) = 637427671.
Proof. vm_compute. reflexivity. Qed.

Lemma mu3_sum : zsumZ (fun k => znth k pk3_MU) (zseq 1 48) = 585892823.
Proof. vm_compute. reflexivity. Qed.

Lemma gamma3_mc : zsumZ (fun k => znth k pk3_GAMMA * znth k MC_reply) (zseq 0 49) = 11996681607.
Proof. vm_compute. reflexivity. Qed.

Lemma nu3_mc : zsumZ (fun k => znth k pk3_NU * znth k MC_reply) (zseq 0 49) = 10425252231.
Proof. vm_compute. reflexivity. Qed.

Lemma lin_bound (W : list Z) (R S : Z) pl :
  forallb (fun k => znth k W <=? R * band_lo k) (zseq 1 48) = true -> 0 <= R ->
  (forall k, 0 <= znth k W) ->
  zsumZ (fun k => znth k W) (zseq 1 48) = S ->
  zsumZ (fun k => znth k W * znth k (CS_reply pl)) (zseq 0 49) <=
  znth 0 W * CAPS0 + CBASE * S + R * (4 * BTEXT + 2 ^ 20).
Proof.
  intros T HR HW HS. rewrite zseq_049, zsumZ_cons. rewrite (CS_reply_at pl 0) by lia.
  change (cs_band pl 0) with CAPS0.
  rewrite (zsumZ_ext _ (fun k => CBASE * znth k W + znth k W * x_c k pl)).
  2: { intros k Hk. apply In_zseq in Hk. cbv beta. rewrite CS_reply_at by lia. unfold cs_band.
       destruct (Z.eqb_spec k 0); [lia|]. ring. }
  rewrite zsumZ_add, zsumZ_mul_l, HS.
  assert (H1 : zsumZ (fun k => znth k W * x_c k pl) (zseq 1 48) <= zsumZ (fun k => R * (band_lo k * x_c k pl)) (zseq 1 48)).
  { apply zsumZ_le. intros k Hk. cbv beta. rewrite forallb_forall in T. specialize (T k Hk). cbv beta in T.
    apply Z.leb_le in T. pose proof (x_nonneg k pl). pose proof (HW k). nia. }
  rewrite zsumZ_mul_l in H1. pose proof (Z.mul_le_mono_nonneg_l _ _ R HR (x_weighted pl)). lia.
Qed.

Lemma tab_nonneg (W : list Z) k : forallb (fun x => 0 <=? x) W = true -> 0 <= znth k W.
Proof.
  intros T. unfold znth. destruct (Nat.lt_ge_cases (Z.to_nat k) (length W)) as [L|L].
  - rewrite forallb_forall in T. apply Z.leb_le. apply T. apply nth_In. exact L.
  - rewrite nth_overflow by exact L. lia.
Qed.

Lemma pk3_BETA_nonneg k : 0 <= znth k pk3_BETA.
Proof. apply tab_nonneg. vm_compute. reflexivity. Qed.

Lemma pk3_MU_nonneg k : 0 <= znth k pk3_MU.
Proof. apply tab_nonneg. vm_compute. reflexivity. Qed.

Lemma caps_mc_nonneg pl k : 0 <= k < 49 -> 0 <= znth k (CS_reply pl) /\ 0 <= znth k MC_reply.
Proof. intros Hk. split; [exact (CS_reply_nonneg pl k Hk)|apply MC_reply_nonneg]. Qed.

Theorem CS_reply_GALL3 pl : GALL3 (CS_reply pl) MC_reply <= GALLB3.
Proof.
  pose proof (GALL3_lin (CS_reply pl) MC_reply (CS_reply_len pl) MC_reply_len (caps_mc_nonneg pl)) as H.
  pose proof (lin_bound pk3_BETA 512239 637427671 pl beta3_tab ltac:(lia) pk3_BETA_nonneg beta3_sum) as H2.
  rewrite gamma3_mc in H. change (znth 0 pk3_BETA) with 6881070 in H2.
  unfold pk3_D, pk3_G0 in H. unfold GALLB3, CAPS0, CBASE, BTEXT in *. lia.
Qed.

Theorem CS_reply_GMAP3 pl : GMAP3 (CS_reply pl) MC_reply <= GMAPB3.
Proof.
  pose proof (GMAP3_lin (CS_reply pl) MC_reply (CS_reply_len pl) MC_reply_len (caps_mc_nonneg pl)) as H.
  pose proof (lin_bound pk3_MU 65930 585892823 pl mu3_tab ltac:(lia) pk3_MU_nonneg mu3_sum) as H2.
  rewrite nu3_mc in H. change (znth 0 pk3_MU) with 214830 in H2.
  unfold pk3_D, pk3_M0 in H. unfold GMAPB3, CAPS0, CBASE, BTEXT in *. lia.
Qed.

Lemma capok3_B : CAPOK2 GALLB3 GMAPB3 BMAX NMAX.
Proof. unfold CAPOK2. repeat split; first [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity. Qed.

Theorem CS_reply_capok3 pl : CAPOK2 (GALL3 (CS_reply pl) MC_reply) (GMAP3 (CS_reply pl) MC_reply) BMAX NMAX.
Proof.
  apply (CAPOK2_mono GALLB3 GMAPB3 BMAX NMAX);
    [apply CS_reply_GALL3 | apply CS_reply_GMAP3 | lia | lia | exact capok3_B].
Qed.
