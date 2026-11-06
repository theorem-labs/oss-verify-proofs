From Stdlib Require Import ZArith List Bool Lia Arith.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0g YO0s YO0u YO0x YO10 YO0q YO0d YO03 YO0j YO0m YO0n YO0o YO04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import PlaceCap.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import AllocSI AllocGS AllocMB AllocCount AllocBound AllocSlots AllocPack AllocPackRoom.
Import ListNotations.
Local Open Scope Z_scope.

Definition pw_tab : list Z := [0; 1; 12; 28; 44; 1; 76; 92; 108; 9; 140; 172; 17; 268; 300; 2; 33; 556; 652; 10; 65;
  1132; 1324; 18; 129; 2316; 2700; 34; 257; 4652; 5420; 66; 513; 9324; 10892; 130; 1025; 18684; 21804; 258; 2049;
  37420; 43660; 514; 4097; 74860; 87340; 1026; 2050].

Definition pw (k : Z) : Z := znth k pw_tab.

Definition pv_tab : list Z := [0; 1; 1; 12; 17; 2; 28; 33; 38; 18; 49; 60; 34; 92; 102; 4; 66; 188; 220; 20; 130; 380;
  444; 36; 258; 774; 902; 68; 514; 1553; 1809; 132; 1026; 3110; 3633; 260; 2050; 6230; 7270; 516; 4098; 12476; 14556;
  1028; 8194; 24956; 29116; 2052; 4100].

Definition pv (k : Z) : Z := znth k pv_tab.

Definition pf_RATIO : Z := 328689900.

Definition pf_RB : Z := 20643210.

Definition pf_MAX : Z := 3145728.

Definition pf_E : Z := 128.

Definition pf_BMAX : Z := 2 ^ 32 - 1.

Definition pf_NMAX : Z := 352321430.

Lemma pf_tab_at (f : Z -> bool) k : forallb f (zseq 0 49) = true -> 0 <= k < 49 -> f k = true.
Proof. intros H Hk. rewrite forallb_forall in H. apply H. apply In_zseq. lia. Qed.

Lemma pf_tab_nonneg l : forallb (fun z => 0 <=? z) l = true -> forall k, 0 <= znth k l.
Proof.
  intros T k. apply znth_nonneg.
  rewrite forallb_forall in T. apply Forall_forall. intros z Hz. apply Z.leb_le, T, Hz.
Qed.

Lemma pw_nonneg k : 0 <= pw k.
Proof. apply pf_tab_nonneg. reflexivity. Qed.

Lemma pv_nonneg k : 0 <= pv k.
Proof. apply pf_tab_nonneg. reflexivity. Qed.

Lemma pw_pos_tab : forallb (fun k => (k =? 0) || (1 <=? pw k)) (zseq 0 49) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pv_ratio_tab :
  forallb (fun k => (pv k =? 0) || (2 * (101 * znth k pk_MU + znth k pk_BETA) <=? pf_RATIO * pv k)) (zseq 0 49) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pv_beta_tab : forallb (fun k => (pv k =? 0) || (2 * znth k pk_BETA <=? pf_RB * pv k)) (zseq 0 49) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pv_pw_tab : forallb (fun k => (pv k <=? 2 * pw k) && (negb (pv k =? 0) || (pw k =? 0))) (zseq 0 49) = true.
Proof. vm_compute. reflexivity. Qed.

Theorem pw_zero : pw 0 = 0.
Proof. reflexivity. Qed.

Theorem pw_pos : forall k, 1 <= k < 49 -> 1 <= pw k.
Proof.
  intros k Hk. pose proof (pf_tab_at _ k pw_pos_tab ltac:(lia)) as T. cbv beta in T.
  apply orb_true_iff in T as [T|T]; [apply Z.eqb_eq in T; lia | apply Z.leb_le in T; exact T].
Qed.

Theorem pv_ratio : forall k, 0 <= k < 49 -> pv k <> 0 ->
  2 * (101 * znth k pk_MU + znth k pk_BETA) <= pf_RATIO * pv k.
Proof.
  intros k Hk Hw. pose proof (pf_tab_at _ k pv_ratio_tab Hk) as T. cbv beta in T.
  apply orb_true_iff in T as [T|T]; [apply Z.eqb_eq in T; contradiction | apply Z.leb_le in T; exact T].
Qed.

Theorem pv_ratio_15 : pv 15 = 4 /\ 2 * (101 * znth 15 pk_MU + znth 15 pk_BETA) = pf_RATIO * pv 15.
Proof. split; reflexivity. Qed.

Theorem pv_beta : forall k, 0 <= k < 49 -> pv k <> 0 -> 2 * znth k pk_BETA <= pf_RB * pv k.
Proof.
  intros k Hk Hw. pose proof (pf_tab_at _ k pv_beta_tab Hk) as T. cbv beta in T.
  apply orb_true_iff in T as [T|T]; [apply Z.eqb_eq in T; contradiction | apply Z.leb_le in T; exact T].
Qed.

Theorem pv_pw : forall k, 0 <= k < 49 -> pv k <= 2 * pw k /\ (pv k = 0 -> pw k = 0).
Proof.
  intros k Hk. pose proof (pf_tab_at _ k pv_pw_tab Hk) as T. cbv beta in T.
  apply andb_true_iff in T as [T1 T2]. apply Z.leb_le in T1. split; [exact T1|].
  intros E. apply orb_true_iff in T2 as [T2|T2]; [apply negb_true_iff, Z.eqb_neq in T2; contradiction|].
  apply Z.eqb_eq in T2. exact T2.
Qed.

Definition CS_of (beta : Z -> Z) : list Z := map (fun k => 3 * beta k + 271) (zseq 0 49).

Lemma CS_of_len beta : length (CS_of beta) = 49%nat.
Proof. unfold CS_of. rewrite length_map. reflexivity. Qed.

Lemma pf_nth_zseq i : (i < 49)%nat -> nth i (zseq 0 49) 0 = Z.of_nat i.
Proof. intros Hi. do 49 (destruct i as [|i]; [reflexivity|]). lia. Qed.

Lemma pf_nth_map (f : Z -> Z) l i : (i < length l)%nat -> nth i (map f l) 0 = f (nth i l 0).
Proof.
  revert i. induction l as [|a l IH]; intros i Hi; [cbn in Hi; lia|].
  destruct i as [|i]; [reflexivity|]. cbn [map nth]. apply IH. cbn in Hi. lia.
Qed.

Lemma CS_of_nth beta k : 0 <= k < 49 -> znth k (CS_of beta) = 3 * beta k + 271.
Proof.
  intros Hk. unfold CS_of, znth.
  rewrite pf_nth_map by (change (length (zseq 0 49)) with 49%nat; lia).
  rewrite pf_nth_zseq by lia. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma pf_split (A : list Z) beta :
  zsumZ (fun k => znth k A * znth k (CS_of beta)) (zseq 0 49) =
  3 * zsumZ (fun k => znth k A * beta k) (zseq 0 49) + 271 * zsumZ (fun k => znth k A) (zseq 0 49).
Proof.
  rewrite (zsumZ_ext (fun k => znth k A * znth k (CS_of beta)) (fun k => 3 * (znth k A * beta k) + 271 * znth k A)
    (zseq 0 49)).
  - rewrite zsumZ_add, !zsumZ_mul_l. reflexivity.
  - intros k Hk. apply In_zseq in Hk. rewrite CS_of_nth by lia. ring.
Qed.

Lemma CS_of_nonneg beta : (forall k, 0 <= k < 49 -> 0 <= beta k) ->
  forall k, 0 <= k < 49 -> 0 <= znth k (CS_of beta).
Proof. intros H k Hk. rewrite CS_of_nth by exact Hk. pose proof (H k Hk). lia. Qed.

Lemma pf_GALL beta : (forall k, 0 <= k < 49 -> 0 <= beta k) ->
  pk_D * GALL (CS_of beta) <= 3 * zsumZ (fun k => znth k pk_BETA * beta k) (zseq 0 49) + 2888952956696.
Proof.
  intros H. pose proof (GALL_lin (CS_of beta) (CS_of_len beta) (CS_of_nonneg beta H)) as L.
  rewrite (pf_split pk_BETA beta) in L.
  assert (E : zsumZ (fun k => znth k pk_BETA) (zseq 0 49) = 644308741) by (vm_compute; reflexivity).
  rewrite E in L. unfold pk_G0 in L. lia.
Qed.

Lemma pf_GMAP beta : (forall k, 0 <= k < 49 -> 0 <= beta k) ->
  pk_D * GMAP (CS_of beta) <= 3 * zsumZ (fun k => znth k pk_MU * beta k) (zseq 0 49) + 2667249182488.
Proof.
  intros H. pose proof (GMAP_lin (CS_of beta) (CS_of_len beta) (CS_of_nonneg beta H)) as L.
  rewrite (pf_split pk_MU beta) in L.
  assert (E : zsumZ (fun k => znth k pk_MU) (zseq 0 49) = 586107653) by (vm_compute; reflexivity).
  rewrite E in L. unfold pk_M0 in L. lia.
Qed.

Lemma pf_ratio_sum beta : (forall k, 0 <= k < 49 -> 0 <= beta k) -> (forall k, 0 <= k < 49 -> pv k = 0 -> beta k = 0) ->
  2 * (101 * zsumZ (fun k => znth k pk_MU * beta k) (zseq 0 49) + zsumZ (fun k => znth k pk_BETA * beta k) (zseq 0 49)) <=
  pf_RATIO * zsumZ (fun k => pv k * beta k) (zseq 0 49).
Proof.
  intros H0 Hz. rewrite <- !zsumZ_mul_l, <- zsumZ_add, <- zsumZ_mul_l. apply zsumZ_le. intros k Hk. apply In_zseq in Hk.
  cbv beta. pose proof (H0 k ltac:(lia)) as B.
  destruct (Z.eq_dec (pv k) 0) as [E|E].
  - rewrite (Hz k ltac:(lia) E). lia.
  - pose proof (pv_ratio k ltac:(lia) E) as R.
    assert (M : (2 * (101 * znth k pk_MU + znth k pk_BETA)) * beta k <= (pf_RATIO * pv k) * beta k)
      by (apply Z.mul_le_mono_nonneg_r; lia).
    nia.
Qed.

Lemma pf_beta_sum beta : (forall k, 0 <= k < 49 -> 0 <= beta k) -> (forall k, 0 <= k < 49 -> pv k = 0 -> beta k = 0) ->
  2 * zsumZ (fun k => znth k pk_BETA * beta k) (zseq 0 49) <= pf_RB * zsumZ (fun k => pv k * beta k) (zseq 0 49).
Proof.
  intros H0 Hz. rewrite <- !zsumZ_mul_l. apply zsumZ_le. intros k Hk. apply In_zseq in Hk. cbv beta.
  pose proof (H0 k ltac:(lia)) as B.
  destruct (Z.eq_dec (pv k) 0) as [E|E].
  - rewrite (Hz k ltac:(lia) E). lia.
  - pose proof (pv_beta k ltac:(lia) E) as R.
    assert (M : (2 * znth k pk_BETA) * beta k <= (pf_RB * pv k) * beta k) by (apply Z.mul_le_mono_nonneg_r; lia).
    nia.
Qed.

Lemma pf_GALL_nonneg caps : (forall k, 0 <= k < 49 -> 0 <= znth k caps) -> 0 <= GALL caps.
Proof.
  intros H. unfold GALL. pose proof (H 48 ltac:(lia)).
  assert (0 <= zsumZ (fun c => znth c (NF caps) + RED) (zseq 0 48)).
  { apply zsumZ_nonneg. intros c _. pose proof (NF_nonneg caps c (fun j Hj => H j ltac:(lia))). unfold RED. lia. }
  lia.
Qed.

Theorem pf_bounds : forall caps (beta : Z -> Z) n,
  0 <= n <= pf_MAX ->
  (forall k, 0 <= k < 49 -> 0 <= beta k /\ 0 <= znth k caps <= 3 * beta k + 271) ->
  zsumZ (fun k => pv k * beta k) (zseq 0 49) <= 2 * n + pf_E ->
  (forall k, 0 <= k < 49 -> pv k = 0 -> beta k = 0) ->
  0 <= GALL caps /\ GMAP caps + GALL caps / 101 <= 167052 /\ GALL caps <= 988596.
Proof.
  intros caps beta n Hn Hb Hs Hz.
  assert (H0 : forall k, 0 <= k < 49 -> 0 <= beta k) by (intros k Hk; apply (proj1 (Hb k Hk))).
  assert (Hle : forall k, 0 <= k < 49 -> znth k caps <= znth k (CS_of beta))
    by (intros k Hk; rewrite CS_of_nth by exact Hk; apply (proj2 (proj2 (Hb k Hk)))).
  pose proof (GALL_mono caps (CS_of beta) Hle) as GA.
  pose proof (GMAP_mono caps (CS_of beta) Hle) as GM.
  pose proof (pf_GALL beta H0) as LA.
  pose proof (pf_GMAP beta H0) as LM.
  pose proof (pf_ratio_sum beta H0 Hz) as R.
  pose proof (pf_beta_sum beta H0 Hz) as RB.
  assert (G0 : 0 <= GALL caps) by (apply pf_GALL_nonneg; intros k Hk; apply (proj1 (proj2 (Hb k Hk)))).
  pose proof (Z.mul_div_le (GALL caps) 101 ltac:(lia)) as DV.
  unfold pf_RATIO, pf_RB, pf_MAX, pf_E, pk_D in *.
  set (S := zsumZ (fun k => pv k * beta k) (zseq 0 49)) in *.
  set (SM := zsumZ (fun k => znth k pk_MU * beta k) (zseq 0 49)) in *.
  set (SB := zsumZ (fun k => znth k pk_BETA * beta k) (zseq 0 49)) in *.
  set (g := GALL caps / 101) in *.
  split; [exact G0|]. split; lia.
Qed.

Lemma pf_capok : forall H M, 0 <= H -> M + H / 101 <= 299524 -> H / 101 <= 42967 -> CAPOK2 H M pf_BMAX pf_NMAX.
Proof.
  intros H M H0 H1 H2.
  assert (Hg : 0 <= H / 101) by (apply Z.div_pos; lia).
  pose proof (Z.mod_pos_bound H 101 ltac:(lia)) as Hm.
  pose proof (Z.div_mod H 101 ltac:(lia)) as Hd.
  assert (P : page_round (pf_NMAX + IB + UNIT) = 352321536) by (vm_compute; reflexivity).
  assert (EM : MMAX = 8388608) by reflexivity.
  assert (R : RQ2 H pf_NMAX = 352321536).
  { unfold RQ2, AREA2. rewrite P, EM. unfold METAS_PER_AREA, PGSZ. set (g := H / 101) in *. lia. }
  assert (S : slot_cap 352321536 = 299579) by (vm_compute; reflexivity).
  unfold CAPOK2. rewrite R, S, P.
  unfold LIVE2, SLOTS2, NA2, AREA2, METAS_PER_AREA, PGSZ, KRES.
  rewrite EM.
  assert (EL : MG_LIVE = 35184372088832) by reflexivity.
  assert (ER : MG_REQ = 1073741824) by reflexivity.
  assert (EB : pf_BMAX = 4294967295) by reflexivity.
  assert (E40 : 2 ^ 40 = 1099511627776) by reflexivity.
  rewrite EL, ER, EB, E40.
  set (g := H / 101) in *. lia.
Qed.

Theorem pack_fit : forall caps (beta : Z -> Z) n,
  length caps = 49%nat -> 0 <= n <= pf_MAX ->
  (forall k, 0 <= k < 49 -> 0 <= beta k /\ 0 <= znth k caps <= 3 * beta k + 271) ->
  zsumZ (fun k => pv k * beta k) (zseq 0 49) <= 2 * n + pf_E ->
  (forall k, 0 <= k < 49 -> pv k = 0 -> beta k = 0) ->
  CAPOK2 (GALL caps) (GMAP caps) pf_BMAX pf_NMAX.
Proof.
  intros caps beta n _ Hn Hb Hs Hz.
  destruct (pf_bounds caps beta n Hn Hb Hs Hz) as (G0 & G1 & G2).
  assert (D : GALL caps / 101 <= 988596 / 101) by (apply Z.div_le_mono; lia).
  change (988596 / 101) with 9788 in D.
  apply pf_capok; lia.
Qed.

Lemma pf_one beta n : (forall k, 0 <= k < 49 -> 0 <= beta k) ->
  zsumZ (fun k => pw k * beta k) (zseq 0 49) <= n + 64 -> (forall k, 0 <= k < 49 -> pw k = 0 -> beta k = 0) ->
  zsumZ (fun k => pv k * beta k) (zseq 0 49) <= 2 * n + pf_E /\ (forall k, 0 <= k < 49 -> pv k = 0 -> beta k = 0).
Proof.
  intros H0 Hs Hz. split.
  - assert (L : zsumZ (fun k => pv k * beta k) (zseq 0 49) <= zsumZ (fun k => 2 * (pw k * beta k)) (zseq 0 49)).
    { apply zsumZ_le. intros k Hk. apply In_zseq in Hk. cbv beta.
      destruct (pv_pw k ltac:(lia)) as [P _]. pose proof (H0 k ltac:(lia)).
      assert (pv k * beta k <= (2 * pw k) * beta k) by (apply Z.mul_le_mono_nonneg_r; lia). lia. }
    rewrite zsumZ_mul_l in L. unfold pf_E. lia.
  - intros k Hk E. apply (Hz k Hk). exact (proj2 (pv_pw k Hk) E).
Qed.

Theorem pack_fit_one : forall caps (beta : Z -> Z) n,
  length caps = 49%nat -> 0 <= n <= pf_MAX ->
  (forall k, 0 <= k < 49 -> 0 <= beta k /\ 0 <= znth k caps <= 3 * beta k + 271) ->
  zsumZ (fun k => pw k * beta k) (zseq 0 49) <= n + 64 ->
  (forall k, 0 <= k < 49 -> pw k = 0 -> beta k = 0) ->
  CAPOK2 (GALL caps) (GMAP caps) pf_BMAX pf_NMAX.
Proof.
  intros caps beta n Hl Hn Hb Hs Hz.
  destruct (pf_one beta n (fun k Hk => proj1 (Hb k Hk)) Hs Hz) as [S Z].
  exact (pack_fit caps beta n Hl Hn Hb S Z).
Qed.

Theorem pack_fit_room : forall b (beta : Z -> Z) n r,
  length (pb_cap b) = 49%nat -> 0 <= n <= pf_MAX ->
  (forall k, 0 <= k < 49 -> 0 <= beta k /\ 0 <= znth k (pb_cap b) <= 3 * beta k + 271) ->
  zsumZ (fun k => pv k * beta k) (zseq 0 49) <= 2 * n + pf_E ->
  (forall k, 0 <= k < 49 -> pv k = 0 -> beta k = 0) ->
  0 <= r <= pf_NMAX -> pb_bytes b + r <= pf_BMAX ->
  znth (band r) (pb_live b) + 1 <= znth (band r) (pb_cap b) -> room_pack b r.
Proof.
  intros b beta n r Hl Hn Hb Hs Hz Hr HB Hc.
  apply (room_pack_of b r pf_BMAX pf_NMAX); [exact (pack_fit (pb_cap b) beta n Hl Hn Hb Hs Hz) | exact Hr | exact HB | exact Hc].
Qed.

Lemma CS_of_bound beta : (forall k, 0 <= k < 49 -> 0 <= beta k) ->
  forall k, 0 <= k < 49 -> 0 <= beta k /\ 0 <= znth k (CS_of beta) <= 3 * beta k + 271.
Proof. intros H k Hk. rewrite CS_of_nth by exact Hk. pose proof (H k Hk). lia. Qed.

Theorem pack_fit_CS : forall (beta : Z -> Z) n,
  0 <= n <= pf_MAX -> (forall k, 0 <= k < 49 -> 0 <= beta k) ->
  zsumZ (fun k => pv k * beta k) (zseq 0 49) <= 2 * n + pf_E ->
  (forall k, 0 <= k < 49 -> pv k = 0 -> beta k = 0) ->
  CAPOK2 (GALL (CS_of beta)) (GMAP (CS_of beta)) pf_BMAX pf_NMAX.
Proof.
  intros beta n Hn H0 Hs Hz.
  exact (pack_fit (CS_of beta) beta n (CS_of_len beta) Hn (CS_of_bound beta H0) Hs Hz).
Qed.

Theorem pack_fit_CS_one : forall (beta : Z -> Z) n,
  0 <= n <= pf_MAX -> (forall k, 0 <= k < 49 -> 0 <= beta k) ->
  zsumZ (fun k => pw k * beta k) (zseq 0 49) <= n + 64 ->
  (forall k, 0 <= k < 49 -> pw k = 0 -> beta k = 0) ->
  CAPOK2 (GALL (CS_of beta)) (GMAP (CS_of beta)) pf_BMAX pf_NMAX.
Proof.
  intros beta n Hn H0 Hs Hz.
  exact (pack_fit_one (CS_of beta) beta n (CS_of_len beta) Hn (CS_of_bound beta H0) Hs Hz).
Qed.
