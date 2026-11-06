From Stdlib Require Import ZArith List Bool Lia Arith.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0g YO0s YO0u YO0x YO10 YO0q YO0d YO03 YO0j YO0m YO0n YO0o YO04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import PlaceCap.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import AllocSI AllocGS AllocMB AllocCount AllocBound AllocSlots AllocPack AllocPackRoom AllocPack3.
Import ListNotations.
Local Open Scope Z_scope.

Definition pk3_cm (caps mc : list Z) : list Z :=
  map (fun k => znth k caps + (if k <? 48 then znth k mc else 0)) (zseq 0 49).

Lemma pk3_map_zseq (f : Z -> Z) k : 0 <= k < 49 -> znth k (map f (zseq 0 49)) = f k.
Proof.
  intros Hk. unfold znth.
  rewrite (nth_indep (map f (zseq 0 49)) 0 (f 0)) by (rewrite length_map; unfold zseq; rewrite length_map, length_seq; lia).
  rewrite map_nth. f_equal. unfold zseq.
  pose proof (map_nth (fun j : nat => 0 + Z.of_nat j) (seq 0 (Z.to_nat 49)) 0%nat (Z.to_nat k)) as E. cbv beta in E.
  rewrite (nth_indep _ 0 (0 + Z.of_nat 0)) by (rewrite length_map, length_seq; lia).
  rewrite E, seq_nth by lia. lia.
Qed.

Lemma pk3_cm_znth caps mc k : 0 <= k < 49 ->
  znth k (pk3_cm caps mc) = znth k caps + (if k <? 48 then znth k mc else 0).
Proof. intros Hk. exact (pk3_map_zseq (fun k => znth k caps + (if k <? 48 then znth k mc else 0)) k Hk). Qed.

Lemma pk3_cm_lt caps mc k : 0 <= k < 48 -> znth k (pk3_cm caps mc) = znth k caps + znth k mc.
Proof. intros Hk. rewrite pk3_cm_znth by lia. destruct (Z.ltb_spec k 48); [reflexivity | lia]. Qed.

Lemma pk3_cm_48 caps mc : znth 48 (pk3_cm caps mc) = znth 48 caps.
Proof. rewrite pk3_cm_znth, Z.ltb_irrefl by lia. cbv iota. lia. Qed.

Lemma pk3_cm_nonneg caps mc : (forall k, 0 <= k < 49 -> 0 <= znth k caps /\ 0 <= znth k mc) ->
  forall k, 0 <= k < 49 -> 0 <= znth k (pk3_cm caps mc).
Proof.
  intros Hc k Hk. pose proof (Hc k Hk) as [H1 H2].
  destruct (Z.eq_dec k 48) as [->|Ne]; [rewrite pk3_cm_48 | rewrite pk3_cm_lt by lia]; lia.
Qed.

Lemma pk3_cm_mono caps mc caps' mc' : (forall k, 0 <= k < 49 -> znth k caps <= znth k caps') ->
  (forall k, 0 <= k < 49 -> znth k mc <= znth k mc') ->
  forall k, 0 <= k < 49 -> znth k (pk3_cm caps mc) <= znth k (pk3_cm caps' mc').
Proof.
  intros Hc Hm k Hk. pose proof (Hc k Hk). pose proof (Hm k Hk).
  destruct (Z.eq_dec k 48) as [->|Ne]; [rewrite !pk3_cm_48 | rewrite !pk3_cm_lt by lia]; lia.
Qed.

Lemma nf3b_eq caps mc k : (k <= 48)%nat -> nf3_build caps mc k = nf_build (pk3_cm caps mc) k.
Proof.
  induction k as [|k IH]; intros Hk; [reflexivity|]. cbn [nf3_build nf_build]. rewrite IH by lia.
  unfold nf3_next, nf_next. rewrite (pk3_cm_lt caps mc (Z.of_nat k)) by lia.
  replace (znth (Z.of_nat k) caps + znth (Z.of_nat k) mc + COARSE)
    with (znth (Z.of_nat k) caps + COARSE + znth (Z.of_nat k) mc) by ring.
  reflexivity.
Qed.

Lemma NF3_eq caps mc : NF3 caps mc = NF (pk3_cm caps mc).
Proof. unfold NF3, NF. apply nf3b_eq. lia. Qed.

Lemma GALL3_eq caps mc : GALL3 caps mc = GALL (pk3_cm caps mc).
Proof. unfold GALL3, GALL. rewrite NF3_eq, pk3_cm_48. reflexivity. Qed.

Lemma GMAP3_eq caps mc : GMAP3 caps mc = GMAP (pk3_cm caps mc).
Proof. unfold GMAP3, GMAP. rewrite NF3_eq, pk3_cm_48. reflexivity. Qed.

Lemma PKC3_cm X caps mc s : PKC3 X caps mc s -> PKC X (pk3_cm caps mc) s.
Proof. unfold PKC3, PKC. rewrite NF3_eq. intros H. exact H. Qed.

Lemma NF3_nonneg caps mc c : (forall k, 0 <= k < 49 -> 0 <= znth k caps /\ 0 <= znth k mc) ->
  0 <= znth c (NF3 caps mc).
Proof.
  intros Hc. rewrite NF3_eq. apply NF_nonneg. intros j Hj. apply (pk3_cm_nonneg caps mc Hc). lia.
Qed.

Lemma NF3_mono caps mc caps' mc' : (forall k, 0 <= k < 49 -> znth k caps <= znth k caps') ->
  (forall k, 0 <= k < 49 -> znth k mc <= znth k mc') ->
  forall c, 0 <= c < 48 -> znth c (NF3 caps mc) <= znth c (NF3 caps' mc').
Proof.
  intros Hc Hm c Hc48. rewrite !NF3_eq. exact (NF_mono _ _ (pk3_cm_mono caps mc caps' mc' Hc Hm) c Hc48).
Qed.

Lemma GALL3_mono caps mc caps' mc' : (forall k, 0 <= k < 49 -> znth k caps <= znth k caps') ->
  (forall k, 0 <= k < 49 -> znth k mc <= znth k mc') -> GALL3 caps mc <= GALL3 caps' mc'.
Proof. intros Hc Hm. rewrite !GALL3_eq. exact (GALL_mono _ _ (pk3_cm_mono caps mc caps' mc' Hc Hm)). Qed.

Lemma GMAP3_mono caps mc caps' mc' : (forall k, 0 <= k < 49 -> znth k caps <= znth k caps') ->
  (forall k, 0 <= k < 49 -> znth k mc <= znth k mc') -> GMAP3 caps mc <= GMAP3 caps' mc'.
Proof. intros Hc Hm. rewrite !GMAP3_eq. exact (GMAP_mono _ _ (pk3_cm_mono caps mc caps' mc' Hc Hm)). Qed.

Definition pk3_D : Z := 199987200.

Definition pk3_BETA : list Z := [6881070;6659100;10321605;6665400;8265096;9839400;11479300;6678000;7393500;8625750;
  10350900;6444900;7365600;8593200;10311840;6444900;7365600;8593200;10311840;6444900;7365600;8593200;10311840;6640200;
  7588800;8853600;10624320;7030800;8035200;9374400;11249280;6249600;7142400;8332800;9999360;6249600;7142400;8332800;
  9999360;6249600;7142400;8332800;9999360;12499200;14284800;16665600;19998720;24998400;199987200].

Definition pk3_GAMMA : list Z := [6881070;6659100;10321605;6665400;8265096;9839400;11479300;6678000;7393500;8625750;
  10350900;6444900;7365600;8593200;10311840;6444900;7365600;8593200;10311840;6444900;7365600;8593200;10311840;6640200;
  7588800;8853600;10624320;7030800;8035200;9374400;11249280;6249600;7142400;8332800;9999360;6249600;7142400;8332800;
  9999360;6249600;7142400;8332800;9999360;12499200;14284800;16665600;19998720;24998400;0].

Definition pk3_G0 : Z := 2714345287885.

Definition pk3_MU : list Z := [214830;207900;322245;214200;265608;316200;368900;6678000;7393500;8625750;10350900;
  6444900;7365600;8593200;10311840;6444900;7365600;8593200;10311840;6444900;7365600;8593200;10311840;6640200;7588800;
  8853600;10624320;7030800;8035200;9374400;11249280;6249600;7142400;8332800;9999360;6249600;7142400;8332800;9999360;
  6249600;7142400;8332800;9999360;12499200;14284800;16665600;19998720;24998400;199987200].

Definition pk3_NU : list Z := [214830;207900;322245;214200;265608;316200;368900;6678000;7393500;8625750;10350900;
  6444900;7365600;8593200;10311840;6444900;7365600;8593200;10311840;6444900;7365600;8593200;10311840;6640200;7588800;
  8853600;10624320;7030800;8035200;9374400;11249280;6249600;7142400;8332800;9999360;6249600;7142400;8332800;9999360;
  6249600;7142400;8332800;9999360;12499200;14284800;16665600;19998720;24998400;0].

Definition pk3_M0 : Z := 2508414008525.

Definition pk3_chkG (W G : list Z) : bool :=
  forallb (fun k => (if k <? 48 then znth k W else 0) <=? znth k G) (zseq 0 49).

Lemma pk3_certG : pk_chkW (fun _ => false) pk3_BETA pk3_G0 pk_A pk_B = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pk3_certM : pk_chkW nestF pk3_MU pk3_M0 pk_A pk_B = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pk3_certGa : pk3_chkG pk3_BETA pk3_GAMMA = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pk3_certNu : pk3_chkG pk3_MU pk3_NU = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pk3_cm_sum W caps mc :
  zsumZ (fun k => znth k W * znth k (pk3_cm caps mc)) (zseq 0 49) =
  zsumZ (fun k => znth k W * znth k caps) (zseq 0 49) +
  zsumZ (fun k => (if k <? 48 then znth k W else 0) * znth k mc) (zseq 0 49).
Proof.
  rewrite <- zsumZ_add. apply zsumZ_ext. intros k Hk. apply In_zseq in Hk. cbv beta.
  rewrite pk3_cm_znth by lia. destruct (k <? 48); cbv iota; ring.
Qed.

Lemma pk3_lin skip W W0 G caps mc : (forall k, 0 <= k < 49 -> 0 <= znth k caps /\ 0 <= znth k mc) ->
  pk_chkW skip W W0 pk_A pk_B = true -> pk3_chkG W G = true ->
  pk3_D * (zsumZ (fun c => if skip c then 0 else znth c (NF3 caps mc) + RED) (zseq 0 48) + znth 48 caps) <=
  zsumZ (fun k => znth k W * znth k caps) (zseq 0 49) + zsumZ (fun k => znth k G * znth k mc) (zseq 0 49) + W0.
Proof.
  intros Hc HW HG.
  pose proof (pk_linW skip W W0 (pk3_cm caps mc) (pk3_cm_nonneg caps mc Hc) HW) as H.
  rewrite <- NF3_eq, pk3_cm_48, pk3_cm_sum in H.
  assert (H2 : zsumZ (fun k => (if k <? 48 then znth k W else 0) * znth k mc) (zseq 0 49) <=
               zsumZ (fun k => znth k G * znth k mc) (zseq 0 49)).
  { apply zsumZ_le. intros k Hk. unfold pk3_chkG in HG. rewrite forallb_forall in HG.
    pose proof (HG k Hk) as Gk. cbv beta in Gk. apply Z.leb_le in Gk. apply In_zseq in Hk.
    pose proof (proj2 (Hc k ltac:(lia))). cbv beta. apply Z.mul_le_mono_nonneg_r; lia. }
  unfold pk3_D, pk_D in *. lia.
Qed.

Theorem GALL3_lin : forall caps mc, length caps = 49%nat -> length mc = 49%nat ->
  (forall k, 0 <= k < 49 -> 0 <= znth k caps /\ 0 <= znth k mc) ->
  pk3_D * GALL3 caps mc <= zsumZ (fun k => znth k pk3_BETA * znth k caps) (zseq 0 49) +
    zsumZ (fun k => znth k pk3_GAMMA * znth k mc) (zseq 0 49) + pk3_G0.
Proof.
  intros caps mc _ _ Hc. exact (pk3_lin (fun _ => false) pk3_BETA pk3_G0 pk3_GAMMA caps mc Hc pk3_certG pk3_certGa).
Qed.

Theorem GMAP3_lin : forall caps mc, length caps = 49%nat -> length mc = 49%nat ->
  (forall k, 0 <= k < 49 -> 0 <= znth k caps /\ 0 <= znth k mc) ->
  pk3_D * GMAP3 caps mc <= zsumZ (fun k => znth k pk3_MU * znth k caps) (zseq 0 49) +
    zsumZ (fun k => znth k pk3_NU * znth k mc) (zseq 0 49) + pk3_M0.
Proof.
  intros caps mc _ _ Hc. exact (pk3_lin nestF pk3_MU pk3_M0 pk3_NU caps mc Hc pk3_certM pk3_certNu).
Qed.

Lemma pk3_b48 s caps mc L M : UPB3 s L M -> (forall k, 0 <= k < 49 -> 0 <= znth k L <= znth k caps) ->
  bcount s 48 <= znth 48 (pk3_cm caps mc).
Proof.
  intros (U1 & _) HB. rewrite pk3_cm_48. pose proof (U1 48 ltac:(lia)). pose proof (HB 48 ltac:(lia)). lia.
Qed.

Theorem nused_pack3 : forall s caps mc L M, WF s -> SI s -> PKS [] s -> PKC3 [] caps mc s -> UPB3 s L M ->
  length caps = 49%nat -> length L = 49%nat -> (forall k, 0 <= k < 49 -> 0 <= znth k L <= znth k caps) ->
  nused s <= GALL3 caps mc.
Proof.
  intros s caps mc L M HW HS HP HC HU _ _ HB. rewrite GALL3_eq. apply PKC3_cm in HC.
  assert (Hl : (length (map fst (used_metas s)) <= length (pk_tgt s (fun _ => false)))%nat).
  { apply (ac_count pk_tdec (pk_RT s)).
    - apply NoDup_used_metas_keys. exact (proj1 (inv_keys HW)).
    - intros g Hg. apply in_map_iff in Hg as ([g' ag] & E & Hin). cbn [fst] in E. subst g'.
      apply (used_metas_usedX s g ag HW) in Hin.
      exact (pk_tgt_ex s (fun _ => false) g ag HW HP Hin (fun _ => eq_refl)).
    - intros g g' x _ _ R1 R2. exact (pk_RT_inj s g g' x R1 R2). }
  rewrite length_map in Hl. pose proof (pk_tgt_len s (fun _ => false)) as E.
  pose proof (pk_small_le s (fun _ => false) (pk3_cm caps mc) HC) as Hs. cbv beta iota in Hs.
  pose proof (pk3_b48 s caps mc L M HU HB) as Hb.
  unfold nused, GALL. lia.
Qed.

Theorem mapped_pack3 : forall s caps mc L M, WF s -> SI s -> PKS [] s -> PKC3 [] caps mc s -> UPB3 s L M ->
  length caps = 49%nat -> length L = 49%nat -> (forall k, 0 <= k < 49 -> 0 <= znth k L <= znth k caps) ->
  map_count s <= GMAP3 caps mc.
Proof.
  intros s caps mc L M HW HS HP HC HU _ _ HB. rewrite GMAP3_eq. apply PKC3_cm in HC.
  unfold map_count. rewrite mapc_count.
  match goal with |- Z.of_nat (length ?l) <= _ => assert (Hl : (length l <= length (pk_tgt s nestF))%nat) end.
  { apply (ac_count pk_tdec (pk_RR s)).
    - apply NoDup_filter. apply seq_NoDup.
    - intros k Hk. apply filter_In in Hk as [_ Hk]. cbv beta in Hk.
      destruct (nth_error (st_regions s) k) as [rg|] eqn:Hr; [|discriminate].
      apply andb_true_iff in Hk as [Lv Mp].
      assert (Kd : rg_kind rg = RkMap) by (unfold is_map in Mp; destruct (rg_kind rg); try discriminate; reflexivity).
      pose proof HS as (OM & _). destruct (OM k rg Hr Kd Lv) as (g & ag & U & Mpos & Pk).
      pose proof HP as (_ & _ & _ & P4).
      destruct (pk_tgt_ex s nestF g ag HW HP U (fun Hc => P4 g ag U (proj2 Hc) Mpos)) as (x & Hx & Rx).
      exists x. split; [exact Hx|]. exists g, ag. split; [exact U|]. split; [exact Pk | exact Rx].
    - intros k k' x _ _ (g & a & U & Pk & R1) (g' & a' & U' & Pk' & R2).
      pose proof (pk_RT_inj s g g' x R1 R2) as <-. rewrite (usedX_fun _ _ _ _ _ U U') in Pk. congruence. }
  pose proof (pk_tgt_len s nestF) as E. pose proof (pk_small_le s nestF (pk3_cm caps mc) HC) as Hs.
  pose proof (pk3_b48 s caps mc L M HU HB) as Hb. unfold GMAP. lia.
Qed.

Theorem map_bytes_pack3 : forall s caps mc L M, WF s -> SI s -> GS s -> PKS [] s -> PKC3 [] caps mc s -> UPB3 s L M ->
  length caps = 49%nat -> length L = 49%nat -> (forall k, 0 <= k < 49 -> 0 <= znth k L <= znth k caps) ->
  map_bytes s <= MMAX * GMAP3 caps mc + ubytes s.
Proof.
  intros s caps mc L M HW HS HG HP HC HU _ _ HB. rewrite GMAP3_eq. apply PKC3_cm in HC.
  unfold map_bytes. rewrite rsum_idx.
  match goal with |- zsum ?c ?l <= _ => assert (Hl : zsum c l <= zsum pk_w (pk_tgt s nestF)) end.
  { apply (ac_wsum pk_tdec (pk_RR s)).
    - apply seq_NoDup.
    - intros x Hx. unfold pk_tgt in Hx. apply in_app_iff in Hx as [Hx|Hx]; apply in_map_iff in Hx as (y & <- & Hy);
        unfold pk_w; cbn [snd]; rewrite MM; [lia|].
      unfold pk_ub48 in Hy. apply filter_In in Hy as [Hy _]. pose proof (ub_nonneg s HW y Hy). lia.
    - intros k _. cbv beta.
      destruct (nth_error (st_regions s) k) as [rg|] eqn:Hr; cbv beta iota; [|left; lia].
      unfold f_mapb. destruct (rg_live rg && is_map rg) eqn:E; cbv beta iota; [right|left; lia].
      apply andb_true_iff in E as [Lv Mp].
      assert (Kd : rg_kind rg = RkMap) by (unfold is_map in Mp; destruct (rg_kind rg); try discriminate; reflexivity).
      pose proof HS as (OM & _). destruct (OM k rg Hr Kd Lv) as (g & ag & U & Mpos & Pk).
      pose proof (inv_groups HW g ag U) as (_ & _ & _ & _ & Gmp & _).
      destruct (Gmp Mpos) as (r & rg' & Em & Hr' & _ & _ & Len & _).
      rewrite Em in Pk. cbn in Pk. subst r. unfold region_of in Hr'. rewrite Hr in Hr'. injection Hr' as <-.
      rewrite Len.
      pose proof HP as (_ & _ & _ & P4).
      destruct (pk_tgt_ex s nestF g ag HW HP U (fun Hc => P4 g ag U (proj2 Hc) Mpos)) as (x & Hx & Rx).
      exists x. split; [exact Hx|]. split; [exists g, ag; split; [exact U|]; split; [rewrite Em; reflexivity | exact Rx]|].
      destruct Rx as (a & Ua & Hm). rewrite (usedX_fun _ _ _ _ _ Ua U) in Hm.
      destruct (HG g ag U Mpos) as [G48 G63].
      unfold pk_w. destruct x as [p [n|]]; cbn [fst snd] in Hm |- *.
      + destruct Hm as (E63 & _ & fr & F & ->). pose proof (G63 E63 fr F). rewrite MM. unfold PGSZ in *. lia.
      + destruct Hm as (_ & C). apply G48. lia.
    - intros k k' x _ _ (g & a & U & Pk & R1) (g' & a' & U' & Pk' & R2).
      pose proof (pk_RT_inj s g g' x R1 R2) as <-. rewrite (usedX_fun _ _ _ _ _ U U') in Pk. congruence. }
  rewrite pk_wsum in Hl.
  assert (Hsub : zsum snd (pk_ub48 s) <= ubytes s).
  { change (ubytes s) with (zsum snd (user_blocks s)). unfold pk_ub48. apply pk_zsum_filter.
    intros b Hb. exact (ub_nonneg s HW b Hb). }
  pose proof (pk_small_le s nestF (pk3_cm caps mc) HC) as Hs. pose proof (pk3_b48 s caps mc L M HU HB) as Hb.
  unfold GMAP. rewrite MM in *. lia.
Qed.

Lemma pack3_room4 : forall A b n, WF A -> res_ok_pack3 A b -> room_pack3 b n -> ROOM4 A n.
Proof.
  intros A b n HW (HII & HSI & HGS & HNL & HNR & (MB1 & MB2) & HPK & HPC & HUP & HMS & Hub & HlL & HlC & HlM & Hbd & Hby & Hh)
    (Hn & Hcap & Hmc & C1 & C2 & C3 & C4).
  assert (Hbd' : forall k, 0 <= k < 49 -> 0 <= znth k (p3_live b) <= znth k (p3_cap b))
    by (intros k Hk; exact (proj1 (Hbd k Hk))).
  pose proof (mapped_pack3 A (p3_cap b) (p3_mcap b) (p3_live b) (p3_mis b) HW HSI HPK HPC HUP HlC HlL Hbd') as T4.
  pose proof (map_bytes_pack3 A (p3_cap b) (p3_mcap b) (p3_live b) (p3_mis b) HW HSI HGS HPK HPC HUP HlC HlL Hbd') as T7.
  pose proof (nareas_hand A HII) as NA1.
  destruct (shift_small A (GALL3 (p3_cap b) (p3_mcap b)) HII Hh C4) as [SH1 SH2].
  pose proof HII as (_ & Hsh & _ & _ & Hrt & _).
  assert (HD : hand A / METAS_PER_AREA <= GALL3 (p3_cap b) (p3_mcap b) / METAS_PER_AREA).
  { apply Z.div_le_mono; [unfold METAS_PER_AREA; lia | exact Hh]. }
  assert (BK : brk_bytes A / PGSZ <= nareas A + 1).
  { apply Z.div_le_upper_bound; [unfold PGSZ; lia|]. unfold PGSZ in *. lia. }
  pose proof (page_round_ge (n + IB + UNIT)) as PR.
  assert (MX0 : 0 < MMAX) by (unfold MMAX; reflexivity).
  assert (AR : area A <= AREA2 (GALL3 (p3_cap b) (p3_mcap b))) by (unfold area, AREA2; unfold PGSZ in *; lia).
  assert (RQ1 : Z.max (Z.max MMAX (page_round (n + IB + UNIT))) (area A) <= RQ2 (GALL3 (p3_cap b) (p3_mcap b)) n).
  { unfold RQ2. lia. }
  assert (SC : slot_cap (RQ2 (GALL3 (p3_cap b) (p3_mcap b)) n) <=
               slot_cap (Z.max (Z.max MMAX (page_round (n + IB + UNIT))) (area A))).
  { apply slot_cap_anti. lia. }
  unfold ROOM4. split; [|split; [|split]].
  - unfold LIVE_UB. rewrite Hrt. unfold LIVE2, AREA2, NA2 in *. unfold PGSZ, MMAX in *. lia.
  - unfold SLOT_UB. unfold SLOTS2, NA2 in C2. lia.
  - unfold RQ2 in C3. unfold PGSZ in *. lia.
  - unfold RQ2 in C3. unfold PGSZ in *. lia.
Qed.

Lemma room_pack3_of b n BMAX NMAX :
  CAPOK2 (GALL3 (p3_cap b) (p3_mcap b)) (GMAP3 (p3_cap b) (p3_mcap b)) BMAX NMAX -> 0 <= n <= NMAX ->
  p3_bytes b + n <= BMAX -> znth (band n) (p3_live b) + 1 <= znth (band n) (p3_cap b) ->
  (band n + 1 < 48 -> count_mis (p3_mis b) (band n + 1) + 1 <= znth (band n + 1) (p3_mcap b)) -> room_pack3 b n.
Proof.
  intros HC Hn HB Hl Hm. unfold room_pack3. split; [lia|]. split; [exact Hl|]. split; [exact Hm|].
  apply (CAPOK2_mono (GALL3 (p3_cap b) (p3_mcap b)) (GMAP3 (p3_cap b) (p3_mcap b)) BMAX NMAX);
    [lia | lia | exact HB | lia | exact HC].
Qed.

Lemma room_pack3_n b n : room_pack3 b n -> 0 <= n < 2 ^ 62 /\ size_overflows n = false.
Proof.
  intros (Hn0 & _ & _ & _ & _ & C3 & _). pose proof (page_round_ge (n + IB + UNIT)) as PG. unfold PGSZ in C3.
  assert (R : page_round (n + IB + UNIT) <= RQ2 (GALL3 (p3_cap b) (p3_mcap b)) n) by (unfold RQ2; lia).
  split; [unfold MG_REQ, IB, UNIT in *; lia|]. unfold size_overflows. apply Z.leb_gt. unfold MG_REQ, IB, UNIT in *. lia.
Qed.

Lemma room_pack3_req b n : room_pack3 b n -> page_round (n + IB + UNIT) + PGSZ <= MG_REQ.
Proof.
  intros (_ & _ & _ & _ & _ & C3 & _).
  assert (R : page_round (n + IB + UNIT) <= RQ2 (GALL3 (p3_cap b) (p3_mcap b)) n) by (unfold RQ2; lia). lia.
Qed.

Lemma res_ok_pack3_init caps mc : length caps = 49%nat -> length mc = 49%nat ->
  (forall k, 0 <= k < 49 -> 0 <= znth k caps /\ 0 <= znth k mc) ->
  res_ok_pack3 init_state (PB3 (repeat 0 49) 0 caps [] mc).
Proof.
  intros Hlen Hlm Hc.
  assert (NU : forall X g am, ~ usedX X init_state g am).
  { intros X g am H. unfold usedX, MTX, MT in H. destruct (memb g X); cbn in H; discriminate. }
  assert (Z0 : forall k, znth k (repeat 0 49) = 0).
  { intros k. unfold znth. generalize (Z.to_nat k). generalize 49%nat.
    induction n as [|n IH]; intros [|m]; cbn; auto. }
  assert (NN : forall c, 0 <= znth c (NF3 caps mc)) by (intros c; apply NF3_nonneg; exact Hc).
  assert (GC0 : forall f, gcountX [] init_state f = 0) by (intros f; reflexivity).
  assert (B0 : forall k, bcount init_state k = 0) by (intros k; reflexivity).
  assert (UC0 : forall c, upc init_state c = 0) by (intros c; reflexivity).
  assert (MI0 : forall c, mis_in init_state [] c = 0) by (intros c; reflexivity).
  assert (UB0 : ubytes init_state = 0) by reflexivity.
  assert (HD0 : hand init_state = 0) by reflexivity.
  assert (GA : 0 <= GALL3 caps mc).
  { unfold GALL3. pose proof (proj1 (Hc 48 ltac:(lia))).
    assert (0 <= zsumZ (fun c => znth c (NF3 caps mc) + RED) (zseq 0 48))
      by (apply zsumZ_nonneg; intros c _; cbv beta; pose proof (NN c); unfold RED; lia).
    lia. }
  unfold res_ok_pack3. cbn [p3_live p3_bytes p3_cap p3_mis p3_mcap].
  refine (conj II_init (conj SI_init (conj GS_init (conj NL_init (conj noraw_init (conj MB_init _)))))).
  split; [split; [|split; [|split]]; intros *; intros H; exfalso; exact (NU _ _ _ H)|].
  split; [intros c Hc48; rewrite !GC0; split; [apply NN | unfold RED; lia]|].
  split; [split; intros k Hk; rewrite ?B0, ?UC0, ?MI0, ?Z0; try unfold COARSE; lia|].
  split.
  { split; [constructor|]. split; [intros e []|].
    intros c Hc48. pose proof (proj2 (Hc c ltac:(lia))). unfold count_mis. cbn [filter length]. lia. }
  split; [lia|]. split; [reflexivity|]. split; [exact Hlen|]. split; [exact Hlm|].
  split; [intros k Hk; rewrite Z0; pose proof (Hc k Hk); lia|].
  split; lia.
Qed.

Lemma res_ok_pack3_raise A b caps' mc' : res_ok_pack3 A b -> length caps' = 49%nat -> length mc' = 49%nat ->
  (forall k, 0 <= k < 49 -> znth k (p3_cap b) <= znth k caps') ->
  (forall k, 0 <= k < 49 -> znth k (p3_mcap b) <= znth k mc') ->
  res_ok_pack3 A (PB3 (p3_live b) (p3_bytes b) caps' (p3_mis b) mc').
Proof.
  intros (HII & HSI & HGS & HNL & HNR & HMB & HPK & HPC & HUP & (MS1 & MS2 & MS3) & Hub & HlL & HlC & HlM & Hbd & Hby & Hh)
    Hl Hlm Hc Hm.
  unfold res_ok_pack3. cbn [p3_live p3_bytes p3_cap p3_mis p3_mcap].
  refine (conj HII (conj HSI (conj HGS (conj HNL (conj HNR (conj HMB (conj HPK _))))))).
  split; [intros c Hc48; destruct (HPC c Hc48) as [P1 P2]; pose proof (NF3_mono _ _ _ _ Hc Hm c Hc48); split; lia|].
  split; [exact HUP|].
  split; [split; [exact MS1|]; split; [exact MS2|]; intros c Hc48; pose proof (MS3 c Hc48); pose proof (Hm c ltac:(lia)); lia|].
  split; [exact Hub|]. split; [exact HlL|]. split; [exact Hl|]. split; [exact Hlm|].
  split; [intros k Hk; pose proof (Hbd k Hk); pose proof (Hc k Hk); pose proof (Hm k Hk); lia|].
  split; [exact Hby|]. pose proof (GALL3_mono _ _ _ _ Hc Hm). lia.
Qed.
