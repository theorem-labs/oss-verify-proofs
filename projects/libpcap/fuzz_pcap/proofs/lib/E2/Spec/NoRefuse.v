(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Nodes Decode Lps04.   (* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Quant FreeRange. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KArith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KLink OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Quant OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.FreeRange.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CE : CEIL}.
#[using="Type"] Lemma live_bytes_iv_subtract_le : forall a sz lo hi, 0 <= lo -> lo <= hi ->
  live_bytes (iv_subtract a sz lo hi) <= bv_unsigned sz.
Proof.
  intros a sz lo hi Hlo Hlh. pose proof (bv_unsigned_in_range 64 a) as Ra. pose proof (bv_unsigned_in_range 64 sz) as Rs. unfold bv_modulus in *.
  unfold iv_subtract.
  destruct (Z.ltb_spec (bv_unsigned a) lo); destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); cbn;
    rewrite ?unsigned_lit_wrap;
    try pose proof (Z.mod_le (bv_unsigned sz `min` (lo - bv_unsigned a)) (2^64) ltac:(lia) ltac:(lia));
    try pose proof (Z.mod_le (bv_unsigned a + bv_unsigned sz - bv_unsigned a `max` hi) (2^64) ltac:(lia) ltac:(lia)); lia.
Qed.

#[using="Type"] Lemma live_bytes_subtract_le : forall maps lo hi, 0 <= lo -> lo <= hi ->
  live_bytes (maps_subtract maps lo hi) <= live_bytes maps.
Proof.
  intros maps lo hi H0 H. induction maps as [|[a sz] l IH]; cbn; [lia|]. rewrite live_bytes_app.
  pose proof (live_bytes_iv_subtract_le a sz lo hi H0 H). lia.
Qed.

#[using="Type"] Lemma live_bytes_subtract_all_le : forall cuts maps,
  live_bytes (maps_subtract_all maps cuts) <= live_bytes maps.
Proof.
  induction cuts as [|[a n] cuts IH]; intros maps; cbn; [lia|].
  etransitivity; [apply IH|]. apply live_bytes_subtract_le; pose proof (bv_unsigned_in_range 64 a); pose proof (bv_unsigned_in_range 64 n); lia.
Qed.

#[using="Type"] Lemma vm_backing_used_le_live : forall mo, lazyfree mo ->
  vm_backing_used mo <= vm_live_bytes (m_vmmaps mo).
Proof.
  intros mo [Hl Hm]. unfold vm_backing_used, vm_backed_maps, vm_live_bytes. rewrite Hl, Hm. cbn [maps_subtract_all length Z.of_nat].
  pose proof (live_bytes_subtract_all_le (vm_noaccess (m_vmmaps mo)) (vm_maps (m_vmmaps mo))). lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma vm_backing_used_mprotect_le : forall mo addr n, lazyfree mo ->
  vm_backing_used (mprotect_model_next mo addr n) <= vm_live_bytes (m_vmmaps mo).
Proof.
  intros mo addr n [Hl Hm]. unfold vm_backing_used, vm_backed_maps, vm_live_bytes, mprotect_model_next.
  rewrite m_vmmaps_with_vmmaps. cbn [vm_maps vm_noaccess].
  replace (m_vm_lazy (with_vmmaps _ mo)) with (m_vm_lazy mo) by (destruct mo; reflexivity).
  replace (m_vm_materialized (with_vmmaps _ mo)) with (m_vm_materialized mo) by (destruct mo; reflexivity).
  rewrite Hl, Hm. cbn [maps_subtract_all length Z.of_nat].
  pose proof (live_bytes_subtract_all_le (maps_subtract (vm_noaccess (m_vmmaps mo)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)) (vm_maps (m_vmmaps mo))). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma band_count_gran : forall l,
  (forall e, In e l -> ehiZ e <= bottomup_floor \/ page_size <= szZ e) ->
  page_size * band_count l <= band_bytes l.
Proof.
  induction l as [|e l IH]; intros H; cbn; [lia|].
  specialize (IH ltac:(intros x Hx; apply H; right; exact Hx)).
  unfold inband. destruct (Z.ltb_spec bottomup_floor (ehiZ e)); [|lia].
  destruct (H e (or_introl eq_refl)) as [He|He]; [lia|]. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma band_zero_below : forall l B0, B0 <= bottomup_floor ->
  (forall e, In e l -> ehiZ e <= B0) -> band_bytes l = 0 /\ band_count l = 0.
Proof. intros l B0 HB H. apply band_below. intros e He. specialize (H e He). lia. Qed.

Section Census.
Variables (L : mled) (pbrk : Z) (mo : Model) (B : Z).
Hypothesis HK : KL L pbrk mo.
Hypothesis HLI : LI L mo.
Hypothesis HB : gm L + BB L + PINB <= B.
#[using="HB"] Lemma HB0 : gm L + BB L <= B. Proof. pose proof PINB_nonneg. lia. Qed.
(* [comment removed for export] *)
Hypothesis Hfloor : bv_unsigned (vm_start_brk (m_vmmaps mo)) + 2 * PGSZ + B <= bottomup_floor.

Let h := m_vmmaps mo.

#[using="L HLI HB"] Lemma live_le_B : vm_live_bytes h <= B.
Proof. apply LI_elim in HLI. subst h. lia. Qed.

#[using="CE pbrk mo HK"] Lemma BB_ge_brkreg : match ld_brkreg L with Some (_, l) => l | None => 0 end <= BB L /\ 0 <= BB L.
Proof.
  unfold BB. pose proof (kl_phase _ _ _ HK) as P. destruct (ld_brk L).
  - destruct P as [_ ->]. unfold PGSZ. lia.
  - destruct P as (_ & _ & _ & ->). unfold PGSZ. lia.
  - destruct P as (_ & _ & _ & -> & _). unfold PGSZ. lia.
  - destruct P as (b & l & E & _). rewrite E. pose proof (kl_brkreg _ _ _ HK b l E). unfold PGSZ in *. lia.
  - destruct (ld_brkreg L) as [[b l]|] eqn:E; [| lia]. pose proof (kl_brkreg _ _ _ HK b l E). unfold PGSZ in *. lia.
Qed.

#[using="CE pbrk mo HK"] Lemma gm_nonneg : 0 <= gm L.
Proof.
  unfold gm.
  assert (G : forall (l : list (Z * Z)), (forall g, In g l -> 0 < snd g) -> 0 <= fold_right Z.add 0 (map (fun g : Z * Z => mmap_len (snd g)) l)).
  { induction l as [|g l IH]; intros Hl; cbn [fold_right map]; [lia|]. pose proof (Hl g (or_introl eq_refl)). pose proof (mmap_len_ge (snd g) (Hl g (or_introl eq_refl))). specialize (IH ltac:(intros; apply Hl; right; assumption)). lia. }
  assert (M : forall (l : list (Z * Z * Z)), (forall m, In m l -> 0 < snd (fst m)) -> 0 <= fold_right Z.add 0 (map (fun m : Z * Z * Z => mmap_len (snd (fst m))) l)).
  { induction l as [|m l IH]; intros Hl; cbn [fold_right map]; [lia|]. pose proof (Hl m (or_introl eq_refl)). pose proof (mmap_len_ge (snd (fst m)) (Hl m (or_introl eq_refl))). specialize (IH ltac:(intros; apply Hl; right; assumption)). lia. }
  pose proof (G (ld_groups L) ltac:(intros [b l] Hin; cbn; pose proof (kl_groups _ _ _ HK b l Hin); lia)).
  pose proof (M (ld_metas L) ltac:(intros [[b l] k] Hin; cbn; pose proof (kl_metas _ _ _ HK b l k Hin); lia)). lia.
Qed.

#[using="CE L pbrk B HK HB Hfloor"] Lemma brk_below_floor : bv_unsigned (vm_brk h) <= bottomup_floor.
Proof.
  pose proof (kl_brk_hi _ _ _ HK) as H1. pose proof BB_ge_brkreg as [H2 H3]. pose proof gm_nonneg. pose proof HB0. subst h. lia.
Qed.

#[using="CE L pbrk B HK HB Hfloor"] Lemma resv_below_floor : forall e, In e (vm_reserved h) -> ehiZ e <= bottomup_floor.
Proof.
  intros e He. pose proof (kl_resv_top _ _ _ HK e He) as H1. pose proof (kl_start _ _ _ HK) as (_ & _ & S3 & _).
  pose proof BB_ge_brkreg as [_ H3]. pose proof gm_nonneg. pose proof HB0. unfold ehiZ, eloZ, szZ. unfold ehi in H1. subst h. unfold PGSZ in *. lia.
Qed.

#[using="CE L pbrk HK HLI HB Hfloor"] Lemma band_bytes_bound : band_bytes (vm_reserved h ++ vm_maps h) <= B.
Proof.
  rewrite band_bytes_app. destruct (band_zero_below (vm_reserved h) bottomup_floor ltac:(lia) resv_below_floor) as [-> _].
  pose proof (band_bytes_le_live (vm_maps h)). pose proof live_le_B. unfold vm_live_bytes in *. lia.
Qed.

#[using="CE L pbrk HK HLI HB Hfloor"] Lemma band_count_bound : page_size * band_count (vm_reserved h ++ vm_maps h) <= B.
Proof.
  rewrite band_count_app. destruct (band_zero_below (vm_reserved h) bottomup_floor ltac:(lia) resv_below_floor) as [_ ->].
  pose proof (band_count_gran (vm_maps h)) as G.
  assert (Hg : forall e, In e (vm_maps h) -> ehiZ e <= bottomup_floor \/ page_size <= szZ e).
  { intros e He. destruct (kl_gran _ _ _ HK e He) as [Hb|(S1 & S2 & _)].
    - left. pose proof brk_below_floor. unfold ehiZ, eloZ, szZ. unfold ehi in Hb. subst h. lia.
    - right. unfold szZ. rewrite page_size_eq. unfold PGSZ in S2. pose proof (Z_div_mod_eq_full (bv_unsigned (snd e)) 4096). nia. }
  specialize (G Hg). pose proof (band_bytes_le_live (vm_maps h)). pose proof live_le_B. unfold vm_live_bytes in *. lia.
Qed.

(* [comment removed for export] *)
#[using="CE L pbrk HK HLI HB Hfloor"] Theorem gap_available : forall nZ, 0 < nZ ->
  nZ + B + (B / page_size) * (page_size + nZ) <= band_ceiling - bottomup_floor ->
  vm_gap_available h nZ = true.
Proof.
  intros nZ Hn Hfit. apply (vm_gap_available_of_bound h nZ (B / page_size) B Hn).
  - pose proof band_count_bound as C. pose proof (band_count_nonneg (vm_reserved h ++ vm_maps h)).
    rewrite page_size_eq in *. apply Z.div_le_lower_bound; [lia|]. lia.
  - exact band_bytes_bound.
  - exact Hfit.
Qed.

(* [comment removed for export] *)
#[using="CE L pbrk HK HLI HB h"] Theorem backing_le_B : vm_backing_used mo <= B.
Proof. pose proof (vm_backing_used_le_live mo (minv_lazyfree _ (kl_minv _ _ _ HK))). pose proof live_le_B. subst h. lia. Qed.

(* [comment removed for export] *)
#[using="CE L pbrk HK HLI HB Hfloor"] Theorem mmap_not_refusable : forall flags nZ, 0 < nZ ->
  B + nZ <= vm_limit h ->
  nZ + B + (B / page_size) * (page_size + nZ) <= band_ceiling - bottomup_floor ->
  mmap_grant_refusable flags mo nZ = false /\ mmap_reserve_refusable mo nZ = false.
Proof.
  intros flags nZ Hn Hbud Hfit. pose proof (gap_available nZ Hn Hfit) as G. pose proof backing_le_B as BB0.
  unfold mmap_grant_refusable, mmap_reserve_refusable, mmap_noreserve_backed_ok. fold h. rewrite G.
  destruct (mmap_noreserve_b flags); [split; reflexivity|].
  replace (vm_backing_used mo + nZ <=? vm_limit h) with true by (symmetry; apply Z.leb_le; lia). split; reflexivity.
Qed.

(* [comment removed for export] *)
#[using="CE L pbrk HK HLI HB"] Theorem mprotect_not_refusable : forall addr n,
  B <= vm_limit h -> mprotect_refusable mo addr n = false.
Proof.
  intros addr n Hbud. unfold mprotect_refusable, mprotect_budget_ok, vm_backing_within_limit.
  pose proof (vm_backing_used_mprotect_le mo addr n (minv_lazyfree _ (kl_minv _ _ _ HK))) as H1. pose proof live_le_B as H2.
  replace (vm_limit (m_vmmaps (mprotect_model_next mo addr n))) with (vm_limit h) by (unfold mprotect_model_next; rewrite m_vmmaps_with_vmmaps; reflexivity).
  replace (vm_backing_used (mprotect_model_next mo addr n) <=? vm_limit h) with true by (symmetry; apply Z.leb_le; subst h; lia). reflexivity.
Qed.
End Census.

End WithCeil.
