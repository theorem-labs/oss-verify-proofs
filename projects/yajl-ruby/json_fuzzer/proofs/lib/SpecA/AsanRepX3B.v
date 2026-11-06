(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Mem Cells Step Frame Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanHoare AsanRep AsanKern AsanDepot
  AsanWf1 AsanWf3 AsanWf4 AsanWf5 AsanClient AsanRepFrame AsanRepFrame2 AsanBudget AsanHit AsanRepHitB AsanRepX AsanRepCaB AsanRepSecB AsanRepEnqB AsanRepX2B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section RX3.
Variable segs : list Segment.
Variable E : aenv.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).
#[warnings="-notation-for-abbreviation"] Notation SB := (ae_space_beg E).
#[warnings="-notation-for-abbreviation"] Notation T := (ae_thread E).
#[warnings="-notation-for-abbreviation"] Notation PA := (ae_ptr_array E).
#[warnings="-notation-for-abbreviation"] Notation AREPX := (ARepX segs E (DepotR segs E)).

Section DPX.
Variables (a1 a2 : astate) (m m' : mem) (blo bhi lo usp : Z).
Hypothesis ND : nd_same a1 a2.
Hypothesis WF1 : AWf E [] [] a1.
Hypothesis RENV2 : renv_ok E a2.
Hypothesis BLO : 0 <= blo.
Hypothesis BHI : bhi <= alloc_ceiling.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis REPX : AREPX a1 m blo bhi.
Hypothesis DEP : arep_depot (DepotR segs E) a2 m'.
Hypothesis WM : wmono segs m m'.
Hypothesis AG : forall z, 0 <= z < 2^64 -> (z + 1 <= lo \/ usp <= z) -> ~ DepotFPd E a2 z -> m' (wa z) = m (wa z).

Let BS2 : blocks_sep E a2. Proof. exact (proj1 RENV2). Qed.
Let Tpl : (0x1000 <= T /\ (T + 4096 <= 0x10000 \/ 0x603000 <= T)) /\ T + 4096 <= alloc_ceiling. Proof. exact (proj1 (proj2 RENV2)). Qed.
Let IMG_IN : forall r, In r (arep_img_ranges E ++ depot_static E) -> fst (ae_img E) <= fst r /\ fst r + snd r <= fst (ae_img E) + snd (ae_img E).
Proof. exact (proj1 (proj2 (proj2 RENV2))). Qed.
Let IMG_LO : 0x10000 <= fst (ae_img E). Proof. exact (proj1 (proj2 (proj2 (proj2 RENV2)))). Qed.
Let IMG_LOW : forall r, In r (arep_img_ranges E ++ depot_static E) -> 0x10000 <= fst r /\ fst r + snd r <= 0x603000.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 RENV2))))). Qed.
Let IMG_DEPSEP : forall x y, In x (arep_img_ranges E) -> In y (depot_static E) -> fst x + snd x <= fst y \/ fst y + snd y <= fst x.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 RENV2)))))). Qed.
Let AK2 : exists mo, AKern E a2 mo. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 RENV2))))))). Qed.
Let TDN : T + 4096 <= ae_depot_nodes E \/ ae_depot_nodes E + kDepotNodeBlockBytes <= T.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 RENV2)))))))). Qed.
Let DN0 : ae_depot_nodes E + kDepotNodeBlockBytes <= PA \/ PA + kPtrArrayLen <= ae_depot_nodes E.
Proof. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 RENV2)))))))). Qed.
Lemma Esec : as_sec a2 = as_sec a1. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ND)))))))). Qed.

(* [comment removed for export] *)
Lemma dfp_facts : forall x, DepotFPd E a2 x ->
     (forall r, In r (arep_img_ranges E) -> ~ (fst r <= x < fst r + snd r))
  /\ ~ (T <= x < T + 4096)
  /\ ~ (ae_resv_beg E <= x < ae_resv_beg E + 0x2000011000)
  /\ ~ (PA <= x < PA + 0x800000)
  /\ (forall sc, In sc (as_sec a1) -> ~ (sc_map_beg sc <= x < sc_map_beg sc + sc_map_size sc))
  /\ ~ (kLowAppEnd < x < kHighMemBeg).
Proof.
  intros x Hx. destruct AK2 as [mo2 K2]. pose proof Tpl as [[T1 T2] T3].
  pose proof (proj1 WF1) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & E20 &
                              E21 & E22 & E23 & E24 & E25 & E26 & E27 & E28 & E29 & E30 & E31 & E32 & E33 & _).
  pose proof WF1 as (_ & _ & _ & _ & _ & (_ & _ & S3 & _) & _).
  rewrite kHighMemBeg_val in E2. unfold img_sep in E33.
  destruct (DepotFPd_where E a2 x Hx) as [(r' & Hr' & R)|[(b & Hb & R)|(b & Hb & R)]].
  - (* [comment removed for export] *)
    assert (Hr'' : In r' (arep_img_ranges E ++ depot_static E)) by (apply in_app_iff; right; exact Hr').
    pose proof (IMG_LOW r' Hr'') as [L1 L2]. pose proof (IMG_IN r' Hr'') as [L3 L4].
    split.
    { intros r Hr Rr. destruct (IMG_DEPSEP r r' Hr Hr'); clear -R Rr H; lia. }
    split; [clear -R L1 L2 T1 T2; lia|]. split; [clear -R L2 E2; lia|]. split; [clear -R L3 L4 E33; lia|]. split.
    { intros sc Hsc Rs. destruct (S3 sc Hsc) as (_ & _ & _ & _ & _ & _ & SR). pose proof (SR _ E29) as X. destruct (ae_img E); cbn [fst snd] in *. clear -R Rs X L3 L4. lia. }
    rewrite kLowAppEnd_val. clear -R L2. lia.
  - (* [comment removed for export] *)
    pose proof (BS2 b kDepotNodeBlockBytes (or_introl (conj Hb eq_refl))) as (AM & CE & BR & BSC & BF & BI). rewrite Esec in BSC. unfold img_sep in BI. unfold app_mem in AM.
    split.
    { intros r Hr Rr. pose proof (IMG_IN r ltac:(apply in_app_iff; left; exact Hr)) as [I1 I2]. destruct (ae_img E); cbn [fst snd] in *. clear -R Rr BI I1 I2. lia. }
    split.
    { destruct Hb as [<-|Hb]; [clear -R TDN; lia|].
      destruct (ak_blocks_sep _ _ _ K2 b kDepotNodeBlockBytes (or_introl (conj Hb eq_refl))) as (_ & _ & _ & _ & _ & RR). pose proof (RR _ E13) as X. cbn [fst snd] in X. clear -R X. lia. }
    split; [clear -R BR; lia|]. split.
    { destruct Hb as [<-|Hb]; [unfold kPtrArrayLen in DN0; clear -R DN0; lia|].
      destruct (ak_blocks_sep _ _ _ K2 b kDepotNodeBlockBytes (or_introl (conj Hb eq_refl))) as (_ & _ & _ & _ & _ & RR). pose proof (RR _ E8) as X. cbn [fst snd] in X. clear -R X. lia. }
    split; [intros sc Hsc Rs; destruct (BSC sc Hsc); clear -R Rs H; lia|].
    rewrite kLowAppEnd_val, kHighMemBeg_val in *. clear -R AM. lia.
  - (* [comment removed for export] *)
    pose proof (BS2 b kStoreBlockBytes (or_intror (conj Hb eq_refl))) as (AM & CE & BR & BSC & BF & BI). rewrite Esec in BSC. unfold img_sep in BI. unfold app_mem in AM.
    split.
    { intros r Hr Rr. pose proof (IMG_IN r ltac:(apply in_app_iff; left; exact Hr)) as [I1 I2]. destruct (ae_img E); cbn [fst snd] in *. clear -R Rr BI I1 I2. lia. }
    split.
    { destruct Hb as [<-|Hb]; [pose proof (ak_store_sep _ _ _ K2) as (_ & _ & X & _); unfold kPageSize, kStoreBlockBytes in *; clear -R X; lia|].
      destruct (ak_blocks_sep _ _ _ K2 b kStoreBlockBytes (or_intror (conj Hb eq_refl))) as (_ & _ & _ & _ & _ & RR). pose proof (RR _ E13) as X. cbn [fst snd] in X. unfold kStoreBlockBytes in *. clear -R X. lia. }
    split; [clear -R BR; lia|]. split.
    { destruct Hb as [<-|Hb]; [pose proof (ak_store_sep _ _ _ K2) as (_ & _ & _ & _ & X); unfold kPtrArrayLen, kStoreBlockBytes in *; clear -R X; lia|].
      destruct (ak_blocks_sep _ _ _ K2 b kStoreBlockBytes (or_intror (conj Hb eq_refl))) as (_ & _ & _ & _ & _ & RR). pose proof (RR _ E8) as X. cbn [fst snd] in X. unfold kStoreBlockBytes in *. clear -R X. lia. }
    split; [intros sc Hsc Rs; destruct (BSC sc Hsc); clear -R Rs H; lia|].
    rewrite kLowAppEnd_val, kHighMemBeg_val in *. clear -R AM. lia.
Qed.

(* [comment removed for export] *)
Lemma AG_at : forall x, 0 <= x < alloc_ceiling -> ~ DepotFPd E a2 x -> m' (wa x) = m (wa x).
Proof. intros x Hx ND'. pose proof alloc_ceiling_range as CR. apply AG; [clear -Hx CR; lia| left; clear -Hx LO; lia| exact ND']. Qed.

Lemma AGimg : forall a, in_ranges (arep_img_ranges E) a -> m' (wa a) = m (wa a).
Proof.
  intros a (r & Hr & R). pose proof (IMG_LOW r ltac:(apply in_app_iff; left; exact Hr)) as [L1 L2]. pose proof alloc_ceiling_range as CR.
  apply AG_at; [clear -R L1 L2 CR; lia|]. intros Dx. destruct (dfp_facts a Dx) as (NI & _). exact (NI r Hr R).
Qed.
Lemma AG_resv : forall a, ae_resv_beg E <= a < ae_resv_beg E + 0x2000011000 -> m' (wa a) = m (wa a).
Proof.
  intros a R. pose proof (proj1 WF1) as (E1 & E2 & E3 & E4 & E5 & _). rewrite kHighMemBeg_val in E2.
  apply AG_at; [clear -R E2 E5; lia|]. intros Dx. destruct (dfp_facts a Dx) as (_ & _ & NR & _). exact (NR R).
Qed.
Lemma space_resv : forall a, SB <= a < SB + kSpaceSize + 0x1000 -> ae_resv_beg E <= a < ae_resv_beg E + 0x2000011000.
Proof. intros a Ha. pose proof (proj1 WF1) as (E1 & E2 & E3 & E4 & _). clear -Ha E3 E4. lia. Qed.
Lemma AGri : forall a, ae_region_info E <= a < ae_region_info E + kRegSize * kNumClasses -> m' (wa a) = m (wa a).
Proof. intros a Ha. apply AG_resv. apply space_resv. unfold ae_region_info, kRegSize, kNumClasses, kSpaceSize in *. clear -Ha. lia. Qed.
Lemma AGfa : forall a c', 0 <= c' < kNumClasses -> free_array SB c' <= a < free_array SB c' + rg_mapped_fa (region_of a1 c') -> m' (wa a) = m (wa a).
Proof.
  intros a c' Hc Ha. apply AG_resv. apply space_resv.
  assert (RM : in_some_region_map E a1 a = true).
  { unfold in_some_region_map. apply Bool.orb_true_iff. right. apply existsb_exists. exists c'. split; [apply In_ziota; unfold kNumClasses in Hc; lia|].
    apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; lia. }
  pose proof (region_map_in_space E [] [] a1 a WF1 RM) as SP. unfold kSpaceSize in *. clear -SP. lia.
Qed.
Lemma AGthr : forall a, in_ranges (arep_thr_ranges E) a -> m' (wa a) = m (wa a).
Proof.
  intros a Ha. pose proof (proj1 WF1) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & _). pose proof Tpl as [[T1 T2] T3].
  assert (HT : T <= a < T + 4096).
  { destruct Ha as (r & Hr & R). unfold arep_thr_ranges in Hr.
    unfold kThrStackTop, kThrQCache, kThrCache, kPerClassSize, kNumClasses, kThrCacheStats, kThrStats, kThrUnwinding in Hr.
    repeat (destruct Hr as [<-|Hr]; [cbn [fst snd] in R; clear -R; lia|]). destruct Hr. }
  apply AG_at; [clear -HT T1 T3; lia|]. intros Dx. destruct (dfp_facts a Dx) as (_ & NT & _). exact (NT HT).
Qed.
Lemma AGptr : forall a, PA <= a < PA + 8 * kChunksBlockCount -> m' (wa a) = m (wa a).
Proof.
  intros a Ha. pose proof (proj1 WF1) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & _). unfold app_mem in E16.
  unfold kChunksBlockCount in Ha. rewrite ?kLowAppEnd_val, ?kHighMemBeg_val in E16.
  apply AG_at; [clear -Ha E16 E17; lia|]. intros Dx. destruct (dfp_facts a Dx) as (_ & _ & _ & NP & _). apply NP. clear -Ha. lia.
Qed.
Lemma AG_secmap : forall a sc, In sc (as_sec a1) -> sc_map_beg sc <= a < sc_map_beg sc + sc_map_size sc -> m' (wa a) = m (wa a).
Proof.
  intros a sc Hsc Ha. pose proof WF1 as (_ & _ & _ & _ & _ & (_ & _ & S3 & _) & _). destruct (S3 sc Hsc) as (_ & AM & CE & _).
  unfold app_mem in AM. rewrite ?kLowAppEnd_val, ?kHighMemBeg_val in AM.
  apply AG_at; [clear -Ha AM CE; lia|]. intros Dx. destruct (dfp_facts a Dx) as (_ & _ & _ & _ & NS & _). exact (NS sc Hsc Ha).
Qed.
Lemma AGsec : forall a sc, In sc (as_sec a1) -> sc_map_beg sc <= a < sc_map_beg sc + 32 -> m' (wa a) = m (wa a).
Proof.
  intros a sc Hsc Ha. pose proof WF1 as (_ & _ & _ & _ & _ & (_ & _ & S3 & _) & _). destruct (S3 sc Hsc) as (_ & _ & _ & POS & MODS & _).
  pose proof (AsanRepFrame.pos_mod_ge E (sc_map_size sc) kPageSize POS MODS ltac:(unfold kPageSize; lia)) as GE. unfold kPageSize in GE.
  apply (AG_secmap a sc Hsc). clear -Ha GE. lia.
Qed.
Lemma AGcm : forall a cb cm, as_chunks a1 !! cb = Some cm -> chunk_meta_fp cm a -> m' (wa a) = m (wa a).
Proof.
  intros a cb cm Hcm Ha. pose proof (chunk_meta_in_block E [] [] a1 cb cm a WF1 Hcm Ha) as [BL BU].
  destruct (block_where E [] [] a1 cb cm WF1 Hcm) as [(J1 & J2 & _)|(sc & Hsc & _ & L1 & L2)].
  - apply AG_resv. apply space_resv. clear -BL BU J1 J2. lia.
  - apply (AG_secmap a sc Hsc). unfold kPageSize in L1. clear -BL BU L1 L2. lia.
Qed.
Lemma AGbat : forall a b, In b (as_tq a1 ++ as_gq a1) -> b_addr b <= a < b_addr b + 24 + 8 * kBatchCap -> m' (wa a) = m (wa a).
Proof.
  intros a b Hb Ha. apply AG_resv. pose proof WF1 as (WE & WR & _ & _ & WQ & _).
  destruct (batch_block E [] a1 b WQ ltac:(unfold all_batches; rewrite app_assoc; apply in_app_iff; left; exact Hb)) as (CV & _).
  assert (HB24 : 1 <= kBatchClass <= kLargestClassID) by (unfold kBatchClass, kLargestClassID; lia).
  pose proof (carved_in_space E a1 kBatchClass _ HB24 WR CV) as [J1 J2].
  assert (CS : class_size kBatchClass = 8192) by reflexivity.
  apply space_resv. unfold kBatchCap, kSpaceSize, kRegionSize in *. clear -Ha J1 J2 CS. lia.
Qed.
Lemma AGsh : forall g v, Sh E a1 (8 * g) = Some v -> m' (wa (kShadowBase + g)) = m (wa (kShadowBase + g)).
Proof.
  intros g v Hg. pose proof (AsanRepSecB.Sh_granule_range E a1 WF1 _ _ Hg) as GR. pose proof alloc_ceiling_range as CR.
  assert (BAND : kLowAppEnd < kShadowBase + g < kHighMemBeg) by (rewrite kLowAppEnd_val, kHighMemBeg_val; unfold kShadowBase; clear -GR; lia).
  pose proof BAND as BANDn. rewrite kLowAppEnd_val, kHighMemBeg_val in BANDn.
  apply AG_at; [clear -BANDn CR; lia|]. intros Dx. destruct (dfp_facts _ Dx) as (_ & _ & _ & _ & _ & NB). exact (NB BAND).
Qed.

Theorem ARepX_dput_step : AREPX a2 m' blo bhi.
Proof.
  pose proof REPX as (RA & RB & RC & RD & RE & RF & RG & _ & RI & RJ).
  pose proof (frameA' segs E a1 m m' AGimg RA) as RA'. pose proof (frameB' segs E a1 m m' AGri RB) as RB'.
  pose proof (frameC' segs E a1 m m' WM AGfa RC) as RC'. pose proof (frameD' segs E a1 m m' AGthr RD) as RD'.
  pose proof (frameE' segs E a1 m m' WM AGptr AGsec RE) as RE'. pose proof (frameF' segs a1 m m' AGcm RF) as RF'.
  pose proof (frameG' segs a1 m m' AGbat RG) as RG'. pose proof (frameI' segs E a1 m m' WM AGimg RI) as RI'.
  assert (RJ' : arep_shadow_but segs E blo bhi a1 m').
  { intros g v Hg OUT. eapply rw_cells_agree'; [| exact (RJ g v Hg OUT)]. cbn. intros x Hx. replace x with (kShadowBase + g) by (clear -Hx; lia). exact (AGsh g v Hg). }
  pose proof DEP as RH. revert RA' RB' RC' RD' RE' RF' RG' RI' RJ' RH. generalize ND. clear. intros ND0.
  destruct a1, a2. unfold nd_same in ND0. cbn in ND0.
  destruct ND0 as (-> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & ->).
  intros RA RB RC RD RE RF RG RI RJ RH.
  split; [exact RA|]. split; [exact RB|]. split; [exact RC|]. split; [exact RD|]. split; [exact RE|]. split; [exact RF|].
  split; [destruct RG as [RG1 RG2]; split; eapply arep_batch_list_indep; eassumption|].
  split; [exact RH|]. split; [exact RI| exact RJ].
Qed.
End DPX.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition blk_mono (s0 s : astate) : Prop :=
  (forall x, In x (as_node_blocks s0) -> In x (as_node_blocks s)) /\ (forall x, In x (as_store_blocks s0) -> In x (as_store_blocks s)).
Lemma blk_mono_refl : forall s, blk_mono s s. Proof. intros s. split; intros x H; exact H. Qed.
Ltac bm_keep := lazymatch goal with H : blk_mono ?a0 ?st |- blk_mono ?a0 _ =>
  revert H; destruct st; intros [H1 H2]; split; intros x__ Hx__; cbn;
  first [exact (H1 x__ Hx__) | exact (H2 x__ Hx__) | apply in_app_iff; left; first [exact (H1 x__ Hx__) | exact (H2 x__ Hx__)]] end.
Lemma call_mmap_ordie_bm : forall s0 l fl, presW (blk_mono s0) (call_mmap_ordie E l fl).
Proof. intros; unfold call_mmap_ordie. pw. Qed.
Lemma store_alloc_bm : forall s0 c, presW (blk_mono s0) (store_alloc E c).
Proof. intros; unfold store_alloc, store_alloc_once. pw; try apply call_mmap_ordie_bm; bm_keep. Qed.
Lemma depot_put_bm : forall s0 k, presW (blk_mono s0) (depot_put E k).
Proof. intros; unfold depot_put. pw; try apply call_mmap_ordie_bm; try apply store_alloc_bm; bm_keep. Qed.
Theorem depot_put_blocks_mono : forall s0 k,
  hoareW (fun s => s = s0) (depot_put E k)
         (fun s' _ => (forall x, In x (as_node_blocks s0) -> In x (as_node_blocks s')) /\ (forall x, In x (as_store_blocks s0) -> In x (as_store_blocks s'))).
Proof.
  intros s0 k. eapply hoareW_conseq; [apply (depot_put_bm s0 k)| intros s ->; apply blk_mono_refl| intros s' r H; exact H].
Qed.
End RX3.
End RC__1.
