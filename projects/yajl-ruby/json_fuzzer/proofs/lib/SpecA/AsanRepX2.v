(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Mem Cells Step Frame Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanHoare AsanRep AsanKern AsanDepot
  AsanWf1 AsanWf3 AsanWf4 AsanWf5 AsanWf6 AsanClient AsanRepFrame AsanRepFrame2 AsanBudget AsanHit AsanRepHit AsanRepX AsanRepCa AsanRepRefill.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section RX2.
Variable segs : list Segment.
Variable E : aenv.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).
#[warnings="-notation-for-abbreviation"] Notation SB := (ae_space_beg E).
#[warnings="-notation-for-abbreviation"] Notation T := (ae_thread E).
#[warnings="-notation-for-abbreviation"] Notation PA := (ae_ptr_array E).
#[warnings="-notation-for-abbreviation"] Notation AREPX := (ARepX segs E (DepotR segs E)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition nd_same (a b : astate) : Prop :=
     as_regions b = as_regions a /\ as_cache_inited b = as_cache_inited a /\ as_cache b = as_cache a /\ as_cache_stale b = as_cache_stale a
  /\ as_cache_allocated b = as_cache_allocated a /\ as_cache_mapped b = as_cache_mapped a /\ as_ptr_committed b = as_ptr_committed a
  /\ as_sec b = as_sec a /\ as_sec_stale b = as_sec_stale a /\ as_sec_stats b = as_sec_stats a
  /\ as_glob_allocated b = as_glob_allocated a /\ as_glob_mapped b = as_glob_mapped a /\ as_oom b = as_oom a
  /\ as_chunks b = as_chunks a /\ as_dead b = as_dead a /\ as_tq b = as_tq a /\ as_gq b = as_gq a
  /\ as_ia_inited b = as_ia_inited a /\ as_ts b = as_ts a /\ as_residue b = as_residue a
  /\ as_nprim_ever b = as_nprim_ever a /\ as_everc b = as_everc a.
Lemma nd_same_refl : forall a, nd_same a a. Proof. intros a. repeat split; reflexivity. Qed.
Lemma nd_same_trans : forall a b c, nd_same a b -> nd_same b c -> nd_same a c.
Proof. intros a b c H1 H2. unfold nd_same in *. intuition congruence. Qed.

Ltac nd_keep := lazymatch goal with H : nd_same ?a0 ?st |- nd_same ?a0 _ => revert H; destruct st; intros H; exact H end.
Lemma call_mmap_ordie_nd : forall a0 l fl, presW (nd_same a0) (call_mmap_ordie E l fl).
Proof. intros; unfold call_mmap_ordie. pw. Qed.
Lemma store_alloc_nd : forall a0 c, presW (nd_same a0) (store_alloc E c).
Proof. intros; unfold store_alloc, store_alloc_once. pw; try apply call_mmap_ordie_nd; nd_keep. Qed.
Lemma depot_put_nd : forall a0 k, presW (nd_same a0) (depot_put E k).
Proof. intros; unfold depot_put. pw; try apply call_mmap_ordie_nd; try apply store_alloc_nd; nd_keep. Qed.
(* [comment removed for export] *)


(* [comment removed for export] *)
Lemma avail_nd : forall D a1 a2 c x, nd_same a1 a2 -> avail E D a1 c x -> avail E D a2 c x.
Proof.
  intros D a1 a2 c x ND AV. destruct a1, a2. unfold nd_same in ND. cbn in ND.
  destruct ND as (-> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & ->). exact AV.
Qed.
Lemma carved_nd : forall a1 a2 c x, nd_same a1 a2 -> carved E a1 c x -> carved E a2 c x.
Proof.
  intros a1 a2 c x ND CV. destruct a1, a2. unfold nd_same in ND. cbn in ND.
  destruct ND as (-> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & ->). exact CV.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ARepX_depot_swap : forall a1 a2 (m : mem) blo bhi,
  nd_same a1 a2 -> AREPX a1 m blo bhi -> arep_depot (DepotR segs E) a2 m -> AREPX a2 m blo bhi.
Proof.
  intros a1 a2 m blo bhi ND (RA & RB & RC & RD & RE & RF & RG & _ & RI & RJ) RH.
  destruct a1, a2. unfold nd_same in ND. cbn in ND.
  destruct ND as (-> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & -> & ->).
  split; [exact RA|]. split; [exact RB|]. split; [exact RC|]. split; [exact RD|]. split; [exact RE|]. split; [exact RF|].
  split; [destruct RG as [RG1 RG2]; split; eapply arep_batch_list_indep; eassumption|].
  split; [exact RH|]. split; [exact RI| exact RJ].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FRX.
Variables (P : list Z) (D : list batch) (s : astate) (m m' : mem) (blo bhi : Z).
#[warnings="-notation-for-abbreviation"] Notation WIN a := (kShadowBase + blo / 8 <= a < kShadowBase + (bhi + 7) / 8).
Hypothesis WF : AWf E P D s.
Hypothesis BS : blocks_sep E s.
Hypothesis IMG_IN : forall r, In r (arep_img_ranges E ++ depot_static E) -> fst (ae_img E) <= fst r /\ fst r + snd r <= fst (ae_img E) + snd (ae_img E).
Hypothesis IMG_LOW : forall r, In r (arep_img_ranges E ++ depot_static E) -> 0x10000 <= fst r /\ fst r + snd r <= 0x603000.
Hypothesis BLO : 0 <= blo.
Hypothesis BHI : bhi <= alloc_ceiling.
Hypothesis WM : wmono segs m m'.
Hypothesis AG : forall a, arep_fp E (DepotFP E) s a -> ~ WIN a -> m' (wa a) = m (wa a).

(* [comment removed for export] *)
Lemma win_band : forall a, WIN a -> kLowAppEnd < a < kHighMemBeg.
Proof.
  intros a Ha. pose proof alloc_ceiling_range as CR. rewrite kLowAppEnd_val, kHighMemBeg_val. unfold kShadowBase in Ha.
  clear -Ha BLO BHI CR. Z.div_mod_to_equations. lia.
Qed.
Lemma AG_app : forall a, arep_fp E (DepotFP E) s a -> (a < kLowAppEnd \/ kHighMemBeg <= a) -> m' (wa a) = m (wa a).
Proof. intros a Ha R. apply AG; [exact Ha|]. intros W. pose proof (win_band a W). clear -H R. lia. Qed.

Lemma AGimg : forall a, in_ranges (arep_img_ranges E) a -> m' (wa a) = m (wa a).
Proof.
  intros a (r & Hr & R). pose proof (IMG_LOW r ltac:(apply in_app_iff; left; exact Hr)) as [L1 L2].
  apply AG_app; [left; exists r; split; [exact Hr| exact R]| left; rewrite kLowAppEnd_val; clear -R L2; lia].
Qed.
Lemma AGri : forall a, ae_region_info E <= a < ae_region_info E + kRegSize * kNumClasses -> m' (wa a) = m (wa a).
Proof.
  intros a Ha. pose proof (proj1 WF) as (E1 & E2 & E3 & E4 & _).
  apply AG_app; [right; left; exact Ha| right]. unfold ae_region_info, kSpaceSize in *. clear -Ha E2 E3. lia.
Qed.
Lemma AGfa : forall a c', 0 <= c' < kNumClasses -> free_array SB c' <= a < free_array SB c' + rg_mapped_fa (region_of s c') -> m' (wa a) = m (wa a).
Proof.
  intros a c' Hc Ha. pose proof (proj1 WF) as (E1 & E2 & E3 & E4 & _).
  apply AG_app; [do 3 right; left; exists c'; split; [exact Hc| exact Ha]| right].
  unfold free_array, region_beg, kRegionSize, kFreeArrayOffset in Ha. clear -Ha Hc E2 E3. nia.
Qed.
Lemma AGthr : forall a, in_ranges (arep_thr_ranges E) a -> m' (wa a) = m (wa a).
Proof.
  intros a Ha. pose proof (proj1 WF) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & _). unfold app_mem in E14.
  assert (HT : T <= a < T + 4096).
  { destruct Ha as (r & Hr & R). unfold arep_thr_ranges in Hr.
    unfold kThrStackTop, kThrQCache, kThrCache, kPerClassSize, kNumClasses, kThrCacheStats, kThrStats, kThrUnwinding in Hr.
    repeat (destruct Hr as [<-|Hr]; [cbn [fst snd] in R; clear -R; lia|]). destruct Hr. }
  apply AG_app; [do 2 right; left; exact Ha| clear -HT E14; lia].
Qed.
Lemma AGptr : forall a, PA <= a < PA + 8 * kChunksBlockCount -> m' (wa a) = m (wa a).
Proof.
  intros a Ha. pose proof (proj1 WF) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & _). unfold app_mem in E16.
  apply AG_app; [do 4 right; left; exact Ha| unfold kChunksBlockCount in Ha; clear -Ha E16; lia].
Qed.
Lemma AGsec : forall a sc, In sc (as_sec s) -> sc_map_beg sc <= a < sc_map_beg sc + 32 -> m' (wa a) = m (wa a).
Proof.
  intros a sc Hsc Ha. pose proof WF as (_ & _ & _ & _ & _ & (_ & _ & S3 & _) & _). destruct (S3 sc Hsc) as (_ & AM & _ & POS & MODS & _).
  pose proof (AsanRepFrame.pos_mod_ge E (sc_map_size sc) kPageSize POS MODS ltac:(unfold kPageSize; lia)) as GE. unfold app_mem, kPageSize in *.
  apply AG_app; [do 5 right; left; exists sc; split; [exact Hsc| exact Ha]| clear -Ha AM GE; lia].
Qed.
Lemma AGcm : forall a cb cm, as_chunks s !! cb = Some cm -> chunk_meta_fp cm a -> m' (wa a) = m (wa a).
Proof.
  intros a cb cm Hcm Ha. pose proof (proj1 WF) as (E1 & E2 & E3 & E4 & _).
  pose proof (chunk_meta_in_block E P D s cb cm a WF Hcm Ha) as [BL BU].
  apply AG_app; [do 6 right; left; exists cb, cm; split; [exact Hcm| exact Ha]|].
  destruct (block_where E P D s cb cm WF Hcm) as [(J1 & J2 & _)|(sc & Hsc & _ & L1 & L2)].
  - right. clear -BL J1 E2 E3. lia.
  - pose proof WF as (_ & _ & _ & _ & _ & (_ & _ & S3 & _) & _). destruct (S3 sc Hsc) as (_ & AM & _). unfold app_mem, kPageSize in *. clear -BL BU L1 L2 AM. lia.
Qed.
Lemma AGbat : forall a b, In b (as_tq s ++ as_gq s) -> b_addr b <= a < b_addr b + 24 + 8 * kBatchCap -> m' (wa a) = m (wa a).
Proof.
  intros a b Hb Ha. pose proof WF as (WE & WR & _ & _ & WQ & _). pose proof WE as (E1 & E2 & E3 & E4 & _).
  destruct (batch_block E D s b WQ ltac:(unfold all_batches; rewrite app_assoc; apply in_app_iff; left; exact Hb)) as (CV & _).
  assert (HB24 : 1 <= kBatchClass <= kLargestClassID) by (unfold kBatchClass, kLargestClassID; lia).
  pose proof (carved_in_space E s kBatchClass _ HB24 WR CV) as [J1 J2].
  apply AG_app; [do 7 right; left; exists b; split; [exact Hb| exact Ha]| right]. unfold kRegionSize in J1. clear -Ha J1 E2 E3. lia.
Qed.
Lemma AGdep : forall a, DepotFP E s a -> m' (wa a) = m (wa a).
Proof.
  intros a Ha. assert (FPa : arep_fp E (DepotFP E) s a) by (do 8 right; left; exact Ha).
  destruct (DepotFP_where E s a Ha) as [(r & Hr & R)|[(b & Hb & R)|(b & Hb & R)]].
  - pose proof (IMG_LOW r ltac:(apply in_app_iff; right; exact Hr)) as [L1 L2]. apply AG_app; [exact FPa| left; rewrite kLowAppEnd_val; clear -R L2; lia].
  - pose proof (BS b kDepotNodeBlockBytes (or_introl (conj Hb eq_refl))) as (AM & _). unfold app_mem in AM. apply AG_app; [exact FPa| clear -R AM; lia].
  - pose proof (BS b kStoreBlockBytes (or_intror (conj Hb eq_refl))) as (AM & _). unfold app_mem in AM. apply AG_app; [exact FPa| clear -R AM; lia].
Qed.

Theorem ARepX_frame : AREPX s m blo bhi -> AREPX s m' blo bhi.
Proof.
  intros (RA & RB & RC & RD & RE & RF & RG & RH & RI & RJ).
  split; [exact (frameA' segs E s m m' AGimg RA)|].
  split; [exact (frameB' segs E s m m' AGri RB)|].
  split; [exact (frameC' segs E s m m' WM AGfa RC)|].
  split; [exact (frameD' segs E s m m' AGthr RD)|].
  split; [exact (frameE' segs E s m m' WM AGptr AGsec RE)|].
  split; [exact (frameF' segs s m m' AGcm RF)|].
  split; [exact (frameG' segs s m m' AGbat RG)|].
  split; [exact (frameH' segs E s m m' WM AGdep RH)|].
  split; [exact (frameI' segs E s m m' WM AGimg RI)|].
  intros g v Hg OUT. eapply rw_cells_agree'; [| exact (RJ g v Hg OUT)]. cbn. intros x Hx. replace x with (kShadowBase + g) by (clear -Hx; lia).
  apply AG; [do 9 right; exists g, v; split; [reflexivity| exact Hg]|].
  intros W. clear -W OUT BLO. Z.div_mod_to_equations. lia.
Qed.
End FRX.
End RX2.
End RC__1.
