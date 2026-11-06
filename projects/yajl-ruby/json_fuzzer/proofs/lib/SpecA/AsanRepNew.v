(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Mem Cells Step Frame Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanHoare AsanRep AsanKern AsanDepot
  AsanWf1 AsanWf3 AsanWf4 AsanWf5 AsanWf6 AsanClient AsanRepFrame AsanRepFrame2 AsanBudget AsanHit AsanRepHit AsanRepX AsanRepRefill.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section NB.
Variable E : aenv.
#[warnings="-notation-for-abbreviation"] Notation SB := (ae_space_beg E).
#[warnings="-notation-for-abbreviation"] Notation T := (ae_thread E).
#[warnings="-notation-for-abbreviation"] Notation RI := (ae_region_info E).
#[warnings="-notation-for-abbreviation"] Notation PA := (ae_ptr_array E).

Variables (a a1 : astate) (n ab : Z).
Hypothesis WF0 : AWf E [] [] a.
Hypothesis WF1 : AWf E [] [] a1.
Hypothesis CH : as_chunks a1 = as_chunks a.
Hypothesis BS1 : blocks_sep E a1.
Hypothesis IMG_IN : forall r, In r (arep_img_ranges E ++ depot_static E) -> fst (ae_img E) <= fst r /\ fst r + snd r <= fst (ae_img E) + snd (ae_img E).
Hypothesis Hn : 0 < n <= 2^27.

(* [comment removed for export] *)
Lemma sh_cell_band : forall g v, Sh E a1 (8 * g) = Some v -> kLowAppEnd < kShadowBase + g < kHighMemBeg.
Proof.
  intros g v Hg.
  assert (GR : 0 <= 8 * g < 2^47).
  { pose proof WF1 as WF2. pose proof alloc_ceiling_range as CR. unfold Sh in Hg.
    destruct (in_some_region_map E a1 (8 * g)) eqn:RM.
    - pose proof (region_map_in_space E [] [] a1 (8 * g) WF2 RM) as SP. pose proof (proj1 WF2) as (E1 & E2 & E3 & E4 & E5 & _).
      unfold kSpaceSize in *. clear -SP E2 E3 E4 E5 CR. rewrite kHighMemBeg_val in E2. lia.
    - destruct (in_some_sec_map a1 (8 * g)) eqn:SM.
      + unfold in_some_sec_map in SM. apply existsb_exists in SM as (sc & Hsc & Hb0). apply andb_true_iff in Hb0 as [B1 B2].
        apply Z.leb_le in B1. apply Z.ltb_lt in B2. pose proof WF2 as (_ & _ & _ & _ & _ & (_ & _ & S3 & _) & _). destruct (S3 sc Hsc) as (_ & HB & S & _).
        unfold app_mem in HB. rewrite kHighMemBeg_val, kLowAppEnd_val in HB. clear -B1 B2 HB S CR. lia.
      + cbn [orb] in Hg. destruct (sh_default_dom E (8 * g) && negb (sh_excluded E (8 * g))) eqn:C; [|discriminate].
        apply andb_true_iff in C as [C _]. unfold sh_default_dom in C. apply Bool.orb_true_iff in C as [C|C].
        * apply andb_true_iff in C as [C _]. apply andb_true_iff in C as [C1 C2]. apply Z.leb_le in C1. apply Z.ltb_lt in C2.
          rewrite kLowAppEnd_val in C2. clear -C1 C2. lia.
        * apply andb_true_iff in C as [C1 C2]. apply Z.leb_le in C1. apply Z.leb_le in C2.
          rewrite kHighMemBeg_val in C1. unfold kHighMemEnd in C2. clear -C1 C2. lia. }
  rewrite kLowAppEnd_val, kHighMemBeg_val; unfold kShadowBase; clear -GR; lia.
Qed.

(* [comment removed for export] *)
Lemma thr_ranges_in_page : forall x, in_ranges (arep_thr_ranges E) x -> T <= x < T + 4096.
Proof.
  intros x (r & Hr & R). unfold arep_thr_ranges in Hr.
  unfold kThrStackTop, kThrQCache, kThrCache, kPerClassSize, kNumClasses, kThrCacheStats, kThrStats, kThrUnwinding in Hr.
  repeat (destruct Hr as [<-|Hr]; [cbn [fst snd] in R; clear -R; lia|]). destruct Hr.
Qed.

(* [comment removed for export] *)
Lemma newblk_fp_free_prim : from_primary n = true -> avail E [] a1 (malloc_class n) ab ->
  forall x, ab <= x < ab + class_size (malloc_class n) -> ~ arep_fp E (DepotFP E) a1 x.
Proof.
  intros PR AV x Hx FP. set (c := malloc_class n) in *.
  assert (N64 : 0 <= n <= 64512) by (pose proof (proj1 (from_primary_iff n ltac:(clear -Hn; lia)) PR); clear -H Hn; lia).
  pose proof (malloc_class_ok n N64) as [HCc _]. fold c in HCc. pose proof (class_size_mod c HCc) as [_ CSZ].
  destruct AV as (CV & NF & NCa & NCB & NBT).
  pose proof WF1 as (WE & WR & WC & WK & WQ & WS & WD). pose proof WS as (WS1 & WS2 & WS3 & WS4 & WS5).
  pose proof WE as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & E20 &
                    E21 & E22 & E23 & E24 & E25 & E26 & E27 & E28 & E29 & E30 & E31 & _).
  pose proof (carved_in_space E a1 c ab HCc WR CV) as [SP1 SP2].
  pose proof CV as (k & Hk & Hab & Hk1). unfold region_of in Hk1. unfold region_beg in Hab.
  destruct (proj2 WR c HCc) as (RG1 & RG2 & RG3 & _). cbv zeta in RG1, RG2, RG3. unfold region_of in RG1, RG3.
  rewrite kHighMemBeg_val in E2. unfold kSpaceSize, kRegionSize, kFreeArrayOffset in *.
  assert (BLK : SB + c * 2^32 <= ab /\ ab + class_size c <= SB + c * 2^32 + 3758096384) by (rewrite Hab; clear -Hk Hk1 RG1 RG3 CSZ; nia).
  destruct FP as [X|[X|[X|[X|[X|[X|[X|[X|[X|X]]]]]]]]].
  - (* [comment removed for export] *) destruct X as (r & Hr & R). pose proof (IMG_IN r ltac:(apply in_app_iff; left; exact Hr)) as [_ I2]. rewrite kLowAppEnd_val in E31.
    clear -R I2 E31 E2 E3 SP1 Hx. lia.
  - (* [comment removed for export] *) unfold ae_region_info, kRegSize, kNumClasses, kSpaceSize in X. clear -X SP2 Hx. lia.
  - (* [comment removed for export] *) pose proof (thr_ranges_in_page x X) as R. clear -R E19 E3 E4 SP1 SP2 Hx. lia.
  - (* [comment removed for export] *) destruct X as (c' & Hc' & R). pose proof (RG_any E [] [] a1 WF1 c' ltac:(unfold kNumClasses in Hc'; clear -Hc'; lia)) as [_ [G3 G4]].
    unfold free_array, region_beg, kRegionSize, kFreeArrayOffset, kFreeArraySize, kNumClasses in *.
    clear -R G3 G4 BLK Hx Hc' HCc. unfold kLargestClassID in HCc. destruct (Z_lt_le_dec c' c); nia.
  - (* [comment removed for export] *) unfold kChunksBlockCount in X. clear -X E20 E3 E4 SP1 SP2 Hx. lia.
  - (* [comment removed for export] *) destruct X as (sc & Hsc & R). destruct (WS3 sc Hsc) as (_ & _ & _ & POS & MODS & SSP & _).
    pose proof (pos_mod_ge E (sc_map_size sc) kPageSize POS MODS ltac:(unfold kPageSize; lia)) as GE. unfold kPageSize, kSpaceSize in *.
    clear -R SSP GE SP1 SP2 Hx. lia.
  - (* [comment removed for export] *) destruct X as (cb & cm & Hcm & R).
    pose proof (chunk_meta_in_block E [] [] a1 cb cm x WF1 Hcm R) as [BI _].
    destruct (block_where E [] [] a1 cb cm WF1 Hcm) as [(J1 & J2 & c'' & Hc'' & _ & CV'' & _ & _ & SPAN)|(sc & Hsc & _ & L1 & L2)].
    + destruct (carved_blocks_disjoint E a1 c ab c'' (blk_lo cm) HCc Hc'' WR CV CV'') as [[_ EQ]|D].
      * apply NCB. exists cb, cm. split; [exact Hcm| unfold blk_lo in EQ; symmetry; exact EQ].
      * clear -D BI SPAN Hx. lia.
    + destruct (WS3 sc Hsc) as (_ & _ & _ & POS & MODS & SSP & _). unfold kPageSize, kSpaceSize in *. clear -BI L1 L2 SSP SP1 SP2 Hx. lia.
  - (* [comment removed for export] *) destruct X as (b & Hb & R).
    destruct (batch_block E [] a1 b WQ ltac:(unfold all_batches; rewrite app_nil_r; exact Hb)) as (CVb & _).
    assert (HB24 : 1 <= kBatchClass <= kLargestClassID) by (unfold kBatchClass, kLargestClassID; clear; lia).
    destruct (carved_blocks_disjoint E a1 c ab kBatchClass (b_addr b) HCc HB24 WR CV CVb) as [[_ EQ]|D].
    + apply NBT. exists b. split; [unfold all_batches; rewrite app_nil_r; exact Hb| symmetry; exact EQ].
    + change (class_size kBatchClass) with 8192 in D. unfold kBatchCap in R. clear -D R Hx. lia.
  - (* [comment removed for export] *) destruct (DepotFP_where E a1 x X) as [(r & Hr & R)|[(b & Hb & R)|(b & Hb & R)]].
    + pose proof (IMG_IN r ltac:(apply in_app_iff; right; exact Hr)) as [_ I2]. rewrite kLowAppEnd_val in E31. clear -R I2 E31 E2 E3 SP1 Hx. lia.
    + destruct (BS1 b kDepotNodeBlockBytes (or_introl (conj Hb eq_refl))) as (_ & _ & BR & _). clear -R BR E3 E4 SP1 SP2 Hx. lia.
    + destruct (BS1 b kStoreBlockBytes (or_intror (conj Hb eq_refl))) as (_ & _ & BR & _). clear -R BR E3 E4 SP1 SP2 Hx. lia.
  - (* [comment removed for export] *) destruct X as (g & v & -> & Hg). pose proof (sh_cell_band g v Hg) as B. rewrite kHighMemBeg_val in B. clear -B E2 E3 SP1 Hx. lia.
Qed.

(* [comment removed for export] *)
Lemma newblk_fp_free_sec : forall r0, from_primary n = false -> ab = r0 + kPageSize ->
  as_sec a1 = as_sec a ++ [mkSec r0 (map_size n) (needed n)] -> sec_fresh E a r0 (map_size n) ->
  forall x, ab <= x < ab + round_up (needed n) kPageSize -> ~ arep_fp E (DepotFP E) a1 x.
Proof.
  intros r0 PR Eab SEC FR x Hx FP.
  set (msz := map_size n) in *. assert (MSZ : msz = round_up (needed n) kPageSize + kPageSize) by reflexivity.
  assert (XM : r0 + 4096 <= x < r0 + msz) by (rewrite MSZ; unfold kPageSize in *; clear -Hx Eab; lia).
  destruct FR as (R4K & AM & CE & SPC & SECS & RSV).
  pose proof WF1 as (WE & WR & WC & WK & WQ & WS & WD). pose proof WS as (WS1 & WS2 & WS3 & WS4 & WS5).
  pose proof WE as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & E20 &
                    E21 & E22 & E23 & E24 & E25 & E26 & E27 & E28 & E29 & E30 & E31 & _).
  pose proof (RSV _ E7) as XR. pose proof (RSV _ E13) as XT. pose proof (RSV _ E8) as XP. pose proof (RSV _ E29) as XI. cbn [fst snd] in XR, XT, XP.
  unfold kSpaceSize in *.
  destruct FP as [X|[X|[X|[X|[X|[X|[X|[X|[X|X]]]]]]]]].
  - (* [comment removed for export] *) destruct X as (r & Hr & R). pose proof (IMG_IN r ltac:(apply in_app_iff; left; exact Hr)) as [I1 I2].
    destruct (ae_img E); cbn [fst snd] in *. clear -R I1 I2 XI XM. lia.
  - (* [comment removed for export] *) unfold ae_region_info, kRegSize, kNumClasses, kSpaceSize in X. clear -X XR E3 E4 XM. lia.
  - (* [comment removed for export] *) pose proof (thr_ranges_in_page x X) as R. clear -R XT XM. lia.
  - (* [comment removed for export] *) destruct X as (c' & Hc' & R). pose proof (RG_any E [] [] a1 WF1 c' ltac:(unfold kNumClasses in Hc'; clear -Hc'; lia)) as [_ [G3 G4]].
    unfold free_array, region_beg, kRegionSize, kFreeArrayOffset, kFreeArraySize, kNumClasses in *. clear -R G3 G4 Hc' SPC XM. nia.
  - (* [comment removed for export] *) unfold kChunksBlockCount in X. clear -X XP XM. lia.
  - (* [comment removed for export] *) destruct X as (sc & Hsc & R). rewrite SEC in Hsc. apply in_app_iff in Hsc. destruct Hsc as [Hsc|[<-|[]]].
    + pose proof (SECS sc Hsc) as D. pose proof WF0 as (_ & _ & _ & _ & _ & (_ & _ & S3 & _) & _). destruct (S3 sc Hsc) as (_ & _ & _ & POS & MODS & _).
      pose proof (pos_mod_ge E (sc_map_size sc) kPageSize POS MODS ltac:(unfold kPageSize; lia)) as GE. unfold kPageSize in GE. clear -R D GE XM. lia.
    + cbn [sc_map_beg] in R. clear -R XM. lia.
  - (* [comment removed for export] *) destruct X as (cb & cm & Hcm & R). rewrite CH in Hcm.
    pose proof (chunk_meta_in_block E [] [] a cb cm x WF0 Hcm R) as [BI _].

    destruct (block_where E [] [] a cb cm WF0 Hcm) as [(J1 & J2 & _)|(sc & Hsc & _ & L1 & L2)].
    + unfold kSpaceSize in J2. clear -BI J1 J2 SPC XM. lia.
    + pose proof (SECS sc Hsc) as D. unfold kPageSize in L1. clear -BI L1 L2 D XM. lia.
  - (* [comment removed for export] *) destruct X as (b & Hb & R).
    destruct (batch_block E [] a1 b WQ ltac:(unfold all_batches; rewrite app_nil_r; exact Hb)) as (CVb & _).
    assert (HB24 : 1 <= kBatchClass <= kLargestClassID) by (unfold kBatchClass, kLargestClassID; clear; lia).
    pose proof (carved_in_space E a1 kBatchClass _ HB24 WR CVb) as [J1 J2]. change (class_size kBatchClass) with 8192 in J2.
    unfold kBatchCap, kSpaceSize, kRegionSize in *. clear -R J1 J2 SPC XM. lia.
  - (* [comment removed for export] *) destruct (DepotFP_where E a1 x X) as [(r & Hr & R)|[(b & Hb & R)|(b & Hb & R)]].
    + pose proof (IMG_IN r ltac:(apply in_app_iff; right; exact Hr)) as [I1 I2]. destruct (ae_img E); cbn [fst snd] in *. clear -R I1 I2 XI XM. lia.
    + destruct (BS1 b kDepotNodeBlockBytes (or_introl (conj Hb eq_refl))) as (_ & _ & _ & BSC & _).
      pose proof (BSC (mkSec r0 msz (needed n)) ltac:(rewrite SEC; apply in_app_iff; right; left; reflexivity)) as D. cbn [sc_map_beg sc_map_size] in D.
      clear -R D XM. lia.
    + destruct (BS1 b kStoreBlockBytes (or_intror (conj Hb eq_refl))) as (_ & _ & _ & BSC & _).
      pose proof (BSC (mkSec r0 msz (needed n)) ltac:(rewrite SEC; apply in_app_iff; right; left; reflexivity)) as D. cbn [sc_map_beg sc_map_size] in D.
      clear -R D XM. lia.
  - (* [comment removed for export] *) destruct X as (g & v & -> & Hg). pose proof (sh_cell_band g v Hg) as B. unfold app_mem in AM. clear -B AM XM. lia.
Qed.

(* [comment removed for export] *)
Theorem newblk_fp_free :
  (if from_primary n
   then as_cache_inited a1 = true /\ avail E [] a1 (malloc_class n) ab
        /\ exists x, ab = chunk_of_compact SB (malloc_class n) x /\ (16 * x) mod class_size (malloc_class n) = 0
   else exists r0, ab = r0 + kPageSize /\ as_sec a1 = as_sec a ++ [mkSec r0 (map_size n) (needed n)] /\ sec_fresh E a r0 (map_size n)) ->
  forall x, ab <= x < ab + (if from_primary n then class_size (malloc_class n) else round_up (needed n) kPageSize) -> ~ arep_fp E (DepotFP E) a1 x.
Proof.
  destruct (from_primary n) eqn:PR.
  - intros (_ & AV & _). exact (newblk_fp_free_prim PR AV).
  - intros (r0 & Eab & SEC & FR). exact (newblk_fp_free_sec r0 PR Eab SEC FR).
Qed.
End NB.
End RC__1.
