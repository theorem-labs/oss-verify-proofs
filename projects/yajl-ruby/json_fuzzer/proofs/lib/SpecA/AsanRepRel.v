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
  AsanWf1 AsanWf3 AsanWf4 AsanWf5 AsanClient AsanRepFrame AsanRepFrame2 AsanBudget AsanHit AsanRepHit AsanRepX AsanRepCa AsanRepSec AsanRepEnq AsanRepFlip.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section RRL.
Variable segs : list Segment.
Variable E : aenv.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).
#[warnings="-notation-for-abbreviation"] Notation RW := (rw_cells segs).
#[warnings="-notation-for-abbreviation"] Notation SB := (ae_space_beg E).
#[warnings="-notation-for-abbreviation"] Notation T := (ae_thread E).
#[warnings="-notation-for-abbreviation"] Notation RI := (ae_region_info E).
#[warnings="-notation-for-abbreviation"] Notation PA := (ae_ptr_array E).
#[warnings="-notation-for-abbreviation"] Notation AREP := (ARep segs E (DepotR segs E)).

(* [comment removed for export] *)
Definition rel_st (cb n : Z) (a : astate) : astate :=
  upd_dead (fun d => <[cb := n]> d) (upd_chunks (delete cb) (upd_ts (ts_on_real_free n) a)).

Section REL.
Variables (D : list batch) (s : astate) (m m' : mem) (lo cb : Z) (cm : chunkmeta) (qi qj g : Z).
#[warnings="-notation-for-abbreviation"] Notation n := (cm_n cm).
#[warnings="-notation-for-abbreviation"] Notation ab := (cm_alloc_beg cm).
#[warnings="-notation-for-abbreviation"] Notation ub := (cm_user_beg cm).
#[warnings="-notation-for-abbreviation"] Notation l8 := ((cm_n cm + 7) / 8).
#[warnings="-notation-for-abbreviation"] Notation s' := (rel_st cb (cm_n cm) s).

(* [comment removed for export] *)
Definition FPWrel (z : Z) : Prop :=
     lo <= z \/ (cb <= z < cb + 4) \/ (ab <= z < ab + 8)
  \/ (kShadowBase + g <= z < kShadowBase + g + l8)
  \/ (T + kThrStats + 40 <= z < T + kThrStats + 56).

Hypothesis Hcm : as_chunks s !! cb = Some cm.
Hypothesis ST : cm_state cm = CQuarantined qi qj.
Hypothesis G8 : 8 * g = cb + 16.
Hypothesis REP : AREP s m.
Hypothesis WF : AWf E [] D s.
Hypothesis RENV : renv_ok E s.
Hypothesis WM : wmono segs m m'.
Hypothesis AG : forall z, 0 <= z < 2^64 -> ~ FPWrel z -> m' (wa z) = m (wa z).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis NC_sh : RW m' (kShadowBase + g) [CB (Z.to_nat l8) (repeat (zb kAsanHeapLeftRedzoneMagic) (Z.to_nat l8))].
Hypothesis NC_st : RW m' (T + kThrStats + 40) [C8 (zw (ts_real_frees (as_ts s) + 1)); C8 (zw (ts_really_freed (as_ts s) + n))].

Let BS : blocks_sep E s. Proof. exact (proj1 RENV). Qed.
Let Tpl : (0x1000 <= T /\ (T + 4096 <= 0x10000 \/ 0x603000 <= T)) /\ T + 4096 <= alloc_ceiling. Proof. exact (proj1 (proj2 RENV)). Qed.
Let IMG_IN : forall r, In r (arep_img_ranges E ++ depot_static E) -> fst (ae_img E) <= fst r /\ fst r + snd r <= fst (ae_img E) + snd (ae_img E).
Proof. exact (proj1 (proj2 (proj2 RENV))). Qed.
Let IMG_LO : 0x10000 <= fst (ae_img E). Proof. exact (proj1 (proj2 (proj2 (proj2 RENV)))). Qed.
Let IMG_LOW : forall r, In r (arep_img_ranges E ++ depot_static E) -> 0x10000 <= fst r /\ fst r + snd r <= 0x603000.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 RENV))))). Qed.
Let AK : exists mo, AKern E s mo. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 RENV))))))). Qed.
Let TDN : T + 4096 <= ae_depot_nodes E \/ ae_depot_nodes E + kDepotNodeBlockBytes <= T.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 RENV)))))))). Qed.

(* [comment removed for export] *)
Lemma rl_chunks : as_chunks s' = delete cb (as_chunks s). Proof. destruct s; reflexivity. Qed.
Lemma rl_lookup : forall cb0, as_chunks s' !! cb0 = if decide (cb0 = cb) then None else as_chunks s !! cb0.
Proof. intros cb0. rewrite rl_chunks. destruct (decide (cb0 = cb)) as [->|NE]; [apply lookup_delete_eq| rewrite lookup_delete_ne by congruence; reflexivity]. Qed.
Lemma rl_regions : as_regions s' = as_regions s. Proof. destruct s; reflexivity. Qed.
Lemma rl_sec : as_sec s' = as_sec s. Proof. destruct s; reflexivity. Qed.
Lemma rl_tq : as_tq s' = as_tq s. Proof. destruct s; reflexivity. Qed.
Lemma rl_gq : as_gq s' = as_gq s. Proof. destruct s; reflexivity. Qed.
Lemma rl_ts : as_ts s' = ts_on_real_free n (as_ts s). Proof. destruct s; reflexivity. Qed.

(* [comment removed for export] *)
Lemma geo : blk_lo cm + 16 <= ub /\ ub + n <= blk_hi s cm /\ cb = ub - 16 /\ ub mod 16 = 0 /\ 1 <= n < 2^40
  /\ 8 * l8 = round_up n 8 /\ n <= round_up n 8 < n + 8 /\ g = ub / 8 /\ blk_lo cm = ab.
Proof.
  pose proof (chunk_user_in_block E [] D s cb cm WF Hcm) as (A & B & C). pose proof (chunk_user_aligned E [] D s cb cm WF Hcm) as D0.
  unfold user_lo, user_hi, kChunkHeaderSize in *. pose proof WF as (_ & _ & _ & [K1 _] & _). destruct (K1 _ _ Hcm) as (_ & N & _).
  unfold blk_lo. repeat split; try assumption; try lia; unfold round_up; clear -N C D0 G8; Z.div_mod_to_equations; lia.
Qed.
Lemma geo2 : ub + round_up n 8 <= blk_hi s cm /\ ub + 8 <= blk_hi s cm.
Proof.
  pose proof WF as (WE & WR & WC & [K1 _] & _). destruct (K1 _ _ Hcm) as (A & B & C & D0 & _).
  unfold blk_hi, cm_chunk_beg, cm_user_beg in *. rewrite C in *.
  change (16 * 2 ^ rz_log (cm_n cm)) with (rz_size (cm_n cm)) in *.
  pose proof (rz_size_pos (cm_n cm)) as RP. pose proof (rounded_ge (cm_n cm)) as (RG1 & RG2 & RG3).
  assert (RU : round_up (cm_n cm) 8 <= rounded (cm_n cm) /\ 8 <= rounded (cm_n cm)) by (unfold round_up; clear -RG1 RG3 B; Z.div_mod_to_equations; lia).
  destruct (cm_prim cm) as [c|].
  - destruct D0 as (D1 & D2 & _). pose proof (proj1 (from_primary_iff (cm_n cm) ltac:(lia)) D1) as LE.
    pose proof (malloc_class_ok (cm_n cm) ltac:(lia)) as [_ NE]. rewrite <- D2 in NE. unfold needed1 in NE. clear -NE RU RP. lia.
  - destruct D0 as (D1 & _). pose proof (map_size_facts (cm_n cm)) as (_ & MG & _). unfold needed in MG. rewrite D1 in MG. unfold needed1 in MG. unfold kPageSize in *.
    clear -MG RU RP. lia.
Qed.

(* [comment removed for export] *)
Lemma blk_where : (ae_resv_beg E <= blk_lo cm /\ blk_hi s cm <= ae_resv_beg E + 0x2000011000
                    /\ exists c, 1 <= c <= kLargestClassID /\ cm_prim cm = Some c /\ carved E s c (blk_lo cm) /\ blk_hi s cm = blk_lo cm + class_size c)
                  \/ (exists sc, In sc (as_sec s) /\ blk_lo cm = sc_map_beg sc + kPageSize /\ blk_hi s cm = sc_map_beg sc + sc_map_size sc).
Proof.
  pose proof (proj1 WF) as (E1 & E2 & E3 & E4 & _).
  destruct (block_where E [] D s cb cm WF Hcm) as [(J1 & J2 & c & Hc & PR & CV & _ & _ & SP)|(sc & Hsc & _ & L1 & L2)]; [left| right].
  - split; [| split; [| exists c; auto]]; unfold kSpaceSize in *; clear -J1 J2 E3 E4; lia.
  - exists sc. auto.
Qed.

Lemma blk_facts : forall a, blk_lo cm <= a < blk_hi s cm ->
  0 <= a < alloc_ceiling /\ ~ (kLowAppEnd <= a < kHighMemBeg) /\ ~ (T <= a < T + 4096)
  /\ (forall x, In x (arep_img_ranges E ++ depot_static E) -> ~ (fst x <= a < fst x + snd x))
  /\ ~ (PA <= a < PA + 0x800000)
  /\ (forall b len, (In b (ae_depot_nodes E :: as_node_blocks s) /\ len = kDepotNodeBlockBytes) \/ (In b (ae_store_blk E :: as_store_blocks s) /\ len = kStoreBlockBytes) ->
        ~ (b <= a < b + len)).
Proof.
  intros a Ha. pose proof (proj1 WF) as WE. pose proof alloc_ceiling_range as CR. destruct AK as [mo2 K2].
  pose proof WE as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & E28 & E29 & _).
  rewrite kHighMemBeg_val in E2. rewrite kLowAppEnd_val, kHighMemBeg_val.
  pose proof (BS (ae_depot_nodes E) kDepotNodeBlockBytes (or_introl (conj (or_introl eq_refl) eq_refl))) as (_ & _ & DNR & DNS & _).
  pose proof (ak_store_sep _ _ _ K2) as (SBR & SBS & _).
  destruct blk_where as [(R1 & R2 & _)|(sc & Hsc & L1 & L2)].
  - (* [comment removed for export] *)
    split; [clear -Ha R1 R2 E2 E5; lia|]. split; [clear -Ha R1 E2; lia|]. split; [clear -Ha R1 R2 E19; lia|]. split.
    { intros x Hx R. pose proof (IMG_LOW x Hx) as [L1 L2]. clear -Ha R1 E2 R L2. lia. }
    split; [clear -Ha R1 R2 E20; lia|].
    intros b len [[[<-|Hb] ->]|[[<-|Hb] ->]].
    + clear -Ha R1 R2 DNR. lia.
    + destruct (ak_blocks_sep _ _ _ K2 b kDepotNodeBlockBytes (or_introl (conj Hb eq_refl))) as (_ & _ & _ & BR & _). unfold kResvLen in BR. clear -Ha R1 R2 BR. lia.
    + unfold kResvLen, kStoreBlockBytes in *. clear -Ha R1 R2 SBR. lia.
    + destruct (ak_blocks_sep _ _ _ K2 b kStoreBlockBytes (or_intror (conj Hb eq_refl))) as (_ & _ & _ & BR & _). unfold kResvLen, kStoreBlockBytes in *. clear -Ha R1 R2 BR. lia.
  - (* [comment removed for export] *)
    pose proof WF as (_ & _ & _ & _ & _ & (_ & _ & S3 & _) & _). destruct (S3 sc Hsc) as (_ & AM & CE & POS & _ & _ & SR). unfold app_mem in AM. rewrite kHighMemBeg_val, kLowAppEnd_val in AM.
    unfold kPageSize in L1.
    split; [clear -Ha L1 L2 AM CE; lia|]. split; [clear -Ha L1 L2 AM; lia|]. split.
    { pose proof (SR _ E13) as X. cbn [fst snd] in X. clear -Ha L1 L2 X. lia. }
    split.
    { intros x Hx R. pose proof (IMG_IN x Hx) as [I1 I2]. pose proof (SR _ E29) as X. destruct (ae_img E); cbn [fst snd] in *. clear -Ha L1 L2 X I1 I2 R. lia. }
    split; [pose proof (SR _ E8) as X; cbn [fst snd] in X; clear -Ha L1 L2 X; lia|].
    intros b len [[[<-|Hb] ->]|[[<-|Hb] ->]].
    + destruct (DNS sc Hsc); clear -Ha L1 L2 H; lia.
    + destruct (ak_blocks_sep _ _ _ K2 b kDepotNodeBlockBytes (or_introl (conj Hb eq_refl))) as (_ & _ & _ & _ & BSC & _). destruct (BSC sc Hsc); clear -Ha L1 L2 H; lia.
    + destruct (SBS sc Hsc); unfold kStoreBlockBytes; clear -Ha L1 L2 H; lia.
    + destruct (ak_blocks_sep _ _ _ K2 b kStoreBlockBytes (or_intror (conj Hb eq_refl))) as (_ & _ & _ & _ & BSC & _). destruct (BSC sc Hsc); clear -Ha L1 L2 H; lia.
Qed.

(* [comment removed for export] *)
Lemma blk_vs_chunk : forall cb' cm' a, as_chunks s !! cb' = Some cm' -> cb' <> cb -> chunk_meta_fp cm' a -> ~ (blk_lo cm <= a < blk_hi s cm).
Proof.
  intros cb' cm' a H' NE FPa R. pose proof (chunk_meta_in_block E [] D s cb' cm' a WF H' FPa) as [B1 B2].
  destruct (chunks_disjoint E [] D s cb' cm' cb cm WF H' Hcm NE); clear -B1 B2 R H; lia.
Qed.
Lemma blk_vs_batch : forall b a, In b (as_tq s ++ as_gq s) -> b_addr b <= a < b_addr b + 24 + 8 * kBatchCap -> ~ (blk_lo cm <= a < blk_hi s cm).
Proof.
  intros b a Hb Ha R. pose proof WF as (WE & WR & _ & _ & WQ & _).
  destruct (batch_block E D s b WQ ltac:(unfold all_batches; rewrite app_assoc; apply in_app_iff; left; exact Hb)) as (CV & _ & _ & NCB).
  assert (CS : class_size kBatchClass = 8192) by reflexivity. assert (HB24 : 1 <= kBatchClass <= kLargestClassID) by (unfold kBatchClass, kLargestClassID; lia).
  destruct blk_where as [(R1 & R2 & c & Hc & PR & CVc & SP)|(sc & Hsc & L1 & L2)].
  - destruct (carved_blocks_disjoint E s c (blk_lo cm) kBatchClass (b_addr b) Hc HB24 WR CVc CV) as [[_ EQ]|DJ].
    + apply NCB. exists cb, cm. split; [exact Hcm| exact EQ].
    + unfold kBatchCap in Ha. clear -Ha R DJ SP CS. lia.
  - pose proof (carved_in_space E s kBatchClass _ HB24 WR CV) as [I1 I2].
    pose proof WF as (_ & _ & _ & _ & _ & (_ & _ & S3 & _) & _). destruct (S3 sc Hsc) as (_ & _ & _ & _ & _ & SP & _).
    unfold kBatchCap, kPageSize, kRegionSize, kSpaceSize in *. clear -Ha R L1 L2 I1 I2 SP CS. lia.
Qed.

Lemma carved_below : forall c' a0, 1 <= c' <= kLargestClassID -> carved E s c' a0 ->
  region_beg SB c' <= a0 /\ a0 + class_size c' <= region_beg SB c' + rg_alloc_user (region_of s c').
Proof.
  intros c' a0 Hc' (k & K0 & KE & KB). pose proof (class_size_mod c' Hc') as [_ CS]. unfold region_of in KB. unfold region_of.
  rewrite KE. clear -K0 KB CS. split; nia.
Qed.

(* [comment removed for export] *)
Lemma blk_vs_fa_ri : forall a, blk_lo cm <= a < blk_hi s cm ->
  ~ (RI <= a < RI + kRegSize * kNumClasses) /\ forall c', 0 <= c' < kNumClasses -> ~ (free_array SB c' <= a < free_array SB c' + rg_mapped_fa (region_of s c')).
Proof.
  intros a Ha. pose proof WF as (WE & [WR0 WR] & _). pose proof (proj1 WF) as (E1 & E2 & E3 & E4 & _).
  assert (FAB : forall c', 0 <= c' < kNumClasses -> 0 <= rg_mapped_fa (region_of s c') <= kFreeArraySize).
  { intros c' Hc'. destruct (Z_le_dec 1 c'); [destruct (Z_le_dec c' kLargestClassID)|].
    - destruct (WR c' ltac:(lia)) as (_ & _ & _ & _ & A5 & _ & A7 & _). cbv zeta in A5, A7. split; assumption.
    - unfold region_of, get_region. destruct (as_regions s !! c') as [r|] eqn:Hr; [pose proof (WR0 c' r Hr); unfold kNumClasses in *; lia|]. cbn. unfold kFreeArraySize; lia.
    - unfold region_of, get_region. destruct (as_regions s !! c') as [r|] eqn:Hr; [pose proof (WR0 c' r Hr); lia|]. cbn. unfold kFreeArraySize; lia. }
  destruct blk_where as [(R1 & R2 & c & Hc & PR & CV & SP)|(sc & Hsc & L1 & L2)].
  - pose proof (carved_below c (blk_lo cm) Hc CV) as [C1 C2].
    destruct (WR c Hc) as (W1 & _ & W3 & _). cbv zeta in W1, W3.
    unfold ae_region_info, free_array, region_beg, kRegionSize, kFreeArrayOffset, kFreeArraySize, kRegSize, kNumClasses, kSpaceSize, kLargestClassID in *.
    split; [clear -Ha C1 C2 W1 W3 SP Hc; nia|].
    intros c' Hc' X. pose proof (FAB c' Hc') as [F1 F2].
    destruct (Z.lt_trichotomy c' c) as [LT|[->|GT]]; [clear -Ha C1 C2 W1 W3 SP Hc Hc' X F1 F2 LT| clear -Ha C1 C2 W1 W3 SP Hc X F1 F2| clear -Ha C1 C2 W1 W3 SP Hc Hc' X F1 F2 GT]; nia.
  - pose proof WF as (_ & _ & _ & _ & _ & (_ & _ & S3 & _) & _). destruct (S3 sc Hsc) as (_ & _ & _ & _ & _ & SPc & _). unfold kPageSize in L1.
    unfold ae_region_info, free_array, region_beg, kRegionSize, kFreeArrayOffset, kFreeArraySize, kRegSize, kNumClasses, kSpaceSize in *.
    split; [clear -Ha L1 L2 SPc; lia|]. intros c' Hc' X. pose proof (FAB c' Hc') as [F1 F2]. clear -Ha L1 L2 SPc Hc' X F1 F2. nia.
Qed.

(* [comment removed for export] *)
Lemma shw_band : forall z, kShadowBase + g <= z < kShadowBase + g + l8 -> kLowAppEnd < z < kHighMemBeg.
Proof.
  intros z Hz. pose proof geo as (G1 & G2 & _ & _ & G5 & G6 & G7 & G9 & _). pose proof (blk_facts ub ltac:(clear -G1 G2 G5; lia)) as (B1 & _).
  pose proof (blk_facts (ub + n - 1) ltac:(clear -G1 G2 G5; lia)) as (B2 & _). pose proof alloc_ceiling_range as CR.
  rewrite kLowAppEnd_val, kHighMemBeg_val. unfold kShadowBase in Hz. rewrite G9 in Hz. clear -Hz B1 B2 G5 G6 G7 CR. Z.div_mod_to_equations. lia.
Qed.
Lemma cb_in_blk : forall a, (cb <= a < cb + 4) \/ (ab <= a < ab + 8) -> blk_lo cm <= a < blk_hi s cm.
Proof. intros a Ha. pose proof geo as (G1 & G2 & G3 & _ & _ & _ & _ & _ & G10). pose proof geo2 as [_ G7]. clear -Ha G1 G3 G7 G10. lia. Qed.

(* [comment removed for export] *)
Lemma AG_fp : forall a, arep_fp E (DepotFP E) s a -> ~ (T <= a < T + 4096) -> ~ (blk_lo cm <= a < blk_hi s cm) -> ~ (kLowAppEnd < a < kHighMemBeg) -> m' (wa a) = m (wa a).
Proof.
  intros a Ha NT NB NBD. pose proof (fp_range E s WF BS IMG_IN IMG_LO a Ha) as BC || pose proof I as BC.
  assert (BC' : 0 <= a < alloc_ceiling).
  { split; [| exact (fp_below_ceiling E (DepotFP E) [] D IMG_IN (DepotFP_where E) s a WF BS Ha)].
    destruct (fp_locate E (DepotFP E) [] D IMG_IN (DepotFP_where E) s a WF BS Ha) as [X|[[X _]|[X _]]].
    - destruct X as (r0 & Hr & R). pose proof (IMG_IN r0 Hr). clear -R H IMG_LO. lia.
    - pose proof (sh_band_below_ceiling a X). rewrite kLowAppEnd_val in *. clear -H. lia.
    - unfold app_addr in X. rewrite kHighMemBeg_val in X. clear -X. lia. }
  pose proof alloc_ceiling_range as CR.
  apply AG; [clear -BC' CR; lia|]. unfold FPWrel. intros [X|[X|[X|[X|X]]]].
  - clear -X BC' LO. lia.
  - exact (NB (cb_in_blk a (or_introl X))).
  - exact (NB (cb_in_blk a (or_intror X))).
  - exact (NBD (shw_band a X)).
  - unfold kThrStats in X. clear -X NT. lia.
Qed.

Lemma AGimg : forall a, in_ranges (arep_img_ranges E) a -> m' (wa a) = m (wa a).
Proof.
  intros a (x & Hx & R). pose proof Tpl as [[T1 T2] T3].
  assert (Hx' : In x (arep_img_ranges E ++ depot_static E)) by (apply in_app_iff; left; exact Hx).
  pose proof (IMG_LOW x Hx') as [L1 L2].
  apply AG_fp; [left; exists x; split; [exact Hx| exact R]| clear -R L1 L2 T1 T2; lia| | rewrite kLowAppEnd_val; clear -R L2; lia].
  intros C. destruct (blk_facts a C) as (_ & _ & _ & NI & _). exact (NI x Hx' R).
Qed.
Lemma Tpage_apart : forall a, T <= a < T + 4096 ->
     ~ (ae_resv_beg E <= a < ae_resv_beg E + 0x2000011000)
  /\ ~ (ae_ptr_array E <= a < ae_ptr_array E + 0x800000)
  /\ (forall sc, In sc (as_sec s) -> ~ (sc_map_beg sc <= a < sc_map_beg sc + sc_map_size sc))
  /\ (forall b0 len, (In b0 (ae_depot_nodes E :: as_node_blocks s) /\ len = kDepotNodeBlockBytes) \/ (In b0 (ae_store_blk E :: as_store_blocks s) /\ len = kStoreBlockBytes) ->
        ~ (b0 <= a < b0 + len))
  /\ ~ (kLowAppEnd < a < kHighMemBeg) /\ ~ (0x10000 <= a < 0x603000).
Proof.
  intros a Ha. destruct AK as [mo K]. pose proof WF as (WE & _ & _ & _ & _ & WS & _). destruct WS as (_ & _ & S3 & _).
  pose proof WE as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & E20 & E21 & E22 & E23 & _).
  split; [clear -Ha E19; lia|]. split; [clear -Ha E23; lia|]. split.
  { intros sc Hsc. destruct (S3 sc Hsc) as (_ & _ & _ & _ & _ & _ & RSV). pose proof (RSV _ E13) as X. cbn [fst snd] in X. clear -Ha X. lia. }
  split.
  { intros b0 len H. destruct H as [[[<-|Hb0] ->]|[[<-|Hb0] ->]].
    - clear -Ha TDN. lia.
    - destruct (ak_blocks_sep _ _ _ K b0 kDepotNodeBlockBytes (or_introl (conj Hb0 eq_refl))) as (_ & _ & _ & _ & _ & R). pose proof (R _ E13) as X. cbn [fst snd] in X. clear -Ha X. lia.
    - pose proof (ak_store_sep _ _ _ K) as (_ & _ & X & _). unfold kPageSize, kStoreBlockBytes in *. clear -Ha X. lia.
    - destruct (ak_blocks_sep _ _ _ K b0 kStoreBlockBytes (or_intror (conj Hb0 eq_refl))) as (_ & _ & _ & _ & _ & R). pose proof (R _ E13) as X. cbn [fst snd] in X. clear -Ha X. lia. }
  unfold app_mem in E14. rewrite ?kLowAppEnd_val, ?kHighMemBeg_val in *. pose proof Tpl as [[T1 T2] T3]. clear -Ha E14 T1 T2 T3. split; lia.
Qed.

Lemma AG_resv : forall a, arep_fp E (DepotFP E) s a -> ae_resv_beg E <= a < ae_resv_beg E + 0x2000011000 ->
  ~ (blk_lo cm <= a < blk_hi s cm) -> m' (wa a) = m (wa a).
Proof.
  intros a Ha R NB. pose proof (proj1 WF) as (E1 & E2 & _). rewrite kHighMemBeg_val in E2.
  apply AG_fp; [exact Ha| | exact NB| rewrite kHighMemBeg_val; clear -R E2; lia].
  intros HT. destruct (Tpage_apart a HT) as (NR & _). exact (NR R).
Qed.
Lemma space_resv : forall a, SB <= a < SB + kSpaceSize + 0x1000 -> ae_resv_beg E <= a < ae_resv_beg E + 0x2000011000.
Proof. intros a Ha. pose proof (proj1 WF) as (E1 & E2 & E3 & E4 & _). clear -Ha E3 E4. lia. Qed.
Lemma AGri : forall a, RI <= a < RI + kRegSize * kNumClasses -> m' (wa a) = m (wa a).
Proof.
  intros a Ha. apply AG_resv; [right; left; exact Ha| | intros C; exact (proj1 (blk_vs_fa_ri a C) Ha)].
  apply space_resv. unfold ae_region_info, kRegSize, kNumClasses, kSpaceSize in *. clear -Ha. lia.
Qed.
Lemma AGfa : forall a c', 0 <= c' < kNumClasses -> free_array SB c' <= a < free_array SB c' + rg_mapped_fa (region_of s c') -> m' (wa a) = m (wa a).
Proof.
  intros a c' Hc Ha. apply AG_resv; [do 3 right; left; exists c'; split; [exact Hc| exact Ha]| | intros C; exact (proj2 (blk_vs_fa_ri a C) c' Hc Ha)].
  assert (RM : in_some_region_map E s a = true).
  { unfold in_some_region_map. apply Bool.orb_true_iff. right. apply existsb_exists. exists c'. split; [apply In_ziota; unfold kNumClasses in Hc; lia|].
    apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; lia. }
  pose proof (region_map_in_space E [] D s a WF RM) as SP. apply space_resv. unfold kSpaceSize in *. clear -SP. lia.
Qed.
Lemma AGbat : forall a b, In b (as_tq s ++ as_gq s) -> b_addr b <= a < b_addr b + 24 + 8 * kBatchCap -> m' (wa a) = m (wa a).
Proof.
  intros a b Hb Ha. apply AG_resv; [do 7 right; left; exists b; split; [exact Hb| exact Ha]| | exact (blk_vs_batch b a Hb Ha)].
  pose proof WF as (WE & WR & _ & _ & WQ & _).
  destruct (batch_block E D s b WQ ltac:(unfold all_batches; rewrite app_assoc; apply in_app_iff; left; exact Hb)) as (CV & _).
  assert (HB24 : 1 <= kBatchClass <= kLargestClassID) by (unfold kBatchClass, kLargestClassID; lia).
  pose proof (carved_in_space E s kBatchClass _ HB24 WR CV) as [J1 J2].
  assert (CS : class_size kBatchClass = 8192) by reflexivity.
  apply space_resv. unfold kBatchCap, kSpaceSize, kRegionSize in *. clear -Ha J1 J2 CS. lia.
Qed.
Lemma AG_secmap : forall a sc, arep_fp E (DepotFP E) s a -> In sc (as_sec s) -> sc_map_beg sc <= a < sc_map_beg sc + 32 -> m' (wa a) = m (wa a).
Proof.
  intros a sc Ha Hsc R. pose proof WF as (_ & _ & _ & _ & _ & (_ & _ & S3 & _ & S5) & _). destruct (S3 sc Hsc) as (_ & AM & _ & POS & MODS & SSP & SR).
  pose proof (AsanRepFrame.pos_mod_ge E (sc_map_size sc) kPageSize POS MODS ltac:(unfold kPageSize; lia)) as GE. unfold kPageSize in GE.
  pose proof (proj1 WF) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & _).
  apply AG_fp; [exact Ha| | | unfold app_mem in AM; clear -R AM GE; lia].
  - intros HT. destruct (Tpage_apart a HT) as (_ & _ & NS & _). apply (NS sc Hsc). clear -R GE. lia.
  - intros C. destruct blk_where as [(R1 & R2 & _)|(sc' & Hsc' & L1 & L2)].
    + pose proof (SR _ E7) as X. cbn [fst snd] in X. clear -R C R1 R2 X GE. lia.
    + (* [comment removed for export] *)
      destruct (Z.eq_dec (sc_map_beg sc') (sc_map_beg sc)) as [EQ|NE]; [unfold kPageSize in L1; clear -R C L1 GE EQ; lia|].
      destruct (S5 sc' sc Hsc' Hsc ltac:(intros X; apply NE; rewrite X; reflexivity)) as [Y|Y]; unfold kPageSize in L1; clear -R C L1 L2 Y GE; lia.
Qed.
Lemma AGsec : forall a sc, In sc (as_sec s) -> sc_map_beg sc <= a < sc_map_beg sc + 32 -> m' (wa a) = m (wa a).
Proof. intros a sc Hsc Ha. apply (AG_secmap a sc); [do 5 right; left; exists sc; split; [exact Hsc| exact Ha]| exact Hsc| exact Ha]. Qed.
Lemma AGcm : forall a cb' cm', as_chunks s !! cb' = Some cm' -> cb' <> cb -> chunk_meta_fp cm' a -> m' (wa a) = m (wa a).
Proof.
  intros a cb' cm' Hcm' NE Ha.
  pose proof (chunk_meta_in_block E [] D s cb' cm' a WF Hcm' Ha) as [BL BU].
  destruct (block_where E [] D s cb' cm' WF Hcm') as [(J1 & J2 & _)|(sc & Hsc & _ & L1 & L2)].
  - apply AG_resv; [do 6 right; left; exists cb', cm'; split; [exact Hcm'| exact Ha]| | exact (blk_vs_chunk cb' cm' a Hcm' NE Ha)].
    apply space_resv. clear -BL BU J1 J2. lia.
  - pose proof WF as (_ & _ & _ & _ & _ & (_ & _ & S3 & _) & _). destruct (S3 sc Hsc) as (_ & AM & _ & POS & MODS & SSP & SR).
    pose proof (proj1 WF) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & _).
    apply AG_fp; [do 6 right; left; exists cb', cm'; split; [exact Hcm'| exact Ha]| | exact (blk_vs_chunk cb' cm' a Hcm' NE Ha)| unfold app_mem, kPageSize in *; clear -BL BU L1 L2 AM; lia].
    intros HT. destruct (Tpage_apart a HT) as (_ & _ & NS & _). apply (NS sc Hsc). unfold kPageSize in L1. clear -BL BU L1 L2. lia.
Qed.
Lemma AGptr : forall a, PA <= a < PA + 8 * kChunksBlockCount -> m' (wa a) = m (wa a).
Proof.
  intros a Ha. unfold kChunksBlockCount in Ha.
  pose proof (proj1 WF) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & _). unfold app_mem in E16.
  apply AG_fp; [do 4 right; left; unfold kChunksBlockCount; exact Ha| | | clear -Ha E16; lia].
  - intros HT. destruct (Tpage_apart a HT) as (_ & NP & _). clear -Ha NP. lia.
  - intros C. destruct (blk_facts a C) as (_ & _ & _ & _ & NP & _). apply NP. clear -Ha. lia.
Qed.
Lemma AGdep : forall a, DepotFP E s a -> m' (wa a) = m (wa a).
Proof.
  intros a Ha. pose proof Tpl as [[T1 T2] T3]. assert (FPa : arep_fp E (DepotFP E) s a) by (do 8 right; left; exact Ha).
  destruct (DepotFP_where E s a Ha) as [(r & Hr & R)|[(b & Hb & R)|(b & Hb & R)]].
  - assert (Hr' : In r (arep_img_ranges E ++ depot_static E)) by (apply in_app_iff; right; exact Hr).
    pose proof (IMG_LOW r Hr') as [L1 L2].
    apply AG_fp; [exact FPa| clear -R L1 L2 T1 T2; lia| intros C; destruct (blk_facts a C) as (_ & _ & _ & NI & _); exact (NI r Hr' R)| rewrite kLowAppEnd_val; clear -R L2; lia].
  - pose proof (BS b kDepotNodeBlockBytes (or_introl (conj Hb eq_refl))) as (AM & _). unfold app_mem in AM.
    apply AG_fp; [exact FPa| | | clear -R AM; lia].
    + intros HT. destruct (Tpage_apart a HT) as (_ & _ & _ & NB & _). exact (NB b kDepotNodeBlockBytes (or_introl (conj Hb eq_refl)) R).
    + intros C. destruct (blk_facts a C) as (_ & _ & _ & _ & _ & NB). exact (NB b kDepotNodeBlockBytes (or_introl (conj Hb eq_refl)) R).
  - pose proof (BS b kStoreBlockBytes (or_intror (conj Hb eq_refl))) as (AM & _). unfold app_mem in AM.
    apply AG_fp; [exact FPa| | | clear -R AM; lia].
    + intros HT. destruct (Tpage_apart a HT) as (_ & _ & _ & NB & _). exact (NB b kStoreBlockBytes (or_intror (conj Hb eq_refl)) R).
    + intros C. destruct (blk_facts a C) as (_ & _ & _ & _ & _ & NB). exact (NB b kStoreBlockBytes (or_intror (conj Hb eq_refl)) R).
Qed.
(* [comment removed for export] *)
Lemma AGsh_out : forall g' v, Sh E s (8 * g') = Some v -> (8 * g' + 8 <= ub \/ ub + 8 * l8 <= 8 * g') -> m' (wa (kShadowBase + g')) = m (wa (kShadowBase + g')).
Proof.
  intros g' v Hg OUT.
  assert (GR : 0 <= 8 * g' < 2^47).
  { pose proof WF as WF0. pose proof alloc_ceiling_range as CR. unfold Sh in Hg.
    destruct (in_some_region_map E s (8 * g')) eqn:RM.
    - pose proof (region_map_in_space E [] D s (8 * g') WF0 RM) as SP. pose proof (proj1 WF0) as (E1 & E2 & E3 & E4 & E5 & _).
      unfold kSpaceSize in *. rewrite kHighMemBeg_val in E2. clear -SP E2 E3 E4 E5 CR. lia.
    - destruct (in_some_sec_map s (8 * g')) eqn:SM.
      + unfold in_some_sec_map in SM. apply existsb_exists in SM as (sc & Hsc & Hb). apply andb_true_iff in Hb as [B1 B2].
        apply Z.leb_le in B1. apply Z.ltb_lt in B2. pose proof WF0 as (_ & _ & _ & _ & _ & (_ & _ & S3 & _) & _). destruct (S3 sc Hsc) as (_ & HB & S & _).
        unfold app_mem in HB. rewrite kHighMemBeg_val, kLowAppEnd_val in HB. clear -B1 B2 HB S CR. lia.
      + cbn [orb] in Hg. destruct (sh_default_dom E (8 * g') && negb (sh_excluded E (8 * g'))) eqn:C; [|discriminate].
        apply andb_true_iff in C as [C _]. unfold sh_default_dom in C. apply Bool.orb_true_iff in C as [C|C].
        * apply andb_true_iff in C as [C _]. apply andb_true_iff in C as [C1 C2]. apply Z.leb_le in C1. apply Z.ltb_lt in C2. rewrite kLowAppEnd_val in C2. clear -C1 C2. lia.
        * apply andb_true_iff in C as [C1 C2]. apply Z.leb_le in C1. apply Z.leb_le in C2. rewrite kHighMemBeg_val in C1. unfold kHighMemEnd in C2. clear -C1 C2. lia. }
  pose proof geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G9 & G10).
  assert (BAND : 2147446784 < kShadowBase + g' < 17594333495296) by (unfold kShadowBase; clear -GR; lia).
  pose proof alloc_ceiling_range as CR.
  pose proof (proj1 WF) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & _). unfold app_mem in E14. rewrite kHighMemBeg_val, kLowAppEnd_val in E14.
  apply AG; [clear -BAND CR; lia|].
  unfold FPWrel. intros [X|[X|[X|[X|X]]]].
  - clear -X BAND CR LO. lia.
  - destruct (blk_facts _ (cb_in_blk _ (or_introl X))) as (_ & NB & _). apply NB. rewrite kLowAppEnd_val, kHighMemBeg_val. clear -BAND. lia.
  - destruct (blk_facts _ (cb_in_blk _ (or_intror X))) as (_ & NB & _). apply NB. rewrite kLowAppEnd_val, kHighMemBeg_val. clear -BAND. lia.
  - unfold kShadowBase in X. rewrite G9 in X. clear -X OUT G4 G6. Z.div_mod_to_equations. lia.
  - unfold kThrStats in X. clear -X BAND E14. lia.
Qed.
(* [comment removed for export] *)
Lemma AGthr_cells : forall A k, T <= A -> A + k <= T + 4096 -> (A + k <= T + kThrStats + 40 \/ T + kThrStats + 56 <= A) -> agree_on m m' A k.
Proof.
  intros A k H0 H1 H2 z Hz. pose proof Tpl as [[T1 T2] T3]. pose proof alloc_ceiling_range as CR.
  pose proof (proj1 WF) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & _). unfold app_mem in E14. rewrite kLowAppEnd_val, kHighMemBeg_val in E14.
  assert (HT : T <= z < T + 4096) by (clear -Hz H0 H1; lia).
  apply AG; [clear -Hz H0 H1 T1 T3 CR; lia|]. unfold FPWrel. intros [X|[X|[X|[X|X]]]].
  - clear -X HT T3 LO. lia.
  - destruct (blk_facts _ (cb_in_blk _ (or_introl X))) as (_ & _ & NT & _). exact (NT HT).
  - destruct (blk_facts _ (cb_in_blk _ (or_intror X))) as (_ & _ & NT & _). exact (NT HT).
  - pose proof (shw_band z X) as B. rewrite kLowAppEnd_val, kHighMemBeg_val in B. clear -B HT E14. lia.
  - clear -X Hz H2. lia.
Qed.
Ltac thr_ag := apply AGthr_cells; unfold kThrUnwinding, kThrCache, kThrCacheStats, kThrStats, kPerClassSize, kThrStackTop, kThrQCache, kNumClasses in *;
  cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]; try lia.

Lemma blk_hi_span : forall cm', blk_hi s cm' = cm_alloc_beg cm' + block_span cm'.
Proof. intros cm'. unfold blk_hi, block_span. destruct (cm_prim cm'); lia. Qed.

(* [comment removed for export] *)
Lemma rl_find_chunk_keep : forall cb0 cm0 a, as_chunks s !! cb0 = Some cm0 -> cb0 <> cb -> blk_lo cm0 <= a < blk_hi s cm0 -> find_chunk s' a = Some cm0.
Proof.
  intros cb0 cm0 a Hcm0 NE0 Ha. unfold find_chunk.
  assert (SPAN : forall cm', blk_hi s cm' = cm_alloc_beg cm' + block_span cm').
  { intros cm'. unfold blk_hi, block_span. destruct (cm_prim cm'); lia. }
  set (f := fun (_ : Z) (cm1 : chunkmeta) (acc : option chunkmeta) => match acc with Some _ => acc | None =>
             if (cm_alloc_beg cm1 <=? a) && (a <? cm_alloc_beg cm1 + block_span cm1) then Some cm1 else None end).
  assert (IND : forall mm, (forall k v, mm !! k = Some v -> as_chunks s !! k = Some v) ->
            (map_fold f None mm = None /\ mm !! cb0 = None) \/ map_fold f None mm = Some cm0).
  { intros mm. induction mm as [|k v mm NONE FIRST IH] using map_first_key_ind; intros SUB.
    - left. split; [apply map_fold_empty| apply lookup_empty].
    - rewrite map_fold_insert_first_key by assumption.
      assert (SUB' : forall k0 v0, mm !! k0 = Some v0 -> as_chunks s !! k0 = Some v0).
      { intros k0 v0 H. apply SUB. rewrite lookup_insert_ne; [exact H|]. intros ->. rewrite NONE in H. discriminate. }
      pose proof (SUB k v ltac:(apply lookup_insert_eq)) as Hk.
      destruct (IH SUB') as [[R NCB]|R]; rewrite R; cbn.
      + destruct ((cm_alloc_beg v <=? a) && (a <? cm_alloc_beg v + block_span v)) eqn:C.
        * right. apply andb_prop in C as [C1 C2]. apply Z.leb_le in C1. apply Z.ltb_lt in C2.
          destruct (Z.eq_dec k cb0) as [->|NE]; [rewrite Hcm0 in Hk; injection Hk as <-; reflexivity|].
          exfalso. destruct (chunks_disjoint E [] D s k v cb0 cm0 WF Hk Hcm0 NE) as [DJ|DJ]; rewrite SPAN in *; unfold blk_lo in *; lia.
        * left. split; [reflexivity|]. rewrite lookup_insert_ne; [exact NCB|]. intros ->.
          rewrite Hcm0 in Hk. injection Hk as <-. rewrite SPAN in Ha. unfold blk_lo in Ha.
          assert (C' : (cm_alloc_beg cm0 <=? a) && (a <? cm_alloc_beg cm0 + block_span cm0) = true) by (apply andb_true_intro; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
          rewrite C' in C. discriminate.
      + right. reflexivity. }
  destruct (IND (as_chunks s') ltac:(intros k v H; rewrite rl_lookup in H; destruct (decide (k = cb)); [discriminate| exact H])) as [[_ X]|X]; [| exact X].
  rewrite rl_lookup, decide_False in X by exact NE0. rewrite Hcm0 in X. discriminate.
Qed.

(* [comment removed for export] *)
Lemma Sh_rel_in : forall a, blk_lo cm <= a < blk_hi s cm -> Sh E s' a = Some kAsanHeapLeftRedzoneMagic.
Proof.
  intros a Ha. unfold Sh.
  assert (RM : in_some_region_map E s' a = in_some_region_map E s a) by (unfold in_some_region_map, region_of, get_region; rewrite rl_regions; reflexivity).
  assert (SM : in_some_sec_map s' a = in_some_sec_map s a) by (unfold in_some_sec_map; rewrite rl_sec; reflexivity).
  rewrite RM, SM.
  assert (FC : find_chunk s' a = None).
  { destruct (find_chunk s' a) as [cm0|] eqn:F; [exfalso| reflexivity].
    destruct (find_chunk_some s' a cm0 F) as (cb0 & H0 & R0). rewrite rl_lookup in H0. destruct (decide (cb0 = cb)) as [->|NE]; [discriminate|].
    destruct (chunks_disjoint E [] D s cb0 cm0 cb cm WF H0 Hcm NE) as [X|X]; rewrite blk_hi_span in X; unfold blk_lo in *; rewrite ?blk_hi_span in Ha; clear -Ha R0 X; lia. }
  rewrite FC. pose proof (chunk_block_committed E [] D s cb cm WF Hcm) as CB. unfold blk_hi in *.
  destruct (cm_prim cm) as [c|].
  - destruct CB as (Hc & L1 & L2). unfold in_some_region_map.
    rewrite (existsb_In _ (ziota 0 32) c); [reflexivity| apply In_ziota; unfold kLargestClassID in Hc; lia|].
    unfold region_of. apply andb_true_intro; split; [apply Z.leb_le| apply Z.ltb_lt]; unfold blk_lo in *; lia.
  - destruct CB as (sc & Hsc & L1 & L2). unfold in_some_sec_map.
    rewrite (existsb_In _ (as_sec s) sc Hsc); [rewrite orb_true_r; reflexivity|].
    apply andb_true_intro; split; [apply Z.leb_le| apply Z.ltb_lt]; unfold blk_lo, kPageSize in *; lia.
Qed.
Lemma Sh_rel_out : forall a, ~ (blk_lo cm <= a < blk_hi s cm) -> Sh E s' a = Sh E s a.
Proof.
  intros a Ha. unfold Sh.
  assert (RM : in_some_region_map E s' a = in_some_region_map E s a) by (unfold in_some_region_map, region_of, get_region; rewrite rl_regions; reflexivity).
  assert (SM : in_some_sec_map s' a = in_some_sec_map s a) by (unfold in_some_sec_map; rewrite rl_sec; reflexivity).
  rewrite RM, SM.
  assert (FC : find_chunk s' a = find_chunk s a).
  { destruct (find_chunk s a) as [cm0|] eqn:F0.
    - destruct (find_chunk_some s a cm0 F0) as (cb0 & H0 & R0).
      assert (NE : cb0 <> cb).
      { intros ->. rewrite Hcm in H0. injection H0 as E0. apply Ha. subst cm0. rewrite blk_hi_span. unfold blk_lo. exact R0. }
      apply (rl_find_chunk_keep cb0 cm0 a H0 NE). rewrite blk_hi_span. unfold blk_lo. exact R0.
    - destruct (find_chunk s' a) as [cm0|] eqn:F3; [exfalso| reflexivity].
      destruct (find_chunk_some s' a cm0 F3) as (cb0 & H0 & R0). rewrite rl_lookup in H0.
      destruct (decide (cb0 = cb)) as [->|NE]; [discriminate|].
      pose proof (find_chunk_block E [] D s cb0 cm0 a WF H0 ltac:(rewrite blk_hi_span; unfold blk_lo; exact R0)). congruence. }
  rewrite FC. reflexivity.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma repD_rel : arep_thread segs E s' m'.
Proof.
  pose proof REP as (_ & _ & _ & RD & _). destruct RD as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8).
  assert (Egc : forall c', get_cache s' c' = get_cache s c') by (intros c'; destruct s; reflexivity).
  assert (Eci : as_cache_inited s' = as_cache_inited s) by (destruct s; reflexivity).
  assert (Eca : as_cache_allocated s' = as_cache_allocated s) by (destruct s; reflexivity).
  assert (Ecm : as_cache_mapped s' = as_cache_mapped s) by (destruct s; reflexivity).
  assert (Etqb : tq_bytes s' = tq_bytes s) by (destruct s; reflexivity).
  unfold arep_thread. rewrite rl_tq, Eca, Ecm, rl_ts, Etqb.
  split; [eapply rw_cells_agree'; [| exact D1]; thr_ag|].
  split; [eapply rw_cells_agree'; [| exact D2]; thr_ag|].
  split; [eapply rw_cells_agree'; [| exact D3]; thr_ag|].
  split.
  { intros c' Hc'. destruct (D4 c' Hc') as (X1 & junk & X2 & L). unfold percls_cells. rewrite !Egc, Eci. unfold kNumClasses in Hc'.
    split.
    - eapply rw_cells_agree'; [| exact X1]. unfold percls_cells. thr_ag.
    - exists junk. split; [| exact L]. eapply u32arr_agree; [| exact X2]. rewrite length_app, length_map. thr_ag. }
  split; [eapply rw_cells_agree'; [| exact D5]; thr_ag|].
  split.
  { apply u64arr_of_cells.
    - destruct D6 as [_ W6]. eapply wr_at_transport; [| exact WM]. unfold tstats_words in *. rewrite length_map in *. cbn [length] in *. exact W6.
    - pose proof NC_st as NC. apply rh_split with (cs1 := [C8 (zw (ts_real_frees (as_ts s) + 1))]) in NC as [N5 N6].
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in N6.
      intros i w Hi.
      Ltac oldw D6 i := eapply rw_cells_agree'; [| exact (u64arr_cell segs _ _ _ i _ D6 eq_refl)]; thr_ag.
      do 5 (destruct i as [|i]; [cbn in Hi; injection Hi as <-; oldw D6 0%nat || oldw D6 1%nat || oldw D6 2%nat || oldw D6 3%nat || oldw D6 4%nat |]).
      destruct i as [|i]; [cbn in Hi; injection Hi as <-; replace (T + kThrStats + 8 * Z.of_nat 5) with (T + kThrStats + 40) by lia; exact N5|].
      destruct i as [|i]; [cbn in Hi; injection Hi as <-; replace (T + kThrStats + 8 * Z.of_nat 6) with (T + kThrStats + 40 + 8) by lia; exact N6|].
      do 7 (destruct i as [|i]; [cbn in Hi; injection Hi as <-;
        oldw D6 7%nat || oldw D6 8%nat || oldw D6 9%nat || oldw D6 10%nat || oldw D6 11%nat || oldw D6 12%nat || oldw D6 13%nat |]).
      destruct i; cbn in Hi; discriminate. }
  split.
  { replace (ts_by_size (ts_on_real_free n (as_ts s))) with (ts_by_size (as_ts s)) by reflexivity.
    eapply u64arr_agree; [| exact D7]. rewrite length_map, length_ziota. thr_ag. }
  eapply rw_cells_agree'; [| exact D8]; thr_ag.
Qed.

(* [comment removed for export] *)
Lemma repF_rel : arep_chunks segs s' m'.
Proof.
  pose proof REP as (_ & _ & _ & _ & _ & RF & _).
  intros cb0 cm0 H0. rewrite rl_lookup in H0. destruct (decide (cb0 = cb)) as [->|NE]; [discriminate|].
  destruct (RF cb0 cm0 H0) as (X0 & (b1' & Hb1' & X1) & X2 & X3). split; [exact X0|]. split; [| split].
  - exists b1'. split; [exact Hb1'|]. eapply rw_cells_agree'; [| exact X1]. intros x Hx. cbn in Hx. apply (AGcm x cb0 cm0 H0 NE). left; lia.
  - intros Hrz. eapply rw_cells_agree'; [| exact (X2 Hrz)]. intros x Hx. cbn in Hx. apply (AGcm x cb0 cm0 H0 NE). right; left; split; [exact Hrz| lia].
  - destruct (cm_state cm0) as [i|i j] eqn:ST0; [exact I|]. eapply rw_cells_agree'; [| exact X3]. intros x Hx. cbn in Hx. apply (AGcm x cb0 cm0 H0 NE). right; right. rewrite ST0. lia.
Qed.

(* [comment removed for export] *)
Lemma repJ_rel : arep_shadow segs E s' m'.
Proof.
  pose proof REP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & RJ). pose proof geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G9 & G10). pose proof geo2 as [G12 G11].
  intros g0 v Hg.
  destruct (Z_le_gt_dec (blk_lo cm) (8 * g0)) as [LE|GT]; [destruct (Z_lt_le_dec (8 * g0) (blk_hi s cm)) as [LT|GE]|].
  - (* [comment removed for export] *)
    rewrite (Sh_rel_in (8 * g0) (conj LE LT)) in Hg. injection Hg as <-.
    pose proof (block_Sh E [] D s cb cm (8 * g0) WF Hcm (conj LE LT)) as Hs.
    destruct (Z_le_gt_dec ub (8 * g0)) as [U1|U1]; [destruct (Z_lt_le_dec (8 * g0) (ub + round_up n 8)) as [U2|U2]|].
    + (* [comment removed for export] *)
      replace (kShadowBase + g0) with (kShadowBase + g + (g0 - g)) by lia.
      apply (CB_byte segs m' (kShadowBase + g) (Z.to_nat l8) (zb kAsanHeapLeftRedzoneMagic) (g0 - g) NC_sh).
      clear -U1 U2 G4 G6 G9. Z.div_mod_to_equations. lia.
    + (* [comment removed for export] *)
      assert (EQ : chunk_shadow cm (8 * g0) = kAsanHeapLeftRedzoneMagic).
      { unfold chunk_shadow. rewrite ST.
        replace (8 * g0 <? ub) with false by (symmetry; apply Z.ltb_ge; exact U1).
        replace (8 * g0 <? ub + round_up n 8) with false by (symmetry; apply Z.ltb_ge; exact U2). reflexivity. }
      rewrite EQ in Hs. eapply rw_cells_agree'; [| exact (RJ g0 _ Hs)]. intros x Hx. cbn in Hx. replace x with (kShadowBase + g0) by lia.
      apply (AGsh_out g0 _ Hs). right. clear -U2 G6. lia.
    + (* [comment removed for export] *)
      assert (EQ : chunk_shadow cm (8 * g0) = kAsanHeapLeftRedzoneMagic).
      { unfold chunk_shadow. rewrite ST. replace (8 * g0 <? ub) with true by (symmetry; apply Z.ltb_lt; clear -U1; lia). reflexivity. }
      rewrite EQ in Hs. eapply rw_cells_agree'; [| exact (RJ g0 _ Hs)]. intros x Hx. cbn in Hx. replace x with (kShadowBase + g0) by lia.
      apply (AGsh_out g0 _ Hs). left. clear -U1 G4. Z.div_mod_to_equations. lia.
  - rewrite (Sh_rel_out (8 * g0) ltac:(clear -GE; lia)) in Hg.
    eapply rw_cells_agree'; [| exact (RJ g0 v Hg)]. intros x Hx. cbn in Hx. replace x with (kShadowBase + g0) by lia. apply (AGsh_out g0 v Hg). right. clear -GE G12 G6. lia.
  - rewrite (Sh_rel_out (8 * g0) ltac:(clear -GT; lia)) in Hg.
    eapply rw_cells_agree'; [| exact (RJ g0 v Hg)]. intros x Hx. cbn in Hx. replace x with (kShadowBase + g0) by lia. apply (AGsh_out g0 v Hg). left.
    unfold blk_lo in GT, G1. clear -GT G1 G4. Z.div_mod_to_equations. lia.
Qed.

Theorem ARep_after_rel : AREP s' m'.
Proof.
  pose proof REP as (RA & RB & RC & _ & RE & RF & RG & RH & RI & _).
  apply (AsanRepFlip.ARep_xfer9 segs E s s' m'); try (destruct s; reflexivity).
  - exact (frameA' segs E s m m' AGimg RA).
  - exact (frameB' segs E s m m' AGri RB).
  - exact (frameC' segs E s m m' WM AGfa RC).
  - exact repD_rel.
  - exact (frameE' segs E s m m' WM AGptr AGsec RE).
  - exact repF_rel.
  - exact (frameG' segs s m m' AGbat RG).
  - pose proof (frameH' segs E s m m' WM AGdep RH) as [DI DR]. unfold arep_depot. split.
    + revert DI. clear. unfold depot_inv, depot_n_ids, dphi. destruct s; cbn; exact (fun H => H).
    + revert DR. clear. unfold DepotRep, depot_hashes, depot_keys, node_blocks, store_blocks, node_addr. destruct s; cbn; exact (fun H => H).
  - exact (frameI' segs E s m m' WM AGimg RI).
  - exact repJ_rel.
Qed.
End REL.
End RRL.
End RC__1.
