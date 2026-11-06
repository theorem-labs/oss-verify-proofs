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
  AsanWf1 AsanWf3 AsanWf4 AsanWf5 AsanWf6 AsanClient AsanRepFrame AsanRepFrame2 AsanBudget AsanHit AsanRepHit AsanRepX AsanRepCa AsanRepSec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section RFL.
Variable segs : list Segment.
Variable E : aenv.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).
#[warnings="-notation-for-abbreviation"] Notation RW := (rw_cells segs).
#[warnings="-notation-for-abbreviation"] Notation SB := (ae_space_beg E).
#[warnings="-notation-for-abbreviation"] Notation T := (ae_thread E).
#[warnings="-notation-for-abbreviation"] Notation RI := (ae_region_info E).
#[warnings="-notation-for-abbreviation"] Notation PA := (ae_ptr_array E).
#[warnings="-notation-for-abbreviation"] Notation AREP := (ARep segs E (DepotR segs E)).

Section FLIP.
Variables (s s2 : astate) (m m' : mem) (lo cb : Z) (cm : chunkmeta) (aid fid : Z) (b1 : Z).
#[warnings="-notation-for-abbreviation"] Notation n := (cm_n cm).
#[warnings="-notation-for-abbreviation"] Notation ub := (cm_user_beg cm).
#[warnings="-notation-for-abbreviation"] Notation l8 := (round_up n 8 / 8).
Definition s3 : astate := upd_chunks (fun mm => <[cb := flipped cm aid fid]> mm) s2.

(* [comment removed for export] *)
Hypothesis Eregions : as_regions s2 = as_regions s.
Hypothesis Eci : as_cache_inited s2 = as_cache_inited s.
Hypothesis Ecache : as_cache s2 = as_cache s.
Hypothesis Ecst : as_cache_stale s2 = as_cache_stale s.
Hypothesis Ecal : as_cache_allocated s2 = as_cache_allocated s.
Hypothesis Ecm : as_cache_mapped s2 = as_cache_mapped s.
Hypothesis Eptr : as_ptr_committed s2 = as_ptr_committed s.
Hypothesis Esec : as_sec s2 = as_sec s.
Hypothesis Esst : as_sec_stale s2 = as_sec_stale s.
Hypothesis Estats : as_sec_stats s2 = as_sec_stats s.
Hypothesis Ega : as_glob_allocated s2 = as_glob_allocated s.
Hypothesis Egm : as_glob_mapped s2 = as_glob_mapped s.
Hypothesis Eoom : as_oom s2 = as_oom s.
Hypothesis Echunks : as_chunks s2 = as_chunks s.
Hypothesis Edead : as_dead s2 = as_dead s.
Hypothesis Etq : as_tq s2 = as_tq s.
Hypothesis Egq : as_gq s2 = as_gq s.
Hypothesis Eia : as_ia_inited s2 = as_ia_inited s.
Hypothesis Eres : as_residue s2 = as_residue s.
Hypothesis Enp : as_nprim_ever s2 = as_nprim_ever s.
Hypothesis Eevc : as_everc s2 = as_everc s.
Hypothesis Ets : as_ts s2 = ts_on_free n (as_ts s).

Hypothesis Hcm : as_chunks s !! cb = Some cm.
Hypothesis ST : cm_state cm = CAllocated aid.
Hypothesis HB1 : Z.land b1 127 = kHeaderByte1.

(* [comment removed for export] *)
Definition FPWflip (z : Z) : Prop :=
  lo <= z \/ DepotFPd E s2 z \/ (cb <= z < cb + 24)
  \/ (T + kThrStats + 24 <= z < T + kThrStats + 40)
  \/ (kShadowBase + ub / 8 <= z < kShadowBase + ub / 8 + l8).

Hypothesis WM : wmono segs m m'.
Hypothesis AG : forall z, 0 <= z < 2^64 -> ~ FPWflip z -> m' (wa z) = m (wa z).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis REP : AREP s m.
Hypothesis WF : AWf E [] [] s.
Hypothesis BS : blocks_sep E s.
Hypothesis Tpl : (0x1000 <= T /\ (T + 4096 <= 0x10000 \/ 0x603000 <= T)) /\ T + 4096 <= alloc_ceiling.
Hypothesis IMG_IN : forall x, In x (arep_img_ranges E ++ depot_static E) -> fst (ae_img E) <= fst x /\ fst x + snd x <= fst (ae_img E) + snd (ae_img E).
Hypothesis IMG_LO : 0x10000 <= fst (ae_img E).
Hypothesis IMG_LOW : forall x, In x (arep_img_ranges E ++ depot_static E) -> 0x10000 <= fst x /\ fst x + snd x <= 0x603000.
(* [comment removed for export] *)
Hypothesis IMG_DEPSEP : forall x y, In x (arep_img_ranges E) -> In y (depot_static E) -> fst x + snd x <= fst y \/ fst y + snd y <= fst x.
Hypothesis AK : exists mo, AKern E s mo.
Hypothesis AK2 : exists mo, AKern E s2 mo.
Hypothesis TDN : T + 4096 <= ae_depot_nodes E \/ ae_depot_nodes E + kDepotNodeBlockBytes <= T.
(* [comment removed for export] *)
Hypothesis DEP2 : DepotR segs E s2 m'.
(* [comment removed for export] *)
Hypothesis NC_hdr : RW m' cb [C1 (zb kChunkQuarantine); C1 (zb b1); C2 (zw (n / 2^32)); C4 (zw n); C8 (zw aid)].
Hypothesis NC_fid : RW m' ub [C8 (zw fid)].
Hypothesis NC_thr : RW m' (T + kThrStats + 24) [C8 (zw (ts_frees (as_ts s) + 1)); C8 (zw (ts_freed (as_ts s) + n))].
Hypothesis NC_sh : RW m' (kShadowBase + ub / 8) [CB (Z.to_nat l8) (repeat (zb kAsanHeapFreeMagic) (Z.to_nat l8))].

Hypothesis WF2 : AWf E [] [] s2.
(* [comment removed for export] *)
Hypothesis DN0 : ae_depot_nodes E + kDepotNodeBlockBytes <= PA \/ PA + kPtrArrayLen <= ae_depot_nodes E.

(* [comment removed for export] *)
Lemma s3_chunks : as_chunks s3 = <[cb := flipped cm aid fid]> (as_chunks s).
Proof. unfold s3. rewrite <- Echunks. destruct s2; reflexivity. Qed.
Ltac fld3 H := unfold s3; rewrite <- H; destruct s2; reflexivity.
Lemma s3_regions : as_regions s3 = as_regions s. Proof. fld3 Eregions. Qed.
Lemma s3_sec : as_sec s3 = as_sec s. Proof. fld3 Esec. Qed.
Lemma s3_tq : as_tq s3 = as_tq s. Proof. fld3 Etq. Qed.
Lemma s3_gq : as_gq s3 = as_gq s. Proof. fld3 Egq. Qed.

(* [comment removed for export] *)
Lemma geo : blk_lo cm + 16 <= ub /\ ub + n <= blk_hi s cm /\ cb = ub - 16 /\ ub mod 16 = 0 /\ 1 <= n < 2^40
  /\ 8 * l8 = round_up n 8 /\ n <= round_up n 8 < n + 8.
Proof.
  pose proof (chunk_user_in_block E [] [] s cb cm WF Hcm) as (A & B & C). pose proof (chunk_user_aligned E [] [] s cb cm WF Hcm) as D.
  unfold user_lo, user_hi, kChunkHeaderSize in *. pose proof WF as (_ & _ & _ & [K1 _] & _). destruct (K1 _ _ Hcm) as (_ & N & _).
  repeat split; try assumption; try lia; unfold round_up; clear -N; Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
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
  destruct (block_where E [] [] s cb cm WF Hcm) as [(J1 & J2 & c & Hc & PR & CV & _ & _ & SP)|(sc & Hsc & _ & L1 & L2)]; [left| right].
  - split; [| split; [| exists c; auto]]; unfold kSpaceSize in *; clear -J1 J2 E3 E4; lia.
  - exists sc. auto.
Qed.

Lemma blk_facts : forall a, blk_lo cm <= a < blk_hi s cm ->
  0 <= a < alloc_ceiling /\ ~ (kLowAppEnd <= a < kHighMemBeg) /\ ~ (T <= a < T + 4096)
  /\ (forall x, In x (arep_img_ranges E ++ depot_static E) -> ~ (fst x <= a < fst x + snd x))
  /\ ~ (PA <= a < PA + 0x800000)
  /\ (forall b len, (In b (ae_depot_nodes E :: as_node_blocks s2) /\ len = kDepotNodeBlockBytes) \/ (In b (ae_store_blk E :: as_store_blocks s2) /\ len = kStoreBlockBytes) ->
        ~ (b <= a < b + len)).
Proof.
  intros a Ha. pose proof (proj1 WF) as WE. pose proof alloc_ceiling_range as CR. destruct AK2 as [mo2 K2].
  pose proof WE as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & E28 & E29 & _).
  rewrite kHighMemBeg_val in E2. rewrite kLowAppEnd_val, kHighMemBeg_val.
  pose proof (BS (ae_depot_nodes E) kDepotNodeBlockBytes (or_introl (conj (or_introl eq_refl) eq_refl))) as (_ & _ & DNR & DNS & _).
  pose proof (ak_store_sep _ _ _ K2) as (SBR & SBS & _). rewrite Esec in SBS.
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
    + destruct (ak_blocks_sep _ _ _ K2 b kDepotNodeBlockBytes (or_introl (conj Hb eq_refl))) as (_ & _ & _ & _ & BSC & _). rewrite Esec in BSC. destruct (BSC sc Hsc); clear -Ha L1 L2 H; lia.
    + destruct (SBS sc Hsc); unfold kStoreBlockBytes; clear -Ha L1 L2 H; lia.
    + destruct (ak_blocks_sep _ _ _ K2 b kStoreBlockBytes (or_intror (conj Hb eq_refl))) as (_ & _ & _ & _ & BSC & _). rewrite Esec in BSC. destruct (BSC sc Hsc); clear -Ha L1 L2 H; lia.
Qed.

(* [comment removed for export] *)
Lemma blk_vs_chunk : forall cb' cm' a, as_chunks s !! cb' = Some cm' -> cb' <> cb -> chunk_meta_fp cm' a -> ~ (blk_lo cm <= a < blk_hi s cm).
Proof.
  intros cb' cm' a H' NE FPa R. pose proof (chunk_meta_in_block E [] [] s cb' cm' a WF H' FPa) as [B1 B2].
  destruct (chunks_disjoint E [] [] s cb' cm' cb cm WF H' Hcm NE); clear -B1 B2 R H; lia.
Qed.
Lemma blk_vs_batch : forall b a, In b (as_tq s ++ as_gq s) -> b_addr b <= a < b_addr b + 24 + 8 * kBatchCap -> ~ (blk_lo cm <= a < blk_hi s cm).
Proof.
  intros b a Hb Ha R. pose proof WF as (WE & WR & _ & _ & WQ & _).
  destruct (batch_block E [] s b WQ ltac:(unfold all_batches; rewrite app_assoc; apply in_app_iff; left; exact Hb)) as (CV & _ & _ & NCB).
  assert (CS : class_size kBatchClass = 8192) by reflexivity. assert (HB24 : 1 <= kBatchClass <= kLargestClassID) by (unfold kBatchClass, kLargestClassID; lia).
  destruct blk_where as [(R1 & R2 & c & Hc & PR & CVc & SP)|(sc & Hsc & L1 & L2)].
  - destruct (carved_blocks_disjoint E s c (blk_lo cm) kBatchClass (b_addr b) Hc HB24 WR CVc CV) as [[_ EQ]|D].
    + apply NCB. exists cb, cm. split; [exact Hcm| exact EQ].
    + unfold kBatchCap in Ha. clear -Ha R D SP CS. lia.
  - pose proof (carved_in_space E s kBatchClass _ HB24 WR CV) as [I1 I2].
    pose proof WF as (_ & _ & _ & _ & _ & (_ & _ & S3 & _) & _). destruct (S3 sc Hsc) as (_ & _ & _ & _ & _ & SP & _).
    unfold kBatchCap, kPageSize, kRegionSize, kSpaceSize in *. clear -Ha R L1 L2 I1 I2 SP CS. lia.
Qed.

(* [comment removed for export] *)
Lemma shw_band : forall z, kShadowBase + ub / 8 <= z < kShadowBase + ub / 8 + l8 -> kLowAppEnd < z < kHighMemBeg.
Proof.
  intros z Hz. pose proof geo as (G1 & G2 & _ & _ & G5 & G6 & G7). pose proof (blk_facts ub ltac:(clear -G1 G2 G5; lia)) as (B1 & _).
  pose proof (blk_facts (ub + n - 1) ltac:(clear -G1 G2 G5; lia)) as (B2 & _). pose proof alloc_ceiling_range as CR.
  rewrite kLowAppEnd_val, kHighMemBeg_val. unfold kShadowBase in Hz. clear -Hz B1 B2 G5 G6 G7 CR. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma AG_fp : forall a, arep_fp E (DepotFP E) s a ->
  ~ (T <= a < T + 4096) -> ~ DepotFPd E s2 a -> ~ (cb <= a < cb + 24) -> ~ (kLowAppEnd < a < kHighMemBeg) -> m' (wa a) = m (wa a).
Proof.
  intros a Ha NT ND NC NB. pose proof (fp_range E s WF BS IMG_IN IMG_LO a Ha) as BC. pose proof alloc_ceiling_range as CR.
  apply AG; [clear -BC CR; lia|]. unfold FPWflip. intros [X|[X|[X|[X|X]]]].
  - clear -X BC LO. lia.
  - exact (ND X).
  - exact (NC X).
  - unfold kThrStats in X. clear -X NT. lia.
  - exact (NB (shw_band a X)).
Qed.

(* [comment removed for export] *)
Lemma depot_fp_cases : forall a, DepotFPd E s2 a ->
  in_ranges (depot_static E) a
  \/ exists b len, ((In b (ae_depot_nodes E :: as_node_blocks s2) /\ len = kDepotNodeBlockBytes) \/ (In b (ae_store_blk E :: as_store_blocks s2) /\ len = kStoreBlockBytes))
                   /\ b <= a < b + len.
Proof.
  intros a [X|[(b & Hb & R)|(b & Hb & R)]].
  - left. destruct X as (r & Hr & R). exists r. split; [| exact R]. unfold depot_static.
    destruct Hr as [<-|[<-|[]]]; [left| right; left]; reflexivity.
  - right. exists b, kDepotNodeBlockBytes. split; [left; split; [exact Hb| reflexivity]| exact R].
  - right. exists b, kStoreBlockBytes. split; [right; split; [exact Hb| reflexivity]| exact R].
Qed.

(* [comment removed for export] *)
Lemma AGimg : forall a, in_ranges (arep_img_ranges E) a -> m' (wa a) = m (wa a).
Proof.
  intros a (x & Hx & R). pose proof Tpl as [[T1 T2] T3]. destruct AK2 as [mo2 K2].
  assert (Hx' : In x (arep_img_ranges E ++ depot_static E)) by (apply in_app_iff; left; exact Hx).
  pose proof (IMG_LOW x Hx') as [L1 L2]. pose proof (IMG_IN x Hx') as [L3 L4].
  pose proof geo as (G1 & G2 & G3 & G4 & G5 & _). pose proof geo2 as [G6 G7].
  apply AG_fp; [left; exists x; split; [exact Hx| exact R]| clear -R L1 L2 T1 T2; lia| | | rewrite kLowAppEnd_val; clear -R L2; lia].
  - intros D. destruct (depot_fp_cases a D) as [(y & Hy & Ry)|(b & len & Hbl & Rb)].
    + assert (Hy' : In y (depot_static E)) by (unfold depot_static; destruct Hy as [<-|[<-|[]]]; [left| right; left]; reflexivity).
      destruct (IMG_DEPSEP x y Hx Hy'); clear -R Ry H; lia.
    + pose proof (BS (ae_depot_nodes E) kDepotNodeBlockBytes (or_introl (conj (or_introl eq_refl) eq_refl))) as (_ & _ & _ & _ & _ & DI0).
      pose proof (BS (ae_store_blk E) kStoreBlockBytes (or_intror (conj (or_introl eq_refl) eq_refl))) as (_ & _ & _ & _ & _ & SI0).
      unfold img_sep in DI0, SI0.
      pose proof (proj1 WF) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E29 & _).
      destruct Hbl as [[[<-|Hb] ->]|[[<-|Hb] ->]].
      * clear -R Rb L3 L4 DI0. lia.
      * destruct (ak_blocks_sep _ _ _ K2 b kDepotNodeBlockBytes (or_introl (conj Hb eq_refl))) as (_ & _ & _ & _ & _ & BRS). pose proof (BRS _ E29) as X.
        destruct (ae_img E); cbn [fst snd] in *. clear -R Rb L3 L4 X. lia.
      * clear -R Rb L3 L4 SI0. lia.
      * destruct (ak_blocks_sep _ _ _ K2 b kStoreBlockBytes (or_intror (conj Hb eq_refl))) as (_ & _ & _ & _ & _ & BRS). pose proof (BRS _ E29) as X.
        destruct (ae_img E); cbn [fst snd] in *. clear -R Rb L3 L4 X. lia.
  - intros C. destruct (blk_facts a ltac:(clear -C G1 G3 G7; lia)) as (_ & _ & _ & NI & _). exact (NI x Hx' R).
Qed.

(* [comment removed for export] *)
Lemma depot_blk_apart : forall b len a,
  (In b (ae_depot_nodes E :: as_node_blocks s2) /\ len = kDepotNodeBlockBytes) \/ (In b (ae_store_blk E :: as_store_blocks s2) /\ len = kStoreBlockBytes) ->
  b <= a < b + len ->
  ~ (ae_resv_beg E <= a < ae_resv_beg E + 0x2000011000) /\ (forall sc, In sc (as_sec s) -> ~ (sc_map_beg sc <= a < sc_map_beg sc + sc_map_size sc))
  /\ ~ (PA <= a < PA + 0x800000) /\ ~ (T <= a < T + 4096) /\ ~ (kLowAppEnd <= a < kHighMemBeg).
Proof.
  intros b len a Hbl R. destruct AK2 as [mo2 K2]. pose proof (proj1 WF) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & _).
  pose proof (BS (ae_depot_nodes E) kDepotNodeBlockBytes (or_introl (conj (or_introl eq_refl) eq_refl))) as (DAM & _ & DNR & DNS & _).
  pose proof (ak_store_sep _ _ _ K2) as (SBR & SBS & SBT & _ & SBP). rewrite Esec in SBS.
  pose proof (BS (ae_store_blk E) kStoreBlockBytes (or_intror (conj (or_introl eq_refl) eq_refl))) as (SAM & _).
  assert (NT : ~ (T <= a < T + 4096)).
  { intros HT. destruct (Tpage_apart E s2 WF2 Tpl (ex_intro _ mo2 K2) TDN a HT) as (_ & _ & _ & NB & _). exact (NB b len Hbl R). }
  unfold app_mem, kResvLen, kStoreBlockBytes, kPtrArrayLen, kPageSize in *. rewrite ?kLowAppEnd_val, ?kHighMemBeg_val in *.
  destruct Hbl as [[[<-|Hb] ->]|[[<-|Hb] ->]].
  - split; [clear -R DNR; lia|]. split; [intros sc Hsc X; destruct (DNS sc Hsc); clear -R X H; lia|]. split; [clear -R DN0; lia|]. split; [exact NT| clear -R DAM; lia].
  - destruct (ak_blocks_sep _ _ _ K2 b kDepotNodeBlockBytes (or_introl (conj Hb eq_refl))) as (AM & _ & _ & BR & BSC & BRS). rewrite Esec in BSC. unfold app_mem, kResvLen in AM, BR. rewrite ?kLowAppEnd_val, ?kHighMemBeg_val in AM.
    pose proof (BRS _ E8) as XP. cbn [fst snd] in XP.
    split; [clear -R BR; lia|]. split; [intros sc Hsc X; destruct (BSC sc Hsc); clear -R X H; lia|]. split; [clear -R XP; lia|]. split; [exact NT| clear -R AM; lia].
  - split; [clear -R SBR; lia|]. split; [intros sc Hsc X; destruct (SBS sc Hsc); clear -R X H; lia|]. split; [clear -R SBP; lia|]. split; [exact NT| clear -R SAM; lia].
  - destruct (ak_blocks_sep _ _ _ K2 b kStoreBlockBytes (or_intror (conj Hb eq_refl))) as (AM & _ & _ & BR & BSC & BRS). rewrite Esec in BSC. unfold app_mem, kResvLen in AM, BR. unfold kStoreBlockBytes in *. rewrite ?kLowAppEnd_val, ?kHighMemBeg_val in AM.
    pose proof (BRS _ E8) as XP. cbn [fst snd] in XP.
    split; [clear -R BR; lia|]. split; [intros sc Hsc X; destruct (BSC sc Hsc); clear -R X H; lia|]. split; [clear -R XP; lia|]. split; [exact NT| clear -R AM; lia].
Qed.

(* [comment removed for export] *)
Lemma AG_resv : forall a, arep_fp E (DepotFP E) s a -> ae_resv_beg E <= a < ae_resv_beg E + 0x2000011000 ->
  ~ (cb <= a < cb + 24) -> m' (wa a) = m (wa a).
Proof.
  intros a Ha R NC. pose proof (proj1 WF) as (E1 & E2 & _). rewrite kHighMemBeg_val in E2.
  apply AG_fp; [exact Ha| | | exact NC| rewrite kHighMemBeg_val; clear -R E2; lia].
  - intros HT. destruct (Tpage_apart E s WF Tpl AK TDN a HT) as (NR & _). exact (NR R).
  - intros D. destruct (depot_fp_cases a D) as [(y & Hy & Ry)|(b & len & Hbl & Rb)].
    + assert (Hy' : In y (arep_img_ranges E ++ depot_static E)) by (apply in_app_iff; right; unfold depot_static; destruct Hy as [<-|[<-|[]]]; [left| right; left]; reflexivity).
      pose proof (IMG_LOW y Hy') as [L1 L2]. clear -R Ry L2 E2. lia.
    + destruct (depot_blk_apart b len a Hbl Rb) as (NR & _). exact (NR R).
Qed.
Lemma space_resv : forall a, SB <= a < SB + kSpaceSize + 0x1000 -> ae_resv_beg E <= a < ae_resv_beg E + 0x2000011000.
Proof. intros a Ha. pose proof (proj1 WF) as (E1 & E2 & E3 & E4 & _). clear -Ha E3 E4. lia. Qed.

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

Lemma cb_in_blk : forall a, cb <= a < cb + 24 -> blk_lo cm <= a < blk_hi s cm.
Proof. intros a Ha. pose proof geo as (G1 & G2 & G3 & _). pose proof geo2 as [_ G7]. clear -Ha G1 G3 G7. lia. Qed.

Lemma AGri : forall a, RI <= a < RI + kRegSize * kNumClasses -> m' (wa a) = m (wa a).
Proof.
  intros a Ha. apply AG_resv; [right; left; exact Ha| apply space_resv; unfold ae_region_info, kRegSize, kNumClasses, kSpaceSize in *; clear -Ha; lia|].
  intros C. exact (proj1 (blk_vs_fa_ri a (cb_in_blk a C)) Ha).
Qed.
Lemma AGfa : forall a c', 0 <= c' < kNumClasses -> free_array SB c' <= a < free_array SB c' + rg_mapped_fa (region_of s c') -> m' (wa a) = m (wa a).
Proof.
  intros a c' Hc Ha. apply AG_resv; [do 3 right; left; exists c'; split; [exact Hc| exact Ha]| |].
  - assert (RM : in_some_region_map E s a = true).
    { unfold in_some_region_map. apply Bool.orb_true_iff. right. apply existsb_exists. exists c'. split; [apply In_ziota; unfold kNumClasses in Hc; lia|].
      apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; lia. }
    pose proof (region_map_in_space E [] [] s a WF RM) as SP. apply space_resv. clear -SP. lia.
  - intros C. exact (proj2 (blk_vs_fa_ri a (cb_in_blk a C)) c' Hc Ha).
Qed.
Lemma AGbat : forall a b, In b (as_tq s ++ as_gq s) -> b_addr b <= a < b_addr b + 24 + 8 * kBatchCap -> m' (wa a) = m (wa a).
Proof.
  intros a b Hb Ha. apply AG_resv; [do 7 right; left; exists b; split; [exact Hb| exact Ha]| | intros C; exact (blk_vs_batch b a Hb Ha (cb_in_blk a C))].
  pose proof WF as (WE & WR & _ & _ & WQ & _).
  destruct (batch_block E [] s b WQ ltac:(unfold all_batches; rewrite app_assoc; apply in_app_iff; left; exact Hb)) as (CV & _).
  assert (HB24 : 1 <= kBatchClass <= kLargestClassID) by (unfold kBatchClass, kLargestClassID; lia).
  pose proof (carved_in_space E s kBatchClass _ HB24 WR CV) as [J1 J2]. assert (CS : class_size kBatchClass = 8192) by reflexivity.
  apply space_resv. unfold kBatchCap, kSpaceSize, kRegionSize in *. clear -Ha J1 J2 CS. lia.
Qed.

(* [comment removed for export] *)
Lemma AG_secmap : forall a sc, arep_fp E (DepotFP E) s a -> In sc (as_sec s) -> sc_map_beg sc <= a < sc_map_beg sc + sc_map_size sc ->
  ~ (cb <= a < cb + 24) -> m' (wa a) = m (wa a).
Proof.
  intros a sc Ha Hsc R NC. pose proof WF as (_ & _ & _ & _ & _ & (_ & _ & S3 & _) & _). destruct (S3 sc Hsc) as (_ & AM & _).
  apply AG_fp; [exact Ha| | | exact NC| unfold app_mem in AM; clear -R AM; lia].
  - intros HT. destruct (Tpage_apart E s WF Tpl AK TDN a HT) as (_ & _ & NS & _). exact (NS sc Hsc R).
  - intros D. destruct (depot_fp_cases a D) as [(y & Hy & Ry)|(b & len & Hbl & Rb)].
    + assert (Hy' : In y (arep_img_ranges E ++ depot_static E)) by (apply in_app_iff; right; unfold depot_static; destruct Hy as [<-|[<-|[]]]; [left| right; left]; reflexivity).
      pose proof (IMG_IN y Hy') as [L1 L2]. destruct (S3 sc Hsc) as (_ & _ & _ & _ & _ & _ & SR).
      pose proof (proj1 WF) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E29 & _).
      pose proof (SR _ E29) as X. destruct (ae_img E); cbn [fst snd] in *. clear -R Ry L1 L2 X. lia.
    + destruct (depot_blk_apart b len a Hbl Rb) as (_ & NS & _). exact (NS sc Hsc R).
Qed.
Lemma AGsec : forall a sc, In sc (as_sec s) -> sc_map_beg sc <= a < sc_map_beg sc + 32 -> m' (wa a) = m (wa a).
Proof.
  intros a sc Hsc Ha. pose proof WF as (_ & _ & _ & _ & _ & (_ & _ & S3 & _ & S5) & _). destruct (S3 sc Hsc) as (_ & _ & _ & POS & MODS & _ & SR).
  pose proof (proj1 WF) as (_ & _ & _ & _ & _ & _ & E7 & _). pose proof (SR _ E7) as SPc. cbn [fst snd] in SPc.
  pose proof (AsanRepFrame.pos_mod_ge E (sc_map_size sc) kPageSize POS MODS ltac:(unfold kPageSize; lia)) as GE. unfold kPageSize in GE.
  apply (AG_secmap a sc); [do 5 right; left; exists sc; split; [exact Hsc| exact Ha]| exact Hsc| clear -Ha GE; lia|].
  intros C. pose proof (cb_in_blk a C) as R.
  destruct blk_where as [(R1 & R2 & _)|(sc' & Hsc' & L1 & L2)].
  - clear -Ha R R1 R2 SPc GE. lia.
  - destruct (secchunk_eq_dec sc sc') as [->|NE]; [unfold kPageSize in L1; clear -Ha R L1; lia|].
    destruct (S5 sc sc' Hsc Hsc' NE); unfold kPageSize in L1; clear -Ha R L1 L2 H GE; lia.
Qed.
Lemma AGcm : forall a cb' cm', as_chunks s !! cb' = Some cm' -> cb' <> cb -> chunk_meta_fp cm' a -> m' (wa a) = m (wa a).
Proof.
  intros a cb' cm' Hcm' NE Ha. pose proof (chunk_meta_in_block E [] [] s cb' cm' a WF Hcm' Ha) as [BL BU].
  assert (NC : ~ (cb <= a < cb + 24)) by (intros C; exact (blk_vs_chunk cb' cm' a Hcm' NE Ha (cb_in_blk a C))).
  destruct (block_where E [] [] s cb' cm' WF Hcm') as [(J1 & J2 & _)|(sc & Hsc & _ & L1 & L2)].
  - apply AG_resv; [do 6 right; left; exists cb', cm'; split; [exact Hcm'| exact Ha]| apply space_resv; clear -BL BU J1 J2; lia| exact NC].
  - apply (AG_secmap a sc); [do 6 right; left; exists cb', cm'; split; [exact Hcm'| exact Ha]| exact Hsc| unfold kPageSize in L1; clear -BL BU L1 L2; lia| exact NC].
Qed.
(* [comment removed for export] *)
Lemma AGmag : forall a, 16 < 16 * 2 ^ cm_rz_log cm -> cm_alloc_beg cm <= a < cm_alloc_beg cm + 16 -> m' (wa a) = m (wa a).
Proof.
  intros a RZ Ha. pose proof geo as (G1 & G2 & G3 & _). unfold blk_lo in G1.
  assert (FPa : chunk_meta_fp cm a) by (right; left; split; [exact RZ| exact Ha]).
  pose proof (chunk_meta_in_block E [] [] s cb cm a WF Hcm FPa) as [BL BU].
  assert (RZ32 : 32 <= 16 * 2 ^ cm_rz_log cm).
  { pose proof WF as (_ & _ & _ & [K1 _] & _). destruct (K1 _ _ Hcm) as (_ & _ & C & _). rewrite C in RZ |- *.
    change (16 * 2 ^ rz_log (cm_n cm)) with (rz_size (cm_n cm)) in *. pose proof (rz_size_values (cm_n cm)) as V. cbn in V. clear -V RZ. lia. }
  assert (NC : ~ (cb <= a < cb + 24)) by (unfold cm_user_beg in G3; clear -Ha G3 RZ32; lia).
  destruct blk_where as [(J1 & J2 & _)|(sc & Hsc & L1 & L2)].
  - apply AG_resv; [do 6 right; left; exists cb, cm; split; [exact Hcm| exact FPa]| clear -BL BU J1 J2; lia| exact NC].
  - apply (AG_secmap a sc); [do 6 right; left; exists cb, cm; split; [exact Hcm| exact FPa]| exact Hsc| unfold kPageSize in L1; clear -BL BU L1 L2; lia| exact NC].
Qed.
Lemma AGptr : forall a, PA <= a < PA + 8 * kChunksBlockCount -> m' (wa a) = m (wa a).
Proof.
  intros a Ha. pose proof (proj1 WF) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & _). unfold kChunksBlockCount in Ha.
  apply AG_fp; [do 4 right; left; unfold kChunksBlockCount; exact Ha| | | | unfold app_mem in E16; clear -Ha E16; lia].
  - intros HT. destruct (Tpage_apart E s WF Tpl AK TDN a HT) as (_ & NP & _). clear -Ha NP. lia.
  - intros D. destruct (depot_fp_cases a D) as [(y & Hy & Ry)|(b & len & Hbl & Rb)].
    + assert (Hy' : In y (arep_img_ranges E ++ depot_static E)) by (apply in_app_iff; right; unfold depot_static; destruct Hy as [<-|[<-|[]]]; [left| right; left]; reflexivity).
      pose proof (IMG_IN y Hy') as [L1 L2].
      pose proof (proj1 WF) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E33 & _).
      unfold img_sep in E33. clear -Ha Ry L1 L2 E33. lia.
    + destruct (depot_blk_apart b len a Hbl Rb) as (_ & _ & NP & _). clear -Ha NP. lia.
  - intros C. destruct (blk_facts a (cb_in_blk a C)) as (_ & _ & _ & _ & NP & _). clear -Ha NP. lia.
Qed.
Lemma AGdep_irrelevant : True. Proof. exact I. Qed.

(* [comment removed for export] *)
Lemma AGsh_out : forall g v, Sh E s (8 * g) = Some v -> (8 * g + 8 <= ub \/ ub + 8 * l8 <= 8 * g) -> m' (wa (kShadowBase + g)) = m (wa (kShadowBase + g)).
Proof.
  intros g v Hg OUT. pose proof (AsanRepSec.Sh_granule_range segs E s) as SGR || idtac.
  assert (GR : 0 <= 8 * g < 2^47).
  { pose proof WF as WF0. pose proof alloc_ceiling_range as CR. unfold Sh in Hg.
    destruct (in_some_region_map E s (8 * g)) eqn:RM.
    - pose proof (region_map_in_space E [] [] s (8 * g) WF0 RM) as SP. pose proof (proj1 WF0) as (E1 & E2 & E3 & E4 & E5 & _).
      unfold kSpaceSize in *. rewrite kHighMemBeg_val in E2. clear -SP E2 E3 E4 E5 CR. lia.
    - destruct (in_some_sec_map s (8 * g)) eqn:SM.
      + unfold in_some_sec_map in SM. apply existsb_exists in SM as (sc & Hsc & Hb). apply andb_true_iff in Hb as [B1 B2].
        apply Z.leb_le in B1. apply Z.ltb_lt in B2. pose proof WF0 as (_ & _ & _ & _ & _ & (_ & _ & S3 & _) & _). destruct (S3 sc Hsc) as (_ & HB & S & _).
        unfold app_mem in HB. rewrite kHighMemBeg_val, kLowAppEnd_val in HB. clear -B1 B2 HB S CR. lia.
      + cbn [orb] in Hg. destruct (sh_default_dom E (8 * g) && negb (sh_excluded E (8 * g))) eqn:C; [|discriminate].
        apply andb_true_iff in C as [C _]. unfold sh_default_dom in C. apply Bool.orb_true_iff in C as [C|C].
        * apply andb_true_iff in C as [C _]. apply andb_true_iff in C as [C1 C2]. apply Z.leb_le in C1. apply Z.ltb_lt in C2. rewrite kLowAppEnd_val in C2. clear -C1 C2. lia.
        * apply andb_true_iff in C as [C1 C2]. apply Z.leb_le in C1. apply Z.leb_le in C2. rewrite kHighMemBeg_val in C1. unfold kHighMemEnd in C2. clear -C1 C2. lia. }
  pose proof geo as (G1 & G2 & G3 & G4 & G5 & G6 & _). pose proof geo2 as [G7 G8].
  assert (BAND : 2147446784 < kShadowBase + g < 17594333495296) by (unfold kShadowBase; clear -GR; lia).
  pose proof alloc_ceiling_range as CR.
  apply AG; [clear -BAND CR; lia|].
  unfold FPWflip. intros [X|[X|[X|[X|X]]]].
  - clear -X BAND CR LO. lia.
  - destruct (depot_fp_cases _ X) as [(y & Hy & Ry)|(b & len & Hbl & Rb)].
    + assert (Hy' : In y (arep_img_ranges E ++ depot_static E)) by (apply in_app_iff; right; unfold depot_static; destruct Hy as [<-|[<-|[]]]; [left| right; left]; reflexivity).
      pose proof (IMG_LOW y Hy') as [L1 L2]. clear -Ry L2 BAND. lia.
    + destruct (depot_blk_apart b len _ Hbl Rb) as (_ & _ & _ & _ & NB). apply NB. rewrite kLowAppEnd_val, kHighMemBeg_val. clear -BAND. lia.
  - destruct (blk_facts _ (cb_in_blk _ X)) as (_ & NB & _). apply NB. rewrite kLowAppEnd_val, kHighMemBeg_val. clear -BAND. lia.
  - destruct (Tpage_apart E s WF Tpl AK TDN (kShadowBase + g) ltac:(unfold kThrStats in X; clear -X; lia)) as (_ & _ & _ & _ & NBAND & _). apply NBAND.
    rewrite kLowAppEnd_val, kHighMemBeg_val. clear -BAND. lia.
  - unfold kShadowBase in X. clear -X OUT G4 G6. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma AGthr_cells : forall A k, T <= A -> A + k <= T + 4096 -> (A + k <= T + kThrStats + 24 \/ T + kThrStats + 40 <= A) -> agree_on m m' A k.
Proof.
  intros A k H0 H1 H2 z Hz. pose proof Tpl as [[T1 T2] T3]. pose proof alloc_ceiling_range as CR. destruct AK2 as [mo2 K2].
  pose proof (proj1 WF) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & _). unfold app_mem in E14. rewrite kLowAppEnd_val, kHighMemBeg_val in E14.
  assert (HT : T <= z < T + 4096) by (clear -Hz H0 H1; lia).
  apply AG; [clear -Hz H0 H1 T1 T3 CR; lia|]. unfold FPWflip. intros [X|[X|[X|[X|X]]]].
  - clear -X HT T3 LO. lia.
  - destruct (Tpage_apart E s2 WF2 Tpl (ex_intro _ mo2 K2) TDN z HT) as (_ & _ & _ & NB & _ & NI).
    destruct (depot_fp_cases _ X) as [(y & Hy & Ry)|(b & len & Hbl & Rb)]; [| exact (NB b len Hbl Rb)].
    assert (Hy' : In y (arep_img_ranges E ++ depot_static E)) by (apply in_app_iff; right; unfold depot_static; destruct Hy as [<-|[<-|[]]]; [left| right; left]; reflexivity).
    pose proof (IMG_LOW y Hy') as [L1 L2]. clear -Ry L1 L2 NI. apply NI. lia.
  - destruct (blk_facts _ (cb_in_blk _ X)) as (_ & _ & NT & _). exact (NT HT).
  - clear -X Hz H2. lia.
  - pose proof (shw_band z X) as B. rewrite kLowAppEnd_val, kHighMemBeg_val in B. clear -B HT E14. lia.
Qed.
Ltac thr_ag := apply AGthr_cells; unfold kThrUnwinding, kThrCache, kThrCacheStats, kThrStats, kPerClassSize, kThrStackTop, kThrQCache, kNumClasses in *;
  cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]; try lia.

Hypothesis FID : 1 <= fid.

(* [comment removed for export] *)
Lemma ARep_xfer9 : forall sa sb mm,
  as_regions sb = as_regions sa -> as_ptr_committed sb = as_ptr_committed sa -> as_sec sb = as_sec sa -> as_sec_stats sb = as_sec_stats sa ->
  as_glob_allocated sb = as_glob_allocated sa -> as_glob_mapped sb = as_glob_mapped sa -> as_tq sb = as_tq sa -> as_gq sb = as_gq sa -> as_ia_inited sb = as_ia_inited sa ->
  arep_instance segs E sa mm -> arep_regioninfo segs E sa mm -> arep_region_mem segs E sa mm -> arep_thread segs E sb mm ->
  arep_secondary segs E sa mm -> arep_chunks segs sb mm -> arep_batches segs sa mm -> arep_depot (DepotR segs E) sb mm ->
  arep_globals segs E sa mm -> arep_shadow segs E sb mm -> AREP sb mm.
Proof.
  intros sa sb mm. destruct sa, sb; cbn. intros -> -> -> -> -> -> -> -> ->.
  intros RA RB RC RD' RE RF RG RH RI RJ.
  split; [exact RA|]. split; [exact RB|]. split; [exact RC|]. split; [exact RD'|]. split; [exact RE|]. split; [exact RF|].
  split; [destruct RG as [RG1 RG2]; split; eapply arep_batch_list_indep; eassumption|]. split; [exact RH|]. split; [exact RI| exact RJ].
Qed.

Lemma WF3 : AWf E [cb] [] s3.
Proof. unfold s3. apply (proj1 (AWf_flip E [] s2 cb cm aid fid WF2 ltac:(rewrite Echunks; exact Hcm) ST FID)). Qed.

Lemma s3_lookup : forall cb0, as_chunks s3 !! cb0 = if decide (cb0 = cb) then Some (flipped cm aid fid) else as_chunks s !! cb0.
Proof.
  intros cb0. rewrite s3_chunks. destruct (decide (cb0 = cb)) as [->|NE]; [apply lookup_insert_eq| rewrite lookup_insert_ne by congruence; reflexivity].
Qed.

Lemma blk_flipped : blk_lo (flipped cm aid fid) = blk_lo cm /\ blk_hi s3 (flipped cm aid fid) = blk_hi s cm
  /\ cm_user_beg (flipped cm aid fid) = ub /\ cm_chunk_beg (flipped cm aid fid) = cm_chunk_beg cm /\ cm_n (flipped cm aid fid) = n
  /\ cm_alloc_beg (flipped cm aid fid) = cm_alloc_beg cm /\ cm_rz_log (flipped cm aid fid) = cm_rz_log cm.
Proof. unfold flipped, blk_lo, blk_hi, cm_user_beg, cm_chunk_beg. cbn. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
Lemma Sh_s3_in : forall a, blk_lo cm <= a < blk_hi s cm -> Sh E s3 a = Some (chunk_shadow (flipped cm aid fid) a).
Proof.
  intros a Ha. pose proof blk_flipped as (B1 & B2 & _). apply (block_Sh E [cb] [] s3 cb); [exact WF3| rewrite s3_lookup; rewrite decide_True by reflexivity; reflexivity| rewrite B1, B2; exact Ha].
Qed.
Lemma Sh_s3_out : forall a, ~ (blk_lo cm <= a < blk_hi s cm) -> Sh E s3 a = Sh E s a.
Proof.
  intros a Ha. unfold Sh.
  assert (RM : in_some_region_map E s3 a = in_some_region_map E s a) by (unfold in_some_region_map, region_of, get_region; rewrite s3_regions; reflexivity).
  assert (SM : in_some_sec_map s3 a = in_some_sec_map s a) by (unfold in_some_sec_map; rewrite s3_sec; reflexivity).
  rewrite RM, SM.
  assert (FC : find_chunk s3 a = find_chunk s a).
  { destruct (find_chunk s a) as [cm0|] eqn:F0.
    - destruct (find_chunk_some s a cm0 F0) as (cb0 & H0 & R0).
      assert (NE : cb0 <> cb).
      { intros ->. rewrite Hcm in H0. injection H0 as E0. apply Ha. first [rewrite <- E0 in R0| rewrite E0 in R0]. unfold blk_lo, blk_hi, block_span in *. destruct (cm_prim cm); lia. }
      apply (find_chunk_block E [cb] [] s3 cb0 cm0 a WF3); [rewrite s3_lookup, decide_False by exact NE; exact H0|].
      unfold blk_lo, blk_hi, block_span in *; destruct (cm_prim cm0); lia.
    - destruct (find_chunk s3 a) as [cm0|] eqn:F3; [exfalso| reflexivity].
      destruct (find_chunk_some s3 a cm0 F3) as (cb0 & H0 & R0). rewrite s3_lookup in H0.
      destruct (decide (cb0 = cb)) as [->|NE].
      + injection H0 as <-. apply Ha. pose proof blk_flipped as (B1 & B2 & _). unfold blk_lo, blk_hi, block_span in *. cbn in R0. destruct (cm_prim cm); lia.
      + pose proof (find_chunk_block E [] [] s cb0 cm0 a WF H0 ltac:(unfold blk_lo, blk_hi, block_span in *; destruct (cm_prim cm0); lia)). congruence. }
  rewrite FC. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma repD_flip : arep_thread segs E s3 m'.
Proof.
  pose proof REP as (_ & _ & _ & RD & _). destruct RD as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8).
  assert (Etq3 : as_tq s3 = as_tq s) by apply s3_tq.
  assert (Eca3 : as_cache_allocated s3 = as_cache_allocated s) by (unfold s3; rewrite <- Ecal; destruct s2; reflexivity).
  assert (Ecm3 : as_cache_mapped s3 = as_cache_mapped s) by (unfold s3; rewrite <- Ecm; destruct s2; reflexivity).
  assert (Ets3 : as_ts s3 = ts_on_free n (as_ts s)) by (unfold s3; rewrite <- Ets; destruct s2; reflexivity).
  assert (Egc3 : forall c', get_cache s3 c' = get_cache s c') by (intros c'; unfold get_cache, s3; rewrite <- Ecache; destruct s2; reflexivity).
  assert (Eci3 : as_cache_inited s3 = as_cache_inited s) by (unfold s3; rewrite <- Eci; destruct s2; reflexivity).
  assert (Etqb3 : tq_bytes s3 = tq_bytes s) by (unfold tq_bytes; rewrite Etq3; reflexivity).
  unfold arep_thread. rewrite Etq3, Eca3, Ecm3, Ets3, Etqb3.
  split; [eapply rw_cells_agree'; [| exact D1]; thr_ag|].
  split; [eapply rw_cells_agree'; [| exact D2]; thr_ag|].
  split; [eapply rw_cells_agree'; [| exact D3]; thr_ag|].
  split.
  { intros c' Hc'. destruct (D4 c' Hc') as (X1 & junk & X2 & L). unfold percls_cells. rewrite !Egc3, Eci3. unfold kNumClasses in Hc'.
    split.
    - eapply rw_cells_agree'; [| exact X1]. unfold percls_cells. thr_ag.
    - exists junk. split; [| exact L]. eapply u32arr_agree; [| exact X2]. rewrite length_app, length_map. thr_ag. }
  split; [eapply rw_cells_agree'; [| exact D5]; thr_ag|].
  split.
  { apply u64arr_of_cells.
    - destruct D6 as [_ W6]. eapply wr_at_transport; [| exact WM]. unfold tstats_words in *. rewrite length_map in *. cbn [length] in *. exact W6.
    - apply rh_split with (cs1 := [C8 (zw (ts_frees (as_ts s) + 1))]) in NC_thr as [N3 N4]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in N4.
      intros i w Hi.
      Ltac oldw D6 i := eapply rw_cells_agree'; [| exact (u64arr_cell segs _ _ _ i _ D6 eq_refl)]; thr_ag.
      do 3 (destruct i as [|i]; [cbn in Hi; injection Hi as <-; oldw D6 0%nat || oldw D6 1%nat || oldw D6 2%nat |]).
      destruct i as [|i]; [cbn in Hi; injection Hi as <-; replace (T + kThrStats + 8 * Z.of_nat 3) with (T + kThrStats + 24) by lia; exact N3|].
      destruct i as [|i]; [cbn in Hi; injection Hi as <-; replace (T + kThrStats + 8 * Z.of_nat 4) with (T + kThrStats + 24 + 8) by lia; exact N4|].
      do 9 (destruct i as [|i]; [cbn in Hi; injection Hi as <-;
        oldw D6 5%nat || oldw D6 6%nat || oldw D6 7%nat || oldw D6 8%nat || oldw D6 9%nat || oldw D6 10%nat || oldw D6 11%nat || oldw D6 12%nat || oldw D6 13%nat |]).
      destruct i; cbn in Hi; discriminate. }
  split.
  { replace (ts_by_size (ts_on_free n (as_ts s))) with (ts_by_size (as_ts s)) by reflexivity.
    eapply u64arr_agree; [| exact D7]. rewrite length_map, length_ziota. thr_ag. }
  eapply rw_cells_agree'; [| exact D8]; thr_ag.
Qed.

(* [comment removed for export] *)
Lemma repF_flip : arep_chunks segs s3 m'.
Proof.
  pose proof REP as (_ & _ & _ & _ & _ & RF & _). pose proof blk_flipped as (B1 & B2 & B3 & B4 & B5 & B6 & B7). pose proof geo as (G1 & G2 & G3 & _).
  intros cb0 cm0 H0. rewrite s3_lookup in H0. destruct (decide (cb0 = cb)) as [->|NE].
  - injection H0 as <-. destruct (RF cb cm Hcm) as [ECB (X1 & X2 & X3)]. split; [rewrite B4; exact ECB|].
    split; [| split].
    + exists b1. split; [exact HB1|]. rewrite B4, B5. unfold flipped; cbn [cm_state hdr_state hdr_alloc_id].
      rewrite <- ECB. exact NC_hdr.
    + rewrite B6, B7, B4. intros RZ. eapply rw_cells_agree'; [| exact (X2 RZ)]. intros x Hx. cbn in Hx. apply (AGmag x RZ). clear -Hx. lia.
    + unfold flipped; cbn [cm_state]. rewrite B3 || idtac. exact NC_fid.
  - destruct (RF cb0 cm0 H0) as (X0 & (b1' & Hb1' & X1) & X2 & X3). split; [exact X0|]. split; [| split].
    + exists b1'. split; [exact Hb1'|]. eapply rw_cells_agree'; [| exact X1]. intros x Hx. cbn in Hx. apply (AGcm x cb0 cm0 H0 NE). left; lia.
    + intros Hrz. eapply rw_cells_agree'; [| exact (X2 Hrz)]. intros x Hx. cbn in Hx. apply (AGcm x cb0 cm0 H0 NE). right; left; split; [exact Hrz| lia].
    + destruct (cm_state cm0) as [i|i j] eqn:ST0; [exact I|]. eapply rw_cells_agree'; [| exact X3]. intros x Hx. cbn in Hx. apply (AGcm x cb0 cm0 H0 NE). right; right. rewrite ST0. lia.
Qed.

(* [comment removed for export] *)
Lemma repJ_flip : arep_shadow segs E s3 m'.
Proof.
  pose proof REP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & RJ). pose proof geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7). pose proof geo2 as [G8 G9].
  pose proof blk_flipped as (B1 & B2 & B3 & B4 & B5 & _).
  intros g v Hg.
  destruct (Z_le_gt_dec (blk_lo cm) (8 * g)) as [LE|GT]; [destruct (Z_lt_le_dec (8 * g) (blk_hi s cm)) as [LT|GE]|].
  - (* [comment removed for export] *)
    rewrite (Sh_s3_in (8 * g) (conj LE LT)) in Hg. injection Hg as <-.
    destruct (Z_le_gt_dec ub (8 * g)) as [U1|U1]; [destruct (Z_lt_le_dec (8 * g) (ub + round_up n 8)) as [U2|U2]|].
    + (* [comment removed for export] *)
      unfold chunk_shadow. rewrite B3, B5. replace (cm_state (flipped cm aid fid)) with (CQuarantined aid fid) by reflexivity.
      replace (8 * g <? ub) with false by (symmetry; apply Z.ltb_ge; exact U1).
      replace (8 * g <? ub + round_up n 8) with true by (symmetry; apply Z.ltb_lt; exact U2).
      replace (kShadowBase + g) with (kShadowBase + ub / 8 + (g - ub / 8)) by lia.
      apply (CB_byte segs m' (kShadowBase + ub / 8) (Z.to_nat l8) (zb kAsanHeapFreeMagic) (g - ub / 8) NC_sh).
      clear -U1 U2 G4 G6. Z.div_mod_to_equations. lia.
    + (* [comment removed for export] *)
      assert (EQ : chunk_shadow (flipped cm aid fid) (8 * g) = chunk_shadow cm (8 * g)).
      { unfold chunk_shadow. rewrite B3, B5, ST. replace (cm_state (flipped cm aid fid)) with (CQuarantined aid fid) by reflexivity.
        replace (8 * g <? ub) with false by (symmetry; apply Z.ltb_ge; exact U1).
        replace (8 * g <? ub + round_up n 8) with false by (symmetry; apply Z.ltb_ge; exact U2).
        replace (8 * g <? ub + n / 8 * 8) with false by (symmetry; apply Z.ltb_ge; clear -U2 G7; Z.div_mod_to_equations; lia).
        replace (8 * g <? ub + n) with false by (symmetry; apply Z.ltb_ge; clear -U2 G7; lia). reflexivity. }
      rewrite EQ. pose proof (block_Sh E [] [] s cb cm (8 * g) WF Hcm (conj LE LT)) as Hs.
      eapply rw_cells_agree'; [| exact (RJ g _ Hs)]. intros x Hx. cbn in Hx. replace x with (kShadowBase + g) by lia. apply (AGsh_out g _ Hs). right. clear -U2 G6. lia.
    + assert (EQ : chunk_shadow (flipped cm aid fid) (8 * g) = chunk_shadow cm (8 * g)).
      { unfold chunk_shadow. rewrite B3, B5, ST. replace (cm_state (flipped cm aid fid)) with (CQuarantined aid fid) by reflexivity.
        replace (8 * g <? ub) with true by (symmetry; apply Z.ltb_lt; clear -U1; lia). reflexivity. }
      rewrite EQ. pose proof (block_Sh E [] [] s cb cm (8 * g) WF Hcm (conj LE LT)) as Hs.
      eapply rw_cells_agree'; [| exact (RJ g _ Hs)]. intros x Hx. cbn in Hx. replace x with (kShadowBase + g) by lia. apply (AGsh_out g _ Hs). left. clear -U1 G4. Z.div_mod_to_equations. lia.
  - rewrite (Sh_s3_out (8 * g) ltac:(clear -GE; lia)) in Hg.
    eapply rw_cells_agree'; [| exact (RJ g v Hg)]. intros x Hx. cbn in Hx. replace x with (kShadowBase + g) by lia. apply (AGsh_out g v Hg). right. clear -GE G8 G6. lia.
  - rewrite (Sh_s3_out (8 * g) ltac:(clear -GT; lia)) in Hg.
    eapply rw_cells_agree'; [| exact (RJ g v Hg)]. intros x Hx. cbn in Hx. replace x with (kShadowBase + g) by lia. apply (AGsh_out g v Hg). left. unfold blk_lo in GT, G1. clear -GT G1 G4. Z.div_mod_to_equations. lia.
Qed.

Theorem ARep_after_flip : AREP s3 m'.
Proof.
  pose proof REP as (RA & RB & RC & _ & RE & RF & RG & RH & RI & _).
  apply (ARep_xfer9 s s3 m'); try (unfold s3; first [rewrite <- Eregions| rewrite <- Eptr| rewrite <- Esec| rewrite <- Estats| rewrite <- Ega| rewrite <- Egm| rewrite <- Etq| rewrite <- Egq| rewrite <- Eia]; destruct s2; reflexivity).
  - exact (frameA' segs E s m m' AGimg RA).
  - exact (frameB' segs E s m m' AGri RB).
  - exact (frameC' segs E s m m' WM AGfa RC).
  - exact repD_flip.
  - exact (frameE' segs E s m m' WM AGptr AGsec RE).
  - exact repF_flip.
  - exact (frameG' segs s m m' AGbat RG).
  - unfold arep_depot. destruct DEP2 as [DI DR]. split.
    + unfold s3. revert DI. clear. unfold depot_inv, depot_n_ids, dphi. destruct s2; cbn; exact (fun H => H).
    + unfold s3. revert DR. clear. unfold DepotRep, depot_hashes, depot_keys, node_blocks, store_blocks, node_addr. destruct s2; cbn; exact (fun H => H).
  - exact (frameI' segs E s m m' WM AGimg RI).
  - exact repJ_flip.
Qed.
End FLIP.
End RFL.
End RC__1.
