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
  AsanWf1 AsanWf3 AsanWf4 AsanWf5 AsanWf6 AsanClient AsanRepFrame AsanRepFrame2 AsanBudget AsanHit AsanRepHitB AsanRepX AsanRepCaB AsanRepSecB AsanRepRefillB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section REN.
Variable segs : list Segment.
Variable E : aenv.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).
#[warnings="-notation-for-abbreviation"] Notation RW := (rw_cells segs).
#[warnings="-notation-for-abbreviation"] Notation SB := (ae_space_beg E).
#[warnings="-notation-for-abbreviation"] Notation T := (ae_thread E).
#[warnings="-notation-for-abbreviation"] Notation RI := (ae_region_info E).
#[warnings="-notation-for-abbreviation"] Notation PA := (ae_ptr_array E).
#[warnings="-notation-for-abbreviation"] Notation AREP := (ARep segs E (DepotR segs E)).

Definition enq1_st (a : astate) (l : list batch) (b : batch) (cb n : Z) : astate :=
  upd_tq (fun _ => l ++ [mkBatch (b_addr b) (b_items b ++ [cb]) (b_size b + n)]) a.

(* [comment removed for export] *)
Definition renv_ok (a : astate) : Prop :=
     blocks_sep E a
  /\ ((0x1000 <= T /\ (T + 4096 <= 0x10000 \/ 0x603000 <= T)) /\ T + 4096 <= alloc_ceiling)
  /\ (forall r, In r (arep_img_ranges E ++ depot_static E) -> fst (ae_img E) <= fst r /\ fst r + snd r <= fst (ae_img E) + snd (ae_img E))
  /\ 0x10000 <= fst (ae_img E)
  /\ (forall r, In r (arep_img_ranges E ++ depot_static E) -> 0x10000 <= fst r /\ fst r + snd r <= 0x603000)
  /\ (forall x y, In x (arep_img_ranges E) -> In y (depot_static E) -> fst x + snd x <= fst y \/ fst y + snd y <= fst x)
  /\ (exists mo, AKern E a mo)
  /\ (T + 4096 <= ae_depot_nodes E \/ ae_depot_nodes E + kDepotNodeBlockBytes <= T)
  /\ (ae_depot_nodes E + kDepotNodeBlockBytes <= ae_ptr_array E \/ ae_ptr_array E + kPtrArrayLen <= ae_depot_nodes E).

Definition FPWe1 (lo ba bcnt : Z) (z : Z) : Prop :=
  lo <= z \/ (ba + 8 <= z < ba + 24) \/ (ba + 24 + 8 * bcnt <= z < ba + 24 + 8 * bcnt + 8) \/ (T + kThrQCache + 24 <= z < T + kThrQCache + 32).

(* [comment removed for export] *)
Lemma ARep_tq_xfer : forall s s' m,
  as_regions s' = as_regions s -> as_cache_inited s' = as_cache_inited s -> as_cache s' = as_cache s ->
  as_ptr_committed s' = as_ptr_committed s -> as_sec s' = as_sec s -> as_sec_stale s' = as_sec_stale s -> as_sec_stats s' = as_sec_stats s ->
  as_glob_allocated s' = as_glob_allocated s -> as_glob_mapped s' = as_glob_mapped s -> as_oom s' = as_oom s ->
  as_chunks s' = as_chunks s -> as_dead s' = as_dead s -> as_gq s' = as_gq s ->
  as_keys s' = as_keys s -> as_frames s' = as_frames s -> as_ia_inited s' = as_ia_inited s ->
  as_node_blocks s' = as_node_blocks s -> as_store_blocks s' = as_store_blocks s -> as_store_stored s' = as_store_stored s -> as_ndepot_ins s' = as_ndepot_ins s ->
  arep_instance segs E s m -> arep_regioninfo segs E s m -> arep_region_mem segs E s m -> arep_thread segs E s' m ->
  arep_secondary segs E s m -> arep_chunks segs s m -> arep_batches segs s' m -> arep_depot (DepotR segs E) s m ->
  arep_globals segs E s m -> arep_shadow segs E s m -> AREP s' m.
Proof.
  intros s s' m. destruct s, s'; cbn. intros -> -> -> -> -> -> -> -> -> -> -> -> -> -> -> -> -> -> -> ->.
  intros RA RB RC RD' RE RF RG RH RI RJ.
  split; [exact RA|]. split; [exact RB|]. split; [exact RC|]. split; [exact RD'|]. split; [exact RE|]. split; [exact RF|].
  split; [exact RG|]. split; [exact RH|]. split; [exact RI| exact RJ].
Qed.

(* [comment removed for export] *)
Section WFS.
Variables (P : list Z) (s : astate) (cb n : Z).
Hypothesis PEND : pending s cb n.
Hypothesis WF : AWf E (cb :: P) [] s.
Hypothesis RENV : renv_ok s.

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
Lemma fp_range : forall a, arep_fp E (DepotFP E) s a -> 0 <= a < alloc_ceiling.
Proof.
  intros a Ha. split; [| exact (fp_below_ceiling E (DepotFP E) (cb :: P) [] IMG_IN (DepotFP_where E) s a WF BS Ha)].
  destruct (fp_locate E (DepotFP E) (cb :: P) [] IMG_IN (DepotFP_where E) s a WF BS Ha) as [X|[[X _]|[X _]]].
  - destruct X as (r0 & Hr & R). pose proof (IMG_IN r0 Hr). clear -R H IMG_LO. lia.
  - pose proof (sh_band_below_ceiling a X). rewrite kLowAppEnd_val in *. clear -H. lia.
  - unfold app_addr in X. rewrite kHighMemBeg_val in X. clear -X. lia.
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

(* [comment removed for export] *)
Lemma CS24 : class_size kBatchClass = 8192. Proof. reflexivity. Qed.
Lemma bat_range : forall b0, In b0 (as_tq s ++ as_gq s) ->
  SB + kBatchClass * kRegionSize <= b_addr b0 /\ b_addr b0 + 8192 <= SB + kBatchClass * kRegionSize + rg_mapped_user (region_of s kBatchClass) /\ carved E s kBatchClass (b_addr b0).
Proof.
  intros b0 Hb0. pose proof WF as (WE & [_ WR] & _ & _ & (WQ1 & _) & _).
  destruct (WQ1 b0 Hb0) as [(CV & _) _]. pose proof CV as (k & Hk & Hab & Hk1).
  destruct (WR kBatchClass ltac:(unfold kBatchClass, kLargestClassID; lia)) as (Q1 & _). cbv zeta in Q1. unfold region_of in *.
  rewrite CS24 in *. unfold region_beg in Hab. split; [| split; [| exact CV]]; rewrite Hab; clear -Hk Hk1 Q1; nia.
Qed.
Lemma ublk_facts : forall x0 a, SB + kBatchClass * kRegionSize <= x0 -> x0 + 8192 <= SB + kBatchClass * kRegionSize + rg_mapped_user (region_of s kBatchClass) -> x0 <= a < x0 + 8192 ->
  0 <= a < alloc_ceiling /\ ~ (kLowAppEnd <= a < kHighMemBeg) /\ ~ (T <= a < T + 4096)
  /\ (forall x, In x (arep_img_ranges E ++ depot_static E) -> ~ (fst x <= a < fst x + snd x))
  /\ ~ (PA <= a < PA + 0x800000)
  /\ (forall sc, In sc (as_sec s) -> ~ (sc_map_beg sc <= a < sc_map_beg sc + sc_map_size sc))
  /\ (forall bb len, (In bb (ae_depot_nodes E :: as_node_blocks s) /\ len = kDepotNodeBlockBytes) \/ (In bb (ae_store_blk E :: as_store_blocks s) /\ len = kStoreBlockBytes) ->
        ~ (bb <= a < bb + len))
  /\ ~ (RI <= a < RI + kRegSize * kNumClasses)
  /\ (forall c', 0 <= c' < kNumClasses -> ~ (free_array SB c' <= a < free_array SB c' + rg_mapped_fa (region_of s c'))).
Proof.
  intros x0 a R1 R2 Ha. pose proof WF as (WE & [WR0 WR] & _ & _ & _ & (_ & _ & S3 & _) & _).
  pose proof alloc_ceiling_range as CR. destruct AK as [mo K].
  pose proof WE as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & E20 & _).
  destruct (WR kBatchClass ltac:(unfold kBatchClass, kLargestClassID; lia)) as (Q1 & _ & Q3 & _). cbv zeta in Q1, Q3.
  pose proof (RG_any E (cb :: P) [] s WF) as RG.
  rewrite kHighMemBeg_val in E2. rewrite kLowAppEnd_val, kHighMemBeg_val. unfold kBatchClass, kRegionSize, kFreeArrayOffset, kSpaceSize, kResvLen in *.
  assert (SP : ae_resv_beg E <= a < ae_resv_beg E + 0x2000011000 /\ SB <= a < SB + 2^37) by (clear -Ha R1 R2 Q1 Q3 E3 E4; lia).
  destruct SP as [SP1 SP2].
  split; [clear -Ha R1 E2 E3 E5 SP1; lia|]. split; [clear -SP2 E2 E3; lia|]. split; [clear -SP1 E19; lia|]. split.
  { intros x Hx Rx. pose proof (IMG_LOW x Hx) as [L1 L2]. clear -SP2 E2 E3 Rx L2. lia. }
  split; [clear -SP1 E20; lia|]. split.
  { intros sc Hsc Rs. destruct (S3 sc Hsc) as (_ & _ & _ & _ & _ & _ & SR). pose proof (SR _ E7) as X. cbn [fst snd] in X. clear -SP1 Rs X. lia. }
  split.
  { pose proof (BS (ae_depot_nodes E) kDepotNodeBlockBytes (or_introl (conj (or_introl eq_refl) eq_refl))) as (_ & _ & DNR & _).
    pose proof (ak_store_sep _ _ _ K) as (SBR & _).
    intros bb len [[[<-|Hbb] ->]|[[<-|Hbb] ->]].
    - clear -SP1 DNR. lia.
    - destruct (ak_blocks_sep _ _ _ K bb kDepotNodeBlockBytes (or_introl (conj Hbb eq_refl))) as (_ & _ & _ & BR & _). unfold kResvLen in BR. clear -SP1 BR. lia.
    - unfold kResvLen, kStoreBlockBytes in *. clear -SP1 SBR. lia.
    - destruct (ak_blocks_sep _ _ _ K bb kStoreBlockBytes (or_intror (conj Hbb eq_refl))) as (_ & _ & _ & BR & _). unfold kResvLen, kStoreBlockBytes in *. clear -SP1 BR. lia. }
  split; [unfold ae_region_info, kRegSize, kNumClasses, kSpaceSize; clear -SP2; lia|].
  intros c' Hc' Rf. unfold kNumClasses in Hc'. pose proof (RG c' Hc') as [_ [G3 G4]]. unfold free_array, region_beg, kRegionSize, kFreeArrayOffset, kFreeArraySize in *.
  clear -Ha R1 R2 Q1 Q3 Hc' G3 G4 Rf. lia.
Qed.

Lemma bat_facts : forall b0 a, In b0 (as_tq s ++ as_gq s) -> b_addr b0 <= a < b_addr b0 + 8192 ->
  0 <= a < alloc_ceiling /\ ~ (kLowAppEnd <= a < kHighMemBeg) /\ ~ (T <= a < T + 4096)
  /\ (forall x, In x (arep_img_ranges E ++ depot_static E) -> ~ (fst x <= a < fst x + snd x))
  /\ ~ (PA <= a < PA + 0x800000)
  /\ (forall sc, In sc (as_sec s) -> ~ (sc_map_beg sc <= a < sc_map_beg sc + sc_map_size sc))
  /\ (forall bb len, (In bb (ae_depot_nodes E :: as_node_blocks s) /\ len = kDepotNodeBlockBytes) \/ (In bb (ae_store_blk E :: as_store_blocks s) /\ len = kStoreBlockBytes) ->
        ~ (bb <= a < bb + len))
  /\ ~ (RI <= a < RI + kRegSize * kNumClasses)
  /\ (forall c', 0 <= c' < kNumClasses -> ~ (free_array SB c' <= a < free_array SB c' + rg_mapped_fa (region_of s c'))).
Proof. intros b0 a Hb0 Ha. pose proof (bat_range b0 Hb0) as (R1 & R2 & _). exact (ublk_facts (b_addr b0) a R1 R2 Ha). Qed.

(* [comment removed for export] *)
Lemma bat_vs_chunk : forall b0 cb' cm' a, In b0 (as_tq s ++ as_gq s) -> as_chunks s !! cb' = Some cm' -> chunk_meta_fp cm' a ->
  ~ (b_addr b0 <= a < b_addr b0 + 8192).
Proof.
  intros b0 cb' cm' a Hb0 H' FPa R. pose proof WF as (WE & WR & _ & _ & WQ & _).
  pose proof (chunk_meta_in_block E (cb :: P) [] s cb' cm' a WF H' FPa) as [B1 B2].
  destruct (batch_block E [] s b0 WQ ltac:(unfold all_batches; rewrite app_assoc; apply in_app_iff; left; exact Hb0)) as (CV & _ & _ & NCB).
  assert (HB24 : 1 <= kBatchClass <= kLargestClassID) by (unfold kBatchClass, kLargestClassID; lia).
  destruct (block_where E (cb :: P) [] s cb' cm' WF H') as [(J1 & J2 & c & Hc & PR & CVc & _ & _ & SP)|(sc & Hsc & _ & L1 & L2)]; unfold blk_lo in *.
  - destruct (carved_blocks_disjoint E s c (cm_alloc_beg cm') kBatchClass (b_addr b0) Hc HB24 WR CVc CV) as [[_ EQ]|D].
    + apply NCB. exists cb', cm'. split; [exact H'| exact EQ].
    + rewrite CS24 in D. clear -B1 B2 R D SP. lia.
  - destruct (bat_facts b0 a Hb0 R) as (_ & _ & _ & _ & _ & NS & _). apply (NS sc Hsc). unfold kPageSize in L1. clear -B1 B2 L1 L2. lia.
Qed.
Lemma bat_vs_bat : forall b1 b2 a, In b1 (as_tq s ++ as_gq s) -> In b2 (as_tq s ++ as_gq s) -> b_addr b1 <> b_addr b2 ->
  b_addr b1 <= a < b_addr b1 + 8192 -> ~ (b_addr b2 <= a < b_addr b2 + 8192).
Proof.
  intros b1 b2 a H1 H2 NE R1 R2. pose proof WF as (WE & WR & _).
  pose proof (bat_range b1 H1) as (_ & _ & C1). pose proof (bat_range b2 H2) as (_ & _ & C2).
  assert (HB24 : 1 <= kBatchClass <= kLargestClassID) by (unfold kBatchClass, kLargestClassID; lia).
  destruct (carved_blocks_disjoint E s kBatchClass (b_addr b1) kBatchClass (b_addr b2) HB24 HB24 WR C1 C2) as [[_ EQ]|D]; [exact (NE EQ)|].
  rewrite CS24 in D. clear -R1 R2 D. lia.
Qed.

Section ENQ1.
Variables (m m' : mem) (lo : Z) (l : list batch) (b : batch).
#[warnings="-notation-for-abbreviation"] Notation bcnt := (zlen (b_items b)).
#[warnings="-notation-for-abbreviation"] Notation ba := (b_addr b).
#[warnings="-notation-for-abbreviation"] Notation s' := (enq1_st s l b cb n).
Hypothesis TQ : as_tq s = l ++ [b].
Hypothesis ROOMb : bcnt < kBatchCap.
Hypothesis REP : AREP s m.
Hypothesis WM : wmono segs m m'.
Hypothesis AG : forall z, 0 <= z < 2^64 -> ~ FPWe1 lo ba bcnt z -> m' (wa z) = m (wa z).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis NC_qb : RW m' (T + kThrQCache + 24) [C8 (zw (tq_bytes s + n))].
Hypothesis NC_hdr : RW m' (ba + 8) [C8 (zw (b_size b + n)); C8 (zw (bcnt + 1))].
Hypothesis NC_item : RW m' (ba + 24 + 8 * bcnt) [C8 (zw cb)].

Lemma Hb : In b (as_tq s ++ as_gq s).
Proof. apply in_app_iff. left. rewrite TQ. apply in_app_iff. right. left. reflexivity. Qed.

(* [comment removed for export] *)
Lemma enq1_tq : as_tq s' = l ++ [mkBatch ba (b_items b ++ [cb]) (b_size b + n)]. Proof. destruct s; reflexivity. Qed.
Lemma enq1_gq : as_gq s' = as_gq s. Proof. destruct s; reflexivity. Qed.
Lemma enq1_tq_bytes : tq_bytes s' = tq_bytes s + n.
Proof. unfold tq_bytes. rewrite enq1_tq, TQ, !qbytes_app. cbn [qbytes fold_right b_size]. lia. Qed.

(* [comment removed for export] *)
Lemma AG_fp : forall a, arep_fp E (DepotFP E) s a -> ~ (T <= a < T + 4096) -> ~ (ba <= a < ba + 8192) -> m' (wa a) = m (wa a).
Proof.
  intros a Ha NT NB. pose proof (fp_range a Ha) as BC'. pose proof alloc_ceiling_range as CR.
  pose proof ROOMb as RB. unfold kBatchCap in RB. assert (Z0 : 0 <= zlen (b_items b)) by (unfold zlen; clear; lia).
  apply AG; [clear -BC' CR; lia|]. unfold FPWe1. unfold kThrQCache. clear -NT NB BC' LO RB Z0. lia.
Qed.

Lemma AGimg : forall a, in_ranges (arep_img_ranges E) a -> m' (wa a) = m (wa a).
Proof.
  intros a (x & Hx & R). pose proof Tpl as [[T1 T2] T3].
  assert (Hx' : In x (arep_img_ranges E ++ depot_static E)) by (apply in_app_iff; left; exact Hx).
  pose proof (IMG_LOW x Hx') as [L1 L2].
  apply AG_fp; [left; exists x; split; [exact Hx| exact R]| clear -R L1 L2 T1 T2; lia|].
  intros Rb. destruct (bat_facts b a Hb Rb) as (_ & _ & _ & NI & _). exact (NI x Hx' R).
Qed.
Lemma AGri : forall a, RI <= a < RI + kRegSize * kNumClasses -> m' (wa a) = m (wa a).
Proof.
  intros a Ha. apply AG_fp; [right; left; exact Ha| | intros Rb; destruct (bat_facts b a Hb Rb) as (_ & _ & _ & _ & _ & _ & _ & NR & _); exact (NR Ha)].
  intros HT. destruct (Tpage_apart a HT) as (NR & _). apply NR. pose proof (proj1 WF) as (_ & _ & E3 & E4 & _).
  unfold ae_region_info, kRegSize, kNumClasses, kSpaceSize in *. clear -Ha E3 E4. lia.
Qed.
Lemma AGfa : forall a c', 0 <= c' < kNumClasses -> free_array SB c' <= a < free_array SB c' + rg_mapped_fa (region_of s c') -> m' (wa a) = m (wa a).
Proof.
  intros a c' Hc Ha. apply AG_fp; [do 3 right; left; exists c'; split; [exact Hc| exact Ha]| | intros Rb; destruct (bat_facts b a Hb Rb) as (_ & _ & _ & _ & _ & _ & _ & _ & NF); exact (NF c' Hc Ha)].
  assert (RM : in_some_region_map E s a = true).
  { unfold in_some_region_map. apply Bool.orb_true_iff. right. apply existsb_exists. exists c'. split; [apply In_ziota; unfold kNumClasses in Hc; lia|].
    apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; lia. }
  pose proof (region_map_in_space E (cb :: P) [] s a WF RM) as SP. intros HT. destruct (Tpage_apart a HT) as (NR & _). apply NR.
  pose proof (proj1 WF) as (_ & _ & E3 & E4 & _). unfold kSpaceSize in *. clear -SP E3 E4. lia.
Qed.
Lemma AGptr : forall a, PA <= a < PA + 8 * kChunksBlockCount -> m' (wa a) = m (wa a).
Proof.
  intros a Ha. unfold kChunksBlockCount in Ha. apply AG_fp; [do 4 right; left; unfold kChunksBlockCount; exact Ha| | intros Rb; destruct (bat_facts b a Hb Rb) as (_ & _ & _ & _ & NP & _); apply NP; clear -Ha; lia].
  intros HT. destruct (Tpage_apart a HT) as (_ & NP & _). clear -Ha NP. lia.
Qed.
Lemma AGsec : forall a sc, In sc (as_sec s) -> sc_map_beg sc <= a < sc_map_beg sc + 32 -> m' (wa a) = m (wa a).
Proof.
  intros a sc Hsc Ha. pose proof WF as (WE & _ & _ & _ & _ & (_ & _ & S3 & _) & _). destruct (S3 sc Hsc) as (_ & _ & _ & POS & MODS & _).
  pose proof (AsanRepFrame.pos_mod_ge E (sc_map_size sc) kPageSize POS MODS ltac:(unfold kPageSize; lia)) as GE. unfold kPageSize in GE.
  apply AG_fp; [do 5 right; left; exists sc; split; [exact Hsc| exact Ha]| |].
  - intros HT. destruct (Tpage_apart a HT) as (_ & _ & NS & _). apply (NS sc Hsc). clear -Ha GE. lia.
  - intros Rb. destruct (bat_facts b a Hb Rb) as (_ & _ & _ & _ & _ & NS & _). apply (NS sc Hsc). clear -Ha GE. lia.
Qed.
Lemma AGcm : forall a cb' cm', as_chunks s !! cb' = Some cm' -> chunk_meta_fp cm' a -> m' (wa a) = m (wa a).
Proof.
  intros a cb' cm' Hcm Ha. pose proof (chunk_meta_in_block E (cb :: P) [] s cb' cm' a WF Hcm Ha) as [BL BU].
  apply AG_fp; [do 6 right; left; exists cb', cm'; split; [exact Hcm| exact Ha]| | exact (bat_vs_chunk b cb' cm' a Hb Hcm Ha)].
  intros HT. destruct (Tpage_apart a HT) as (NR & _ & NS & _).
  destruct (block_where E (cb :: P) [] s cb' cm' WF Hcm) as [(J1 & J2 & _)|(sc & Hsc & _ & L1 & L2)]; unfold blk_lo in *.
  - apply NR. pose proof (proj1 WF) as (_ & _ & E3 & E4 & _). unfold kSpaceSize in *. clear -BL BU J1 J2 E3 E4. lia.
  - apply (NS sc Hsc). unfold kPageSize in L1. clear -BL BU L1 L2. lia.
Qed.
(* [comment removed for export] *)
Lemma AGbat : forall a b0, In b0 (as_tq s ++ as_gq s) -> b_addr b0 <> ba -> b_addr b0 <= a < b_addr b0 + 24 + 8 * kBatchCap -> m' (wa a) = m (wa a).
Proof.
  intros a b0 Hb0 NE Ha. unfold kBatchCap in Ha.
  apply AG_fp; [do 7 right; left; exists b0; split; [exact Hb0| unfold kBatchCap; exact Ha]| | exact (bat_vs_bat b0 b a Hb0 Hb NE ltac:(clear -Ha; lia))].
  intros HT. destruct (bat_facts b0 a Hb0 ltac:(clear -Ha; lia)) as (_ & _ & NT & _). exact (NT HT).
Qed.
Lemma AGdep : forall a, DepotFP E s a -> m' (wa a) = m (wa a).
Proof.
  intros a Ha. pose proof Tpl as [[T1 T2] T3]. pose proof (proj1 WF) as (E1 & E2 & _). rewrite kHighMemBeg_val in E2.
  assert (FPa : arep_fp E (DepotFP E) s a) by (do 8 right; left; exact Ha).
  destruct (DepotFP_where E s a Ha) as [(x & Hx & R)|[(bb & Hbb & R)|(bb & Hbb & R)]].
  - assert (Hx' : In x (arep_img_ranges E ++ depot_static E)) by (apply in_app_iff; right; exact Hx).
    pose proof (IMG_LOW x Hx') as [L1 L2].
    apply AG_fp; [exact FPa| clear -R L1 L2 T1 T2; lia| intros Rb; destruct (bat_facts b a Hb Rb) as (_ & _ & _ & NI & _); exact (NI x Hx' R)].
  - apply AG_fp; [exact FPa| | intros Rb; destruct (bat_facts b a Hb Rb) as (_ & _ & _ & _ & _ & _ & NB & _); exact (NB bb kDepotNodeBlockBytes (or_introl (conj Hbb eq_refl)) R)].
    intros HT. destruct (Tpage_apart a HT) as (_ & _ & _ & NB & _). exact (NB bb kDepotNodeBlockBytes (or_introl (conj Hbb eq_refl)) R).
  - apply AG_fp; [exact FPa| | intros Rb; destruct (bat_facts b a Hb Rb) as (_ & _ & _ & _ & _ & _ & NB & _); exact (NB bb kStoreBlockBytes (or_intror (conj Hbb eq_refl)) R)].
    intros HT. destruct (Tpage_apart a HT) as (_ & _ & _ & NB & _). exact (NB bb kStoreBlockBytes (or_intror (conj Hbb eq_refl)) R).
Qed.
Lemma AGsh : forall g v, Sh E s (8 * g) = Some v -> m' (wa (kShadowBase + g)) = m (wa (kShadowBase + g)).
Proof.
  intros g v Hg. pose proof (AsanRepRefillB.Sh_granule_range segs E (cb :: P) [] s s m m' lo kBatchClass O) as GR0 || idtac.
  assert (GR : 0 <= 8 * g < 2^47).
  { pose proof WF as WF0. pose proof alloc_ceiling_range as CR. unfold Sh in Hg.
    destruct (in_some_region_map E s (8 * g)) eqn:RM.
    - pose proof (region_map_in_space E (cb :: P) [] s (8 * g) WF0 RM) as SP. pose proof (proj1 WF0) as (E1 & E2 & E3 & E4 & E5 & _).
      unfold kSpaceSize in *. clear -SP E2 E3 E4 E5 CR. rewrite kHighMemBeg_val in E2. lia.
    - destruct (in_some_sec_map s (8 * g)) eqn:SM.
      + unfold in_some_sec_map in SM. apply existsb_exists in SM as (sc & Hsc & Hb0). apply andb_true_iff in Hb0 as [B1 B2].
        apply Z.leb_le in B1. apply Z.ltb_lt in B2. pose proof WF0 as (_ & _ & _ & _ & _ & (_ & _ & S3 & _) & _). destruct (S3 sc Hsc) as (_ & HB & S & _).
        unfold app_mem in HB. rewrite kHighMemBeg_val, kLowAppEnd_val in HB. clear -B1 B2 HB S CR. lia.
      + cbn [orb] in Hg. destruct (sh_default_dom E (8 * g) && negb (sh_excluded E (8 * g))) eqn:C; [|discriminate].
        apply andb_true_iff in C as [C _]. unfold sh_default_dom in C. apply Bool.orb_true_iff in C as [C|C].
        * apply andb_true_iff in C as [C _]. apply andb_true_iff in C as [C1 C2]. apply Z.leb_le in C1. apply Z.ltb_lt in C2.
          rewrite kLowAppEnd_val in C2. clear -C1 C2. lia.
        * apply andb_true_iff in C as [C1 C2]. apply Z.leb_le in C1. apply Z.leb_le in C2.
          rewrite kHighMemBeg_val in C1. unfold kHighMemEnd in C2. clear -C1 C2. lia. }
  assert (BAND : kLowAppEnd < kShadowBase + g < kHighMemBeg) by (rewrite kLowAppEnd_val, kHighMemBeg_val; unfold kShadowBase; clear -GR; lia).
  apply AG_fp; [do 9 right; exists g, v; split; [reflexivity| exact Hg]| |].
  - intros HT. destruct (Tpage_apart _ HT) as (_ & _ & _ & _ & NBAND & _). apply NBAND. exact BAND.
  - intros Rb. destruct (bat_facts b _ Hb Rb) as (_ & NB & _). apply NB. clear -BAND. lia.
Qed.
(* [comment removed for export] *)
Lemma AGthr_cells : forall A k, T <= A -> A + k <= T + 4096 -> (A + k <= T + kThrQCache + 24 \/ T + kThrQCache + 32 <= A) -> agree_on m m' A k.
Proof.
  intros A k H0 H1 H2 z Hz. pose proof Tpl as [[T1 T2] T3]. pose proof alloc_ceiling_range as CR.
  destruct (bat_facts b ba Hb ltac:(clear; lia)) as (_ & _ & NT & _).
  pose proof (bat_range b Hb) as (R1 & R2 & _).
  apply AG; [clear -Hz H0 H1 T1 T3 CR; lia|]. unfold FPWe1. pose proof ROOMb as RB. unfold kBatchCap in RB. assert (Z0 : 0 <= zlen (b_items b)) by (unfold zlen; clear; lia).
  assert (NTz : ~ (ba <= z < ba + 8192)).
  { intros C. destruct (bat_facts b z Hb C) as (_ & _ & NT' & _). apply NT'. clear -Hz H0 H1. lia. }
  clear -Hz H0 H1 H2 T3 LO RB Z0 NTz. lia.
Qed.
Ltac thr_ag := apply AGthr_cells; unfold kThrUnwinding, kThrCache, kThrCacheStats, kThrStats, kPerClassSize, kThrStackTop, kThrQCache, kNumClasses in *;
  cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]; try lia.

(* [comment removed for export] *)
Lemma repD_enq1 : arep_thread segs E s' m'.
Proof.
  pose proof REP as (_ & _ & _ & RD & _). destruct RD as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8).
  unfold arep_thread. rewrite enq1_tq_bytes, enq1_tq.
  replace (as_cache_allocated s') with (as_cache_allocated s) by (destruct s; reflexivity).
  replace (as_cache_mapped s') with (as_cache_mapped s) by (destruct s; reflexivity).
  replace (as_ts s') with (as_ts s) by (destruct s; reflexivity).
  split; [eapply rw_cells_agree'; [| exact D1]; thr_ag|].
  split; [eapply rw_cells_agree'; [| exact D2]; thr_ag|].
  split.
  { rewrite TQ in D3.
    replace (qcount (l ++ [mkBatch ba (b_items b ++ [cb]) (b_size b + n)])) with (qcount (l ++ [b])) by (unfold qcount; rewrite !length_app; reflexivity).
    replace (list_first (l ++ [mkBatch ba (b_items b ++ [cb]) (b_size b + n)])) with (list_first (l ++ [b])) by (destruct l; reflexivity).
    replace (list_last (l ++ [mkBatch ba (b_items b ++ [cb]) (b_size b + n)])) with (list_last (l ++ [b])) by (unfold list_last; rewrite !last_last; destruct l; reflexivity).
    apply rh_split with (cs1 := [C8 (zw (qcount (l ++ [b]))); C8 (zw (list_first (l ++ [b]))); C8 (zw (list_last (l ++ [b])))]) in D3. destruct D3 as [D3 _].
    apply (rh_join_at segs m' _ (T + kThrQCache + 24) [C8 (zw (qcount (l ++ [b]))); C8 (zw (list_first (l ++ [b]))); C8 (zw (list_last (l ++ [b])))]); [| exact NC_qb| cbn; lia].
    eapply rw_cells_agree'; [| exact D3]. thr_ag. }
  split.
  { intros c' Hc'. destruct (D4 c' Hc') as (X1 & junk & X2 & L). unfold percls_cells in *.
    replace (get_cache s' c') with (get_cache s c') by (destruct s; reflexivity). replace (as_cache_inited s') with (as_cache_inited s) by (destruct s; reflexivity).
    unfold kNumClasses in Hc'. split.
    - eapply rw_cells_agree'; [| exact X1]. thr_ag.
    - exists junk. split; [| exact L]. eapply u32arr_agree; [| exact X2]. rewrite length_app, length_map. thr_ag. }
  split; [eapply rw_cells_agree'; [| exact D5]; thr_ag|].
  split; [eapply u64arr_agree; [| exact D6]; unfold tstats_words; rewrite length_map; cbn [length]; thr_ag|].
  split; [eapply u64arr_agree; [| exact D7]; rewrite length_map, length_ziota; thr_ag|].
  eapply rw_cells_agree'; [| exact D8]; thr_ag.
Qed.

(* [comment removed for export] *)
Lemma nodup_map_sep : forall (f : batch -> Z) l1 x l2 y, List.NoDup (map f (l1 ++ x :: l2)) -> In y (l1 ++ l2) -> f y <> f x.
Proof.
  intros f l1 x l2 y ND IN EQ. rewrite map_app in ND. cbn [map] in ND. apply NoDup_remove_2 in ND. apply ND. rewrite <- map_app, <- EQ. apply in_map. exact IN.
Qed.
Lemma NDaddr : forall b0, In b0 l \/ In b0 (as_gq s) -> b_addr b0 <> ba.
Proof.
  intros b0 Hb0. pose proof WF as (_ & _ & _ & _ & (_ & _ & ND & _) & _). unfold all_batches in ND. rewrite app_nil_r, TQ, <- app_assoc in ND. cbn [app] in ND.
  apply (nodup_map_sep b_addr l b (as_gq s) b0 ND). apply in_app_iff. exact Hb0.
Qed.

Lemma batch_list_keep : forall l0, (forall b0, In b0 l0 -> In b0 (as_tq s ++ as_gq s) /\ b_addr b0 <> ba) ->
  arep_batch_list segs s l0 m -> arep_batch_list segs s' l0 m'.
Proof.
  induction l0 as [|b0 l0 IH]; intros SUB H; [exact I|]. destruct H as [[X1 (junk & X2 & L)] H2].
  destruct (SUB b0 ltac:(left; reflexivity)) as [Hb0 NA].
  pose proof (f_equal Z.of_nat L) as L'. rewrite Z2Nat.id in L' by (cbv; discriminate). unfold kBatchCap in L'.
  split; [| apply IH; [intros b' Hb'; apply SUB; right; exact Hb'| exact H2]]. split.
  - eapply rw_cells_agree'; [| exact X1]. cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]. intros x Hx. apply (AGbat x b0 Hb0 NA). unfold kBatchCap. clear -Hx. lia.
  - exists junk. split; [| exact L]. eapply u64arr_agree; [| exact X2]. rewrite length_app, length_map. intros x Hx. apply (AGbat x b0 Hb0 NA). unfold kBatchCap. clear -Hx L'. lia.
Qed.

Lemma repG_enq1 : arep_batches segs s' m'.
Proof.
  pose proof REP as (_ & _ & _ & _ & _ & _ & [RG1 RG2] & _). unfold arep_batches. rewrite enq1_tq, enq1_gq. rewrite TQ in RG1.
  pose proof WF as (_ & _ & _ & _ & (WQ1 & _ & ND & _) & _).
  split.
  - (* [comment removed for export] *)
    assert (SPLIT : forall l0, (forall b0, In b0 l0 -> In b0 (as_tq s ++ as_gq s) /\ b_addr b0 <> ba) -> arep_batch_list segs s (l0 ++ [b]) m ->
              arep_batch_list segs s' (l0 ++ [mkBatch ba (b_items b ++ [cb]) (b_size b + n)]) m').
    { induction l0 as [|b0 l0 IH]; intros SUB H.
      - (* [comment removed for export] *)
        cbn [app arep_batch_list] in H |- *. destruct H as [[X1 (junk & X2 & L)] _]. split; [| exact I].
        split.
        + cbn [b_addr b_items b_size]. apply rh_split with (cs1 := [C8 (zw 0)]) in X1. destruct X1 as [X1 _].
          apply (rh_join_at segs m' _ (ba + 8) [C8 (zw 0)]); [| | cbn; lia].
          * eapply rw_cells_agree'; [| exact X1]. cbn. intros x Hx. pose proof (fp_range x ltac:(do 7 right; left; exists b; split; [exact Hb| unfold kBatchCap; clear -Hx; lia])) as BC.
            pose proof alloc_ceiling_range as CR. destruct (bat_facts b x Hb ltac:(clear -Hx; lia)) as (_ & _ & NT & _).
            apply AG; [clear -BC CR; lia|]. unfold FPWe1, kThrQCache. assert (Z0 : 0 <= zlen (b_items b)) by (unfold zlen; clear; lia). clear -Hx BC LO NT Z0. lia.
          * replace (zlen (b_items b ++ [cb])) with (zlen (b_items b) + 1) by (unfold zlen; rewrite length_app; cbn [length]; lia). exact NC_hdr.
        + cbn [b_addr b_items b_size]. destruct junk as [|j0 junk]; [exfalso; rewrite app_nil_r in X2; pose proof (f_equal Z.of_nat L) as L'; rewrite Z2Nat.id in L' by (cbv; discriminate); cbn [length] in L'; unfold zlen, kBatchCap in *; clear -L' ROOMb; lia|].
          exists junk. split; [| rewrite length_app; cbn [length] in L |- *; clear -L; lia].
          apply u64arr_of_cells.
          * destruct X2 as [_ W2]. eapply wr_at_transport; [| exact WM]. rewrite !length_app, !length_map in *. cbn [length] in *. rewrite length_app. cbn [length].
            replace (length (b_items b) + 1 + length junk)%nat with (length (b_items b) + S (length junk))%nat by lia. exact W2.
          * intros i w Hi. pose proof alloc_ceiling_range as CR. cbn [length] in L.
            rewrite map_app, <- app_assoc in Hi. cbn [map app] in Hi.
            destruct (Nat.lt_ge_cases i (length (b_items b) + S (length junk))) as [LI|GE].
            2:{ exfalso. rewrite (proj2 (nth_error_None _ _)) in Hi; [discriminate|]. rewrite length_app, length_map. cbn [length]. clear -GE. lia. }
            destruct (Nat.eq_dec i (length (b_items b))) as [->|NE].
            -- rewrite nth_error_app2 in Hi by (rewrite length_map; lia). rewrite length_map, Nat.sub_diag in Hi. cbn in Hi. injection Hi as <-.
               unfold zlen in NC_item. exact NC_item.
            -- assert (Hi' : nth_error (map zw (b_items b) ++ j0 :: junk) i = Some w).
               { destruct (Nat.lt_ge_cases i (length (b_items b))) as [LT2|GE2].
                 - rewrite nth_error_app1 in Hi |- * by (rewrite length_map; exact LT2). exact Hi.
                 - rewrite nth_error_app2 in Hi |- * by (rewrite length_map; exact GE2). rewrite length_map in Hi |- *.
                   destruct (i - length (b_items b))%nat as [|k] eqn:D; [clear -NE GE2 D; lia|]. cbn [nth_error] in Hi |- *. exact Hi. }
               eapply rw_cells_agree'; [| exact (u64arr_cell segs m _ _ i w X2 Hi')]. cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]. intros x Hx.
               pose proof (fp_range x ltac:(do 7 right; left; exists b; split; [exact Hb| unfold kBatchCap in *; clear -Hx LI L; lia])) as BC.
               destruct (bat_facts b x Hb ltac:(unfold kBatchCap in *; clear -Hx LI L; lia)) as (_ & _ & NT & _).
               apply AG; [clear -BC CR; lia|]. unfold FPWe1, kThrQCache, zlen. clear -Hx LI L NE BC LO NT. lia.
      - (* [comment removed for export] *)
        cbn [app] in H |- *. destruct H as [[X1 (junk & X2 & L)] H2]. destruct (SUB b0 ltac:(left; reflexivity)) as [Hb0 NA].
        pose proof (f_equal Z.of_nat L) as L'. rewrite Z2Nat.id in L' by (cbv; discriminate). unfold kBatchCap in L'.
        split; [| apply IH; [intros b' Hb'; apply SUB; right; exact Hb'| exact H2]].
        replace (match l0 ++ [mkBatch ba (b_items b ++ [cb]) (b_size b + n)] with [] => 0 | b' :: _ => b_addr b' end)
           with (match l0 ++ [b] with [] => 0 | b' :: _ => b_addr b' end) by (destruct l0; reflexivity).
        split.
        + eapply rw_cells_agree'; [| exact X1]. cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]. intros x Hx. apply (AGbat x b0 Hb0 NA). unfold kBatchCap. clear -Hx. lia.
        + exists junk. split; [| exact L]. eapply u64arr_agree; [| exact X2]. rewrite length_app, length_map. intros x Hx. apply (AGbat x b0 Hb0 NA). unfold kBatchCap. clear -Hx L'. lia. }
    apply SPLIT; [| exact RG1]. intros b0 Hb0. split; [apply in_app_iff; left; rewrite TQ; apply in_app_iff; left; exact Hb0| apply NDaddr; left; exact Hb0].
  - apply batch_list_keep; [| exact RG2]. intros b0 Hb0. split; [apply in_app_iff; right; exact Hb0| apply NDaddr; right; exact Hb0].
Qed.

Theorem ARep_after_enq1 : AREP s' m'.
Proof.
  pose proof REP as (RA & RB & RC & _ & RE & RF & RG & RH & RI & RJ).
  apply (ARep_tq_xfer s s' m'); try (destruct s; reflexivity).
  - exact (frameA' segs E s m m' AGimg RA).
  - exact (frameB' segs E s m m' AGri RB).
  - exact (frameC' segs E s m m' WM AGfa RC).
  - exact repD_enq1.
  - exact (frameE' segs E s m m' WM AGptr AGsec RE).
  - exact (frameF' segs s m m' AGcm RF).
  - exact repG_enq1.
  - exact (frameH' segs E s m m' WM AGdep RH).
  - exact (frameI' segs E s m m' WM AGimg RI).
  - exact (frameJ' segs E s m m' AGsh RJ).
Qed.
End ENQ1.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition bpop_st (a : astate) : astate :=
  let c := kBatchClass in let l := get_cache a c in let x := List.last l 0 in let i := Z.of_nat (Nat.pred (length l)) in
  upd_cache_allocated (fun al => al + class_size c)
    (upd_cache_stale (fun st => <[c := <[i := x]> (match st !! c with Some mm => mm | None => ∅ end)]> st)
       (set_cache c (removelast l) a)).
Definition bnew (a : astate) : Z := chunk_of_compact SB kBatchClass (List.last (get_cache a kBatchClass) 0).
Definition enq2_st (a : astate) (cb n : Z) : astate :=
  upd_tq (fun t => t ++ [mkBatch (bnew a) [cb] (kBatchSize + n)]) (bpop_st a).
Definition FPWe2 (a : astate) (lo nb : Z) (z : Z) : Prop :=
     lo <= z \/ (T + kThrQCache <= z < T + kThrQCache + 32)
  \/ (T + kThrCache + kPerClassSize * kBatchClass <= z < T + kThrCache + kPerClassSize * kBatchClass + 4)
  \/ (T + kThrCacheStats + 16 <= z < T + kThrCacheStats + 24)
  \/ (nb <= z < nb + 32)
  \/ (as_tq a <> [] /\ list_last (as_tq a) <= z < list_last (as_tq a) + 8).
  (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ARep_tqc_xfer : forall s0 s0' m,
  as_regions s0' = as_regions s0 -> as_cache_inited s0' = as_cache_inited s0 ->
  as_ptr_committed s0' = as_ptr_committed s0 -> as_sec s0' = as_sec s0 -> as_sec_stale s0' = as_sec_stale s0 -> as_sec_stats s0' = as_sec_stats s0 ->
  as_glob_allocated s0' = as_glob_allocated s0 -> as_glob_mapped s0' = as_glob_mapped s0 -> as_oom s0' = as_oom s0 ->
  as_chunks s0' = as_chunks s0 -> as_dead s0' = as_dead s0 -> as_gq s0' = as_gq s0 ->
  as_keys s0' = as_keys s0 -> as_frames s0' = as_frames s0 -> as_ia_inited s0' = as_ia_inited s0 ->
  as_node_blocks s0' = as_node_blocks s0 -> as_store_blocks s0' = as_store_blocks s0 -> as_store_stored s0' = as_store_stored s0 -> as_ndepot_ins s0' = as_ndepot_ins s0 ->
  arep_instance segs E s0 m -> arep_regioninfo segs E s0 m -> arep_region_mem segs E s0 m -> arep_thread segs E s0' m ->
  arep_secondary segs E s0 m -> arep_chunks segs s0 m -> arep_batches segs s0' m -> arep_depot (DepotR segs E) s0 m ->
  arep_globals segs E s0 m -> arep_shadow segs E s0 m -> AREP s0' m.
Proof.
  intros s0 s0' m. destruct s0, s0'; cbn. intros -> -> -> -> -> -> -> -> -> -> -> -> -> -> -> -> -> -> ->.
  intros RA RB RC RD' RE RF RG RH RI RJ.
  split; [exact RA|]. split; [exact RB|]. split; [exact RC|]. split; [exact RD'|]. split; [exact RE|]. split; [exact RF|].
  split; [exact RG|]. split; [exact RH|]. split; [exact RI| exact RJ].
Qed.

Section ENQ2.
Variables (m m' : mem) (lo : Z) (junk : list word).
#[warnings="-notation-for-abbreviation"] Notation l := (get_cache s kBatchClass).
#[warnings="-notation-for-abbreviation"] Notation nb := (bnew s).
#[warnings="-notation-for-abbreviation"] Notation tq := (as_tq s).
#[warnings="-notation-for-abbreviation"] Notation s' := (enq2_st s cb n).
#[warnings="-notation-for-abbreviation"] Notation ROW := (T + kThrCache + kPerClassSize * kBatchClass).
Hypothesis NE : l <> [].
Hypothesis CI : as_cache_inited s = true.
Hypothesis REP : AREP s m.
Hypothesis WM : wmono segs m m'.
Hypothesis AG : forall z, 0 <= z < 2^64 -> ~ FPWe2 s lo nb z -> m' (wa z) = m (wa z).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis NC_qc : RW m' (T + kThrQCache) [C8 (zw (qcount tq + 1)); C8 (zw (match tq with [] => nb | _ => list_first tq end)); C8 (zw nb); C8 (zw (tq_bytes s + (n + kBatchSize)))].
Hypothesis NC_row : RW m' ROW [C4 (zw (zlen l - 1))].
Hypothesis NC_cst : RW m' (T + kThrCacheStats + 16) [C8 (zw (as_cache_allocated s + class_size kBatchClass))].
Hypothesis NC_nbh : RW m' nb [C8 (zw 0); C8 (zw (n + kBatchSize)); C8 (zw 1)].
Hypothesis NC_nbi : u64arr segs m' (nb + 24) (zw cb :: junk).
Hypothesis LJ : length junk = 1020%nat.
Hypothesis NC_last : forall l0 b0, tq = l0 ++ [b0] -> RW m' (b_addr b0) [C8 (zw nb)].

(* [comment removed for export] *)
Ltac fld2 := unfold enq2_st, bpop_st; destruct s; reflexivity.
Lemma enq2_tq : as_tq s' = tq ++ [mkBatch nb [cb] (kBatchSize + n)]. Proof. fld2. Qed.
Lemma enq2_gq : as_gq s' = as_gq s. Proof. fld2. Qed.
Lemma enq2_cache : as_cache s' = <[kBatchClass := removelast l]> (as_cache s). Proof. fld2. Qed.
Lemma enq2_get_cache : forall c', get_cache s' c' = if decide (c' = kBatchClass) then removelast l else get_cache s c'.
Proof. intros c'. unfold get_cache at 1. rewrite enq2_cache. destruct (decide (c' = kBatchClass)) as [->|NE']; [rewrite lookup_insert_eq; reflexivity| rewrite lookup_insert_ne by congruence; reflexivity]. Qed.
Lemma enq2_cache_inited : as_cache_inited s' = as_cache_inited s. Proof. fld2. Qed.
Lemma enq2_cache_allocated : as_cache_allocated s' = as_cache_allocated s + class_size kBatchClass. Proof. fld2. Qed.
Lemma enq2_cache_mapped : as_cache_mapped s' = as_cache_mapped s. Proof. fld2. Qed.
Lemma enq2_ts : as_ts s' = as_ts s. Proof. fld2. Qed.
Lemma enq2_tq_bytes : tq_bytes s' = tq_bytes s + (kBatchSize + n).
Proof. unfold tq_bytes. rewrite enq2_tq, qbytes_app. cbn [qbytes fold_right b_size]. lia. Qed.

(* [comment removed for export] *)
Lemma HB24 : 1 <= kBatchClass <= kLargestClassID. Proof. unfold kBatchClass, kLargestClassID. lia. Qed.
Lemma x_in : In (List.last l 0) l.
Proof. destruct (removelast_facts l NE) as [EL _]. rewrite EL at 2. apply in_app_iff. right. left. reflexivity. Qed.
Lemma nb_carved : carved E s kBatchClass nb.
Proof. pose proof WF as (_ & _ & (_ & _ & WC3) & _). destruct (WC3 kBatchClass HB24) as (_ & _ & Cx). exact (proj1 (Cx _ x_in)). Qed.
Lemma nb_range : SB + kBatchClass * kRegionSize <= nb /\ nb + 8192 <= SB + kBatchClass * kRegionSize + rg_mapped_user (region_of s kBatchClass).
Proof.
  pose proof nb_carved as (k & Hk & Hab & Hk1). pose proof WF as (WE & [_ WR] & _).
  destruct (WR kBatchClass HB24) as (Q1 & _). cbv zeta in Q1. unfold region_of in *. rewrite CS24 in *. unfold region_beg in Hab. split; rewrite Hab; clear -Hk Hk1 Q1; nia.
Qed.
Lemma nb_vs_bat : forall b0 a, In b0 (as_tq s ++ as_gq s) -> b_addr b0 <= a < b_addr b0 + 8192 -> ~ (nb <= a < nb + 8192).
Proof.
  intros b0 a Hb0 R1 R2. pose proof WF as (WE & WR & _ & _ & (WQ1 & _) & _).
  destruct (WQ1 b0 Hb0) as [(CV & _ & NCC & _) _].
  destruct (carved_blocks_disjoint E s kBatchClass (b_addr b0) kBatchClass nb HB24 HB24 WR CV nb_carved) as [[_ EQ]|D].
  - apply NCC. unfold in_cache. rewrite EQ. unfold bnew, compact_of_chunk, chunk_of_compact. rewrite Z.add_simpl_l, Z.mul_comm, Z.div_mul by lia. exact x_in.
  - rewrite CS24 in D. clear -R1 R2 D. lia.
Qed.
Lemma nb_vs_chunk : forall cb' cm' a, as_chunks s !! cb' = Some cm' -> chunk_meta_fp cm' a -> ~ (nb <= a < nb + 8192).
Proof.
  intros cb' cm' a H' FPa R. pose proof WF as (WE & WR & _ & [K1 _] & _).
  pose proof (chunk_meta_in_block E (cb :: P) [] s cb' cm' a WF H' FPa) as [B1 B2].
  destruct (block_where E (cb :: P) [] s cb' cm' WF H') as [(J1 & J2 & c & Hc & PR & CVc & _ & _ & SP)|(sc & Hsc & _ & L1 & L2)]; unfold blk_lo in *.
  - destruct (carved_blocks_disjoint E s c (cm_alloc_beg cm') kBatchClass nb Hc HB24 WR CVc nb_carved) as [[-> EQ]|D].
    + destruct (K1 _ _ H') as (_ & _ & _ & PRIM & _). rewrite PR in PRIM. destruct PRIM as (_ & _ & _ & _ & NCC & _). apply NCC.
      unfold in_cache. rewrite EQ. unfold bnew, compact_of_chunk, chunk_of_compact. rewrite Z.add_simpl_l, Z.mul_comm, Z.div_mul by lia. exact x_in.
    + rewrite CS24 in D. clear -B1 B2 R D SP. lia.
  - pose proof nb_range as [N1 N2]. pose proof (proj1 WF) as (_ & _ & E3 & E4 & _).
    pose proof WF as (_ & _ & _ & _ & _ & (_ & _ & S3 & _) & _). destruct (S3 sc Hsc) as (_ & _ & _ & _ & _ & SPc & _).
    pose proof (RG_any E (cb :: P) [] s WF kBatchClass ltac:(unfold kBatchClass; lia)) as [[_ G2] _].
    unfold kBatchClass, kRegionSize, kFreeArrayOffset, kSpaceSize, kPageSize in *. clear -B1 B2 R L1 L2 N1 N2 SPc G2. lia.
Qed.

(* [comment removed for export] *)
Lemma last_in : forall l0 b0, tq = l0 ++ [b0] -> In b0 (as_tq s ++ as_gq s) /\ list_last tq = b_addr b0.
Proof.
  intros l0 b0 E0. split; [apply in_app_iff; left; rewrite E0; apply in_app_iff; right; left; reflexivity|].
  rewrite E0. unfold list_last. rewrite last_last. destruct l0; reflexivity.
Qed.
Lemma nb_facts : forall a, nb <= a < nb + 8192 ->
  0 <= a < alloc_ceiling /\ ~ (kLowAppEnd <= a < kHighMemBeg) /\ ~ (T <= a < T + 4096)
  /\ (forall x, In x (arep_img_ranges E ++ depot_static E) -> ~ (fst x <= a < fst x + snd x))
  /\ ~ (PA <= a < PA + 0x800000)
  /\ (forall sc, In sc (as_sec s) -> ~ (sc_map_beg sc <= a < sc_map_beg sc + sc_map_size sc))
  /\ (forall bb len, (In bb (ae_depot_nodes E :: as_node_blocks s) /\ len = kDepotNodeBlockBytes) \/ (In bb (ae_store_blk E :: as_store_blocks s) /\ len = kStoreBlockBytes) ->
        ~ (bb <= a < bb + len))
  /\ ~ (RI <= a < RI + kRegSize * kNumClasses)
  /\ (forall c', 0 <= c' < kNumClasses -> ~ (free_array SB c' <= a < free_array SB c' + rg_mapped_fa (region_of s c'))).
Proof. intros a Ha. pose proof nb_range as [R1 R2]. exact (ublk_facts nb a R1 R2 Ha). Qed.

(* [comment removed for export] *)
Lemma AG_fp2 : forall a, arep_fp E (DepotFP E) s a -> ~ (T <= a < T + 4096) -> ~ (nb <= a < nb + 8192) ->
  (forall l0 b0, tq = l0 ++ [b0] -> ~ (b_addr b0 <= a < b_addr b0 + 8)) -> m' (wa a) = m (wa a).
Proof.
  intros a Ha NT NB NL. pose proof (fp_range a Ha) as BC. pose proof alloc_ceiling_range as CR.
  apply AG; [clear -BC CR; lia|]. unfold FPWe2. intros [X|[X|[X|[X|[X|X]]]]].
  - clear -X BC LO. lia.
  - apply NT. unfold kThrQCache in X. clear -X. lia.
  - apply NT. unfold kThrCache, kPerClassSize, kBatchClass in X. clear -X. lia.
  - apply NT. unfold kThrCacheStats in X. clear -X. lia.
  - apply NB. clear -X. lia.
  - destruct X as [NEq X]. destruct (exists_last NEq) as (l0 & b0 & E0). destruct (last_in l0 b0 E0) as [_ LL]. rewrite LL in X. exact (NL l0 b0 E0 X).
Qed.
(* [comment removed for export] *)
Lemma AG_fp2' : forall a, arep_fp E (DepotFP E) s a -> ~ (T <= a < T + 4096) -> ~ (nb <= a < nb + 8192) ->
  (forall b0, In b0 (as_tq s ++ as_gq s) -> ~ (b_addr b0 <= a < b_addr b0 + 8192)) -> m' (wa a) = m (wa a).
Proof.
  intros a Ha NT NB NL. apply AG_fp2; [exact Ha| exact NT| exact NB|]. intros l0 b0 E0 R. destruct (last_in l0 b0 E0) as [Hb0 _].
  apply (NL b0 Hb0). clear -R. lia.
Qed.

Lemma AGimg2 : forall a, in_ranges (arep_img_ranges E) a -> m' (wa a) = m (wa a).
Proof.
  intros a (x & Hx & R). pose proof Tpl as [[T1 T2] T3].
  assert (Hx' : In x (arep_img_ranges E ++ depot_static E)) by (apply in_app_iff; left; exact Hx).
  pose proof (IMG_LOW x Hx') as [L1 L2].
  apply AG_fp2'; [left; exists x; split; [exact Hx| exact R]| clear -R L1 L2 T1 T2; lia| |].
  - intros Rb. destruct (nb_facts a Rb) as (_ & _ & _ & NI & _). exact (NI x Hx' R).
  - intros b0 Hb0 Rb. destruct (bat_facts b0 a Hb0 Rb) as (_ & _ & _ & NI & _). exact (NI x Hx' R).
Qed.
Lemma AGri2 : forall a, RI <= a < RI + kRegSize * kNumClasses -> m' (wa a) = m (wa a).
Proof.
  intros a Ha. apply AG_fp2'; [right; left; exact Ha| | intros Rb; destruct (nb_facts a Rb) as (_ & _ & _ & _ & _ & _ & _ & NR & _); exact (NR Ha)
                           | intros b0 Hb0 Rb; destruct (bat_facts b0 a Hb0 Rb) as (_ & _ & _ & _ & _ & _ & _ & NR & _); exact (NR Ha)].
  intros HT. destruct (Tpage_apart a HT) as (NR & _). apply NR. pose proof (proj1 WF) as (_ & _ & E3 & E4 & _).
  unfold ae_region_info, kRegSize, kNumClasses, kSpaceSize in *. clear -Ha E3 E4. lia.
Qed.
Lemma AGfa2 : forall a c', 0 <= c' < kNumClasses -> free_array SB c' <= a < free_array SB c' + rg_mapped_fa (region_of s c') -> m' (wa a) = m (wa a).
Proof.
  intros a c' Hc Ha. apply AG_fp2'; [do 3 right; left; exists c'; split; [exact Hc| exact Ha]| | intros Rb; destruct (nb_facts a Rb) as (_ & _ & _ & _ & _ & _ & _ & _ & NF); exact (NF c' Hc Ha)
                           | intros b0 Hb0 Rb; destruct (bat_facts b0 a Hb0 Rb) as (_ & _ & _ & _ & _ & _ & _ & _ & NF); exact (NF c' Hc Ha)].
  assert (RM : in_some_region_map E s a = true).
  { unfold in_some_region_map. apply Bool.orb_true_iff. right. apply existsb_exists. exists c'. split; [apply In_ziota; unfold kNumClasses in Hc; lia|].
    apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; lia. }
  pose proof (region_map_in_space E (cb :: P) [] s a WF RM) as SP. intros HT. destruct (Tpage_apart a HT) as (NR & _). apply NR.
  pose proof (proj1 WF) as (_ & _ & E3 & E4 & _). unfold kSpaceSize in *. clear -SP E3 E4. lia.
Qed.
Lemma AGptr2 : forall a, PA <= a < PA + 8 * kChunksBlockCount -> m' (wa a) = m (wa a).
Proof.
  intros a Ha. unfold kChunksBlockCount in Ha.
  apply AG_fp2'; [do 4 right; left; unfold kChunksBlockCount; exact Ha| | intros Rb; destruct (nb_facts a Rb) as (_ & _ & _ & _ & NP & _); apply NP; clear -Ha; lia
                           | intros b0 Hb0 Rb; destruct (bat_facts b0 a Hb0 Rb) as (_ & _ & _ & _ & NP & _); apply NP; clear -Ha; lia].
  intros HT. destruct (Tpage_apart a HT) as (_ & NP & _). clear -Ha NP. lia.
Qed.
Lemma AGsec2 : forall a sc, In sc (as_sec s) -> sc_map_beg sc <= a < sc_map_beg sc + 32 -> m' (wa a) = m (wa a).
Proof.
  intros a sc Hsc Ha. pose proof WF as (WE & _ & _ & _ & _ & (_ & _ & S3 & _) & _). destruct (S3 sc Hsc) as (_ & _ & _ & POS & MODS & _).
  pose proof (AsanRepFrame.pos_mod_ge E (sc_map_size sc) kPageSize POS MODS ltac:(unfold kPageSize; lia)) as GE. unfold kPageSize in GE.
  apply AG_fp2'; [do 5 right; left; exists sc; split; [exact Hsc| exact Ha]| | |].
  - intros HT. destruct (Tpage_apart a HT) as (_ & _ & NS & _). apply (NS sc Hsc). clear -Ha GE. lia.
  - intros Rb. destruct (nb_facts a Rb) as (_ & _ & _ & _ & _ & NS & _). apply (NS sc Hsc). clear -Ha GE. lia.
  - intros b0 Hb0 Rb. destruct (bat_facts b0 a Hb0 Rb) as (_ & _ & _ & _ & _ & NS & _). apply (NS sc Hsc). clear -Ha GE. lia.
Qed.
Lemma AGcm2 : forall a cb' cm', as_chunks s !! cb' = Some cm' -> chunk_meta_fp cm' a -> m' (wa a) = m (wa a).
Proof.
  intros a cb' cm' Hcm Ha. pose proof (chunk_meta_in_block E (cb :: P) [] s cb' cm' a WF Hcm Ha) as [BL BU].
  apply AG_fp2'; [do 6 right; left; exists cb', cm'; split; [exact Hcm| exact Ha]| | exact (nb_vs_chunk cb' cm' a Hcm Ha)| intros b0 Hb0; exact (bat_vs_chunk b0 cb' cm' a Hb0 Hcm Ha)].
  intros HT. destruct (Tpage_apart a HT) as (NR & _ & NS & _).
  destruct (block_where E (cb :: P) [] s cb' cm' WF Hcm) as [(J1 & J2 & _)|(sc & Hsc & _ & L1 & L2)]; unfold blk_lo in *.
  - apply NR. pose proof (proj1 WF) as (_ & _ & E3 & E4 & _). unfold kSpaceSize in *. clear -BL BU J1 J2 E3 E4. lia.
  - apply (NS sc Hsc). unfold kPageSize in L1. clear -BL BU L1 L2. lia.
Qed.
Lemma AGdep2 : forall a, DepotFP E s a -> m' (wa a) = m (wa a).
Proof.
  intros a Ha. pose proof Tpl as [[T1 T2] T3].
  assert (FPa : arep_fp E (DepotFP E) s a) by (do 8 right; left; exact Ha).
  destruct (DepotFP_where E s a Ha) as [(x & Hx & R)|[(bb & Hbb & R)|(bb & Hbb & R)]].
  - assert (Hx' : In x (arep_img_ranges E ++ depot_static E)) by (apply in_app_iff; right; exact Hx).
    pose proof (IMG_LOW x Hx') as [L1 L2].
    apply AG_fp2'; [exact FPa| clear -R L1 L2 T1 T2; lia| intros Rb; destruct (nb_facts a Rb) as (_ & _ & _ & NI & _); exact (NI x Hx' R)| intros b0 Hb0 Rb; destruct (bat_facts b0 a Hb0 Rb) as (_ & _ & _ & NI & _); exact (NI x Hx' R)].
  - apply AG_fp2'; [exact FPa| | intros Rb; destruct (nb_facts a Rb) as (_ & _ & _ & _ & _ & _ & NB & _); exact (NB bb kDepotNodeBlockBytes (or_introl (conj Hbb eq_refl)) R)
                     | intros b0 Hb0 Rb; destruct (bat_facts b0 a Hb0 Rb) as (_ & _ & _ & _ & _ & _ & NB & _); exact (NB bb kDepotNodeBlockBytes (or_introl (conj Hbb eq_refl)) R)].
    intros HT. destruct (Tpage_apart a HT) as (_ & _ & _ & NB & _). exact (NB bb kDepotNodeBlockBytes (or_introl (conj Hbb eq_refl)) R).
  - apply AG_fp2'; [exact FPa| | intros Rb; destruct (nb_facts a Rb) as (_ & _ & _ & _ & _ & _ & NB & _); exact (NB bb kStoreBlockBytes (or_intror (conj Hbb eq_refl)) R)
                     | intros b0 Hb0 Rb; destruct (bat_facts b0 a Hb0 Rb) as (_ & _ & _ & _ & _ & _ & NB & _); exact (NB bb kStoreBlockBytes (or_intror (conj Hbb eq_refl)) R)].
    intros HT. destruct (Tpage_apart a HT) as (_ & _ & _ & NB & _). exact (NB bb kStoreBlockBytes (or_intror (conj Hbb eq_refl)) R).
Qed.
Lemma Sh_granule_range2 : forall x v, Sh E s x = Some v -> 0 <= x < 2^47.
Proof.
  intros x v Hx. pose proof WF as WF0. pose proof alloc_ceiling_range as CR. unfold Sh in Hx.
  destruct (in_some_region_map E s x) eqn:RM.
  - pose proof (region_map_in_space E (cb :: P) [] s x WF0 RM) as SP. pose proof (proj1 WF0) as (E1 & E2 & E3 & E4 & E5 & _).
    unfold kSpaceSize in *. clear -SP E2 E3 E4 E5 CR. rewrite kHighMemBeg_val in E2. lia.
  - destruct (in_some_sec_map s x) eqn:SM.
    + unfold in_some_sec_map in SM. apply existsb_exists in SM as (sc & Hsc & Hb0). apply andb_true_iff in Hb0 as [B1 B2].
      apply Z.leb_le in B1. apply Z.ltb_lt in B2. pose proof WF0 as (_ & _ & _ & _ & _ & (_ & _ & S3 & _) & _). destruct (S3 sc Hsc) as (_ & HB & S & _).
      unfold app_mem in HB. rewrite kHighMemBeg_val, kLowAppEnd_val in HB. clear -B1 B2 HB S CR. lia.
    + cbn [orb] in Hx. destruct (sh_default_dom E x && negb (sh_excluded E x)) eqn:C; [|discriminate].
      apply andb_true_iff in C as [C _]. unfold sh_default_dom in C. apply Bool.orb_true_iff in C as [C|C].
      * apply andb_true_iff in C as [C _]. apply andb_true_iff in C as [C1 C2]. apply Z.leb_le in C1. apply Z.ltb_lt in C2.
        rewrite kLowAppEnd_val in C2. clear -C1 C2. lia.
      * apply andb_true_iff in C as [C1 C2]. apply Z.leb_le in C1. apply Z.leb_le in C2.
        rewrite kHighMemBeg_val in C1. unfold kHighMemEnd in C2. clear -C1 C2. lia.
Qed.
Lemma AGsh2 : forall g v, Sh E s (8 * g) = Some v -> m' (wa (kShadowBase + g)) = m (wa (kShadowBase + g)).
Proof.
  intros g v Hg. pose proof (Sh_granule_range2 _ _ Hg) as GR.
  assert (BAND : kLowAppEnd < kShadowBase + g < kHighMemBeg) by (rewrite kLowAppEnd_val, kHighMemBeg_val; unfold kShadowBase; clear -GR; lia).
  apply AG_fp2'; [do 9 right; exists g, v; split; [reflexivity| exact Hg]| | |].
  - intros HT. destruct (Tpage_apart _ HT) as (_ & _ & _ & _ & NBAND & _). apply NBAND. exact BAND.
  - intros Rb. destruct (nb_facts _ Rb) as (_ & NB & _). apply NB. clear -BAND. lia.
  - intros b0 Hb0 Rb. destruct (bat_facts b0 _ Hb0 Rb) as (_ & NB & _). apply NB. clear -BAND. lia.
Qed.
(* [comment removed for export] *)
Lemma AGthr_cells2 : forall A k, T <= A -> A + k <= T + 4096 ->
  (A + k <= T + kThrQCache \/ T + kThrQCache + 32 <= A) -> (A + k <= ROW \/ ROW + 4 <= A) ->
  (A + k <= T + kThrCacheStats + 16 \/ T + kThrCacheStats + 24 <= A) -> agree_on m m' A k.
Proof.
  intros A k H0 H1 H2 H3 H4 z Hz. pose proof Tpl as [[T1 T2] T3]. pose proof alloc_ceiling_range as CR.
  destruct (nb_facts nb ltac:(clear; lia)) as (_ & _ & NT & _). pose proof nb_range as [R1 R2].
  apply AG; [clear -Hz H0 H1 T1 T3 CR; lia|]. unfold FPWe2.
  assert (NTz : ~ (nb <= z < nb + 8192)).
  { intros C. destruct (nb_facts z C) as (_ & _ & NT' & _). apply NT'. clear -Hz H0 H1. lia. }
  assert (NLz : forall l0 b0, tq = l0 ++ [b0] -> ~ (b_addr b0 <= z < b_addr b0 + 8)).
  { intros l0 b0 E0 C. destruct (last_in l0 b0 E0) as [Hb0 _]. destruct (bat_facts b0 z Hb0 ltac:(clear -C; lia)) as (_ & _ & NT' & _). apply NT'. clear -Hz H0 H1. lia. }
  intros [X|[X|[X|[X|[X|X]]]]].
  - clear -X Hz H0 H1 T3 LO. lia.
  - clear -X Hz H2. lia.
  - clear -X Hz H3. lia.
  - clear -X Hz H4. lia.
  - apply NTz. clear -X. lia.
  - destruct X as [NEq X]. destruct (exists_last NEq) as (l0 & b0 & E0). destruct (last_in l0 b0 E0) as [_ LL]. rewrite LL in X. exact (NLz l0 b0 E0 X).
Qed.
Ltac thr_ag2 := apply AGthr_cells2; unfold kThrUnwinding, kThrCache, kThrCacheStats, kThrStats, kPerClassSize, kThrStackTop, kThrQCache, kNumClasses, kBatchClass in *;
  cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]; try lia.

(* [comment removed for export] *)
Lemma repD_enq2 : arep_thread segs E s' m'.
Proof.
  pose proof REP as (_ & _ & _ & RD & _). destruct RD as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8).
  unfold arep_thread. rewrite enq2_tq_bytes, enq2_tq, enq2_cache_allocated, enq2_cache_mapped, enq2_ts.
  split; [eapply rw_cells_agree'; [| exact D1]; thr_ag2|].
  split; [eapply rw_cells_agree'; [| exact D2]; thr_ag2|].
  split.
  { replace (qcount (tq ++ [mkBatch nb [cb] (kBatchSize + n)])) with (qcount tq + 1) by (unfold qcount; rewrite length_app; cbn [length]; lia).
    replace (list_first (tq ++ [mkBatch nb [cb] (kBatchSize + n)])) with (match tq with [] => nb | _ => list_first tq end) by (destruct tq; reflexivity).
    replace (list_last (tq ++ [mkBatch nb [cb] (kBatchSize + n)])) with nb by (unfold list_last; rewrite last_last; destruct tq; reflexivity).
    replace (tq_bytes s + (kBatchSize + n)) with (tq_bytes s + (n + kBatchSize)) by lia. exact NC_qc. }
  split.
  { intros c' Hc'. destruct (D4 c' Hc') as (X1 & junk0 & X2 & L). unfold percls_cells in *. rewrite enq2_get_cache, enq2_cache_inited. unfold kNumClasses in Hc'.
    destruct (decide (c' = kBatchClass)) as [->|NE'].
    - destruct (removelast_facts l NE) as [EL LL]. split.
      + apply rh_split with (cs1 := [C4 (zw (zlen l))]) in X1. destruct X1 as [_ X1].
        apply (rh_join_at segs m' _ (ROW + 4) [C4 (zw (zlen (removelast l)))]).
        * replace (zlen (removelast l)) with (zlen l - 1); [exact NC_row|]. unfold zlen. rewrite LL. destruct l eqn:GC; [exfalso; exact (NE eq_refl)| cbn [length Nat.pred]; lia].
        * eapply rw_cells_agree'; [| exact X1]. thr_ag2.
        * cbn. unfold kBatchClass, kThrCache, kPerClassSize. lia.
      + exists (zw (List.last l 0) :: junk0). split.
        * replace (map zw (removelast l) ++ zw (List.last l 0) :: junk0) with (map zw l ++ junk0).
          2:{ rewrite EL at 1. rewrite map_app. cbn [map]. rewrite <- app_assoc. reflexivity. }
          eapply u32arr_agree; [| exact X2]. rewrite length_app, length_map. thr_ag2.
        * cbn [length]. rewrite LL. destruct l eqn:GC; [exfalso; exact (NE eq_refl)| cbn [length Nat.pred] in *; lia].
    - split.
      + eapply rw_cells_agree'; [| exact X1]. thr_ag2.
      + exists junk0. split; [| exact L]. eapply u32arr_agree; [| exact X2]. rewrite length_app, length_map. thr_ag2. }
  split.
  { apply rh_split with (cs1 := [C8 (zw (as_cache_allocated s))]) in D5. destruct D5 as [_ D5].
    apply (rh_join_at segs m' _ (T + kThrCacheStats + 16 + 8) [C8 (zw (as_cache_allocated s + class_size kBatchClass))]); [exact NC_cst| | cbn; lia].
    eapply rw_cells_agree'; [| exact D5]. thr_ag2. }
  split; [eapply u64arr_agree; [| exact D6]; unfold tstats_words; rewrite length_map; cbn [length]; thr_ag2|].
  split; [eapply u64arr_agree; [| exact D7]; rewrite length_map, length_ziota; thr_ag2|].
  eapply rw_cells_agree'; [| exact D8]; thr_ag2.
Qed.

(* [comment removed for export] *)
Lemma NDl : forall pre blast b0, tq = pre ++ [blast] -> In b0 pre \/ In b0 (as_gq s) -> b_addr b0 <> b_addr blast.
Proof.
  intros pre blast b0 E0 Hb0. pose proof WF as (_ & _ & _ & _ & (_ & _ & ND & _) & _). unfold all_batches in ND. rewrite app_nil_r, E0, <- app_assoc in ND. cbn [app] in ND.
  apply (nodup_map_sep b_addr pre blast (as_gq s) b0 ND). apply in_app_iff. exact Hb0.
Qed.
(* [comment removed for export] *)
Lemma batch_keep2 : forall b0 next, In b0 (as_tq s ++ as_gq s) -> (forall l0 bl, tq = l0 ++ [bl] -> b_addr b0 <> b_addr bl) ->
  arep_batch segs s b0 next m -> arep_batch segs s' b0 next m'.
Proof.
  intros b0 next Hb0 NL [X1 (junk0 & X2 & L)]. pose proof (f_equal Z.of_nat L) as L'. rewrite Z2Nat.id in L' by (cbv; discriminate). unfold kBatchCap in L'.
  assert (AGb : forall x, b_addr b0 <= x < b_addr b0 + 8192 -> m' (wa x) = m (wa x)).
  { intros x Hx. apply AG_fp2; [do 7 right; left; exists b0; split; [exact Hb0| unfold kBatchCap; clear -Hx; lia]| | exact (nb_vs_bat b0 x Hb0 Hx)|].
    - intros HT. destruct (bat_facts b0 x Hb0 Hx) as (_ & _ & NT & _). exact (NT HT).
    - intros l0 bl E0 R. destruct (last_in l0 bl E0) as [Hbl _]. apply (bat_vs_bat b0 bl x Hb0 Hbl (NL l0 bl E0) Hx). clear -R. lia. }
  split.
  - eapply rw_cells_agree'; [| exact X1]. cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]. intros x Hx. apply AGb. clear -Hx. lia.
  - exists junk0. split; [| exact L]. eapply u32arr_agree || eapply u64arr_agree; [| exact X2]. rewrite length_app, length_map. intros x Hx. apply AGb. clear -Hx L'. lia.
Qed.

Lemma repG_enq2 : arep_batches segs s' m'.
Proof.
  pose proof REP as (_ & _ & _ & _ & _ & _ & [RG1 RG2] & _). unfold arep_batches. rewrite enq2_tq, enq2_gq.
  split.
  - (* [comment removed for export] *)
    assert (NB : arep_batch_list segs s' [mkBatch nb [cb] (kBatchSize + n)] m').
    { cbn [arep_batch_list]. split; [| exact I]. split; cbn [b_addr b_items b_size zlen length Z.of_nat].
      - replace (kBatchSize + n) with (n + kBatchSize) by lia. change (Z.of_nat 1) with 1. exact NC_nbh.
      - exists junk. split; [cbn [map app]; exact NC_nbi| rewrite LJ; reflexivity]. }
    destruct tq as [|b1 tq1] eqn:Etq; [cbn [app]; exact NB|].
    destruct (exists_last (l := b1 :: tq1) ltac:(discriminate)) as (pre & blast & E0). rewrite <- Etq in *. rewrite E0 in RG1 |- *. rewrite <- app_assoc. cbn [app].
    assert (SPLIT : forall l0, (forall b0, In b0 l0 -> In b0 pre) -> arep_batch_list segs s (l0 ++ [blast]) m ->
              arep_batch_list segs s' (l0 ++ blast :: [mkBatch nb [cb] (kBatchSize + n)]) m').
    { induction l0 as [|b0 l0 IH]; intros SUB H.
      - cbn [app arep_batch_list] in H |- *. destruct H as [[X1 (junk0 & X2 & L)] _]. destruct (last_in pre blast E0) as [Hbl LL].
        pose proof (f_equal Z.of_nat L) as L'. rewrite Z2Nat.id in L' by (cbv; discriminate). unfold kBatchCap in L'.
        assert (AGb : forall x, b_addr blast + 8 <= x < b_addr blast + 8192 -> m' (wa x) = m (wa x)).
        { intros x Hx. apply AG_fp2; [do 7 right; left; exists blast; split; [exact Hbl| unfold kBatchCap; clear -Hx; lia]| | apply (nb_vs_bat blast x Hbl); clear -Hx; lia|].
          - intros HT. destruct (bat_facts blast x Hbl ltac:(clear -Hx; lia)) as (_ & _ & NT & _). exact (NT HT).
          - intros l0 bl E1 R. rewrite E0 in E1. apply app_inj_tail in E1 as [_ <-]. clear -Hx R. lia. }
        split; [| cbn [b_addr]; exact NB]. split.
        + cbn [b_addr]. apply rh_split with (cs1 := [C8 (zw 0)]) in X1. destruct X1 as [_ X1].
          apply (rh_join_at segs m' _ (b_addr blast + 8) [C8 (zw nb)]); [exact (NC_last pre blast E0)| | cbn; lia].
          eapply rw_cells_agree'; [| exact X1]. cbn. intros x Hx. apply AGb. clear -Hx. lia.
        + exists junk0. split; [| exact L]. eapply u64arr_agree; [| exact X2]. rewrite length_app, length_map. intros x Hx. apply AGb. clear -Hx L'. lia.
      - cbn [app] in H |- *. destruct H as [H1 H2]. split; [| apply IH; [intros b' Hb'; apply SUB; right; exact Hb'| exact H2]].
        replace (match l0 ++ blast :: [mkBatch nb [cb] (kBatchSize + n)] with [] => 0 | b' :: _ => b_addr b' end)
           with (match l0 ++ [blast] with [] => 0 | b' :: _ => b_addr b' end) by (destruct l0; reflexivity).
        pose proof (SUB b0 ltac:(left; reflexivity)) as Hpre.
        apply batch_keep2; [apply in_app_iff; left; rewrite E0; apply in_app_iff; left; exact Hpre| | exact H1].
        intros l1 bl E1. rewrite E0 in E1. apply app_inj_tail in E1 as [<- <-]. apply (NDl pre blast b0 E0). left. exact Hpre. }
    apply SPLIT; [intros b0 Hb0; exact Hb0| exact RG1].
  - (* [comment removed for export] *)
    assert (GL : forall l0, (forall b0, In b0 l0 -> In b0 (as_gq s)) -> arep_batch_list segs s l0 m -> arep_batch_list segs s' l0 m').
    { induction l0 as [|b0 l0 IH]; intros SUB H; [exact I|]. destruct H as [H1 H2]. split; [| apply IH; [intros b' Hb'; apply SUB; right; exact Hb'| exact H2]].
      pose proof (SUB b0 ltac:(left; reflexivity)) as Hgq.
      apply batch_keep2; [apply in_app_iff; right; exact Hgq| | exact H1]. intros l1 bl E1. apply (NDl l1 bl b0 E1). right. exact Hgq. }
    apply GL; [intros b0 Hb0; exact Hb0| exact RG2].
Qed.

Theorem ARep_after_enq2 : AREP s' m'.
Proof.
  pose proof REP as (RA & RB & RC & _ & RE & RF & RG & RH & RI & RJ).
  apply (ARep_tqc_xfer s s' m'); try (unfold enq2_st, bpop_st; destruct s; reflexivity).
  - exact (frameA' segs E s m m' AGimg2 RA).
  - exact (frameB' segs E s m m' AGri2 RB).
  - exact (frameC' segs E s m m' WM AGfa2 RC).
  - exact repD_enq2.
  - exact (frameE' segs E s m m' WM AGptr2 AGsec2 RE).
  - exact (frameF' segs s m m' AGcm2 RF).
  - exact repG_enq2.
  - exact (frameH' segs E s m m' WM AGdep2 RH).
  - exact (frameI' segs E s m m' WM AGimg2 RI).
  - exact (frameJ' segs E s m m' AGsh2 RJ).
Qed.
End ENQ2.
End WFS.
End REN.
End RC__1.
