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
  AsanWf1 AsanWf3 AsanWf4 AsanWf5 AsanClient AsanRepFrame AsanRepFrame2 AsanBudget AsanHit AsanRepHitB AsanRepX AsanRepCaB AsanRepSecB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section RRF.
Variable segs : list Segment.
Variable E : aenv.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).
#[warnings="-notation-for-abbreviation"] Notation RW := (rw_cells segs).
#[warnings="-notation-for-abbreviation"] Notation SB := (ae_space_beg E).
#[warnings="-notation-for-abbreviation"] Notation T := (ae_thread E).
#[warnings="-notation-for-abbreviation"] Notation RI := (ae_region_info E).
#[warnings="-notation-for-abbreviation"] Notation INST := (ae_instance E).
#[warnings="-notation-for-abbreviation"] Notation PA := (ae_ptr_array E).
#[warnings="-notation-for-abbreviation"] Notation AREP := (ARep segs E (DepotR segs E)).

(* [comment removed for export] *)
Definition ts_nomap_agree (t t' : tstats) : Prop :=
     ts_mallocs t' = ts_mallocs t /\ ts_malloced t' = ts_malloced t /\ ts_malloced_redzones t' = ts_malloced_redzones t
  /\ ts_frees t' = ts_frees t /\ ts_freed t' = ts_freed t /\ ts_real_frees t' = ts_real_frees t /\ ts_really_freed t' = ts_really_freed t
  /\ ts_reallocs t' = ts_reallocs t /\ ts_realloced t' = ts_realloced t /\ ts_munmaps t' = ts_munmaps t /\ ts_munmaped t' = ts_munmaped t
  /\ ts_malloc_large t' = ts_malloc_large t /\ ts_by_size t' = ts_by_size t.
Lemma ts_nomap_agree_refl : forall t, ts_nomap_agree t t.
Proof. intros t. repeat split; reflexivity. Qed.
Lemma ts_nomap_agree_mmap : forall sz t t', ts_nomap_agree t t' -> ts_nomap_agree t (ts_on_mmap sz t').
Proof. intros sz t t' H. destruct t, t'. cbv in H. destruct H as (?&?&?&?&?&?&?&?&?&?&?&?&?). subst. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
Lemma ARep_ref_xfer : forall s s' m,
  as_ptr_committed s' = as_ptr_committed s -> as_sec s' = as_sec s -> as_sec_stale s' = as_sec_stale s -> as_sec_stats s' = as_sec_stats s ->
  as_glob_allocated s' = as_glob_allocated s -> as_glob_mapped s' = as_glob_mapped s -> as_oom s' = as_oom s ->
  as_chunks s' = as_chunks s -> as_dead s' = as_dead s -> as_tq s' = as_tq s -> as_gq s' = as_gq s ->
  as_keys s' = as_keys s -> as_frames s' = as_frames s -> as_ia_inited s' = as_ia_inited s ->
  as_node_blocks s' = as_node_blocks s -> as_store_blocks s' = as_store_blocks s -> as_store_stored s' = as_store_stored s -> as_ndepot_ins s' = as_ndepot_ins s ->
  arep_instance segs E s m -> arep_regioninfo segs E s' m -> arep_region_mem segs E s' m -> arep_thread segs E s' m ->
  arep_secondary segs E s m -> arep_chunks segs s m -> arep_batches segs s m -> arep_depot (DepotR segs E) s m ->
  arep_globals segs E s m -> arep_shadow segs E s' m -> AREP s' m.
Proof.
  intros s s' m. destruct s, s'; cbn. intros -> -> -> -> -> -> -> -> -> -> -> -> -> -> -> -> -> ->.
  intros RA RB RC RD' RE RF RG RH RI RJ.
  split; [exact RA|]. split; [exact RB|]. split; [exact RC|]. split; [exact RD'|]. split; [exact RE|]. split; [exact RF|].
  split; [destruct RG as [RG1 RG2]; split; eapply arep_batch_list_indep; eassumption|]. split; [exact RH|]. split; [exact RI| exact RJ].
Qed.

Section REF.
Variables (P : list Z) (D : list batch).          (* [comment removed for export] *)
Variables (s s' : astate) (m m' : mem) (lo c : Z).
#[warnings="-notation-for-abbreviation"] Notation r := (region_of s c).
#[warnings="-notation-for-abbreviation"] Notation r' := (region_of s' c).
#[warnings="-notation-for-abbreviation"] Notation RB := (region_beg SB c).
#[warnings="-notation-for-abbreviation"] Notation FA := (free_array SB c).
#[warnings="-notation-for-abbreviation"] Notation ROW := (T + kThrCache + kPerClassSize * c).

(* [comment removed for export] *)
Hypothesis Echunks : as_chunks s' = as_chunks s.
Hypothesis Etq : as_tq s' = as_tq s.
Hypothesis Egq : as_gq s' = as_gq s.
Hypothesis Esec : as_sec s' = as_sec s.
Hypothesis Estats : as_sec_stats s' = as_sec_stats s.
Hypothesis Eptr : as_ptr_committed s' = as_ptr_committed s.
Hypothesis Ekeys : as_keys s' = as_keys s.
Hypothesis Eframes : as_frames s' = as_frames s.
Hypothesis Enb : as_node_blocks s' = as_node_blocks s.
Hypothesis Esb : as_store_blocks s' = as_store_blocks s.
Hypothesis Ess : as_store_stored s' = as_store_stored s.
Hypothesis End_ : as_ndepot_ins s' = as_ndepot_ins s.
Hypothesis Eia : as_ia_inited s' = as_ia_inited s.
Hypothesis Ecal : as_cache_allocated s' = as_cache_allocated s.
Hypothesis Ega : as_glob_allocated s' = as_glob_allocated s.
Hypothesis Egm : as_glob_mapped s' = as_glob_mapped s.
Hypothesis Estale : as_sec_stale s' = as_sec_stale s.
Hypothesis Eoom : as_oom s' = as_oom s.
Hypothesis Edead : as_dead s' = as_dead s.
Hypothesis Ereg : forall c', c' <> c -> region_of s' c' = region_of s c'.
Hypothesis Ecache : forall c', c' <> c -> get_cache s' c' = get_cache s c'.
Hypothesis CI' : as_cache_inited s' = true.
(* [comment removed for export] *)
Hypothesis GRU : rg_mapped_user r <= rg_mapped_user r'.
Hypothesis GRF : rg_mapped_fa r <= rg_mapped_fa r'.
Variable keep : nat.                                   (* [comment removed for export] *)
Hypothesis KEEP : firstn keep (rg_free r') = firstn keep (rg_free r) /\ (keep <= length (rg_free r))%nat /\ (keep <= length (rg_free r'))%nat.

Hypothesis HCc : 1 <= c <= kLargestClassID.
Hypothesis WF : AWf E P D s.
Hypothesis WF' : AWf E P D s'.

(* [comment removed for export] *)
Definition FPWref (z : Z) : Prop :=
  lo <= z
  \/ (RI + kRegSize * c <= z < RI + kRegSize * c + kRegSize)
  \/ (exists i, 0 <= i < kNumClasses /\ T + kThrCache + kPerClassSize * i + 4 <= z < T + kThrCache + kPerClassSize * i + 16)
  \/ (ROW <= z < ROW + kPerClassSize)
  \/ (T + kThrCacheStats + 24 <= z < T + kThrCacheStats + 32)
  \/ (T + kThrStats + 72 <= z < T + kThrStats + 88)
  \/ (RB + rg_mapped_user r <= z < RB + rg_mapped_user r')
  \/ (FA + 4 * Z.of_nat keep <= z < FA + rg_mapped_fa r')
  \/ (kShadowBase + (RB + rg_mapped_user r) / 8 <= z < kShadowBase + (RB + rg_mapped_user r') / 8)
  \/ (kShadowBase + (FA + rg_mapped_fa r) / 8 <= z < kShadowBase + (FA + rg_mapped_fa r') / 8).

Hypothesis WM : wmono segs m m'.
Hypothesis AG : forall z, 0 <= z < 2^64 -> ~ FPWref z -> m' (wa z) = m (wa z).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis REP : AREP s m.
Hypothesis BS : blocks_sep E s.
Hypothesis Tpl : (0x1000 <= T /\ (T + 4096 <= 0x10000 \/ 0x603000 <= T)) /\ T + 4096 <= alloc_ceiling.
Hypothesis IMG_IN : forall x, In x (arep_img_ranges E ++ depot_static E) -> fst (ae_img E) <= fst x /\ fst x + snd x <= fst (ae_img E) + snd (ae_img E).
Hypothesis IMG_LO : 0x10000 <= fst (ae_img E).
Hypothesis IMG_LOW : forall x, In x (arep_img_ranges E ++ depot_static E) -> 0x10000 <= fst x /\ fst x + snd x <= 0x603000.
Hypothesis AK : exists mo, AKern E s mo.
Hypothesis TDN : T + 4096 <= ae_depot_nodes E \/ ae_depot_nodes E + kDepotNodeBlockBytes <= T.

(* [comment removed for export] *)
Lemma fp_range : forall a, arep_fp E (DepotFP E) s a -> 0 <= a < alloc_ceiling.
Proof.
  intros a Ha. split; [| exact (fp_below_ceiling E (DepotFP E) P D IMG_IN (DepotFP_where E) s a WF BS Ha)].
  destruct (fp_locate E (DepotFP E) P D IMG_IN (DepotFP_where E) s a WF BS Ha) as [X|[[X _]|[X _]]].
  - destruct X as (r0 & Hr & R). pose proof (IMG_IN r0 Hr). clear -R H IMG_LO. lia.
  - pose proof (sh_band_below_ceiling a X). rewrite kLowAppEnd_val in *. clear -H. lia.
  - unfold app_addr in X. rewrite kHighMemBeg_val in X. clear -X. lia.
Qed.
Lemma Tpage_apart : forall a, T <= a < T + 4096 ->
     ~ (ae_resv_beg E <= a < ae_resv_beg E + 0x2000011000)
  /\ ~ (ae_ptr_array E <= a < ae_ptr_array E + 0x800000)
  /\ (forall sc, In sc (as_sec s) -> ~ (sc_map_beg sc <= a < sc_map_beg sc + sc_map_size sc))
  /\ (forall b len, (In b (ae_depot_nodes E :: as_node_blocks s) /\ len = kDepotNodeBlockBytes) \/ (In b (ae_store_blk E :: as_store_blocks s) /\ len = kStoreBlockBytes) ->
        ~ (b <= a < b + len))
  /\ ~ (kLowAppEnd < a < kHighMemBeg) /\ ~ (0x10000 <= a < 0x603000).
Proof.
  intros a Ha. destruct AK as [mo K]. pose proof WF as (WE & _ & _ & _ & _ & WS & _). destruct WS as (_ & _ & S3 & _).
  pose proof WE as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & E20 & E21 & E22 & E23 & _).
  split; [clear -Ha E19; lia|]. split; [clear -Ha E23; lia|]. split.
  { intros sc Hsc. destruct (S3 sc Hsc) as (_ & _ & _ & _ & _ & _ & RSV). pose proof (RSV _ E13) as X. cbn [fst snd] in X. clear -Ha X. lia. }
  split.
  { intros b len H. destruct H as [[[<-|Hb] ->]|[[<-|Hb] ->]].
    - clear -Ha TDN. lia.
    - destruct (ak_blocks_sep _ _ _ K b kDepotNodeBlockBytes (or_introl (conj Hb eq_refl))) as (_ & _ & _ & _ & _ & R). pose proof (R _ E13) as X. cbn [fst snd] in X. clear -Ha X. lia.
    - pose proof (ak_store_sep _ _ _ K) as (_ & _ & X & _). unfold kPageSize, kStoreBlockBytes in *. clear -Ha X. lia.
    - destruct (ak_blocks_sep _ _ _ K b kStoreBlockBytes (or_intror (conj Hb eq_refl))) as (_ & _ & _ & _ & _ & R). pose proof (R _ E13) as X. cbn [fst snd] in X. clear -Ha X. lia. }
  unfold app_mem in E14. rewrite ?kLowAppEnd_val, ?kHighMemBeg_val in *. pose proof Tpl as [[T1 T2] T3]. clear -Ha E14 T1 T2 T3. split; lia.
Qed.

(* [comment removed for export] *)
Hypothesis NC_ri : RW m' (RI + kRegSize * c) (region_cells r').
Hypothesis NC_rows : forall i, 0 <= i < kNumClasses -> i <> c -> RW m' (T + kThrCache + kPerClassSize * i) (percls_cells s' i).
Hypothesis NC_row : RW m' ROW (percls_cells s' c)
                    /\ exists junk, u32arr segs m' (ROW + 16) (map zw (get_cache s' c) ++ junk) /\ (length (get_cache s' c) + length junk = 16)%nat.
Hypothesis NC_cst : RW m' (T + kThrCacheStats + 24) [C8 (zw (as_cache_mapped s'))].
Hypothesis NC_thr : RW m' (T + kThrStats + 72) [C8 (zw (ts_mmaps (as_ts s'))); C8 (zw (ts_mmaped (as_ts s')))].
Hypothesis Ets : ts_nomap_agree (as_ts s) (as_ts s').
Hypothesis NC_um : wr_at segs m' RB (rg_mapped_user r').
Hypothesis NC_fa : exists junk, u32arr segs m' FA (map zw (rg_free r') ++ junk) /\ 4 * Z.of_nat (length (rg_free r') + length junk) = rg_mapped_fa r'.
Hypothesis NC_shu : RW m' (kShadowBase + (RB + rg_mapped_user r) / 8)
  [CB (Z.to_nat ((rg_mapped_user r' - rg_mapped_user r) / 8)) (repeat (zb kAsanHeapLeftRedzoneMagic) (Z.to_nat ((rg_mapped_user r' - rg_mapped_user r) / 8)))].
Hypothesis NC_shf : RW m' (kShadowBase + (FA + rg_mapped_fa r) / 8)
  [CB (Z.to_nat ((rg_mapped_fa r' - rg_mapped_fa r) / 8)) (repeat (zb kAsanHeapLeftRedzoneMagic) (Z.to_nat ((rg_mapped_fa r' - rg_mapped_fa r) / 8)))].

(* [comment removed for export] *)
Lemma reg_num : 0 <= rg_alloc_user r <= rg_mapped_user r /\ rg_mapped_user r <= rg_mapped_user r' <= kFreeArrayOffset
  /\ (0 <= rg_mapped_fa r <= rg_mapped_fa r' /\ rg_mapped_fa r' <= kFreeArraySize) /\ 4 * Z.of_nat (length (rg_free r)) <= rg_mapped_fa r
  /\ rg_mapped_user r mod 8 = 0 /\ rg_mapped_user r' mod 8 = 0 /\ rg_mapped_fa r mod 8 = 0 /\ rg_mapped_fa r' mod 8 = 0
  /\ RB mod 8 = 0 /\ FA = RB + kFreeArrayOffset /\ RB = SB + c * kRegionSize /\ 0 <= rg_alloc_user r' <= rg_mapped_user r'.
Proof.
  pose proof WF as (WE & [_ WR] & _). pose proof WF' as (_ & [_ WR'] & _).
  destruct (WR c HCc) as (A1 & A2 & A3 & _ & A5 & A6 & A7 & A8 & _). destruct (WR' c HCc) as (B1 & B2 & B3 & _ & B5 & B6 & B7 & B8 & _).
  cbv zeta in *. unfold rg_num_freed in A8. pose proof (proj1 WE) as SBM.
  unfold kUserMapSize, kFreeArrayMapSize in *. unfold free_array, region_beg, kRegionSize.
  repeat split; try (clear -A1 A2 A3 A5 A6 A7 A8 B1 B2 B3 B5 B6 B7 B8 GRU GRF; Z.div_mod_to_equations; lia).
  clear -SBM. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma AG_fp : forall a, arep_fp E (DepotFP E) s a ->
  ~ (T <= a < T + 4096) -> ~ (RI + kRegSize * c <= a < RI + kRegSize * c + kRegSize) ->
  ~ (RB + rg_mapped_user r <= a < RB + rg_mapped_user r') -> ~ (FA + 4 * Z.of_nat keep <= a < FA + rg_mapped_fa r') ->
  ~ (kLowAppEnd < a < kHighMemBeg) -> m' (wa a) = m (wa a).
Proof.
  intros a Ha NT NRI NU NF NB. pose proof (fp_range a Ha) as BC. pose proof alloc_ceiling_range as CR.
  pose proof reg_num as (R1 & R2 & R3 & _). pose proof (proj1 WF) as (E1 & E2 & E3 & E4 & E5 & _).
  apply AG; [clear -BC CR; lia|]. unfold FPWsec, FPWref. rewrite kLowAppEnd_val, kHighMemBeg_val in *.
  unfold kThrStats, kThrCache, kThrCacheStats, kPerClassSize, kNumClasses, kShadowBase, free_array, region_beg, kRegionSize, kFreeArrayOffset, kFreeArraySize in *.
  intros [X|[X|[(i & Hi & X)|[X|[X|[X|[X|[X|[X|X]]]]]]]]].
  - clear -X BC LO. lia.
  - exact (NRI X).
  - clear -X Hi NT. lia.
  - clear -X NT HCc. unfold kLargestClassID in HCc. lia.
  - clear -X NT. lia.
  - clear -X NT. lia.
  - exact (NU X).
  - exact (NF X).
  - apply NB. clear -X R1 R2 E2 E3 E4 E5 CR HCc. unfold kLargestClassID, kSpaceSize in *. Z.div_mod_to_equations. lia.
  - apply NB. clear -X R1 R2 R3 E2 E3 E4 E5 CR HCc. unfold kLargestClassID, kSpaceSize in *. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma AG_offspace : forall a, arep_fp E (DepotFP E) s a -> ~ (T <= a < T + 4096) ->
  ~ (ae_resv_beg E <= a < ae_resv_beg E + 0x2000011000) -> ~ (kLowAppEnd < a < kHighMemBeg) -> m' (wa a) = m (wa a).
Proof.
  intros a Ha NT NR NB. pose proof reg_num as (R1 & R2 & R3 & _). pose proof (proj1 WF) as (E1 & E2 & E3 & E4 & _).
  apply AG_fp; [exact Ha| exact NT| | | | exact NB]; intros X; apply NR;
    unfold ae_region_info, free_array, region_beg, kRegionSize, kFreeArrayOffset, kFreeArraySize, kRegSize, kSpaceSize, kLargestClassID in *; clear -X R1 R2 R3 E3 E4 HCc; lia.
Qed.

Lemma AGimg : forall a, in_ranges (arep_img_ranges E) a -> m' (wa a) = m (wa a).
Proof.
  intros a (x & Hx & R). pose proof Tpl as [[T1 T2] T3].
  assert (Hx' : In x (arep_img_ranges E ++ depot_static E)) by (apply in_app_iff; left; exact Hx).
  pose proof (IMG_LOW x Hx') as [L1 L2]. pose proof (proj1 WF) as (E1 & E2 & _). rewrite kHighMemBeg_val in E2.
  apply AG_offspace; [left; exists x; split; [exact Hx| exact R]| clear -R L1 L2 T1 T2; lia| clear -R L1 L2 E2; lia| rewrite kLowAppEnd_val; clear -R L2; lia].
Qed.
Lemma AGptr : forall a, PA <= a < PA + 8 * kChunksBlockCount -> m' (wa a) = m (wa a).
Proof.
  intros a Ha. pose proof (proj1 WF) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & E20 & _).
  apply AG_offspace; [do 4 right; left; exact Ha| | unfold kChunksBlockCount in Ha; clear -Ha E20; lia| unfold app_mem, kChunksBlockCount in *; clear -Ha E16; lia].
  intros HT. destruct (Tpage_apart a HT) as (_ & NP & _). unfold kChunksBlockCount in Ha. clear -Ha NP. lia.
Qed.
Lemma AGsec : forall a sc, In sc (as_sec s) -> sc_map_beg sc <= a < sc_map_beg sc + 32 -> m' (wa a) = m (wa a).
Proof.
  intros a sc Hsc Ha. pose proof WF as (WE & _ & _ & _ & _ & (_ & _ & S3 & _) & _). destruct (S3 sc Hsc) as (_ & AM & _ & POS & MODS & _ & SR).
  pose proof (AsanRepFrame.pos_mod_ge E (sc_map_size sc) kPageSize POS MODS ltac:(unfold kPageSize; lia)) as GE.
  pose proof WE as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & _). pose proof (SR _ E7) as XR. cbn [fst snd] in XR.
  apply AG_offspace; [do 5 right; left; exists sc; split; [exact Hsc| exact Ha]| | unfold kPageSize in GE; clear -Ha XR GE; lia| unfold app_mem, kPageSize in *; clear -Ha AM GE; lia].
  intros HT. destruct (Tpage_apart a HT) as (_ & _ & NS & _). apply (NS sc Hsc). unfold kPageSize in GE. clear -Ha GE. lia.
Qed.
Lemma AGdep : forall a, DepotFP E s a -> m' (wa a) = m (wa a).
Proof.
  intros a Ha. pose proof Tpl as [[T1 T2] T3]. destruct AK as [mo K]. pose proof (proj1 WF) as (E1 & E2 & _). rewrite kHighMemBeg_val in E2.
  assert (FPa : arep_fp E (DepotFP E) s a) by (do 8 right; left; exact Ha).
  destruct (DepotFP_where E s a Ha) as [(x & Hx & R)|[(b & Hb & R)|(b & Hb & R)]].
  - assert (Hx' : In x (arep_img_ranges E ++ depot_static E)) by (apply in_app_iff; right; exact Hx).
    pose proof (IMG_LOW x Hx') as [L1 L2].
    apply AG_offspace; [exact FPa| clear -R L1 L2 T1 T2; lia| clear -R L1 L2 E2; lia| rewrite kLowAppEnd_val; clear -R L2; lia].
  - pose proof (BS b kDepotNodeBlockBytes (or_introl (conj Hb eq_refl))) as (AM & _ & BR & _). unfold app_mem in AM.
    apply AG_offspace; [exact FPa| | clear -R BR; lia| clear -R AM; lia].
    intros HT. destruct (Tpage_apart a HT) as (_ & _ & _ & NB & _). exact (NB b kDepotNodeBlockBytes (or_introl (conj Hb eq_refl)) R).
  - pose proof (BS b kStoreBlockBytes (or_intror (conj Hb eq_refl))) as (AM & _ & BR & _). unfold app_mem in AM.
    apply AG_offspace; [exact FPa| | clear -R BR; lia| clear -R AM; lia].
    intros HT. destruct (Tpage_apart a HT) as (_ & _ & _ & NB & _). exact (NB b kStoreBlockBytes (or_intror (conj Hb eq_refl)) R).
Qed.

(* [comment removed for export] *)
Lemma carved_block_below : forall c' a0, 1 <= c' <= kLargestClassID -> carved E s c' a0 ->
  region_beg SB c' <= a0 /\ a0 + class_size c' <= region_beg SB c' + rg_alloc_user (region_of s c').
Proof.
  intros c' a0 Hc' (k & K0 & KE & KB). pose proof (class_size_mod c' Hc') as [_ CS]. unfold region_of in KB. unfold region_of.
  rewrite KE. clear -K0 KB CS. split; nia.
Qed.

Lemma AG_inblock : forall a c' b0, arep_fp E (DepotFP E) s a -> 1 <= c' <= kLargestClassID -> carved E s c' b0 ->
  b0 <= a < b0 + class_size c' -> m' (wa a) = m (wa a).
Proof.
  intros a c' b0 Ha Hc' CV R. pose proof (carved_block_below c' b0 Hc' CV) as [L1 L2].
  pose proof reg_num as (R1 & R2 & R3 & _). pose proof (proj1 WF) as (E1 & E2 & E3 & E4 & _). rewrite kHighMemBeg_val in E2.
  pose proof WF as (_ & [_ WR] & _). destruct (WR c' Hc') as (W1 & _ & W3 & _). cbv zeta in W1, W3. unfold region_of in *.
  apply AG_fp; [exact Ha| | | | |];
    unfold region_of, ae_region_info, free_array, region_beg, kRegionSize, kFreeArrayOffset, kFreeArraySize, kRegSize, kSpaceSize, kLargestClassID in *.
  - intros HT. destruct (Tpage_apart a HT) as (NR & _). apply NR. clear -R L1 L2 W1 W3 E3 E4 Hc'. nia.
  - clear -R L1 L2 W1 W3 Hc' HCc. nia.
  - intros X. destruct (Z.eq_dec c' c) as [->|NE]; [clear -R X L1 L2 R1; nia|]. clear -R X L1 L2 W1 W3 R1 R2 Hc' HCc NE. nia.
  - clear -R L1 L2 W1 W3 R1 R2 R3 Hc' HCc. nia.
  - rewrite kLowAppEnd_val, kHighMemBeg_val. clear -R L1 E2 E3 Hc'. nia.
Qed.

Lemma AGcm : forall a cb cm, as_chunks s !! cb = Some cm -> chunk_meta_fp cm a -> m' (wa a) = m (wa a).
Proof.
  intros a cb cm Hcm Ha.
  pose proof (chunk_meta_in_block E P D s cb cm a WF Hcm Ha) as [BL BU].
  destruct (block_where E P D s cb cm WF Hcm) as [(J1 & J2 & c' & Hc' & _ & CV & _ & _ & SPAN)|(sc & Hsc & _ & L1 & L2)].
  - apply (AG_inblock a c' (blk_lo cm)); [do 6 right; left; exists cb, cm; split; [exact Hcm| exact Ha]| exact Hc'| exact CV| clear -BL BU SPAN; lia].
  - pose proof WF as (WE & _ & _ & _ & _ & (_ & _ & S3 & _) & _). destruct (S3 sc Hsc) as (_ & AM & _ & _ & _ & _ & SR).
    pose proof WE as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & _). pose proof (SR _ E7) as XR. cbn [fst snd] in XR.
    apply AG_offspace; [do 6 right; left; exists cb, cm; split; [exact Hcm| exact Ha]| | unfold kPageSize in L1; clear -BL BU L1 L2 XR; lia| unfold app_mem, kPageSize in *; clear -BL BU L1 L2 AM; lia].
    intros HT. destruct (Tpage_apart a HT) as (_ & _ & NS & _). apply (NS sc Hsc). unfold kPageSize in L1. clear -BL BU L1 L2. lia.
Qed.
Lemma AGbat : forall a b, In b (as_tq s ++ as_gq s) -> b_addr b <= a < b_addr b + 24 + 8 * kBatchCap -> m' (wa a) = m (wa a).
Proof.
  intros a b Hb Ha. pose proof WF as (WE & WR & _ & _ & WQ & _).
  destruct (batch_block E D s b WQ ltac:(unfold all_batches; rewrite app_assoc; apply in_app_iff; left; exact Hb)) as (CV & _).
  assert (HB24 : 1 <= kBatchClass <= kLargestClassID) by (unfold kBatchClass, kLargestClassID; lia).
  assert (CS : class_size kBatchClass = 8192) by reflexivity.
  apply (AG_inblock a kBatchClass (b_addr b)); [do 7 right; left; exists b; split; [exact Hb| exact Ha]| exact HB24| exact CV| unfold kBatchCap in Ha; clear -Ha CS; lia].
Qed.

(* [comment removed for export] *)
Lemma RG_any : forall a0, AWf E P D a0 -> forall c', 0 <= c' < 32 ->
  0 <= rg_mapped_user (region_of a0 c') <= kFreeArrayOffset /\ 0 <= rg_mapped_fa (region_of a0 c') <= kFreeArraySize.
Proof.
  clear. intros a0 WF0 c' Hc'. pose proof WF0 as (_ & [WR0 WR] & _). destruct (Z_le_dec 1 c'); [destruct (Z_le_dec c' kLargestClassID)|].
  - destruct (WR c' ltac:(lia)) as (A1 & _ & A2 & _ & A3 & _ & A4 & _). cbv zeta in *. clear -A1 A2 A3 A4. lia.
  - unfold region_of, get_region. destruct (as_regions a0 !! c') as [r0|] eqn:Hr; [pose proof (WR0 c' r0 Hr); lia|]. cbn. unfold kFreeArrayOffset, kFreeArraySize; lia.
  - unfold region_of, get_region. destruct (as_regions a0 !! c') as [r0|] eqn:Hr; [pose proof (WR0 c' r0 Hr); lia|]. cbn. unfold kFreeArrayOffset, kFreeArraySize; lia.
Qed.
Lemma space_resv : forall a, SB <= a < SB + kSpaceSize + 0x1000 -> ae_resv_beg E <= a < ae_resv_beg E + 0x2000011000.
Proof. intros a Ha. pose proof (proj1 WF) as (E1 & E2 & E3 & E4 & _). clear -Ha E3 E4. lia. Qed.

(* [comment removed for export] *)
Lemma AGri_other : forall a c', 0 <= c' < kNumClasses -> c' <> c -> RI + kRegSize * c' <= a < RI + kRegSize * c' + kRegSize -> m' (wa a) = m (wa a).
Proof.
  intros a c' Hc' NE Ha. pose proof reg_num as (R1 & R2 & R3 & _). pose proof (proj1 WF) as (E1 & E2 & E3 & E4 & _). rewrite kHighMemBeg_val in E2.
  unfold kNumClasses in Hc'.
  apply AG_fp; unfold ae_region_info, free_array, region_beg, kRegionSize, kFreeArrayOffset, kFreeArraySize, kRegSize, kSpaceSize, kNumClasses, kLargestClassID in *.
  - right; left. unfold ae_region_info, kRegSize, kNumClasses, kSpaceSize. clear -Ha Hc'. lia.
  - intros HT. destruct (Tpage_apart a HT) as (NR & _). apply NR. clear -Ha Hc' E3 E4. lia.
  - clear -Ha Hc' NE. lia.
  - clear -Ha Hc' R1 R2 HCc. lia.
  - clear -Ha Hc' R1 R2 R3 HCc. lia.
  - rewrite kLowAppEnd_val, kHighMemBeg_val. clear -Ha Hc' E2 E3. lia.
Qed.
(* [comment removed for export] *)
Lemma AGmap_other : forall a c', 0 <= c' < kNumClasses -> c' <> c ->
  (region_beg SB c' <= a < region_beg SB c' + rg_mapped_user (region_of s c') \/ free_array SB c' <= a < free_array SB c' + rg_mapped_fa (region_of s c')) ->
  (region_beg SB c' <= a < region_beg SB c' + rg_mapped_user (region_of s c') -> arep_fp E (DepotFP E) s a) ->
  m' (wa a) = m (wa a).
Proof.
  intros a c' Hc' NE Ha FPu. pose proof reg_num as (R1 & R2 & R3 & _). pose proof (proj1 WF) as (E1 & E2 & E3 & E4 & _). rewrite kHighMemBeg_val in E2.
  unfold kNumClasses in Hc'. pose proof (RG_any s WF c' Hc') as [G1 G2].
  apply AG_fp; unfold ae_region_info, free_array, region_beg, kRegionSize, kFreeArrayOffset, kFreeArraySize, kRegSize, kSpaceSize, kNumClasses, kLargestClassID in *.
  - destruct Ha as [Ha|Ha]; [exact (FPu Ha)|]. do 3 right; left. exists c'. split; [unfold kNumClasses; clear -Hc'; lia| exact Ha].
  - intros HT. destruct (Tpage_apart a HT) as (NR & _). apply NR. clear -Ha Hc' G1 G2 E3 E4. lia.
  - clear -Ha Hc' G1 G2 HCc. lia.
  - clear -Ha Hc' NE G1 G2 R1 R2 HCc. lia.
  - clear -Ha Hc' NE G1 G2 R1 R2 R3 HCc. lia.
  - rewrite kLowAppEnd_val, kHighMemBeg_val. clear -Ha Hc' G1 G2 E2 E3. lia.
Qed.
Lemma AGfa_keep : forall a, FA <= a < FA + 4 * Z.of_nat keep -> m' (wa a) = m (wa a).
Proof.
  intros a Ha. pose proof reg_num as (R1 & R2 & R3 & R4 & _). pose proof (proj1 WF) as (E1 & E2 & E3 & E4 & _). rewrite kHighMemBeg_val in E2.
  pose proof KEEP as (_ & K2 & _). apply Nat2Z.inj_le in K2.
  apply AG_fp; unfold ae_region_info, free_array, region_beg, kRegionSize, kFreeArrayOffset, kFreeArraySize, kRegSize, kSpaceSize, kNumClasses, kLargestClassID in *.
  - do 3 right; left. exists c. split; [unfold kNumClasses; clear -HCc; lia| unfold free_array, region_beg, kRegionSize, kFreeArrayOffset; clear -Ha K2 R4; lia].
  - intros HT. destruct (Tpage_apart a HT) as (NR & _). apply NR. clear -Ha K2 R3 R4 HCc E3 E4. lia.
  - clear -Ha HCc K2 R3 R4. lia.
  - clear -Ha K2 R1 R2 R3 R4 HCc. lia.
  - clear -Ha. lia.
  - rewrite kLowAppEnd_val, kHighMemBeg_val. clear -Ha HCc E2 E3. lia.
Qed.

(* [comment removed for export] *)
Definition thr_written (z : Z) : Prop :=
     (exists i, 0 <= i < kNumClasses /\ T + kThrCache + kPerClassSize * i + 4 <= z < T + kThrCache + kPerClassSize * i + 16)
  \/ (ROW <= z < ROW + kPerClassSize)
  \/ (T + kThrCacheStats + 24 <= z < T + kThrCacheStats + 32)
  \/ (T + kThrStats + 72 <= z < T + kThrStats + 88).
Lemma AG_T : forall z, T <= z < T + 4096 -> ~ thr_written z -> m' (wa z) = m (wa z).
Proof.
  intros z HT NW. pose proof Tpl as [[T1 T2] T3]. pose proof alloc_ceiling_range as CR.
  pose proof reg_num as (R1 & R2 & R3 & _). pose proof (proj1 WF) as (E1 & E2 & E3 & E4 & E5 & _). rewrite kHighMemBeg_val in E2.
  destruct (Tpage_apart z HT) as (NR & _ & _ & _ & NBAND & _).
  apply AG; [clear -HT T1 T3 CR; lia|]. unfold FPWref, thr_written in *. rewrite kLowAppEnd_val, kHighMemBeg_val in *.
  unfold ae_region_info, free_array, region_beg, kRegionSize, kFreeArrayOffset, kFreeArraySize, kRegSize, kSpaceSize, kNumClasses, kLargestClassID, kShadowBase in *.
  intros [X|[X|[X|[X|[X|[X|[X|[X|[X|X]]]]]]]]].
  - clear -X HT T3 LO. lia.
  - apply NR. clear -X HCc E3 E4. lia.
  - apply NW. left. exact X.
  - apply NW. right; left. exact X.
  - apply NW. do 2 right; left. exact X.
  - apply NW. do 3 right. exact X.
  - apply NR. clear -X R1 R2 HCc E3 E4. lia.
  - apply NR. clear -X R1 R2 R3 HCc E3 E4. lia.
  - apply NBAND. clear -X R1 R2 E2 E3 E4 E5 CR HCc. Z.div_mod_to_equations. lia.
  - apply NBAND. clear -X R1 R2 R3 E2 E3 E4 E5 CR HCc. Z.div_mod_to_equations. lia.
Qed.
Lemma AGthr_cells : forall A k, T <= A -> A + k <= T + 4096 ->
  (A + k <= T + kThrCache
   \/ (T + kThrCacheStats <= A /\ A + k <= T + kThrCacheStats + 24)
   \/ (T + kThrCacheStats + 32 <= A /\ A + k <= T + kThrStats + 72)
   \/ T + kThrStats + 88 <= A
   \/ (exists i, 0 <= i < kNumClasses /\ i <> c /\
         ((T + kThrCache + kPerClassSize * i <= A /\ A + k <= T + kThrCache + kPerClassSize * i + 4)
          \/ (T + kThrCache + kPerClassSize * i + 16 <= A /\ A + k <= T + kThrCache + kPerClassSize * i + kPerClassSize)))) ->
  agree_on m m' A k.
Proof.
  intros A k H0 H1 H2 z Hz. apply AG_T; [clear -Hz H0 H1; lia|]. unfold thr_written.
  unfold kThrCache, kThrCacheStats, kThrStats, kPerClassSize, kNumClasses, kLargestClassID in *.
  intros [(i & Hi & X)|[X|[X|X]]]; destruct H2 as [Y|[Y|[Y|[Y|(j & Hj & NE & Y)]]]];
    first [clear -Hz Hi X Y; lia| clear -Hz Hi Hj X Y; lia| clear -Hz HCc X Y; lia| clear -Hz HCc Hj X Y NE; lia].
Qed.
Ltac thr_ag := apply AGthr_cells; unfold kThrUnwinding, kThrCache, kThrCacheStats, kThrStats, kPerClassSize, kThrStackTop, kThrQCache, kNumClasses in *;
  cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]; try lia.


(* [comment removed for export] *)
Lemma repB_ref : arep_regioninfo segs E s' m'.
Proof.
  pose proof REP as (_ & RB0 & _). intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE]; [exact NC_ri|].
  rewrite (Ereg c' NE). eapply rw_cells_agree'; [| exact (RB0 c' Hc')]. intros x Hx. apply (AGri_other x c' Hc' NE).
  revert Hx. unfold region_cells. cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul zeros repeat]. unfold kRegSize. clear. lia.
Qed.

(* [comment removed for export] *)
Lemma repC_ref : arep_region_mem segs E s' m'.
Proof.
  pose proof REP as (_ & _ & RC0 & _). intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE]; [cbv zeta; split; [exact NC_um| exact NC_fa]|].
  destruct (RC0 c' Hc') as (X1 & junk & X2 & L). cbv zeta. rewrite (Ereg c' NE). split; [eapply wr_at_transport; [exact X1| exact WM]|].
  exists junk. split; [| exact L]. eapply u32arr_agree; [| exact X2]. intros x Hx.
  pose proof (RG_any s WF c' ltac:(unfold kNumClasses in Hc'; exact Hc')) as [G1 G2]. rewrite length_app, length_map in Hx.
  apply (AGmap_other x c' Hc' NE); [right; clear -Hx L; lia| intros [_ Hx2]; exfalso].
  unfold free_array, kFreeArrayOffset in *. clear -Hx Hx2 G1. lia.
Qed.

(* [comment removed for export] *)
Lemma repD_ref : arep_thread segs E s' m'.
Proof.
  pose proof REP as (_ & _ & _ & RD & _). destruct RD as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8). pose proof HCc as HC. unfold kLargestClassID in HC.
  unfold arep_thread. unfold tq_bytes. rewrite Etq, Ecal. fold (tq_bytes s).
  split; [eapply rw_cells_agree'; [| exact D1]; thr_ag|].
  split; [eapply rw_cells_agree'; [| exact D2]; thr_ag|].
  split; [eapply rw_cells_agree'; [| exact D3]; thr_ag|].
  split.
  { intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE]; [exact NC_row|].
    destruct (D4 c' Hc') as (X1 & junk & X2 & L). rewrite (Ecache c' NE). split; [exact (NC_rows c' Hc' NE)|].
    exists junk. split; [| exact L]. eapply u32arr_agree; [| exact X2]. rewrite length_app, length_map, L.
    apply AGthr_cells; unfold kThrCache, kPerClassSize, kNumClasses in *; [clear -Hc'; lia| clear -Hc'; lia|].
    do 4 right. exists c'. split; [exact Hc'|]. split; [exact NE|]. right. clear; lia. }
  split.
  { apply rh_split with (cs1 := [C8 (zw (as_cache_allocated s))]) in D5. destruct D5 as [D5 _].
    apply (rh_join_at segs m' _ (T + kThrCacheStats + 24) [C8 (zw (as_cache_allocated s))]); [| exact NC_cst| cbn; lia].
    eapply rw_cells_agree'; [| exact D5]. thr_ag. }
  split.
  { (* [comment removed for export] *)
    pose proof Ets as (T0 & T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T11 & T12 & T13 & _).
    apply u64arr_of_cells.
    - destruct D6 as [_ W6]. eapply wr_at_transport; [| exact WM]. unfold tstats_words in *. rewrite length_map in *. cbn [length] in *. exact W6.
    - apply rh_split with (cs1 := [C8 (zw (ts_mmaps (as_ts s')))]) in NC_thr as [N9 N10]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in N10.
      unfold tstats_words. rewrite T0, T1, T2, T3, T4, T5, T6, T7, T8, T11, T12, T13. intros i w Hi.
      Ltac oldw D6 i := eapply rw_cells_agree'; [| exact (u64arr_cell segs _ _ _ i _ D6 eq_refl)]; thr_ag.
      do 9 (destruct i as [|i]; [cbn in Hi; injection Hi as <-; oldw D6 0%nat || oldw D6 1%nat || oldw D6 2%nat || oldw D6 3%nat || oldw D6 4%nat || oldw D6 5%nat || oldw D6 6%nat || oldw D6 7%nat || oldw D6 8%nat |]).
      destruct i as [|i]; [cbn in Hi; injection Hi as <-; replace (T + kThrStats + 8 * Z.of_nat 9) with (T + kThrStats + 72) by lia; exact N9|].
      destruct i as [|i]; [cbn in Hi; injection Hi as <-; replace (T + kThrStats + 8 * Z.of_nat 10) with (T + kThrStats + 72 + 8) by lia; exact N10|].
      do 3 (destruct i as [|i]; [cbn in Hi; injection Hi as <-; oldw D6 11%nat || oldw D6 12%nat || oldw D6 13%nat |]).
      destruct i; cbn in Hi; discriminate. }
  split.
  { pose proof Ets as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TB). rewrite TB.
    eapply u64arr_agree; [| exact D7]. rewrite length_map, length_ziota. thr_ag. }
  eapply rw_cells_agree'; [| exact D8]; thr_ag.
Qed.

(* [comment removed for export] *)
#[warnings="-notation-for-abbreviation"] Notation WU x := (RB + rg_mapped_user r <= x < RB + rg_mapped_user r').
#[warnings="-notation-for-abbreviation"] Notation WF_ x := (FA + rg_mapped_fa r <= x < FA + rg_mapped_fa r').

Lemma ref_in_sec_map : forall x, in_some_sec_map s' x = in_some_sec_map s x.
Proof. intros x. unfold in_some_sec_map. rewrite Esec. reflexivity. Qed.
Lemma ref_find_chunk : forall x, find_chunk s' x = find_chunk s x.
Proof. intros x. unfold find_chunk. rewrite Echunks. reflexivity. Qed.

Lemma rm_intro_u : forall a0 c' x, 0 <= c' < 32 -> region_beg SB c' <= x < region_beg SB c' + rg_mapped_user (region_of a0 c') -> in_some_region_map E a0 x = true.
Proof.
  clear. intros a0 c' x Hc' Hx. unfold in_some_region_map. apply orb_true_iff. left. apply existsb_exists. exists c'.
  split; [apply In_ziota; lia|]. apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; lia.
Qed.
Lemma rm_intro_f : forall a0 c' x, 0 <= c' < 32 -> free_array SB c' <= x < free_array SB c' + rg_mapped_fa (region_of a0 c') -> in_some_region_map E a0 x = true.
Proof.
  clear. intros a0 c' x Hc' Hx. unfold in_some_region_map. apply orb_true_iff. right. apply existsb_exists. exists c'.
  split; [apply In_ziota; lia|]. apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; lia.
Qed.
Lemma rm_elim : forall a0 x, in_some_region_map E a0 x = true -> exists c', 0 <= c' < 32 /\
  (region_beg SB c' <= x < region_beg SB c' + rg_mapped_user (region_of a0 c') \/ free_array SB c' <= x < free_array SB c' + rg_mapped_fa (region_of a0 c')).
Proof.
  clear. intros a0 x H. unfold in_some_region_map in H. apply orb_true_iff in H as [H|H]; apply existsb_exists in H as (c' & Hc & Hb);
    apply In_ziota in Hc; apply andb_true_iff in Hb as [B1 B2]; apply Z.leb_le in B1; apply Z.ltb_lt in B2; exists c'; cbn in Hc; (split; [lia|]); [left| right]; lia.
Qed.

Lemma ref_rm_mono : forall x, in_some_region_map E s x = true -> in_some_region_map E s' x = true.
Proof.
  intros x H. destruct (rm_elim s x H) as (c' & Hc' & R). pose proof HCc as HC. unfold kLargestClassID in HC.
  destruct (Z.eq_dec c' c) as [->|NE].
  - destruct R as [R|R]; [eapply (rm_intro_u s' c); [lia|]| eapply (rm_intro_f s' c); [lia|]]; clear -R GRU GRF; lia.
  - destruct R as [R|R]; [eapply (rm_intro_u s' c'); [lia|]| eapply (rm_intro_f s' c'); [lia|]]; rewrite (Ereg c' NE); exact R.
Qed.
Lemma ref_rm_new : forall x, WU x \/ WF_ x -> in_some_region_map E s' x = true.
Proof.
  intros x [R|R]; pose proof reg_num as (R1 & R2 & R3 & _); pose proof HCc as HC; unfold kLargestClassID in HC;
    [eapply (rm_intro_u s' c); [lia|]| eapply (rm_intro_f s' c); [lia|]]; clear -R R1 R2 R3; lia.
Qed.
Lemma ref_rm_back : forall x, in_some_region_map E s' x = true -> in_some_region_map E s x = true \/ WU x \/ WF_ x.
Proof.
  intros x H. destruct (rm_elim s' x H) as (c' & Hc' & R). pose proof HCc as HC. unfold kLargestClassID in HC.
  destruct (Z.eq_dec c' c) as [->|NE].
  - pose proof reg_num as (R1 & R2 & R3 & _). destruct R as [R|R].
    + destruct (Z_lt_le_dec x (RB + rg_mapped_user r)) as [LT|GE]; [left; eapply (rm_intro_u s c); [lia| clear -R LT; lia]| right; left; clear -R GE; lia].
    + destruct (Z_lt_le_dec x (FA + rg_mapped_fa r)) as [LT|GE]; [left; eapply (rm_intro_f s c); [lia| clear -R LT; lia]| right; right; clear -R GE; lia].
  - left. rewrite (Ereg c' NE) in R. destruct R as [R|R]; [eapply (rm_intro_u s c'); [lia| exact R]| eapply (rm_intro_f s c'); [lia| exact R]].
Qed.

Lemma Sh_ref_out : forall x, ~ WU x -> ~ WF_ x -> Sh E s' x = Sh E s x.
Proof.
  intros x NU NF. unfold Sh. rewrite ref_in_sec_map, ref_find_chunk.
  destruct (in_some_region_map E s x) eqn:RM; [rewrite (ref_rm_mono x RM); reflexivity|].
  destruct (in_some_region_map E s' x) eqn:RM'; [| reflexivity]. exfalso. destruct (ref_rm_back x RM') as [X|[X|X]]; [congruence| exact (NU X)| exact (NF X)].
Qed.

(* [comment removed for export] *)
Lemma find_chunk_win : forall x, WU x \/ WF_ x -> find_chunk s x = None.
Proof.
  intros x Hx. destruct (find_chunk s x) as [cm|] eqn:FC; [exfalso| reflexivity].
  destruct (find_chunk_some s x cm FC) as (cb & Hcm & R).
  assert (SPAN : blk_hi s cm = cm_alloc_beg cm + block_span cm) by (unfold blk_hi, block_span; destruct (cm_prim cm); lia).
  pose proof reg_num as (R1 & R2 & R3 & _). pose proof (proj1 WF) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & _).
  destruct (block_where E P D s cb cm WF Hcm) as [(J1 & J2 & c' & Hc' & _ & CV & K1 & K2 & K3)|(sc & Hsc & _ & L1 & L2)]; unfold blk_lo in *.
  - pose proof (carved_block_below c' (cm_alloc_beg cm) Hc' CV) as [B1 B2].
    pose proof WF as (_ & [_ WR] & _). destruct (WR c' Hc') as (W1 & _ & W3 & _). cbv zeta in W1, W3.
    unfold free_array, region_beg, kRegionSize, kFreeArrayOffset, kFreeArraySize, kLargestClassID in *.
    destruct (Z.eq_dec c' c) as [->|NE]; [unfold region_of in *; clear -Hx R SPAN B1 B2 K2 K3 R1 R3; lia|].
    clear -Hx R SPAN B1 B2 K2 K3 W1 W3 R1 R2 R3 Hc' HCc NE. lia.
  - pose proof WF as (_ & _ & _ & _ & _ & (_ & _ & S3 & _) & _). destruct (S3 sc Hsc) as (_ & AM & _ & _ & _ & _ & SR).
    pose proof (SR _ E7) as XR. cbn [fst snd] in XR.
    assert (SP : ae_resv_beg E <= x < ae_resv_beg E + 0x2000011000).
    { apply space_resv. unfold free_array, region_beg, kRegionSize, kFreeArrayOffset, kFreeArraySize, kLargestClassID, kSpaceSize in *. clear -Hx R1 R2 R3 HCc. lia. }
    unfold kPageSize in L1. clear -R SPAN L1 L2 XR SP. lia.
Qed.
Lemma Sh_ref_new : forall x, WU x \/ WF_ x -> Sh E s' x = Some kAsanHeapLeftRedzoneMagic.
Proof.
  intros x Hx. unfold Sh. rewrite (ref_rm_new x Hx), ref_find_chunk, (find_chunk_win x Hx). reflexivity.
Qed.

Lemma Sh_granule_range : forall x v, Sh E s x = Some v -> 0 <= x < 2^47.
Proof.
  intros x v Hx. pose proof WF as WF0. pose proof alloc_ceiling_range as CR. unfold Sh in Hx.
  destruct (in_some_region_map E s x) eqn:RM.
  - pose proof (region_map_in_space E P D s x WF0 RM) as SP. pose proof (proj1 WF0) as (E1 & E2 & E3 & E4 & E5 & _).
    unfold kSpaceSize in *. clear -SP E2 E3 E4 E5 CR. rewrite kHighMemBeg_val in E2. lia.
  - destruct (in_some_sec_map s x) eqn:SM.
    + unfold in_some_sec_map in SM. apply existsb_exists in SM as (sc & Hsc & Hb). apply andb_true_iff in Hb as [B1 B2].
      apply Z.leb_le in B1. apply Z.ltb_lt in B2. pose proof WF0 as (_ & _ & _ & _ & _ & (_ & _ & S3 & _) & _). destruct (S3 sc Hsc) as (_ & HB & S & _).
      unfold app_mem in HB. rewrite kHighMemBeg_val, kLowAppEnd_val in HB. clear -B1 B2 HB S CR. lia.
    + cbn [orb] in Hx. destruct (sh_default_dom E x && negb (sh_excluded E x)) eqn:C; [|discriminate].
      apply andb_true_iff in C as [C _]. unfold sh_default_dom in C. apply Bool.orb_true_iff in C as [C|C].
      * apply andb_true_iff in C as [C _]. apply andb_true_iff in C as [C1 C2]. apply Z.leb_le in C1. apply Z.ltb_lt in C2.
        rewrite kLowAppEnd_val in C2. clear -C1 C2. lia.
      * apply andb_true_iff in C as [C1 C2]. apply Z.leb_le in C1. apply Z.leb_le in C2.
        rewrite kHighMemBeg_val in C1. unfold kHighMemEnd in C2. clear -C1 C2. lia.
Qed.

(* [comment removed for export] *)
Lemma AGsh_out : forall g v, Sh E s (8 * g) = Some v -> ~ WU (8 * g) -> ~ WF_ (8 * g) ->
  m' (wa (kShadowBase + g)) = m (wa (kShadowBase + g)).
Proof.
  intros g v Hg NU NF. pose proof (Sh_granule_range _ _ Hg) as GR. pose proof Tpl as [[T1 T2] T3]. pose proof alloc_ceiling_range as CR.
  pose proof reg_num as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & _). pose proof (proj1 WF) as (E1 & E2 & E3 & E4 & E5 & _). rewrite kHighMemBeg_val in E2.
  assert (BAND : kLowAppEnd < kShadowBase + g < kHighMemBeg) by (rewrite kLowAppEnd_val, kHighMemBeg_val; unfold kShadowBase; clear -GR; lia).
  rewrite kLowAppEnd_val, kHighMemBeg_val in BAND.
  apply AG; [unfold kShadowBase in *; clear -GR; lia|]. unfold FPWref.
  unfold free_array, region_beg in *.
  unfold ae_region_info, kRegionSize, kFreeArrayOffset, kFreeArraySize, kRegSize, kSpaceSize, kNumClasses, kLargestClassID, kShadowBase,
    kThrCache, kPerClassSize, kThrCacheStats, kThrStats in *.
  intros [X|[X|[(i & Hi & X)|[X|[X|[X|[X|[X|[X|X]]]]]]]]].
  - clear -X BAND E2 E5 LO. lia.
  - clear -X BAND E2 E3 HCc. lia.
  - destruct (Tpage_apart (2147450880 + g) ltac:(clear -X Hi; lia)) as (_ & _ & _ & _ & NBAND & _). apply NBAND. rewrite kLowAppEnd_val, kHighMemBeg_val. exact BAND.
  - destruct (Tpage_apart (2147450880 + g) ltac:(clear -X HCc; lia)) as (_ & _ & _ & _ & NBAND & _). apply NBAND. rewrite kLowAppEnd_val, kHighMemBeg_val. exact BAND.
  - destruct (Tpage_apart (2147450880 + g) ltac:(clear -X; lia)) as (_ & _ & _ & _ & NBAND & _). apply NBAND. rewrite kLowAppEnd_val, kHighMemBeg_val. exact BAND.
  - destruct (Tpage_apart (2147450880 + g) ltac:(clear -X; lia)) as (_ & _ & _ & _ & NBAND & _). apply NBAND. rewrite kLowAppEnd_val, kHighMemBeg_val. exact BAND.
  - clear -X BAND R1 R2 E2 E3 HCc. lia.
  - clear -X BAND R1 R2 R3 E2 E3 HCc. lia.
  - apply NU. clear -X R5 R6 R9. Z.div_mod_to_equations. lia.
  - apply NF. clear -X R7 R8 R9. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma repJ_ref : arep_shadow segs E s' m'.
Proof.
  pose proof REP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & RJ). pose proof reg_num as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & _).
  intros g v Hg.
  destruct (Z_le_gt_dec (RB + rg_mapped_user r) (8 * g)) as [U1|U1]; [destruct (Z_lt_le_dec (8 * g) (RB + rg_mapped_user r')) as [U2|U2]|].
  { (* [comment removed for export] *)
    rewrite (Sh_ref_new (8 * g) (or_introl (conj U1 U2))) in Hg. injection Hg as <-.
    replace (kShadowBase + g) with (kShadowBase + (RB + rg_mapped_user r) / 8 + (g - (RB + rg_mapped_user r) / 8)) by lia.
    apply (CB_byte segs m' _ _ (zb kAsanHeapLeftRedzoneMagic) (g - (RB + rg_mapped_user r) / 8) NC_shu).
    clear -U1 U2 R5 R6 R9. Z.div_mod_to_equations. lia. }
  all: destruct (Z_le_gt_dec (FA + rg_mapped_fa r) (8 * g)) as [F1|F1]; [destruct (Z_lt_le_dec (8 * g) (FA + rg_mapped_fa r')) as [F2|F2]|].
  1,4: rewrite (Sh_ref_new (8 * g) (or_intror (conj F1 F2))) in Hg; injection Hg as <-;
    replace (kShadowBase + g) with (kShadowBase + (FA + rg_mapped_fa r) / 8 + (g - (FA + rg_mapped_fa r) / 8)) by lia;
    apply (CB_byte segs m' _ _ (zb kAsanHeapLeftRedzoneMagic) (g - (FA + rg_mapped_fa r) / 8) NC_shf);
    unfold free_array, kFreeArrayOffset in *; clear -F1 F2 R7 R8 R9; Z.div_mod_to_equations; lia.
  all: assert (NU : ~ WU (8 * g)) by (first [clear -U1 U2| clear -U1]; lia).
  all: assert (NF : ~ WF_ (8 * g)) by (first [clear -F1 F2| clear -F1]; lia).
  all: rewrite (Sh_ref_out (8 * g) NU NF) in Hg; eapply rw_cells_agree'; [| exact (RJ g v Hg)]; intros x Hx; cbn in Hx; replace x with (kShadowBase + g) by lia;
       exact (AGsh_out g v Hg NU NF).
Qed.

Theorem ARep_refill : AREP s' m'.
Proof.
  pose proof REP as (RA & RB0 & RC0 & _ & RE & RF & RG & RH & RI & RJ).
  apply (ARep_ref_xfer s s' m'); try assumption.
  - exact (frameA' segs E s m m' AGimg RA).
  - exact repB_ref.
  - exact repC_ref.
  - exact repD_ref.
  - exact (frameE' segs E s m m' WM AGptr AGsec RE).
  - exact (frameF' segs s m m' AGcm RF).
  - exact (frameG' segs s m m' AGbat RG).
  - exact (frameH' segs E s m m' WM AGdep RH).
  - exact (frameI' segs E s m m' WM AGimg RI).
  - exact repJ_ref.
Qed.
End REF.

(* [comment removed for export] *)
Section GAP.
Variables (P : list Z) (D : list batch) (s : astate).
Hypothesis WF : AWf E P D s.

Lemma Sh_space_gap : forall x, SB <= x < SB + kSpaceSize -> in_some_region_map E s x = false -> Sh E s x = Some 0.
Proof.
  intros x Hx RM. pose proof WF as (WE & _ & _ & _ & _ & (_ & _ & S3 & _) & _). pose proof alloc_ceiling_range as CR.
  pose proof WE as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & E28 & _).
  unfold Sh. rewrite RM.
  replace (in_some_sec_map s x) with false.
  2:{ symmetry. destruct (in_some_sec_map s x) eqn:SM; [| reflexivity]. exfalso. unfold in_some_sec_map in SM. apply existsb_exists in SM as (sc & Hsc & Hb).
      apply andb_true_iff in Hb as [B1 B2]. apply Z.leb_le in B1. apply Z.ltb_lt in B2.
      destruct (S3 sc Hsc) as (_ & _ & _ & _ & _ & _ & RSV). specialize (RSV _ E7). cbn [fst snd] in RSV. unfold kSpaceSize in *. clear -Hx B1 B2 RSV E3 E4. lia. }
  cbn [orb]. unfold sh_default_dom, sh_excluded, in_fakestack, in_iarena, in_reginfo, in_img.
  rewrite kHighMemBeg_val in E2 |- *. rewrite kLowAppEnd_val. unfold kHighMemEnd, kIArenaLen, kSpaceSize, kPageSize in *.
  replace (17594333495296 <=? x) with true by (symmetry; apply Z.leb_le; clear -Hx E2 E3; lia).
  replace (x <=? 2 ^ 47 - 1) with true by (symmetry; apply Z.leb_le; clear -Hx E4 E5 CR; lia).
  replace (x <? ae_fs_beg E + ae_fs_len E) with (negb (ae_fs_beg E <=? x)).
  2:{ destruct (Z.leb_spec (ae_fs_beg E) x); cbn; symmetry; [apply Z.ltb_ge| apply Z.ltb_lt]; clear -Hx H E3 E4 E11 E12; lia. }
  replace (x <? ae_iarena E + 65536) with (negb (ae_iarena E <=? x)).
  2:{ destruct (Z.leb_spec (ae_iarena E) x); cbn; symmetry; [apply Z.ltb_ge| apply Z.ltb_lt]; clear -Hx H E3 E4 E27; lia. }
  replace (SB + 2 ^ 37 <=? x) with false by (symmetry; apply Z.leb_gt; clear -Hx; lia).
  rewrite !Bool.andb_negb_r.
  match goal with |- (if (?b || _) && _ then _ else _) = _ => destruct b; reflexivity end.
Qed.

Lemma Sh_beyond_user : forall c x, 1 <= c <= kLargestClassID ->
  region_beg SB c + rg_mapped_user (region_of s c) <= x < region_beg SB c + rg_mapped_user (region_of s c) + kUserMapSize ->
  rg_mapped_user (region_of s c) + kUserMapSize <= kFreeArrayOffset -> Sh E s x = Some 0.
Proof.
  intros c x Hc Hx ROOM. unfold kLargestClassID in Hc.
  apply Sh_space_gap.
  - unfold region_beg, kRegionSize, kFreeArrayOffset, kUserMapSize, kSpaceSize in *. pose proof (RG_any P D s WF c ltac:(lia)) as [[G1 _] _]. clear -Hc Hx ROOM G1. lia.
  - destruct (in_some_region_map E s x) eqn:RM; [exfalso| reflexivity]. destruct (rm_elim s x RM) as (c' & Hc' & R).
    pose proof (RG_any P D s WF c' Hc') as [[G1 G2] [G3 G4]]. pose proof (RG_any P D s WF c ltac:(lia)) as [[G5 G6] _].
    unfold free_array, region_beg, kRegionSize, kFreeArrayOffset, kFreeArraySize, kUserMapSize in *.
    destruct (Z.eq_dec c' c) as [->|NE]; [clear -Hx R ROOM; lia|]. clear -Hc Hc' Hx R NE ROOM G1 G2 G3 G4 G5. lia.
Qed.
Lemma Sh_beyond_fa : forall c x, 1 <= c <= kLargestClassID ->
  free_array SB c + rg_mapped_fa (region_of s c) <= x < free_array SB c + rg_mapped_fa (region_of s c) + kFreeArrayMapSize ->
  rg_mapped_fa (region_of s c) + kFreeArrayMapSize <= kFreeArraySize -> Sh E s x = Some 0.
Proof.
  intros c x Hc Hx ROOM. unfold kLargestClassID in Hc.
  apply Sh_space_gap.
  - unfold free_array, region_beg, kRegionSize, kFreeArrayOffset, kFreeArraySize, kFreeArrayMapSize, kSpaceSize in *. pose proof (RG_any P D s WF c ltac:(lia)) as [_ [G1 _]]. clear -Hc Hx ROOM G1. lia.
  - destruct (in_some_region_map E s x) eqn:RM; [exfalso| reflexivity]. destruct (rm_elim s x RM) as (c' & Hc' & R).
    pose proof (RG_any P D s WF c' Hc') as [[G1 G2] [G3 G4]]. pose proof (RG_any P D s WF c ltac:(lia)) as [_ [G5 G6]].
    unfold free_array, region_beg, kRegionSize, kFreeArrayOffset, kFreeArraySize, kFreeArrayMapSize in *.
    destruct (Z.eq_dec c' c) as [->|NE]; [clear -Hx R ROOM G2 G3; lia|]. clear -Hc Hc' Hx R NE ROOM G1 G2 G3 G4 G5. lia.
Qed.
End GAP.
End RRF.
End RC__1.
