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
  AsanWf1 AsanWf3 AsanWf4 AsanWf5 AsanWf6 AsanClient AsanRepFrame AsanRepFrame2 AsanBudget AsanHit AsanRepHitB AsanRepX AsanRepCaB AsanRepRefillB AsanRepEnqB AsanRepX2B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section RT.
Variable segs : list Segment.
Variable E : aenv.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).
#[warnings="-notation-for-abbreviation"] Notation RW := (rw_cells segs).
#[warnings="-notation-for-abbreviation"] Notation SB := (ae_space_beg E).
#[warnings="-notation-for-abbreviation"] Notation T := (ae_thread E).
#[warnings="-notation-for-abbreviation"] Notation AREP := (ARep segs E (DepotR segs E)).
#[warnings="-notation-for-abbreviation"] Notation AREPX := (ARepX segs E (DepotR segs E)).

(* [comment removed for export] *)
Section DEFS.
Variables (n ab id : Z).
Definition tprim : bool := from_primary n.
Definition tc : Z := malloc_class n.
Definition trz : Z := rz_size n.
Definition tub : Z := ab + trz.
Definition tcb : Z := tub - kChunkHeaderSize.
Definition tspan : Z := if tprim then class_size tc else round_up (needed n) kPageSize.
Definition tcid : Z := class_id (needed n).
Definition tlarge : bool := kMaxSize <? needed n.
Definition tcm : chunkmeta := mkCM ab (rz_log n) (req n) (if tprim then Some tc else None) (CAllocated id).
Definition tail_st (s : astate) : astate :=
  upd_ts (ts_on_malloc (req n) (needed n) tlarge tcid) (upd_dead (delete tcb) (upd_chunks (fun ch => <[tcb := tcm]> ch) s)).
End DEFS.

Section TAIL.
Variables (s : astate) (m m' : mem) (lo n ab id : Z).
#[warnings="-notation-for-abbreviation"] Notation s' := (tail_st n ab id s).
#[warnings="-notation-for-abbreviation"] Notation prim := (tprim n).
#[warnings="-notation-for-abbreviation"] Notation c := (tc n).
#[warnings="-notation-for-abbreviation"] Notation rz := (trz n).
#[warnings="-notation-for-abbreviation"] Notation ub := (tub n ab).
#[warnings="-notation-for-abbreviation"] Notation cb := (tcb n ab).
#[warnings="-notation-for-abbreviation"] Notation span := (tspan n).
#[warnings="-notation-for-abbreviation"] Notation cid := (tcid n).
#[warnings="-notation-for-abbreviation"] Notation large := (tlarge n).
#[warnings="-notation-for-abbreviation"] Notation cm := (tcm n ab id).
#[warnings="-notation-for-abbreviation"] Notation t := (as_ts s).

(* [comment removed for export] *)
Ltac fld := unfold tail_st; destruct s; reflexivity.
Lemma tl_regions : as_regions s' = as_regions s. Proof. fld. Qed.
Lemma tl_cache_inited : as_cache_inited s' = as_cache_inited s. Proof. fld. Qed.
Lemma tl_cache : as_cache s' = as_cache s. Proof. fld. Qed.
Lemma tl_cache_allocated : as_cache_allocated s' = as_cache_allocated s. Proof. fld. Qed.
Lemma tl_cache_mapped : as_cache_mapped s' = as_cache_mapped s. Proof. fld. Qed.
Lemma tl_ptr : as_ptr_committed s' = as_ptr_committed s. Proof. fld. Qed.
Lemma tl_sec : as_sec s' = as_sec s. Proof. fld. Qed.
Lemma tl_sec_stats : as_sec_stats s' = as_sec_stats s. Proof. fld. Qed.
Lemma tl_glob_allocated : as_glob_allocated s' = as_glob_allocated s. Proof. fld. Qed.
Lemma tl_glob_mapped : as_glob_mapped s' = as_glob_mapped s. Proof. fld. Qed.
Lemma tl_chunks : as_chunks s' = <[cb := cm]> (as_chunks s). Proof. fld. Qed.
Lemma tl_tq : as_tq s' = as_tq s. Proof. fld. Qed.
Lemma tl_gq : as_gq s' = as_gq s. Proof. fld. Qed.
Lemma tl_keys : as_keys s' = as_keys s. Proof. fld. Qed.
Lemma tl_frames : as_frames s' = as_frames s. Proof. fld. Qed.
Lemma tl_ia : as_ia_inited s' = as_ia_inited s. Proof. fld. Qed.
Lemma tl_node_blocks : as_node_blocks s' = as_node_blocks s. Proof. fld. Qed.
Lemma tl_store_blocks : as_store_blocks s' = as_store_blocks s. Proof. fld. Qed.
Lemma tl_store_stored : as_store_stored s' = as_store_stored s. Proof. fld. Qed.
Lemma tl_ts : as_ts s' = ts_on_malloc (req n) (needed n) large cid t. Proof. fld. Qed.
Lemma tl_n_chunks : n_chunks s' = n_chunks s. Proof. fld. Qed.
Lemma tl_tq_bytes : tq_bytes s' = tq_bytes s. Proof. fld. Qed.
Lemma tl_gq_bytes : gq_bytes s' = gq_bytes s. Proof. fld. Qed.
Lemma tl_get_cache : forall c', get_cache s' c' = get_cache s c'. Proof. intros c'. unfold get_cache. rewrite tl_cache. reflexivity. Qed.
Lemma tl_region_of : forall c', region_of s' c' = region_of s c'. Proof. intros c'. unfold region_of, get_region. rewrite tl_regions. reflexivity. Qed.


(* [comment removed for export] *)
Definition FPWt (z : Z) : Prop :=
     lo <= z
  \/ (ab <= z < ab + span)
  \/ (kShadowBase + ab / 8 <= z < kShadowBase + (ab + span + 7) / 8)
  \/ (T + kThrStats <= z < T + kThrStats + 24)
  \/ (if large then T + kThrStats + 104 <= z < T + kThrStats + 112 else T + kThrStats + 112 + 8 * cid <= z < T + kThrStats + 112 + 8 * cid + 8).

Hypothesis Hn : 1 <= n < 2^40.
Hypothesis REPX : AREPX s m ab (ab + span).
Hypothesis WF : AWf E [] [] s.
Hypothesis WF' : AWf E [] [] s'.
Hypothesis FRESH : as_chunks s !! cb = None.
Hypothesis RENV : AsanRepEnqB.renv_ok E s.
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
Hypothesis BLK : if prim then carved E s c ab else exists sc, In sc (as_sec s) /\ sc_map_beg sc + kPageSize = ab /\ sc_map_size sc = map_size n.
(* [comment removed for export] *)
Hypothesis NFP : forall x, ab <= x < ab + span -> ~ arep_fp E (DepotFP E) s x.
Hypothesis WM : wmono segs m m'.
Hypothesis AG : forall z, 0 <= z < 2^64 -> ~ FPWt z -> m' (wa z) = m (wa z).
Hypothesis LO : alloc_ceiling <= lo.
(* [comment removed for export] *)
Hypothesis NC_hdr : exists hb1, Z.land hb1 127 = kHeaderByte1 /\ RW m' cb [C1 (zb kChunkAllocated); C1 (zb hb1); C2 (zw (req n / 2^32)); C4 (zw (req n)); C8 (zw id)].
Hypothesis NC_mag : 16 < rz -> RW m' ab [C8 (zw kAllocBegMagicVal); C8 (zw cb)].
Hypothesis NC_sh : forall g, ab <= 8 * g < ab + span -> RW m' (kShadowBase + g) [C1 (zb (chunk_shadow cm (8 * g)))].
Hypothesis NC_st : RW m' (T + kThrStats) [C8 (zw (ts_mallocs t + 1)); C8 (zw (ts_malloced t + req n)); C8 (zw (ts_malloced_redzones t + (needed n - req n)))].
Hypothesis NC_lg : large = true -> RW m' (T + kThrStats + 104) [C8 (zw (ts_malloc_large t + 1))].
Hypothesis NC_by : large = false -> RW m' (T + kThrStats + 112 + 8 * cid) [C8 (zw (match ts_by_size t !! cid with Some v => v | None => 0 end + 1))].

(* [comment removed for export] *)
Lemma REQ : req n = n. Proof. unfold req. clear -Hn. lia. Qed.
Lemma RZF : 16 <= rz <= 2048 /\ rz = 16 * 2 ^ rz_log n /\ rz mod 16 = 0.
Proof.
  pose proof (rz_size_pos n) as X. pose proof (rz_log_range n) as L. unfold trz, rz_size in *.
  split; [exact X|]. split; [reflexivity|].
  replace (16 * 2 ^ rz_log n) with (2 ^ rz_log n * 16) by lia. apply Z_mod_mult.
Qed.
Lemma CIDR : prim = true -> 1 <= c <= kLargestClassID /\ needed n <= class_size c /\ needed n = needed1 n.
Proof.
  unfold tc, tprim. intros PR.
  assert (N64 : 0 <= n <= 64512) by (pose proof (proj1 (from_primary_iff n ltac:(clear -Hn; lia)) PR); clear -H Hn; lia).
  pose proof (malloc_class_ok n N64) as [HC ND]. unfold needed. rewrite PR. split; [exact HC|]. split; [exact ND| reflexivity].
Qed.
Lemma NEEDF : rounded n + rz <= needed n /\ n <= rounded n /\ rounded n < n + 16 /\ rounded n mod 8 = 0.
Proof.
  pose proof (rounded_ge n) as (R1 & R2 & R3). unfold needed, needed1, trz. pose proof (rz_size_pos n) as X.
  destruct (from_primary n); clear -R1 R2 R3 X Hn; repeat split; lia.
Qed.
Lemma CID32 : large = false -> 0 <= cid < 32.
Proof.
  intros LG. unfold tcid. pose proof NEEDF as (N1 & N2 & _). pose proof RZF as (R1 & _). unfold tlarge, kMaxSize in LG. apply Z.ltb_ge in LG.
  pose proof (class_id_spec (needed n) ltac:(clear -N1 N2 R1 Hn LG; lia)) as (C1 & _). clear -C1. lia.
Qed.
(* [comment removed for export] *)
Lemma BLKF : ab mod 8 = 0 /\ span mod 8 = 0 /\ needed n <= span /\ 0 < ab /\ ab + span <= alloc_ceiling /\ (ab + span <= kLowAppEnd \/ kHighMemBeg <= ab)
  /\ (forall x, ab <= x < ab + span -> in_some_region_map E s x || in_some_sec_map s x = true).
Proof.
  pose proof WF as (WE & WR & _ & _ & _ & WS & _). pose proof WS as (_ & _ & WS3 & _).
  pose proof WE as (E1 & E2 & E3 & E4 & E5 & _). pose proof alloc_ceiling_range as CR.
  unfold tspan. generalize BLK. unfold tprim, tc. destruct (from_primary n) eqn:PR; intros B.
  - destruct (CIDR PR) as (HC & ND & _).
    pose proof (carved_in_space E s (malloc_class n) ab HC WR B) as [SP1 SP2].
    pose proof B as (k & Hk & Hab & Hk1). unfold region_of in Hk1. unfold region_beg in Hab.
    destruct (proj2 WR (malloc_class n) HC) as (RG1 & RG2 & RG3 & _). cbv zeta in RG1, RG2, RG3. unfold region_of in RG1, RG3.
    pose proof (class_size_mod (malloc_class n) HC) as [CM CS].
    rewrite kHighMemBeg_val in E2 |- *. unfold kSpaceSize, kRegionSize, kFreeArrayOffset in *.
    split; [rewrite Hab; clear -E1 CM Hk; Z.div_mod_to_equations; nia|].
    split; [clear -CM; Z.div_mod_to_equations; lia|]. split; [exact ND|].
    split; [clear -SP1 E2 E3; lia|]. split; [clear -SP2 E4 E5; lia|]. split; [right; clear -SP1 E2 E3; lia|].
    intros x Hx. apply orb_true_iff. left. unfold in_some_region_map. apply orb_true_iff. left.
    apply (existsb_In _ _ (malloc_class n)); [apply In_ziota; unfold kLargestClassID, tc in HC; clear -HC; cbn; lia|].
    apply andb_true_iff. unfold region_beg, region_of, kRegionSize. rewrite Hab in Hx. split; [apply Z.leb_le| apply Z.ltb_lt]; clear -Hx Hk Hk1 RG1 CS; nia.
  - destruct B as (sc & Hsc & Eab & Esz). destruct (WS3 sc Hsc) as (MOD & AM & CE & POS & MODS & SSP & RSV).
    unfold map_size in Esz. pose proof NEEDF as (N1 & N2 & N3 & N4). pose proof (rz_size_pos n) as RZP. fold (trz n) in RZP.
    assert (RU : needed n <= round_up (needed n) kPageSize /\ round_up (needed n) kPageSize mod 4096 = 0 /\ round_up (needed n) kPageSize < needed n + 4096).
    { unfold round_up, kPageSize. clear -N1 N2 RZP Hn. Z.div_mod_to_equations. lia. }
    destruct RU as (U1 & U2 & U3). unfold kPageSize, app_mem in *.
    split; [rewrite <- Eab; clear -MOD; Z.div_mod_to_equations; lia|].
    split; [clear -U2; Z.div_mod_to_equations; lia|]. split; [exact U1|].
    split.
    { destruct AK as [mo K]. destruct (ak_sec _ _ _ K sc Hsc) as [_ (INS & _)]. destruct INS as (e & _ & LOe & _). unfold elo in LOe.
      pose proof (bv_unsigned_in_range _ (fst e)) as BR. rewrite <- Eab. clear -LOe BR. lia. }
    split; [rewrite <- Eab; rewrite Esz in CE; clear -CE; lia|].
    split; [rewrite <- Eab; rewrite Esz in AM; clear -AM POS U1 N1 N2 Hn RZP; lia|].
    intros x Hx. apply orb_true_iff. right. unfold in_some_sec_map. apply existsb_exists. exists sc. split; [exact Hsc|].
    apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; rewrite <- Eab in Hx; rewrite ?Esz; clear -Hx; lia.
Qed.

(* [comment removed for export] *)
Lemma cm_geo : cm_alloc_beg cm = ab /\ cm_user_beg cm = ub /\ cm_chunk_beg cm = cb /\ cm_n cm = req n /\ cm_state cm = CAllocated id
  /\ blk_lo cm = ab /\ blk_hi s' cm = ab + span.
Proof.
  unfold tcm, tub, tcb, trz, tspan, tprim, cm_user_beg, cm_chunk_beg, blk_lo, blk_hi, rz_size. cbn [cm_alloc_beg cm_rz_log cm_n cm_prim cm_state].
  repeat split; try reflexivity. destruct (from_primary n); [reflexivity|]. rewrite REQ. unfold map_size, kPageSize. lia.
Qed.

(* [comment removed for export] *)
Lemma Sh_tail : forall x, Sh E s' x = if (ab <=? x) && (x <? ab + span) then Some (chunk_shadow cm x) else Sh E s x.
Proof.
  intros x. pose proof cm_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
  assert (NEW : as_chunks s' !! cb = Some cm) by (rewrite tl_chunks; apply lookup_insert_eq).
  destruct ((ab <=? x) && (x <? ab + span)) eqn:IN.
  - apply andb_prop in IN as [I1 I2]. apply Z.leb_le in I1. apply Z.ltb_lt in I2.
    apply (block_Sh E [] [] s' cb cm x WF' NEW). rewrite G6, G7. clear -I1 I2. lia.
  - assert (OUT : ~ (ab <= x < ab + span)).
    { intros [H1 H2]. assert (C : (ab <=? x) && (x <? ab + span) = true) by (apply andb_true_intro; split; [apply Z.leb_le| apply Z.ltb_lt]; lia). rewrite C in IN. discriminate. }
    unfold Sh.
    assert (RM : in_some_region_map E s' x = in_some_region_map E s x) by (unfold in_some_region_map, region_of, get_region; rewrite tl_regions; reflexivity).
    assert (SM : in_some_sec_map s' x = in_some_sec_map s x) by (unfold in_some_sec_map; rewrite tl_sec; reflexivity).
    rewrite RM, SM.
    assert (FC : find_chunk s' x = find_chunk s x).
    { destruct (find_chunk s' x) as [cm'|] eqn:F1.
      - destruct (find_chunk_some _ _ _ F1) as (cb0 & Hcb & Hx). rewrite tl_chunks in Hcb.
        destruct (decide (cb0 = cb)) as [->|NE].
        + rewrite lookup_insert_eq in Hcb. injection Hcb as <-. exfalso. apply OUT. rewrite G1 in Hx. unfold block_span in Hx. unfold tcm in Hx at 1.
          cbn [cm_prim] in Hx. unfold tspan. revert Hx. unfold tprim. destruct (from_primary n); [intros Hx; exact Hx|].
          rewrite G4, REQ. unfold map_size. intros Hx. lia.
        + rewrite lookup_insert_ne in Hcb by congruence. symmetry. apply (find_chunk_block E [] [] s cb0 cm' x WF Hcb). rewrite blk_hi_span. unfold blk_lo. exact Hx.
      - destruct (find_chunk s x) as [cm0|] eqn:F0; [| reflexivity].
        destruct (find_chunk_some _ _ _ F0) as (cb0 & Hcb & Hx).
        assert (Hcb' : as_chunks s' !! cb0 = Some cm0).
        { rewrite tl_chunks. rewrite lookup_insert_ne; [exact Hcb|]. intros E1. rewrite E1 in FRESH. rewrite FRESH in Hcb. discriminate. }
        rewrite (find_chunk_block E [] [] s' cb0 cm0 x WF' Hcb') in F1; [discriminate|]. rewrite blk_hi_span. unfold blk_lo. exact Hx. }
    rewrite FC. reflexivity.
Qed.


(* [comment removed for export] *)
Lemma fp_range : forall a, arep_fp E (DepotFP E) s a -> 0 <= a < alloc_ceiling.
Proof.
  intros a Ha. split; [| exact (fp_below_ceiling E (DepotFP E) [] [] IMG_IN (DepotFP_where E) s a WF BS Ha)].
  destruct (fp_locate E (DepotFP E) [] [] IMG_IN (DepotFP_where E) s a WF BS Ha) as [X|[[X _]|[X _]]].
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
Lemma win_band : forall a, kShadowBase + ab / 8 <= a < kShadowBase + (ab + span + 7) / 8 -> kLowAppEnd < a < kHighMemBeg.
Proof.
  intros a Ha. pose proof alloc_ceiling_range as CR. pose proof BLKF as (B1 & B2 & B3 & B0 & B4 & B5 & _). pose proof NEEDF as (N1 & _). pose proof RZF as (R1 & _).
  pose proof (rounded_ge n) as (Q1 & _).
  rewrite kLowAppEnd_val, kHighMemBeg_val in *. unfold kShadowBase in Ha. clear -Ha B0 B4 B5 B3 N1 R1 Q1 Hn CR. Z.div_mod_to_equations. lia.
Qed.
(* [comment removed for export] *)
Lemma AG_app : forall a, arep_fp E (DepotFP E) s a -> ~ (T <= a < T + 4096) -> (a < kLowAppEnd \/ kHighMemBeg <= a) -> m' (wa a) = m (wa a).
Proof.
  intros a Ha NT R. pose proof (fp_range a Ha) as BC. pose proof alloc_ceiling_range as CR.
  apply AG; [clear -BC CR; lia|]. unfold FPWt. intros [X|[X|[X|[X|X]]]].
  - clear -X BC LO. lia.
  - exact (NFP a X Ha).
  - pose proof (win_band a X). clear -H R. lia.
  - unfold kThrStats in X. clear -X NT. lia.
  - destruct large eqn:LG; unfold kThrStats in X.
    + clear -X NT. lia.
    + pose proof (CID32 LG) as CID. clear -X NT CID. lia.
Qed.
(* [comment removed for export] *)
Lemma AGimg : forall a, in_ranges (arep_img_ranges E) a -> m' (wa a) = m (wa a).
Proof.
  intros a (r & Hr & R). pose proof (IMG_LOW r ltac:(apply in_app_iff; left; exact Hr)) as [L1 L2]. pose proof Tpl as [[T1 T2] T3].
  apply AG_app; [left; exists r; split; [exact Hr| exact R]| clear -R L1 L2 T1 T2; lia| left; rewrite kLowAppEnd_val; clear -R L2; lia].
Qed.
Lemma AGri : forall a, ae_region_info E <= a < ae_region_info E + kRegSize * kNumClasses -> m' (wa a) = m (wa a).
Proof.
  intros a Ha. pose proof (proj1 WF) as (E1 & E2 & E3 & E4 & _).
  apply AG_app; [right; left; exact Ha| | right; unfold ae_region_info, kSpaceSize in *; clear -Ha E2 E3; lia].
  intros HT. destruct (Tpage_apart a HT) as (NR & _). apply NR. unfold ae_region_info, kRegSize, kNumClasses, kSpaceSize in *. clear -Ha E3 E4. lia.
Qed.
Lemma AGfa : forall a c', 0 <= c' < kNumClasses -> free_array SB c' <= a < free_array SB c' + rg_mapped_fa (region_of s c') -> m' (wa a) = m (wa a).
Proof.
  intros a c' Hc Ha. pose proof (proj1 WF) as (E1 & E2 & E3 & E4 & _).
  assert (RM : in_some_region_map E s a = true).
  { unfold in_some_region_map. apply Bool.orb_true_iff. right. apply existsb_exists. exists c'. split; [apply In_ziota; unfold kNumClasses in Hc; lia|].
    apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; lia. }
  pose proof (region_map_in_space E [] [] s a WF RM) as SP.
  apply AG_app; [do 3 right; left; exists c'; split; [exact Hc| exact Ha]| | right; unfold kSpaceSize in *; clear -SP E2 E3; lia].
  intros HT. destruct (Tpage_apart a HT) as (NR & _). apply NR. unfold kSpaceSize in *. clear -SP E3 E4. lia.
Qed.
Lemma AGptr : forall a, ae_ptr_array E <= a < ae_ptr_array E + 8 * kChunksBlockCount -> m' (wa a) = m (wa a).
Proof.
  intros a Ha. pose proof (proj1 WF) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & _). unfold app_mem in E16. unfold kChunksBlockCount in Ha.
  apply AG_app; [do 4 right; left; unfold kChunksBlockCount; exact Ha| | clear -Ha E16; lia].
  intros HT. destruct (Tpage_apart a HT) as (_ & NP & _). apply NP. clear -Ha. lia.
Qed.
Lemma AGsec : forall a sc, In sc (as_sec s) -> sc_map_beg sc <= a < sc_map_beg sc + 32 -> m' (wa a) = m (wa a).
Proof.
  intros a sc Hsc Ha. pose proof WF as (_ & _ & _ & _ & _ & (_ & _ & S3 & _) & _). destruct (S3 sc Hsc) as (_ & AM & _ & POS & MODS & _).
  pose proof (AsanRepFrame.pos_mod_ge E (sc_map_size sc) kPageSize POS MODS ltac:(unfold kPageSize; lia)) as GE. unfold app_mem, kPageSize in *.
  apply AG_app; [do 5 right; left; exists sc; split; [exact Hsc| exact Ha]| | clear -Ha AM GE; lia].
  intros HT. destruct (Tpage_apart a HT) as (_ & _ & NS & _). apply (NS sc Hsc). clear -Ha GE. lia.
Qed.
Lemma AGcm : forall a cb0 cm0, as_chunks s !! cb0 = Some cm0 -> chunk_meta_fp cm0 a -> m' (wa a) = m (wa a).
Proof.
  intros a cb0 cm0 Hcm Ha. pose proof (proj1 WF) as (E1 & E2 & E3 & E4 & _).
  pose proof (chunk_meta_in_block E [] [] s cb0 cm0 a WF Hcm Ha) as [BL BU].
  destruct (block_where E [] [] s cb0 cm0 WF Hcm) as [(J1 & J2 & _)|(sc & Hsc & _ & L1 & L2)].
  - apply AG_app; [do 6 right; left; exists cb0, cm0; split; [exact Hcm| exact Ha]| | right; clear -BL J1 E2 E3; lia].
    intros HT. destruct (Tpage_apart a HT) as (NR & _). apply NR. unfold kSpaceSize in *. clear -BL BU J1 J2 E3 E4. lia.
  - pose proof WF as (_ & _ & _ & _ & _ & (_ & _ & S3 & _) & _). destruct (S3 sc Hsc) as (_ & AM & _). unfold app_mem, kPageSize in *.
    apply AG_app; [do 6 right; left; exists cb0, cm0; split; [exact Hcm| exact Ha]| | clear -BL BU L1 L2 AM; lia].
    intros HT. destruct (Tpage_apart a HT) as (_ & _ & NS & _). apply (NS sc Hsc). clear -BL BU L1 L2. lia.
Qed.
Lemma AGbat : forall a b, In b (as_tq s ++ as_gq s) -> b_addr b <= a < b_addr b + 24 + 8 * kBatchCap -> m' (wa a) = m (wa a).
Proof.
  intros a b Hb Ha. pose proof WF as (WE & WR & _ & _ & WQ & _). pose proof WE as (E1 & E2 & E3 & E4 & _).
  destruct (batch_block E [] s b WQ ltac:(unfold all_batches; rewrite app_assoc; apply in_app_iff; left; exact Hb)) as (CV & _).
  assert (HB24 : 1 <= kBatchClass <= kLargestClassID) by (unfold kBatchClass, kLargestClassID; lia).
  pose proof (carved_in_space E s kBatchClass _ HB24 WR CV) as [J1 J2]. change (class_size kBatchClass) with 8192 in J2. unfold kBatchCap, kRegionSize, kSpaceSize in *.
  apply AG_app; [do 7 right; left; exists b; split; [exact Hb| exact Ha]| | right; clear -Ha J1 E2 E3; lia].
  intros HT. destruct (Tpage_apart a HT) as (NR & _). apply NR. clear -Ha J1 J2 E3 E4. lia.
Qed.
Lemma AGdep : forall a, DepotFP E s a -> m' (wa a) = m (wa a).
Proof.
  intros a Ha. pose proof Tpl as [[T1 T2] T3]. assert (FPa : arep_fp E (DepotFP E) s a) by (do 8 right; left; exact Ha).
  destruct (DepotFP_where E s a Ha) as [(r & Hr & R)|[(b & Hb & R)|(b & Hb & R)]].
  - pose proof (IMG_LOW r ltac:(apply in_app_iff; right; exact Hr)) as [L1 L2].
    apply AG_app; [exact FPa| clear -R L1 L2 T1 T2; lia| left; rewrite kLowAppEnd_val; clear -R L2; lia].
  - pose proof (BS b kDepotNodeBlockBytes (or_introl (conj Hb eq_refl))) as (AM & _). unfold app_mem in AM.
    apply AG_app; [exact FPa| | clear -R AM; lia]. intros HT. destruct (Tpage_apart a HT) as (_ & _ & _ & NB & _). exact (NB b kDepotNodeBlockBytes (or_introl (conj Hb eq_refl)) R).
  - pose proof (BS b kStoreBlockBytes (or_intror (conj Hb eq_refl))) as (AM & _). unfold app_mem in AM.
    apply AG_app; [exact FPa| | clear -R AM; lia]. intros HT. destruct (Tpage_apart a HT) as (_ & _ & _ & NB & _). exact (NB b kStoreBlockBytes (or_intror (conj Hb eq_refl)) R).
Qed.
(* [comment removed for export] *)
Lemma sh_cell_band : forall g v, Sh E s (8 * g) = Some v -> kLowAppEnd < kShadowBase + g < kHighMemBeg.
Proof.
  intros g v Hg.
  assert (GR : 0 <= 8 * g < 2^47).
  { pose proof WF as WF2. pose proof alloc_ceiling_range as CR. unfold Sh in Hg.
    destruct (in_some_region_map E s (8 * g)) eqn:RM.
    - pose proof (region_map_in_space E [] [] s (8 * g) WF2 RM) as SP. pose proof (proj1 WF2) as (E1 & E2 & E3 & E4 & E5 & _).
      unfold kSpaceSize in *. clear -SP E2 E3 E4 E5 CR. rewrite kHighMemBeg_val in E2. lia.
    - destruct (in_some_sec_map s (8 * g)) eqn:SM.
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
Lemma AGsh_out : forall g v, Sh E s (8 * g) = Some v -> (8 * g + 8 <= ab \/ ab + span <= 8 * g) -> m' (wa (kShadowBase + g)) = m (wa (kShadowBase + g)).
Proof.
  intros g v Hg OUT. pose proof (sh_cell_band g v Hg) as B. pose proof BLKF as (B1 & B2 & B3 & B0 & B4 & B5 & _). pose proof alloc_ceiling_range as CR.
  pose proof (proj1 WF) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & _). unfold app_mem in E14.
  apply AG; [rewrite kLowAppEnd_val, kHighMemBeg_val in B; clear -B; lia|]. unfold FPWt. intros [X|[X|[X|[X|X]]]].
  - rewrite kHighMemBeg_val in B. clear -X B LO CR. lia.
  - clear -X B B5. lia.
  - unfold kShadowBase in X, B. clear -X OUT B1 B2. Z.div_mod_to_equations. lia.
  - unfold kThrStats in X. clear -X B E14. lia.
  - destruct large eqn:LG; unfold kThrStats in X; [clear -X B E14; lia|]. pose proof (CID32 LG) as CID. clear -X B E14 CID. lia.
Qed.
(* [comment removed for export] *)
Lemma AGthr_pt : forall z, T <= z < T + 4096 -> ~ (T + kThrStats <= z < T + kThrStats + 24) ->
  ~ (if large then T + kThrStats + 104 <= z < T + kThrStats + 112 else T + kThrStats + 112 + 8 * cid <= z < T + kThrStats + 112 + 8 * cid + 8) ->
  in_ranges (arep_thr_ranges E) z -> m' (wa z) = m (wa z).
Proof.
  intros z Hz N1 N2 FPz. pose proof Tpl as [[T1 T2] T3]. pose proof alloc_ceiling_range as CR.
  pose proof (proj1 WF) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & _). unfold app_mem in E14.
  assert (FP' : arep_fp E (DepotFP E) s z) by (do 2 right; left; exact FPz).
  apply AG; [clear -Hz T1 T3 CR; lia|]. unfold FPWt. intros [X|[X|[X|[X|X]]]].
  - clear -X Hz T3 LO. lia.
  - exact (NFP z X FP').
  - pose proof (win_band z X) as W. clear -W Hz E14. lia.
  - exact (N1 X).
  - exact (N2 X).
Qed.
(* [comment removed for export] *)
Lemma thr_rng : forall k z r, nth_error (arep_thr_ranges E) k = Some r -> fst r <= z < fst r + snd r -> in_ranges (arep_thr_ranges E) z /\ T <= z < T + 4096.
Proof.
  intros k z r Hk Hz. split; [exists r; split; [eapply nth_error_In; exact Hk| exact Hz]|].
  unfold arep_thr_ranges in Hk. unfold kThrStackTop, kThrQCache, kThrCache, kPerClassSize, kNumClasses, kThrCacheStats, kThrStats, kThrUnwinding in Hk.
  do 7 (destruct k as [|k]; [cbn in Hk; injection Hk as <-; cbn [fst snd] in Hz; clear -Hz; lia|]). destruct k; cbn in Hk; discriminate.
Qed.
Ltac thr_pt k := intros z Hz; unfold kThrStackTop, kThrQCache, kThrCache, kPerClassSize, kNumClasses, kThrCacheStats, kThrStats, kThrUnwinding in Hz; cbn in Hz;
  destruct (thr_rng k z _ eq_refl ltac:(cbn [fst snd]; unfold kThrStackTop, kThrQCache, kThrCache, kPerClassSize, kNumClasses, kThrCacheStats, kThrStats, kThrUnwinding; lia)) as [FPz Tz];
  apply (AGthr_pt z Tz); [unfold kThrStats; lia| let LG := fresh "LG" in let CI := fresh "CI" in destruct large eqn:LG; unfold kThrStats; [lia| pose proof (CID32 LG) as CI; lia]| exact FPz].

(* [comment removed for export] *)
Lemma repD_tail : arep_thread segs E s' m'.
Proof.
  pose proof REPX as (_ & _ & _ & RD & _). destruct RD as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8).
  unfold arep_thread. rewrite tl_tq, tl_tq_bytes, tl_cache_allocated, tl_cache_mapped, tl_ts.
  pose proof CID32 as CID.
  split; [eapply rw_cells_agree'; [| exact D1]; cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]; thr_pt 0%nat|].
  split; [eapply rw_cells_agree'; [| exact D2]; cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]; thr_pt 1%nat|].
  split; [eapply rw_cells_agree'; [| exact D3]; cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]; thr_pt 2%nat|].
  split.
  { intros c' Hc'. destruct (D4 c' Hc') as (X1 & junk & X2 & L). unfold percls_cells in *. rewrite tl_get_cache, tl_cache_inited. unfold kNumClasses in Hc'. split.
    - eapply rw_cells_agree'; [| exact X1]. cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]. thr_pt 3%nat.
    - exists junk. split; [| exact L]. eapply u32arr_agree; [| exact X2]. rewrite length_app, length_map. thr_pt 3%nat. }
  split; [eapply rw_cells_agree'; [| exact D5]; cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]; thr_pt 4%nat|].
  split.
  { (* [comment removed for export] *)
    apply u64arr_of_cells.
    - eapply wr_at_transport; [| exact WM]. destruct D6 as [_ W6]. unfold tstats_words in W6 |- *. rewrite !length_map in W6 |- *. exact W6.
    - intros i w Hi. apply rh_split with (cs1 := [C8 (zw (ts_mallocs t + 1))]) in NC_st as X. destruct X as [Y0 X].
      apply rh_split with (cs1 := [C8 (zw (ts_malloced t + req n))]) in X. destruct X as [Y1 Y2]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Y1, Y2.
      destruct i as [|[|[|i]]].
      + cbn in Hi. injection Hi as <-. rewrite Z.mul_0_r, Z.add_0_r. exact Y0.
      + cbn in Hi. injection Hi as <-. exact Y1.
      + cbn in Hi. injection Hi as <-. replace (T + kThrStats + 8 * Z.of_nat 2) with (T + kThrStats + 8 + 8) by lia. exact Y2.
      + pose proof (nth_error_lt _ _ _ Hi) as IL. unfold tstats_words in IL. rewrite length_map in IL. cbn [length] in IL.
        destruct (Nat.eq_dec i 10) as [->|NE].
        * (* [comment removed for export] *) cbn in Hi. destruct large eqn:LG.
          -- injection Hi as <-. replace (T + kThrStats + 8 * Z.of_nat 13) with (T + kThrStats + 104) by lia. exact (NC_lg eq_refl).
          -- injection Hi as <-. assert (OLD : nth_error (tstats_words t) 13 = Some (zw (ts_malloc_large t))) by reflexivity.
             eapply rw_cells_agree'; [| exact (u64arr_cell segs m _ _ _ _ D6 OLD)]. cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul].
             intros z Hz. unfold kThrStats in Hz; cbn in Hz. destruct (thr_rng 5%nat z _ eq_refl ltac:(cbn [fst snd]; unfold kThrStats; lia)) as [FPz Tz].
             apply (AGthr_pt z Tz); [unfold kThrStats; lia| rewrite LG; unfold kThrStats; pose proof (CID eq_refl) as CI; lia| exact FPz].
        * assert (OLD : nth_error (tstats_words t) (S (S (S i))) = Some w).
          { unfold tstats_words in Hi |- *. rewrite nth_error_map in Hi |- *.
            do 11 (destruct i as [|i]; [cbn in Hi |- *; first [exact Hi | exfalso; apply NE; reflexivity] |]). destruct i; cbn in Hi; discriminate. }
          eapply rw_cells_agree'; [| exact (u64arr_cell segs m _ _ _ _ D6 OLD)]. cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul].
          intros z Hz. unfold kThrStats in Hz; cbn in Hz. destruct (thr_rng 5%nat z _ eq_refl ltac:(cbn [fst snd]; unfold kThrStats; lia)) as [FPz Tz].
          apply (AGthr_pt z Tz); [unfold kThrStats; lia| destruct large eqn:LG; unfold kThrStats; [lia| pose proof (CID eq_refl) as CI; lia]| exact FPz]. }
  split.
  { (* [comment removed for export] *)
    apply u64arr_of_cells.
    - eapply wr_at_transport; [| exact WM]. destruct D7 as [_ W7]. rewrite length_map in *. exact W7.
    - intros i w Hi. rewrite nth_error_map in Hi.
      assert (IL : (i < 32)%nat) by (destruct (Nat.lt_ge_cases i 32) as [L|L]; [exact L|]; rewrite (proj2 (nth_error_None _ _)) in Hi; [discriminate|]; rewrite length_ziota; lia).
      rewrite nth_error_ziota in Hi by exact IL. cbn [option_map] in Hi. injection Hi as <-. rewrite Z.add_0_l.
      cbn [ts_by_size ts_on_malloc].
      pose proof (u64arr_cell segs m _ _ i _ D7 ltac:(rewrite nth_error_map, nth_error_ziota by exact IL; reflexivity)) as X. rewrite Z.add_0_l in X.
      destruct large eqn:LG.
      + eapply rw_cells_agree'; [| exact X]. cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul].
        intros z Hz. unfold kThrStats in Hz; cbn in Hz. destruct (thr_rng 5%nat z _ eq_refl ltac:(cbn [fst snd]; unfold kThrStats; lia)) as [FPz Tz].
        apply (AGthr_pt z Tz); [unfold kThrStats; lia| rewrite LG; unfold kThrStats; lia| exact FPz].
      + destruct (decide (Z.of_nat i = cid)) as [EQ|NE].
        * rewrite EQ. rewrite lookup_insert_eq. replace (match ts_by_size t !! cid with Some k => k + 1 | None => 1 end) with (match ts_by_size t !! cid with Some v => v | None => 0 end + 1) by (destruct (ts_by_size t !! cid); lia). exact (NC_by eq_refl).
        * rewrite lookup_insert_ne by congruence.
          eapply rw_cells_agree'; [| exact X]. cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul].
          intros z Hz. unfold kThrStats in Hz; cbn in Hz. destruct (thr_rng 5%nat z _ eq_refl ltac:(cbn [fst snd]; unfold kThrStats; lia)) as [FPz Tz].
          apply (AGthr_pt z Tz); [unfold kThrStats; lia| rewrite LG; unfold kThrStats; pose proof (CID eq_refl) as CI; lia| exact FPz]. }
  eapply rw_cells_agree'; [| exact D8]. cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]. thr_pt 6%nat.
Qed.
(* [comment removed for export] *)
Lemma repF_tail : arep_chunks segs s' m'.
Proof.
  pose proof REPX as (_ & _ & _ & _ & _ & RF & _). pose proof (frameF' segs s m m' AGcm RF) as RF'.
  pose proof cm_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7). pose proof RZF as (R1 & R2 & R3).
  intros cb0 cm0 Hcm. rewrite tl_chunks in Hcm.
  destruct (decide (cb0 = cb)) as [->|NE].
  - rewrite lookup_insert_eq in Hcm. injection Hcm as <-. split; [symmetry; exact G3|].
    split; [| split; [| rewrite G5; exact I]].
    + destruct NC_hdr as (hb1 & HB & HH). exists hb1. split; [exact HB|]. rewrite G3, G4, G5. cbn [hdr_state hdr_alloc_id]. exact HH.
    + intros BIG. rewrite G1, G3. apply NC_mag. rewrite R2. unfold tcm in BIG. cbn [cm_rz_log] in BIG. exact BIG.
  - rewrite lookup_insert_ne in Hcm by congruence. exact (RF' cb0 cm0 Hcm).
Qed.

(* [comment removed for export] *)
Lemma repJ_tail : arep_shadow segs E s' m'.
Proof.
  pose proof REPX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & RJ). pose proof BLKF as (B1 & B2 & _).
  intros g v Hg. rewrite Sh_tail in Hg.
  destruct ((ab <=? 8 * g) && (8 * g <? ab + span)) eqn:IN.
  - apply andb_prop in IN as [I1 I2]. apply Z.leb_le in I1. apply Z.ltb_lt in I2. injection Hg as <-. apply NC_sh. clear -I1 I2. lia.
  - assert (OUT : 8 * g + 8 <= ab \/ ab + span <= 8 * g).
    { destruct (Z_lt_le_dec (8 * g) ab) as [X|X]; [left; clear -X B1; Z.div_mod_to_equations; lia| right].
      destruct (Z_lt_le_dec (8 * g) (ab + span)) as [Y|Y]; [| exact Y].
      exfalso. assert (C' : (ab <=? 8 * g) && (8 * g <? ab + span) = true) by (apply andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia). rewrite C' in IN. discriminate. }
    eapply rw_cells_agree'; [| exact (RJ g v Hg OUT)]. cbn. intros x Hx. replace x with (kShadowBase + g) by (clear -Hx; lia).
    exact (AGsh_out g v Hg OUT).
Qed.

(* [comment removed for export] *)
Theorem ARep_tail : AREP s' m'.
Proof.
  pose proof REPX as (RA & RB & RC & RD & RE & RF & RG & RH & RI & RJ).
  split; [apply (frameA' segs E s' m m' AGimg); unfold tail_st; destruct s; exact RA|].
  split; [apply (frameB' segs E s' m m' AGri); unfold tail_st; destruct s; exact RB|].
  split; [apply (frameC' segs E s' m m' WM); [intros a c' Hc Ha; apply (AGfa a c' Hc); rewrite tl_region_of in Ha; exact Ha| unfold tail_st; destruct s; exact RC]|].
  split; [exact repD_tail|].
  split; [apply (frameE' segs E s' m m' WM AGptr); [intros a sc Hsc; apply AGsec; rewrite tl_sec in Hsc; exact Hsc| unfold tail_st; destruct s; exact RE]|].
  split; [exact repF_tail|].
  split.
  { destruct RG as [RG1 RG2]. apply (frameG' segs s' m m').
    - intros a b Hb. rewrite tl_tq, tl_gq in Hb. exact (AGbat a b Hb).
    - split; [rewrite tl_tq| rewrite tl_gq]; eapply arep_batch_list_indep; eassumption. }
  split; [apply (frameH' segs E s' m m' WM); [intros a Ha; apply AGdep; revert Ha; unfold tail_st; destruct s; intros Ha; exact Ha| unfold tail_st; destruct s; exact RH]|].
  split; [apply (frameI' segs E s' m m' WM AGimg); unfold tail_st; destruct s; exact RI|].
  exact repJ_tail.
Qed.
End TAIL.

(* [comment removed for export] *)
Lemma chunk_shadow_alloc : forall n ab id x, let cm := tcm n ab id in let ub := tub n ab in
  chunk_shadow cm x =
    if x <? ub then kAsanHeapLeftRedzoneMagic
    else if x <? ub + (req n / 8) * 8 then 0
    else if x <? ub + req n then req n mod 8
    else kAsanHeapLeftRedzoneMagic.
Proof.
  intros n ab id x. cbv zeta. unfold chunk_shadow, tcm, tub, trz, rz_size, cm_user_beg. cbn [cm_state cm_n cm_alloc_beg cm_rz_log]. reflexivity.
Qed.
End RT.
End RC__1.
